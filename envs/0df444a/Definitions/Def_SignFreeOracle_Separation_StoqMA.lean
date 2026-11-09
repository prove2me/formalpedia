-- Prove2me | Definitions.Def_SignFreeOracle_Separation_StoqMA
-- name    : SignFreeOracle_Separation_StoqMA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:58.435101+00:00
-- url     : https://prove2.me/theorems/0fd7db94-c6da-49cc-a3cf-2f3f39fed88f
-- title:
--   Operational oracle StoqMA with arbitrary complex witnesses
-- statement:
--   For a fixed Boolean oracle $O$, a promise problem belongs to $\mathrm{StoqMA}^O$ when one uniform restricted circuit family has polynomial width and gate count, and has polynomial-time computable thresholds $a,b$ satisfying
--   $$\tfrac12\le b(m)<a(m)\le1,\qquad a(m)-b(m)\ge1/g(m),\qquad g(m)>0.$$
--   Here $g$ is one fixed natural-coefficient polynomial. Completeness supplies a normalized complex witness on each YES input with acceptance at least $a(m)$; soundness bounds acceptance by $b(m)$ for every normalized complex witness on each NO input. Real thresholds are computed by finite machines to precision $2^{-k}$ in time polynomial in $m+k$, with $k$ unary, using signed binary fixed-point output. The definition takes the union over all such efficient thresholds. It does not assume error amplification or restrict witness phases.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Definition 2.2, p. 7 (PDF p. 7)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_SignFreeOracle_Separation_Circuit

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- A signed dyadic number: sign bit followed by a binary fixed-point mantissa with
half its places before the point. Padding permits every requested precision in polynomial length. -/
noncomputable def dyadic (s : Str) : ℝ :=
  (if s.headD false then -1 else 1) *
    ∑ i ∈ Finset.range s.tail.length,
      if s.tail.getD i false then (2 : ℝ) ^ ((s.tail.length / 2 : ℤ) - i - 1) else 0

/-- Polynomial-time computability of a real threshold on unary lengths, with precision supplied
in unary. The output approximates the real value within 2^{-k}. -/
def EfficientThreshold (f : ℕ → ℝ) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ n k,
    M.result (fun _ => false)
      (tup [List.replicate n true, List.replicate k true]) (p.eval (n + k)) ≠ none ∧
    |dyadic (M.output (fun _ => false)
      (tup [List.replicate n true, List.replicate k true]) (p.eval (n + k))) - f n| ≤
        (2 : ℝ) ^ (-(k : ℤ))

/-- Definition 2.2, p. 7. Soundness covers all normalized complex witnesses, including phases.
No intermediate measurement, arbitrary unitary, or phase oracle is available. -/
def StoqMA (O : Oracle) : Set PromiseProblem :=
  {L | ∃ (a b : ℕ → ℝ) (gap size : Polynomial ℕ) (C : ∀ m, StoqCircuit m),
    EfficientThreshold a ∧ EfficientThreshold b ∧ UniformStoq C ∧
    (∀ m, 0 < gap.eval m ∧ (1 / 2 : ℝ) ≤ b m ∧ b m < a m ∧ a m ≤ 1 ∧
      ((gap.eval m : ℕ) : ℝ)⁻¹ ≤ a m - b m ∧
      m + (C m).witness + (C m).zeros + (C m).plus ≤ size.eval m ∧
      (C m).gates.length ≤ size.eval m) ∧
    ∀ x : Str,
      (x ∈ L.yes → ∃ ψ : QState (C x.length).witness, Normalized ψ ∧
        a x.length ≤ (C x.length).accept O (fun i => x.get i) ψ) ∧
      (x ∈ L.no → ∀ ψ : QState (C x.length).witness, Normalized ψ →
        (C x.length).accept O (fun i => x.get i) ψ ≤ b x.length)}

end SignFreeOracle.Separation



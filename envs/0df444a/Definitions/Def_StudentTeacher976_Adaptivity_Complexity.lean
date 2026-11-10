-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_Complexity
-- name    : StudentTeacher976_Adaptivity_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:09:29.383941+00:00
-- url     : https://prove2.me/theorems/2ef1e836-67ba-4be5-a095-adf5549a98cf
-- title:
--   Oracle computation, hierarchy levels, advice, and admissible resources
-- statement:
--   Let a word be a finite binary string, and let a language be a set of words over all lengths. The polynomial hierarchy is represented by alternating polynomial-length quantifiers over finite polynomial-time oracle machines, with the external oracle empty. Its zeroth level is ordinary polynomial time.
--
--   For each natural level $i$, uniform string computation and decision use a single finite deterministic machine, one fixed oracle language in $\Sigma_i^p$, and one polynomial clock valid on every string. The nonuniform decision class uses one additional polynomial advice bound and one advice string $a(n)$ shared by every $n$-bit input:
--
--   $$
--   \Delta_{i+1}^p=\mathrm P^{\Sigma_i^p},\qquad
--   \Delta_{i+1}^p/\mathrm{poly}=\{L:\text{one such machine decides }L(x)\text{ using }a(|x|)\}.
--   $$
--
--   The advice need not be computable. The round functions are polynomial-time, nondecreasing, eventually larger than every constant, and bounded by $m^{1-\varepsilon}$ for some real $\varepsilon>0$ at all positive lengths. Query functions are polynomial-time, positive, and bounded by one polynomial; they need not be monotone or unbounded. Length functions receive numerical lengths in unary. Resources at the empty input use their length-one value.
--
--   These definitions provide the operational complexity and resource interface for the separation; no hardness or game-success property is included in machine data.
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), §1.2.1, pp.6–7 (PDF pp.6–7); Theorem 1.4, p.7 (PDF p.7); Appendix A, pp.39–40 (PDF pp.39–40); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_Oracle
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_MantriCVQ_SigmaPi
import Definitions.Def_AvgPHETH_AltLen

open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity

abbrev Word := List Bool
abbrev Language := Set Word
abbrev SearchRelation := Word → Word → Prop

/-- Ordinary polynomial-hierarchy levels, including Σ₀ = P; the external oracle is empty.
Ježil–Tsintsilidas, STOC 2027 submission #976 (October 2026), §1.2.1, pp.6–7. -/
def Sigma (i : ℕ) : Set Language := MantriCVQ.SigmaPi (fun _ => false) true i

/-- One finite deterministic transducer, one fixed Σᵖᵢ oracle and one polynomial clock,
valid on every string, including malformed structured inputs. §1.2.1, pp.6–7. -/
def InFP (i : ℕ) (f : Word → Word) : Prop :=
  ∃ (O : Oracle) (M : OTM) (clock : Polynomial ℕ),
    {x | O x = true} ∈ Sigma i ∧
    ∀ x, (M.result O x (clock.eval x.length)).isSome ∧
      M.output O x (clock.eval x.length) = f x

/-- Δᵖᵢ₊₁ = P^(Σᵖᵢ), with an actual finite machine and a clock on every string. -/
def Delta (i : ℕ) : Set Language :=
  {L | ∃ (O : Oracle) (M : OTM) (clock : Polynomial ℕ),
    {x | O x = true} ∈ Sigma i ∧
    (∀ s, (M.result O s (clock.eval s.length)).isSome) ∧
    ∀ x, x ∈ L ↔ M.result O x (clock.eval x.length) = some true}

/-- Δᵖᵢ₊₁/poly: the machine, oracle, time/advice bounds and advice function are fixed
before all inputs. The same a(n) is used on every n-bit string; a need not be computable.
Theorem 1.4, p.7. The clock measures the whole encoded input, not the numerical value n. -/
def DeltaPoly (i : ℕ) : Set Language :=
  {L | ∃ (O : Oracle) (M : OTM) (clock bound : Polynomial ℕ) (a : ℕ → Word),
    {x | O x = true} ∈ Sigma i ∧
    (∀ s, (M.result O s (clock.eval s.length)).isSome) ∧
    (∀ n, (a n).length ≤ bound.eval n) ∧
    ∀ x, x ∈ L ↔ M.result O (tup [x, a x.length])
      (clock.eval (tup [x, a x.length]).length) = some true}

/-- Polynomial-time length functions: numerical lengths are supplied in unary, and output
is unary. This is the raw-length convention of §3 p.19 and Appendix A pp.39–40. -/
def PolyTimeLength (r : ℕ → ℕ) : Prop :=
  InFP 0 (fun x => List.replicate (r x.length) true)

/-- Resource values on the empty input use their value at length one. No bound 1 ≤ r(0) ≤ 0
is imposed. Every positive length keeps its exact source round/query count. -/
def resource (r : ℕ → ℕ) (n : ℕ) : ℕ := r (max 1 n)

/-- Theorem 1.4's unbounded nondecreasing sublinear round functions. Strict increase on ℕ
would contradict the sublinear bound; Appendix A uses only nondecrease. -/
def AdmissibleRounds (r : ℕ → ℕ) : Prop :=
  PolyTimeLength r ∧ Monotone r ∧
    (∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, C < r n) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ m : ℕ, 0 < m →
      1 ≤ r m ∧ (r m : ℝ) ≤ (m : ℝ) ^ (1 - ε)

/-- q is positive and uniformly polynomially bounded, with no monotonicity or
unboundedness requirement (Theorem 1.4, p.7). -/
def AdmissibleQueries (q : ℕ → ℕ) : Prop :=
  PolyTimeLength q ∧ (∀ m : ℕ, 0 < m → 1 ≤ q m) ∧
    ∃ b : Polynomial ℕ, ∀ m, q m ≤ b.eval m

end StudentTeacher976.Adaptivity



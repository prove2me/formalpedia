-- Prove2me | Definitions.Def_SuperactivatedCheating_StateConversion_GameSC
-- name    : SuperactivatedCheating_StateConversion_GameSC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:26.345182+00:00
-- url     : https://prove2.me/theorems/059df05f-e2b8-477b-bea7-eb88cc707e18
-- title:
--   Definition 12 — probability vectors, tensor products up to permutation, the game G_SC and the witnesses
-- statement:
--   A probability vector is a finitely indexed nonnegative real vector summing to 1. $(u\otimes v)_{(i,j)}=u_iv_j$ and $p^{\otimes n}_x=\prod_i p_{x_i}$ for strings $x$ of length $n$. "$u=v$ up to a permutation" for vectors of possibly different lengths means that their multisets of nonzero entries coincide. For probability vectors $p\in\mathbb R^k$, $q\in\mathbb R^l$, the state-conversion game $G_{SC}(p,q)$ has trivial referee register, question state $|\psi_p\rangle=\sum_i\sqrt{p_i}\,|i,i\rangle$ and accepting projection $|\phi_q\rangle\langle\phi_q|$ with $|\phi_q\rangle=\sum_j\sqrt{q_j}\,|j,j\rangle$. The witnesses are $q=(1/3,2/3)$ and $p=\frac1{201}(1,2,2,4,4,4,8,16,32,32,32,64)$, and the polynomials are $S(x)=1+x+2x^2-x^3+2x^4+x^5$ and $P(x)=(1+x)S(x)$ over $\mathbb Z$.
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, Definition 12, p. 15, and the proof of Theorem 11, pp. 15–16

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_QuantumGames

/-!
# Probability vectors, tensor products up to permutation, the state-conversion game `G_SC`

Bhattacharyya, Mančinska, Zhao, *Quantum interaction can superactivate cheating under parallel
repetition*, STOC 2027 submission #399 (October 2026), Definition 12 (p. 15) and the proof of
Theorem 11 (pp. 15–16). Indices are 0-based (`Fin k`); the paper's are 1-based.
-/

namespace SuperactivatedCheating.StateConversion

/-- A probability vector: a finitely indexed nonnegative real vector summing to `1`. -/
def IsProbVec {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The tensor product of vectors, `(u ⊗ v)_{(i, j)} = u_i v_j`. -/
def vtensor {α β : Type*} (u : α → ℝ) (v : β → ℝ) : α × β → ℝ :=
  fun x => u x.1 * v x.2

/-- The tensor power `p^{⊗n}`, indexed by strings `x ∈ αⁿ`: `p^{⊗n}_x = ∏ᵢ p_{xᵢ}`. -/
def vpow {α : Type*} (p : α → ℝ) (n : ℕ) : (Fin n → α) → ℝ :=
  fun x => ∏ i, p (x i)

/-- "`u = v` up to a permutation", for vectors of possibly different lengths: the multisets of
their nonzero entries coincide (zero entries carry no Schmidt coefficient). -/
def EqUpToPerm {α β : Type*} [Fintype α] [Fintype β] (u : α → ℝ) (v : β → ℝ) : Prop :=
  (Finset.univ.val.map u).filter (· ≠ 0) = (Finset.univ.val.map v).filter (· ≠ 0)

/-- Definition 12, p. 15: `|ψ_p⟩_{AB} = Σᵢ √pᵢ |i, i⟩`, with trivial referee register. -/
noncomputable def psiP {k : ℕ} (p : Fin k → ℝ) : Fin k × Fin k × Unit → ℂ :=
  fun x => if x.1 = x.2.1 then (Real.sqrt (p x.1) : ℂ) else 0

/-- Definition 12, p. 15: `|ϕ_q⟩_{ab} = Σⱼ √qⱼ |j, j⟩`, with trivial referee register. -/
noncomputable def phiQ {l : ℕ} (q : Fin l → ℝ) : Fin l × Fin l × Unit → ℂ :=
  fun x => if x.1 = x.2.1 then (Real.sqrt (q x.1) : ℂ) else 0

/-- Definition 12, p. 15: the state-conversion game `G_SC(p, q)`: the referee register is trivial,
the question state is `|ψ_p⟩`, and the accepting projection is `Π_acc = |ϕ_q⟩⟨ϕ_q|`. -/
noncomputable def gameSC {k l : ℕ} (p : Fin k → ℝ) (q : Fin l → ℝ) :
    QuantumGame (Fin k) (Fin k) Unit (Fin l) (Fin l) where
  ψ := psiP p
  acc := pureState (phiQ q)

/-- Proof of Theorem 11, p. 16: `q = (1/3, 2/3)`. -/
noncomputable def qWit : Fin 2 → ℝ := ![1 / 3, 2 / 3]

/-- Proof of Theorem 11, p. 16: `p = (1/201)(1, 2, 2, 4, 4, 4, 8, 16, 32, 32, 32, 64)`. -/
noncomputable def pWit : Fin 12 → ℝ :=
  fun i => (![1, 2, 2, 4, 4, 4, 8, 16, 32, 32, 32, 64] : Fin 12 → ℝ) i / 201

open Polynomial in
/-- Proof of Theorem 11, p. 15: `S(x) = 1 + x + 2x² − x³ + 2x⁴ + x⁵`, over `ℤ`. -/
noncomputable def polyS : ℤ[X] := 1 + X + 2 * X ^ 2 - X ^ 3 + 2 * X ^ 4 + X ^ 5

open Polynomial in
/-- Proof of Theorem 11, p. 15: `P(x) = (1 + x) S(x)`. -/
noncomputable def polyP : ℤ[X] := (1 + X) * polyS

/-! ### Sanity checks -/

example : IsProbVec qWit := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [qWit]
  · simp [qWit, Fin.sum_univ_two]; norm_num

example : IsProbVec pWit := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [pWit]
  · simp [pWit, Fin.sum_univ_succ]; norm_num

example : pWit 11 = 64 / 201 := by
  unfold pWit; congr 1

example : vtensor qWit qWit (1, 1) = 4 / 9 := by norm_num [vtensor, qWit]

/-- Equality up to permutation ignores zero entries but not multiplicities. -/
example : EqUpToPerm (![1, 0] : Fin 2 → ℝ) (![1] : Fin 1 → ℝ) := by
  simp [EqUpToPerm, Fin.univ_succ, Multiset.filter_singleton]

example : ¬ EqUpToPerm (![1, 1] : Fin 2 → ℝ) (![1] : Fin 1 → ℝ) := by
  intro h
  have := congrArg Multiset.card h
  simp [Fin.univ_succ, Multiset.filter_singleton] at this

end SuperactivatedCheating.StateConversion



-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCBrk
-- name    : RPLib_S4_AlgGrpCBrk
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:58:07.335113+00:00
-- url     : https://prove2.me/theorems/ec371b6f-64fc-4914-813b-a8a8cb131c3c
-- title:
--   Larsen's alternative library: the Lie algebra of a subgroup is closed under the commutator
-- statement:
--   `derD N` is the left-invariant derivation `derN N` of `AlgGrpB` as a bundled `Derivation`.
--   `⁅derD X, derD Y⁆ = derD (X * Y - Y * X)` (`derD_bracket`), hence for a subgroup `H ⊆ GL_n(K)`,
--   `lieS H` is closed under `X * Y - Y * X` (`lieS_bracket`), and commuting matrices give commuting
--   derivations (`derN_comm_of_commute`). Any field.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSOGen

/-!
# S4-AlgGrpC, file Brk: the Lie algebra of a subgroup is closed under the commutator

`derD N` is the left-invariant derivation `derN N` of `AlgGrpB` as a bundled `Derivation`.
`⁅derD X, derD Y⁆ = derD (X * Y - Y * X)` (`derD_bracket`), hence for a subgroup `H ⊆ GL_n(K)`,
`lieS H` is closed under `X * Y - Y * X` (`lieS_bracket`), and commuting matrices give commuting
derivations (`derN_comm_of_commute`). Any field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The left-invariant derivation along `N`, bundled. -/
def derD (N : Matrix n n K) : Derivation K (MvPolynomial (Var n) K) (MvPolynomial (Var n) K) :=
  MvPolynomial.mkDerivation K (dN N)

theorem derD_X (N : Matrix n n K) (v : Var n) : derD N (X v) = dN N v :=
  MvPolynomial.mkDerivation_X K (dN N) v

theorem derD_apply (N : Matrix n n K) (f : MvPolynomial (Var n) K) : derD N f = derN N f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [derN_C]; exact (derD N).map_algebraMap a
  | add p q hp hq => rw [map_add, hp, hq, derN_add]
  | mul_X p v hp =>
    rw [Derivation.leibniz, derD_X, hp, derN_mul_X, smul_eq_mul, smul_eq_mul]
    ring

theorem derD_dN_inl (A B : Matrix n n K) (i j : n) :
    derD A (dN B (Sum.inl (i, j))) = ∑ l, X (Sum.inl (i, l)) * C ((A * B) l j) := by
  simp only [dN, Sum.elim_inl, map_sum, Derivation.leibniz, derD_X, smul_eq_mul]
  simp only [MvPolynomial.derivation_C, mul_zero, zero_add, dN, Sum.elim_inl, Finset.sum_mul,
    Matrix.mul_apply, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [C_mul]
  ring

theorem derD_dN_inr (A B : Matrix n n K) (i j : n) :
    derD A (dN B (Sum.inr (i, j))) = ∑ l, C ((B * A) i l) * X (Sum.inr (l, j)) := by
  simp only [dN, Sum.elim_inr, map_sum, Derivation.leibniz, derD_X, smul_eq_mul]
  simp only [MvPolynomial.derivation_C, mul_zero, add_zero, Finset.mul_sum,
    Matrix.mul_apply, map_sum, Finset.sum_mul, Matrix.neg_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [C_mul, map_neg, map_neg]
  ring

theorem derD_bracket (A B : Matrix n n K) : ⁅derD A, derD B⁆ = derD (A * B - B * A) := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.commutator_apply, derD_X, derD_X, derD_X]
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · rw [derD_dN_inl, derD_dN_inl]
    simp only [dN, Sum.elim_inl, ← Finset.sum_sub_distrib, ← mul_sub, ← C_sub, Matrix.sub_apply]
  · rw [derD_dN_inr, derD_dN_inr]
    simp only [dN, Sum.elim_inr, ← Finset.sum_sub_distrib, ← sub_mul, ← C_sub, Matrix.neg_apply,
      Matrix.sub_apply, neg_sub]

theorem derN_bracket (A B : Matrix n n K) (f : MvPolynomial (Var n) K) :
    derN (A * B - B * A) f = derN A (derN B f) - derN B (derN A f) := by
  rw [← derD_apply, ← derD_bracket, Derivation.commutator_apply, derD_apply, derD_apply,
    derD_apply, derD_apply]

theorem derN_zero (f : MvPolynomial (Var n) K) : derN (0 : Matrix n n K) f = 0 := by
  simp [derN, dN]

theorem derN_comm_of_commute {A B : Matrix n n K} (h : Commute A B) (f : MvPolynomial (Var n) K) :
    derN A (derN B f) = derN B (derN A f) := by
  have := derN_bracket A B f
  rw [h.eq, sub_self, derN_zero] at this
  exact sub_eq_zero.1 this.symm

/-- At the identity, the left-invariant vector field along `Z` is the tangent vector `dvec Z`. -/
theorem eval_one_dN (Z : Matrix n n K) :
    (fun v => eval (crd (1 : Matrix.GeneralLinearGroup n K)) (dN Z v)) = dvec Z := by
  funext v
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp [dN, Matrix.one_apply]
  · simp [dN, Matrix.one_apply]

theorem mem_lieS_of_derN {H : Subgroup (Matrix.GeneralLinearGroup n K)} {Z : Matrix n n K}
    (hZ : ∀ f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K)),
      derN Z f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K))) :
    Z ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)) := by
  refine mem_lieS.2 fun f hf => ?_
  have h1 := mem_vanI.1 (hZ f hf) 1 H.one_mem
  rw [eval_derN, eval_one_dN] at h1
  exact h1

/-- The Lie algebra of a subgroup is closed under the commutator. -/
theorem lieS_bracket {H : Subgroup (Matrix.GeneralLinearGroup n K)} {A B : Matrix n n K}
    (hA : A ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (hB : B ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) :
    A * B - B * A ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)) := by
  refine mem_lieS_of_derN fun f hf => ?_
  rw [derN_bracket]
  exact Submodule.sub_mem _ (derN_mem_vanI hA (derN_mem_vanI hB hf))
    (derN_mem_vanI hB (derN_mem_vanI hA hf))

end RamanujanPetersson.AlgGrpC



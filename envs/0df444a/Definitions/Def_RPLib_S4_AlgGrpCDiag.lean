-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCDiag
-- name    : RPLib_S4_AlgGrpCDiag
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:02:54.484205+00:00
-- url     : https://prove2.me/theorems/8a1e4a7b-7269-4b8b-9b1f-df0274a40541
-- title:
--   Larsen's alternative library: conjugation and the diagonal form of the Jordan decomposition
-- statement:
--   * `conj_mem_lieS'`: if `g Z g⁻¹ ⊆ Z'` then `Ad(g)` maps `Lie Z` into `Lie Z'`.
--   * `exists_diag_conj` (K algebraically closed, char 0): every matrix `X` is conjugate to
--     `diagonal lam + N` with `N` nilpotent commuting with `diagonal lam` (an eigenbasis of the
--     semisimple part of the Jordan-Chevalley decomposition of `X`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCRep

/-!
# S4-AlgGrpC, file Diag: conjugation and the diagonal form of the Jordan decomposition

* `conj_mem_lieS'`: if `g Z g⁻¹ ⊆ Z'` then `Ad(g)` maps `Lie Z` into `Lie Z'`.
* `exists_diag_conj` (K algebraically closed, char 0): every matrix `X` is conjugate to
  `diagonal lam + N` with `N` nilpotent commuting with `diagonal lam` (an eigenbasis of the
  semisimple part of the Jordan-Chevalley decomposition of `X`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Conjugation carries tangent vectors of `Z` to those of any `Z'` containing `g Z g⁻¹`. -/
theorem conj_mem_lieS' {Z Z' : Set (Matrix.GeneralLinearGroup n K)}
    {g : Matrix.GeneralLinearGroup n K} (hg : ∀ h ∈ Z, g * h * g⁻¹ ∈ Z') {X : Matrix n n K}
    (hX : X ∈ lieS Z) :
    (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈ lieS Z' :=
  lieS_subst (conjPoly g) (fun h hh => ⟨_, hg h hh, eval_conjPoly g h⟩) (aeval_ptD_conjPoly g X) hX

/-- Diagonal form of the Jordan decomposition over an algebraically closed field of char 0. -/
theorem exists_diag_conj [IsAlgClosed K] [CharZero K] (X : Matrix n n K) :
    ∃ (P : Matrix.GeneralLinearGroup n K) (lam : n → K) (N : Matrix n n K), IsNilpotent N ∧
      Commute (Matrix.diagonal lam) N ∧
      (P : Matrix n n K) * X * ((P⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) =
        Matrix.diagonal lam + N := by
  classical
  obtain ⟨n₀, hn₀a, s₀, hs₀a, hn₀, hs₀, h₀⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := Matrix.toLin' X)
  have h1 : Commute (Matrix.toLin' X) s₀ :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs₀a (Commute.refl _)
  have hc : Commute s₀ n₀ := Algebra.commute_of_mem_adjoin_singleton_of_commute hn₀a h1.symm
  have hint : DirectSum.IsInternal (fun μ => s₀.eigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.eigenspaces_iSupIndep s₀) hs₀.iSup_eigenspace_eq_top
  let v := fun μ => Module.finBasis K (s₀.eigenspace μ)
  let b0 := hint.collectedBasis v
  let _ := FiniteDimensional.fintypeBasisIndex b0
  have hcard : Fintype.card (Σ μ : K, Fin (Module.finrank K (s₀.eigenspace μ))) =
      Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b0, Module.finrank_fintype_fun_eq_card]
  let eqv := Fintype.equivOfCardEq hcard
  let b := b0.reindex eqv
  let lam : n → K := fun j => (eqv.symm j).1
  have hb : ∀ j, s₀ (b j) = lam j • b j := fun j => by
    rw [Module.Basis.reindex_apply]
    exact Module.End.mem_eigenspace_iff.1 (hint.collectedBasis_mem v (eqv.symm j))
  have hD : LinearMap.toMatrixAlgEquiv b s₀ = Matrix.diagonal lam := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, hb, map_smul, Module.Basis.repr_self]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h]
  refine ⟨⟨b.toMatrix (Pi.basisFun K n), (Pi.basisFun K n).toMatrix b,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, lam,
    LinearMap.toMatrixAlgEquiv b n₀, hn₀.map (LinearMap.toMatrixAlgEquiv b),
    by rw [← hD]; exact hc.map (LinearMap.toMatrixAlgEquiv b), ?_⟩
  have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b)
    (b' := Pi.basisFun K n) (c := b) (c' := Pi.basisFun K n) (Matrix.toLin' X)
  rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at key
  change b.toMatrix (Pi.basisFun K n) * X * (Pi.basisFun K n).toMatrix b = _
  rw [key, ← hD, ← map_add, add_comm, ← h₀]
  ext i j
  rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

end RamanujanPetersson.AlgGrpC



-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P10_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:22:10.252744+00:00
-- url     : https://prove2.me/theorems/40fe3497-5349-4509-a510-3dc12356e803
-- title:
--   A simple formula for the average gate fidelity of a quantum dynamical operation: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2. PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10

/-- Nielsen, arXiv:quant-ph/0205035v2, Eq. (2), PDF p.1. The target inverse
conjugates the channel output; the Haar average is normalized. -/
def gateFidelity (d : ℕ) (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  QuditFidelity.averageFidelity d hd (conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ E)

/-- Nielsen, PDF p.2, paragraph before Eq. (11): a complex operator basis
of unitaries with Hilbert--Schmidt squared norm d. -/
structure OrthogonalUnitaryOperatorBasis (d : ℕ) where
  basis : Module.Basis (Fin (d*d)) ℂ (Matrix (Fin d) (Fin d) ℂ)
  unitary : ∀ j, basis j ∈ Matrix.unitaryGroup (Fin d) ℂ
  orthogonal : ∀ j k, (star (basis j)*basis k).trace = if j = k then (d : ℂ) else 0

/-- Nielsen, PDF pp.2--3, discussion leading to Eq. (19): density matrices
forming a complex operator basis. Expansion coefficients are `basis.repr`. -/
structure StateOperatorBasis (d : ℕ) where
  basis : Module.Basis (Fin (d*d)) ℂ (Matrix (Fin d) (Fin d) ℂ)
  density : ∀ k, IsDensityMatrix (basis k)

/-- The three nonidentity Paulis of Eq. (18), PDF p.2, transported from the
frozen Bool convention to Fin 2, in order X, Y, Z. -/
def pauliOperators : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun j => (![pauliX,pauliY,pauliZ] j).submatrix finTwoEquiv finTwoEquiv

/-- A singleton matrix basis for the d=1 sanity checks. -/
def singletonMatrixBasis : Module.Basis (Fin (1*1)) ℂ (Matrix (Fin 1) (Fin 1) ℂ) :=
  (Matrix.stdBasis ℂ (Fin 1) (Fin 1)).reindex finProdFinEquiv

example (d : ℕ) (hd : 0 < d) (E : Superop (Fin d) (Fin d)) :
    gateFidelity d hd E 1 = QuditFidelity.averageFidelity d hd E := by
  simp [gateFidelity,conjSuperop,Function.comp_def]

example : pauliOperators 1 0 1 = -Complex.I := rfl

example (j : Fin (1*1)) : singletonMatrixBasis j = 1 := by
  ext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  have hj : finProdFinEquiv.symm j = ((0 : Fin 1),(0 : Fin 1)) := Subsingleton.elim _ _
  simp [singletonMatrixBasis,Module.Basis.reindex_apply, hj, Matrix.stdBasis_eq_single,ha,hb,Matrix.one_apply]

example : Nonempty (OrthogonalUnitaryOperatorBasis 1) := by
  have h : ∀ j, singletonMatrixBasis j = 1 := fun j => by
    ext a b
    have hj : finProdFinEquiv.symm j = ((0 : Fin 1),(0 : Fin 1)) := Subsingleton.elim _ _
    simp [singletonMatrixBasis,Module.Basis.reindex_apply,hj,Matrix.stdBasis_eq_single,
      Subsingleton.elim a 0,Subsingleton.elim b 0,Matrix.one_apply]
  refine ⟨⟨singletonMatrixBasis,fun j => ?_,fun j k => ?_⟩⟩
  · rw [h]; exact one_mem _
  · rw [h,h]
    have hjk : j = k := Fin.ext (by omega)
    simp [hjk]

example : Nonempty (StateOperatorBasis 1) := by
  have h : ∀ j, singletonMatrixBasis j = 1 := fun j => by
    ext a b
    have hj : finProdFinEquiv.symm j = ((0 : Fin 1),(0 : Fin 1)) := Subsingleton.elim _ _
    simp [singletonMatrixBasis,Module.Basis.reindex_apply,hj,Matrix.stdBasis_eq_single,
      Subsingleton.elim a 0,Subsingleton.elim b 0,Matrix.one_apply]
  refine ⟨⟨singletonMatrixBasis,fun j => ?_⟩⟩
  rw [h]
  exact ⟨Matrix.PosSemidef.one,by simp⟩








end QAlgorithms.Papers.Independent.Independent1.P10



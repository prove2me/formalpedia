-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:58:04.788791+00:00
-- url     : https://prove2.me/theorems/334d2b9e-2446-4d4b-aff7-81cfed906036
-- title:
--   Convergence Group Of Block Det
-- statement:
--   Definitions and structural lemmas for Convergence Group Of Block Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_det_mul_eq_sum_minors_of_enum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.Plucker
variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
variable {R : Type} [CommRing R]
abbrev Sub (ι m : Type) [Fintype m] : Type := ↥(Set.powersetCard ι (Fintype.card m))
def enE (S : Sub ι m) : m ≃ ↥S.1 :=
  Fintype.equivOfCardEq ((Fintype.card_coe S.1).trans S.2).symm
def en (S : Sub ι m) : m → ι := fun i => (enE S i : ι)
theorem en_mem (S : Sub ι m) (i : m) : en S i ∈ S.1 := (enE S i).2
theorem en_injective (S : Sub ι m) : Function.Injective (en S) := fun _ _ h =>
  (enE S).injective (Subtype.ext h)
theorem range_en (S : Sub ι m) : Set.range (en S) = (S.1 : Set ι) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact en_mem S i
  · intro hx
    exact ⟨(enE S).symm ⟨x, hx⟩, by simp [en]⟩
def cmp (M : Matrix ι ι R) : Matrix (Sub ι m) (Sub ι m) R :=
  Matrix.of fun t u => (M.submatrix (en t) (en u)).det
theorem cmp_apply (M : Matrix ι ι R) (t u : Sub ι m) : cmp M t u = (M.submatrix (en t) (en u)).det := rfl
theorem cmp_mul (M N : Matrix ι ι R) : (cmp (M * N) : Matrix (Sub ι m) (Sub ι m) R) = cmp M * cmp N := by
  ext t u
  rw [cmp_apply, submatrix_mul M N (en t) id (en u) Function.bijective_id,
    GlobalTheory.det_mul_eq_sum_minors_of_enum en range_en, Matrix.mul_apply]
  rfl
theorem cmp_eq_zero_of_block (M : Matrix ι ι R) {t t₀ : Sub ι m} (h : t ≠ t₀)
    (hM : ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι), M r c = 0) : cmp M t t₀ = 0 := by
  obtain ⟨x, hx, hx'⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t t₀).1 h
  have h1 : x ∈ Set.range (en t) := by rw [range_en]; exact hx
  obtain ⟨i, rfl⟩ := h1
  exact det_eq_zero_of_row_eq_zero i fun j => hM _ hx' _ (en_mem t₀ j)
theorem cmp_one : (cmp (1 : Matrix ι ι R) : Matrix (Sub ι m) (Sub ι m) R) = 1 := by
  ext t u
  rcases eq_or_ne t u with rfl | h
  · rw [one_apply_eq, cmp_apply, submatrix_one _ (en_injective t), det_one]
  · rw [one_apply_ne h]
    refine cmp_eq_zero_of_block _ h fun r hr c hc => one_apply_ne fun e => hr (e ▸ hc)
def cmpHom (ι m : Type) [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] (R : Type) [CommRing R] :
    Matrix ι ι R →* Matrix (Sub ι m) (Sub ι m) R where
  toFun := cmp
  map_one' := cmp_one
  map_mul' := cmp_mul
def cGL (m : Type) [Fintype m] [DecidableEq m] : GL ι R →* GL (Sub ι m) R := Units.map (cmpHom ι m R)
end GlobalTheory.CompanionTheory.Plucker
namespace GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
section Grp
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
end Grp
section Ht
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
end Ht
end GlobalTheory.CompanionTheory.Plucker



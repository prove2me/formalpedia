-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:39.363276+00:00
-- url     : https://prove2.me/theorems/10cc0432-851d-4cb2-b0d6-5e3621cc6f96
-- title:
--   PConj Int Num
-- statement:
--   Definitions and structural lemmas for PConj Int Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConjIntNum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial NumbersDVR
noncomputable section
namespace ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]
theorem isWeightedHomogeneous_map {σ M : Type*} [AddCommMonoid M] (w : σ → M) (τ : F →+* F)
    {f : MvPolynomial σ F} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w (MvPolynomial.map τ f) m := by
  intro d hd
  rw [coeff_map] at hd
  exact hf fun h => hd (by rw [h, map_zero])
def quotEquiv (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    (MRing ι F ⧸ J) ≃+* (MRing ι F ⧸ J.map (MvPolynomial.map (τ : F →+* F))) :=
  Ideal.quotientEquiv J _ (MvPolynomial.mapEquiv _ τ) (by
    congr 1)
theorem mem_gradedPiece_iff (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) (x : MRing ι F ⧸ J) :
    quotEquiv τ J x ∈ gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m ↔ x ∈ gradedPiece J m := by
  simp only [gradedPiece, Submodule.mem_map, mem_weightedHomogeneousSubmodule]
  constructor
  · rintro ⟨g, hg, hgx⟩
    refine ⟨MvPolynomial.map (τ.symm : F →+* F) g, isWeightedHomogeneous_map _ _ hg, ?_⟩
    have := congrArg (quotEquiv τ J).symm hgx
    rw [RingEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  · rintro ⟨f, hf, rfl⟩
    exact ⟨MvPolynomial.map (τ : F →+* F) f, isWeightedHomogeneous_map _ _ hf, rfl⟩
def pieceEquiv (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    gradedPiece J m ≃+ gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m where
  toFun x := ⟨quotEquiv τ J x, (mem_gradedPiece_iff τ J m x).2 x.2⟩
  invFun y := ⟨(quotEquiv τ J).symm y,
    (mem_gradedPiece_iff τ J m _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (RingEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (RingEquiv.apply_symm_apply _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)
end ConjIntNum
end
end GroundTheory.Heights₂.Heights.HilbertSamuel



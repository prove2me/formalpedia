-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:29:21.019903+00:00
-- url     : https://prove2.me/theorems/94993efb-c97a-412b-b57b-6b4ce1ef9bd3
-- title:
--   Ht Image
-- statement:
--   Definitions and structural lemmas for Ht Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.HN
section HtImageAux
end HtImageAux
section HtImageReal
def htImageCv {P ι : Type*} [Fintype P] [Fintype ι] (y : EuclideanSpace ℝ (P × ι × Fin 2))
    (v : P) : ι → ℂ :=
  fun i => ⟨y (v, i, 0), y (v, i, 1)⟩
def htImageMap {P ι κ : Type*} [Fintype P] [Fintype ι] [Fintype κ] (M : P → Matrix κ ι ℂ) :
    EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × κ × Fin 2) where
  toFun y := WithLp.toLp 2 (fun p => if p.2.2 = 0 then ((M p.1).mulVec (htImageCv y p.1) p.2.1).re
      else ((M p.1).mulVec (htImageCv y p.1) p.2.1).im)
  map_add' y z := by
    have h : ∀ v, htImageCv (y + z) v = htImageCv y v + htImageCv z v := by
      intro v; funext i; apply Complex.ext <;> simp [htImageCv]
    ext p
    simp only [h, Matrix.mulVec_add, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' r y := by
    have h : ∀ v, htImageCv (r • y) v = r • htImageCv y v := by
      intro v; funext i; apply Complex.ext <;> simp [htImageCv]
    ext p
    simp only [h, Matrix.mulVec_smul, PiLp.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type*} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
def htImageMat (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) (v : InfinitePlace K) :
    Matrix κ ι ℂ :=
  (X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v
end HtImageReal
end Formalism.HN



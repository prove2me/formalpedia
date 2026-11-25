-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairs
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairs
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:58.447635+00:00
-- url     : https://prove2.me/theorems/9a8a2a57-6aef-404f-9e14-4cc9c2690eee
-- title:
--   Hermitian Stabiliser Rational Unitriangular Pairs
-- statement:
--   Definitions and structural lemmas for Hermitian Stabiliser Rational Unitriangular Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianStabiliserRationalUnitriangularPairs.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
section Local
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]
end Local
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
def bcL (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (Fin n → E) →ₛₗ[(A.loc p).ιE] (Fin n → (A.loc p).Ep) where
  toFun := A.bc p
  map_add' x y := by funext i; simp [Places.bc]
  map_smul' c x := by funext i; simp [Places.bc]
variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
def B (x y : G.V) : E := ∑ i, ∑ j, x i * G.Hm i j * sig (y j)
def sc (n : ℕ) : (A.loc p).Ep :=
  algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp))⁻¹ ^ (r - n))
def sci (n : ℕ) : (A.loc p).Ep :=
  algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - n))
def locM (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep :=
  Matrix.of fun i j => sc G p j * sci G p i * (A.loc p).ιE (s i j)
end GlobalTheory.HL.RatStab
namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
end GlobalTheory.HL.RatStab
namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
abbrev gg : Fin (r + 1) ⊕ Fin (r + 1) → G.V := Sum.elim G.f G.f'
abbrev idx : Fin (r + 1) ⊕ Fin (r + 1) → ℕ := Sum.elim (fun a => (a : ℕ)) (fun a => (a : ℕ))
def Phi : G.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) where
  toFun x j := B G x (gg G j)
  map_add' x y := by
    funext j
    simp only [B, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    simp only [B, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
def Wc : Submodule E G.V := LinearMap.ker (Phi G)
end GlobalTheory.HL.RatStab
namespace GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
end GlobalTheory.HL.RatStab



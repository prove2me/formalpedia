-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:19.958497+00:00
-- url     : https://prove2.me/theorems/7084e4e4-3a86-4e21-9e64-2fe7087af4b2
-- title:
--   Definite Hermitian Isometric Of Same Bad Primes
-- statement:
--   Definitions and structural lemmas for Definite Hermitian Isometric Of Same Bad Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteHermitianIsometricOfSameBadPrimes.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.SameBad
section Val
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def NormUnit (P : Ideal (𝓞 K)) (x : K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ star c * c * x ∈ locR (K := K) P ∧ (star c * c * x)⁻¹ ∈ locR (K := K) P
end Val
section Ext
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
def ext (h : V →ₗ⋆[K] V →ₗ[K] K) (β : K) : (V × K) →ₗ⋆[K] (V × K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x.1 y.1 + β * (star x.2 * y.2))
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, star_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, star_mul',
        starRingEnd_apply]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]; ring)
end Ext
end GlobalTheory.Mass.SameBad



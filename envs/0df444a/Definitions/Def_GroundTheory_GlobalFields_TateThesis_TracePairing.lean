-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
-- name    : GroundTheory_GlobalFields_TateThesis_TracePairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:47.133786+00:00
-- url     : https://prove2.me/theorems/6b41b035-2298-49d0-83ae-7002a25f6dd2
-- title:
--   Trace Pairing
-- statement:
--   Definitions and structural lemmas for Trace Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun x := ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
def mixedTraceForm : LinearMap.BilinForm ℝ (mixedSpace K) :=
  (LinearMap.mul ℝ (mixedSpace K)).compr₂ (mixedTrace K)
def infiniteTraceForm (x y : InfiniteAdeleRing K) : ℝ :=
  mixedTraceForm K (homeomorphMixedSpace K x) (homeomorphMixedSpace K y)
end
end GroundTheory.Global



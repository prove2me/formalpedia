-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TraceGramNondegenerate
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TraceGramNondegenerate
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:53.316443+00:00
-- url     : https://prove2.me/theorems/85f9e4cc-b139-42c2-a771-7430422ff2b2
-- title:
--   Trace Gram Nondegenerate
-- statement:
--   Definitions and structural lemmas for Trace Gram Nondegenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TraceGramNondegenerate.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
theorem hE_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
theorem hE_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    hE σ J x (y + y') = hE σ J x y + hE σ J x y' := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem hE_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J (c • x) y = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (σ : E →+* E) (algebraMap F E c) = algebraMap F E c := σ.commutes c
  rw [map_mul, hc]
  ring
theorem hE_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J x (c • y) = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
def trForm {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : LinearMap.BilinForm F (Fin M → E) :=
  LinearMap.mk₂ F (fun x y => Algebra.trace F E (hE σ J x y))
    (fun x x' y => by simp only [hE_add_left, map_add])
    (fun c x y => by simp only [hE_smul_left, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [hE_add_right, map_add])
    (fun c x y => by simp only [hE_smul_right, ← Algebra.smul_def, map_smul])
end PI.VolSemiDirect.W.Cj



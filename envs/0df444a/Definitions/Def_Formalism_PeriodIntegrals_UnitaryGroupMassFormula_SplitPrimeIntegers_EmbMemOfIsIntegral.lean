-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:16:15.235244+00:00
-- url     : https://prove2.me/theorems/9a3d67b1-2a4b-4d89-b1e5-14990e89fab5
-- title:
--   Emb Mem Of Is Integral
-- statement:
--   Definitions and structural lemmas for Emb Mem Of Is Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
namespace PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
lemma intsV : (Valued.v (R := (v.adicCompletion F))).Integers (v.adicCompletionIntegers F) :=
  Valuation.valuationSubring.integers _
variable {v} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
def emb (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : E →+* (v.adicCompletion F) :=
  p.comp ((spl : E ⊗[F] (v.adicCompletion F) →+* (v.adicCompletion F) × (v.adicCompletion F)).comp Algebra.TensorProduct.includeLeftRingHom)
lemma emb_mem_of_isIntegral (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (e : E) (he : IsIntegral ℤ e) :
    emb spl p e ∈ (v.adicCompletionIntegers F) := by
  obtain ⟨f, hm, hf⟩ := he
  refine (intsV v).mem_of_integral ⟨f.map (Int.castRingHom _), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).comp
      (Int.castRingHom (v.adicCompletionIntegers F)) = (emb spl p).comp (algebraMap ℤ E) :=
    RingHom.ext_int _ _
  rw [hc, ← Polynomial.hom_eval₂, hf, map_zero]
def phi (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : 𝓞 E →+* (v.adicCompletionIntegers F) :=
  ((emb spl p).comp (algebraMap (𝓞 E) E)).codRestrict (v.adicCompletionIntegers F)
    (fun z => emb_mem_of_isIntegral spl p _ (RingOfIntegers.isIntegral_coe z))
def P (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).comap (phi spl p)
instance (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : (P spl p).IsPrime := Ideal.IsPrime.comap _
end PI.SplitIntLoc.Proof



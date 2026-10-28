-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_CountablySeparated
-- name    : MarkovProcessModule_MarkovProcess_Lifetime_CountablySeparated
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:46:56.745153+00:00
-- url     : https://prove2.me/theorems/493c5363-acd8-42d5-8778-bdf60527772b
-- title:
--   MarkovProcess.Lifetime.CountablySeparated
-- statement:
--   # Countable separation of lifetime paths
--
--   Lifetime and the coordinates at the fixed countable dense time set separate continuous lifetime
--   paths.  Their measurable coding therefore gives a countable separating family.
--
--   Complete pinned Lean module MarkovProcess.Lifetime.CountablySeparated by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Lifetime/CountablySeparated.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_Basic

/-!
# Countable separation of lifetime paths

Lifetime and the coordinates at the fixed countable dense time set separate continuous lifetime
paths.  Their measurable coding therefore gives a countable separating family.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MarkovProcess
namespace LifetimePath

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha]

/-- The lifetime together with all coordinates at the fixed countable dense times. -/
def countableCode (omega : LifetimePath alpha) :
    ENNReal × (DenseTime → Cemetery alpha) :=
  (omega.lifetime, fun q ↦ omega.coordinate (DenseTime.castOrderEmbedding q))

omit [T2Space alpha] in
/-- The lifetime-path code is measurable for the canonical coordinate-generated structure. -/
theorem measurable_countableCode : Measurable (countableCode (alpha := alpha)) := by
  apply measurable_lifetime.prodMk
  rw [measurable_pi_iff]
  intro q
  exact measurable_coordinate (DenseTime.castOrderEmbedding q)

private def denseBefore (L : ENNReal) :
    {q : DenseTime // (DenseTime.castOrderEmbedding q : ENNReal) < L} →
      {t : NNReal // (t : ENNReal) < L} :=
  fun q ↦ ⟨DenseTime.castOrderEmbedding q, q.property⟩

private theorem denseRange_denseBefore (L : ENNReal) :
    DenseRange (denseBefore L) := by
  rw [DenseRange]
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro t
  rw [closure_subtype]
  let U : Set NNReal := {s | (s : ENNReal) < L}
  have hU : IsOpen U := isOpen_lt ENNReal.continuous_coe continuous_const
  have himage :
      ((↑) : {s : NNReal // (s : ENNReal) < L} → NNReal) ''
          Set.range (denseBefore L) =
        Set.range DenseTime.castOrderEmbedding ∩ U := by
    ext s
    constructor
    · rintro ⟨r, ⟨q, hqr⟩, hrs⟩
      have hr := r.property
      have hqrval := congrArg Subtype.val hqr
      change r.1 = s at hrs
      refine ⟨⟨q, hqrval.trans hrs⟩, ?_⟩
      change (s : ENNReal) < L
      rw [← hrs]
      exact hr
    · rintro ⟨⟨q, hq⟩, hs⟩
      subst s
      exact ⟨denseBefore L ⟨q, hs⟩, ⟨⟨q, hs⟩, rfl⟩, rfl⟩
  rw [himage]
  simpa only [inter_comm] using
    ContinuousPath.denseRange_castOrderEmbedding.open_subset_closure_inter hU t.property

omit [MeasurableSpace alpha] in
/-- Lifetime and dense-time coordinates determine a lifetime path. -/
theorem countableCode_injective : Function.Injective (countableCode (alpha := alpha)) := by
  intro omega eta hcode
  have hlifetime : omega.lifetime = eta.lifetime := congrArg Prod.fst hcode
  cases omega with
  | mk omegaLifetime omegaPath homega =>
    cases eta with
    | mk etaLifetime etaPath heta =>
      dsimp only [countableCode] at hcode hlifetime
      subst etaLifetime
      congr
      funext t
      have hdense :
          (fun q ↦ omegaPath (denseBefore omegaLifetime q)) =
            fun q ↦ etaPath (denseBefore omegaLifetime q) := by
        funext q
        have hq := congrFun (congrArg Prod.snd hcode) q.1
        change coordinate (DenseTime.castOrderEmbedding q.1)
            { lifetime := omegaLifetime, livePath := omegaPath,
              continuous_livePath := homega } =
          coordinate (DenseTime.castOrderEmbedding q.1)
            { lifetime := omegaLifetime, livePath := etaPath,
              continuous_livePath := heta } at hq
        rw [coordinate_of_lt _ _ q.property, coordinate_of_lt _ _ q.property] at hq
        exact Sum.inl.inj hq
      have hall : omegaPath = etaPath :=
        (denseRange_denseBefore omegaLifetime).equalizer homega heta hdense
      exact congrFun hall t

/-- Continuous lifetime paths are countably separated by lifetime and fixed dense-time
coordinates. -/
instance instCountablySeparated
    [StandardBorelSpace (Cemetery alpha)] :
    MeasurableSpace.CountablySeparated (LifetimePath alpha) := by
  rcases (inferInstance :
      MeasurableSpace.CountablySeparated
        (ENNReal × (DenseTime → Cemetery alpha))) with ⟨S, hScount, hSmeas, hSsep⟩
  let T : Set (Set (LifetimePath alpha)) :=
    (fun s ↦ countableCode (alpha := alpha) ⁻¹' s) '' S
  refine ⟨T, hScount.image _, ?_, ?_⟩
  · rintro t ⟨s, hs, rfl⟩
    exact hSmeas s hs |>.preimage measurable_countableCode
  · intro omega _ eta _ h
    apply countableCode_injective
    apply hSsep _ trivial _ trivial
    intro s hs
    exact h _ ⟨s, hs, rfl⟩

end
end LifetimePath
end MarkovProcess



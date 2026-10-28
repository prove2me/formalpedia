-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Restart_RestrictedRestartOfJoint
-- name    : MarkovProcessModule_MarkovProcess_Restart_RestrictedRestartOfJoint
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:30:35.02346+00:00
-- url     : https://prove2.me/theorems/e3b4163c-fc08-4394-804a-ff2ece566720
-- title:
--   MarkovProcess.Restart.RestrictedRestartOfJoint
-- statement:
--   # Restricted restart laws from a joint-law factorization
--
--   This file gives a generic measure-theoretic bridge from factorization of the joint law of a
--   conditioning variable and a future variable to the corresponding future-law identity after
--   restriction to any event measurable with respect to the conditioning variable.
--
--   No stochastic process or Markov property is asserted here.
--
--   Complete pinned Lean module MarkovProcess.Restart.RestrictedRestartOfJoint by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Restart/RestrictedRestartOfJoint.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Restricted restart laws from a joint-law factorization

This file gives a generic measure-theoretic bridge from factorization of the joint law of a
conditioning variable and a future variable to the corresponding future-law identity after
restriction to any event measurable with respect to the conditioning variable.

No stochastic process or Markov property is asserted here.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess

noncomputable section

variable {Omega beta gamma : Type*} {mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta} {mGamma : MeasurableSpace gamma}

/-- A factorization of the joint law of `X` and `Y` through `kappa` implies the future-law
restart identity after restriction to every event measurable with respect to `X`. -/
theorem restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
    (mu : @Measure Omega mOmega) [SFinite mu]
    (X : Omega → beta) (hX : @Measurable Omega beta mOmega mBeta X)
    (Y : Omega → gamma) (hY : @Measurable Omega gamma mOmega mGamma Y)
    (kappa : @Kernel beta gamma mBeta mGamma) [IsSFiniteKernel kappa]
    (hJoint : mu.map (fun omega ↦ (X omega, Y omega)) = (mu.map X) ⊗ₘ kappa) :
    ∀ A : Set Omega, MeasurableSet[mBeta.comap X] A →
      (mu.restrict A).map Y =
        (Kernel.comap kappa X hX) ∘ₘ (mu.restrict A) := by
  rintro A ⟨C, hC, rfl⟩
  ext B hB
  rw [Measure.map_apply hY hB, Measure.bind_apply hB (Kernel.aemeasurable _)]
  simp_rw [Kernel.comap_apply]
  rw [Measure.restrict_apply (hY hB), Set.inter_comm]
  calc
    mu (X ⁻¹' C ∩ Y ⁻¹' B) =
        (mu.map (fun omega ↦ (X omega, Y omega))) (C ×ˢ B) := by
      rw [Measure.map_apply (hX.prodMk hY) (hC.prod hB), Set.mk_preimage_prod]
    _ = ((mu.map X) ⊗ₘ kappa) (C ×ˢ B) := by rw [hJoint]
    _ = ∫⁻ x in C, kappa x B ∂(mu.map X) := Measure.compProd_apply_prod hC hB
    _ = ∫⁻ omega in X ⁻¹' C, kappa (X omega) B ∂mu :=
      setLIntegral_map hC (kappa.measurable_coe hB) hX

end
end MarkovProcess



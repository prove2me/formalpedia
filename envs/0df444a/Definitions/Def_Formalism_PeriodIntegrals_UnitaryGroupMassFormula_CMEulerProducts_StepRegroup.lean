-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:15.420822+00:00
-- url     : https://prove2.me/theorems/c1e4cdc6-8ff8-4d65-9b5a-d9053bbe409b
-- title:
--   Step Regroup
-- statement:
--   Definitions and structural lemmas for Step Regroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/StepRegroup.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace CMEul
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
def FibreShape (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (v : Ideal (𝓞 F)) : Prop :=
  (∃ P : Ideal (𝓞 E), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v ∧
      conjIdeal (K := E) P = P ∧ Ideal.absNorm P = Ideal.absNorm v ^ 2 ∧
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v → Q = P) ∨
  (∃ P Q : Ideal (𝓞 E), P.IsMaximal ∧ Q.IsMaximal ∧
      P.comap (algebraMap (𝓞 F) (𝓞 E)) = v ∧ Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v ∧ P ≠ Q ∧
      conjIdeal (K := E) P = Q ∧ conjIdeal (K := E) Q = P ∧
      Ideal.absNorm P = Ideal.absNorm v ∧ Ideal.absNorm Q = Ideal.absNorm v ∧
      ∀ R : Ideal (𝓞 E), R.IsMaximal → R.comap (algebraMap (𝓞 F) (𝓞 E)) = v → R = P ∨ R = Q)
def StepFib : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∀ v : Ideal (𝓞 F), v.IsMaximal → FibreShape F E v
def StepConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∃ σ : 𝓞 E ≃+* 𝓞 E,
      (∀ x : 𝓞 E, algebraMap (𝓞 E) E (σ x) = star (algebraMap (𝓞 E) E x)) ∧
      (∀ x : 𝓞 E, σ (σ x) = x) ∧
      (∀ P : Ideal (𝓞 E), conjIdeal (K := E) P = P.map σ) ∧
      (∀ x : 𝓞 E, σ x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 E))) ∧
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ : 𝓞 E, θ - σ θ ∉ P)
def StepMult : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ), 3 ≤ M →
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => eulerFac K M P.1)
def StepLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (M : ℕ), 3 ≤ M → ∀ v : Ideal (𝓞 F), v.IsMaximal → FibreShape F E v →
    HasProd (fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} =>
      eulerFac E M c.1) (eulerF F E M v)
def StepRegroup : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (M : ℕ), Multipliable (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => eulerFac E M P.1) →
    (∀ v : Ideal (𝓞 F), v.IsMaximal →
      HasProd (fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v} =>
        eulerFac E M c.1) (eulerF F E M v)) →
    lText F E M = lValEta E M
end CMEul



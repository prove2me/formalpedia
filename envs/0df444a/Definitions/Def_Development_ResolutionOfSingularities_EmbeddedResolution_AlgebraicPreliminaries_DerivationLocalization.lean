-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:55.934506+00:00
-- url     : https://prove2.me/theorems/d69ea69c-40c1-492d-9121-d0838639a289
-- title:
--   Derivation Localization
-- statement:
--   Definitions and structural lemmas for Derivation Localization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DerivationLocalization.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w x
variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]
namespace Derivation
theorem isUnit_algebraMap_moduleEnd (M : Submonoid S) [IsLocalization M S'] (y : M) :
    IsUnit ((algebraMap S (Module.End S N)) (y : S)) := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units (M := M) S' y
  have hcomm : ∀ (s : S) (c : S') (n : N), c • s • n = s • c • n := by
    intro s c n
    rw [← IsScalarTower.algebraMap_smul S' s n, ← IsScalarTower.algebraMap_smul S' s (c • n),
      smul_smul, smul_smul, mul_comm]
  have h1 : ∀ n : N, (y : S) • (((u⁻¹ : S'ˣ) : S') • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) (((u⁻¹ : S'ˣ) : S') • n), ← hu, smul_smul,
      u.mul_inv, one_smul]
  have h2 : ∀ n : N, ((u⁻¹ : S'ˣ) : S') • ((y : S) • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) n, ← hu, smul_smul, u.inv_mul, one_smul]
  exact ⟨⟨(algebraMap S (Module.End S N)) (y : S),
    { toFun := fun n => ((u⁻¹ : S'ˣ) : S') • n
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s n => hcomm s ((u⁻¹ : S'ˣ) : S') n },
    LinearMap.ext fun n => h1 n, LinearMap.ext fun n => h2 n⟩, rfl⟩
theorem exists_liftToLocalization (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' N, ∀ s : S, D' (algebraMap S S' s) = D s := by
  have hu : ∀ y : M, IsUnit ((algebraMap S (Module.End S N)) (y : S)) := fun y =>
    isUnit_algebraMap_moduleEnd (S' := S') M y
  have : IsLocalizedModule M (KaehlerDifferential.map R R S S') := inferInstance
  refine ⟨(LinearMap.extendScalarsOfIsLocalization M S'
      (IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu)).compDer (KaehlerDifferential.D R S'), fun s => ?_⟩
  show IsLocalizedModule.lift M (KaehlerDifferential.map R R S S') D.liftKaehlerDifferential hu
      (KaehlerDifferential.D R S' (algebraMap S S' s)) = D s
  have key : IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu
        (KaehlerDifferential.map R R S S' (KaehlerDifferential.D R S s))
      = D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun
      (IsLocalizedModule.lift_comp M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu) (KaehlerDifferential.D R S s)
  rw [← KaehlerDifferential.map_D R R S S' s, key]
  exact D.liftKaehlerDifferential_comp_D s
noncomputable def liftToLocalization (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] : Derivation R S' N :=
  (exists_liftToLocalization (S' := S') D M).choose
theorem exists_mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' S', ∀ s : S,
      D' (algebraMap S S' s) = algebraMap S S' (D s) := by
  obtain ⟨D', hD'⟩ :=
    exists_liftToLocalization (S' := S') (N := S') ((Algebra.linearMap S S').compDer D) M
  exact ⟨D', fun s => hD' s⟩
noncomputable def mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] : Derivation R S' S' :=
  (exists_mapToLocalization (S' := S') D M).choose
end Derivation



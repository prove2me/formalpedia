-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:05:15.080882+00:00
-- url     : https://prove2.me/theorems/e566bcd3-b072-42a3-9e3f-0240ca89c1e2
-- title:
--   Log Derivative Ideal Sheaf
-- statement:
--   Definitions and structural lemmas for Log Derivative Ideal Sheaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_map_away

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
theorem map_logDerivIdeal_basicOpen (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)) =
        @logDerivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (P.ideal (X.affineBasicOpen f)) (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  have hUaff : IsAffineOpen U.1 := U.2
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have tower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have loc : IsLocalization.Away f Γ(X, X.basicOpen f) := hUaff.isLocalization_basicOpen f
  have fp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have noeth : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U rfl
  have hP : (P.ideal U).FG := IsNoetherian.noetherian _
  have key := logDerivIdeal_map_away (S' := Γ(X, X.basicOpen f)) k f hP (I.ideal U)
  rw [← P.map_ideal_basicOpen U f, ← I.map_ideal_basicOpen U f]
  exact key
noncomputable def logDerivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) : X.IdealSheafData where
  ideal U := @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)
  map_ideal_basicOpen := map_logDerivIdeal_basicOpen k p P I
noncomputable def logDerivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) : ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I)
end FunctorialResolution.EmbeddedResolution



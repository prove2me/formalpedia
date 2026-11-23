-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__MumfordConstruction_21e99bcdbc2b8b99
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__MumfordConstruction_21e99bcdbc2b8b99
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:11.065875+00:00
-- url     : https://prove2.me/theorems/093fe775-5a40-423d-8823-4d5ba5b9f3a2
-- title:
--   Mumford Construction
-- statement:
--   Definitions and structural lemmas for Mumford Construction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/MumfordConstruction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Published
def MumfordConstruction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Out.AdmBase R (IsLocalRing.maximalIdeal R) →
    ∀ f : R, f ≠ 0 → f ∈ IsLocalRing.maximalIdeal R →
    ∀ (D : Out.DegData R (IsLocalRing.maximalIdeal R)) (mod : Module (𝓞 E) D.toPre.X)
      (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)),
      (letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) →
      (∀ y, PsiUnitOn D.toPre y {x | f ∉ x.asIdeal}) →
      ∃ (t : SAB H (Sp R)) (P : PELUnif (IsLocalRing.maximalIdeal R) t),
        P.D = D ∧ HEq P.mod mod ∧ HEq P.oD oD ∧
          IsProper (t.G.hom ∣_ (PrimeSpectrum.basicOpen f : (Sp R).Opens))
end GlobalTheory.Published



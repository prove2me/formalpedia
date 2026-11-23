-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:37.791936+00:00
-- url     : https://prove2.me/theorems/7346b8a9-47b3-4293-a852-ba547e310305
-- title:
--   FFVMap
-- statement:
--   Definitions and structural lemmas for FFVMap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/FFVMap.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Gen
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k K : Type} [Field k] [Field K]
end Gen
def FFVMapSt0 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    ∀ (T : CDVR) (io : c.F →+* T.Fr), P.map io ∈ FFV (Dw := Dw) T a n
end ReciprocityTheory.ChartRestriction.G.PullbackSections



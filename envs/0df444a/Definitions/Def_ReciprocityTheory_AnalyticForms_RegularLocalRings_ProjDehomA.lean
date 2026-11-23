-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:31.03115+00:00
-- url     : https://prove2.me/theorems/c4b2faf1-1888-432d-9012-86bc621181c2
-- title:
--   Proj Dehom A
-- statement:
--   Definitions and structural lemmas for Proj Dehom A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
abbrev invW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Localization.Away (segreW P p) :=
  Localization.mk 1 ⟨segreW P p, 1, pow_one _⟩
variable [Nonempty K]
section Proj
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
end Proj
end
end ReciprocityTheory.AnForm.R



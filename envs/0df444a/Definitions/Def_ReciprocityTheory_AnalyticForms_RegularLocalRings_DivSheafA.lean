-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:35.927803+00:00
-- url     : https://prove2.me/theorems/10bdfdbb-9131-4b6d-8429-b6bc4bd47e83
-- title:
--   Div Sheaf A
-- statement:
--   Definitions and structural lemmas for Div Sheaf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
section LocGen
variable {W : Scheme.{u}} {ι' : Type*} (V : ι' → W.Opens) (g : ∀ c, Γ(W, V c))
def dsK (x : W) : Ideal (W.presheaf.stalk x) :=
  ⨅ (c) (hc : x ∈ V c), Ideal.span {W.presheaf.germ (V c) x hc (g c)}
variable {V g}
variable (V g)
def dsJ (U : W.affineOpens) : Ideal Γ(W, U) :=
  ⨅ (x) (hx : x ∈ U.1), Ideal.comap (W.presheaf.germ U.1 x hx).hom (dsK V g x)
variable {V g}
end LocGen
section LocGen
variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}
end LocGen
end
end ReciprocityTheory.AnForm.R



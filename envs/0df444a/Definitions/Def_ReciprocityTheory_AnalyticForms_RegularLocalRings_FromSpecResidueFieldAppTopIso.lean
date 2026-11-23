-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:36.209851+00:00
-- url     : https://prove2.me/theorems/5195b3ce-0339-4c3c-bd99-b35846a4f058
-- title:
--   From Spec Residue Field App Top Iso
-- statement:
--   Definitions and structural lemmas for From Spec Residue Field App Top Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean

import Mathlib
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
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))
def constSec (U : S.Opens) : ℂ →+* Γ(S, U) :=
  (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
def constRes (x : S) : ℂ →+* S.residueField x :=
  (S.evaluation ⊤ x trivial).hom.comp (constSec s ⊤)
def CPt (S : Scheme.{0}) : Type := {x : S // IsClosed ({x} : Set S)}
open Classical in

def valHom (x : S) : S.residueField x → ℂ :=
  if h : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ then h.choose else fun _ => 0
def val {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U) : ℂ :=
  valHom s x (S.evaluation U x hx f)
end
end ReciprocityTheory.AnForm.R



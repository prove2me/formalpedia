-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:54.452564+00:00
-- url     : https://prove2.me/theorems/94d8053f-6712-4f26-a7c5-4e4f53ca18b1
-- title:
--   Away Map Eq Of Red
-- statement:
--   Definitions and structural lemmas for Away Map Eq Of Red, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SecGlue.Red
variable {R R₀ : Type} [CommRing R] [CommRing R₀]
abbrev redI (π : R →+* R₀) (S : Type) [CommRing S] [Algebra R S] : Ideal S :=
  (RingHom.ker π).map (algebraMap R S)
def redPsi (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S] [Algebra R S] :
    R₀ →+* S ⧸ redI π S :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨(Ideal.Quotient.mk (redI π S)).comp (algebraMap R S), fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hx⟩
def IsRed (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (S : Type) [CommRing S] [Algebra R S] (u : Sp S ⟶ Y) : Prop :=
  spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (redPsi π hπ S) ≫ g₀
end GlobalTheory.SecGlue.Red



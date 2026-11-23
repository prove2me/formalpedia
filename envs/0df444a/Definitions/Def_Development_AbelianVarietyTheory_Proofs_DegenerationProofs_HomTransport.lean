-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:39.804548+00:00
-- url     : https://prove2.me/theorems/0f737a28-d0dd-4106-b8f1-1c7d2d13be47
-- title:
--   Hom Transport
-- statement:
--   Definitions and structural lemmas for Hom Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
def img (g : N.Gt) : N'.Gt :=
  ⟨I.φ g.b, fun χ => F (g.s (I.e.symm χ)) * I.h (N.c (I.e.symm χ)) * I.h g.b / I.h (N.c (I.e.symm χ) * g.b),
    fun χ χ' => by
      obtain ⟨χ, rfl⟩ := I.e.surjective χ
      obtain ⟨χ', rfl⟩ := I.e.surjective χ'
      rw [← map_add]
      simp only [AddEquiv.symm_apply_apply]
      rw [I.c_eq, I.c_eq, N.c_add]
      have a := I.θ_eq (N.c χ) (N.c χ') g.b
      have b := congrArg F (g.mult χ χ')
      simp only [map_mul] at b
      apply Additive.ofMul.injective
      replace a := congrArg Additive.ofMul a
      replace b := congrArg Additive.ofMul b
      simp only [ofMul_mul, ofMul_div] at a b ⊢
      linear_combination (norm := abel) a + b⟩
def ofIso {M M' : NumD O} (J : NumD.Iso M M') : NumD.Hom (RingHom.id O) M M' where
  φ := J.φ.toMonoidHom
  h := J.h
  h_one := J.h_one
  θ_eq := J.θ_eq
  σ_eq := J.σ_eq
  lam := J.lam
  th_eq := J.th_eq
  e := J.e
  c_eq := J.c_eq
  ψ_eq := J.ψ_eq
def isoOfBijective {M M' : NumD O} (J : NumD.Hom (RingHom.id O) M M') (hJ : Function.Bijective J.φ) :
    NumD.Iso M M' where
  φ := MulEquiv.ofBijective J.φ hJ
  h := J.h
  h_one := J.h_one
  θ_eq := J.θ_eq
  σ_eq := J.σ_eq
  lam := J.lam
  th_eq := J.th_eq
  e := J.e
  c_eq := J.c_eq
  ψ_eq := J.ψ_eq
end GlobalTheory.Ex.NumD.Hom
end



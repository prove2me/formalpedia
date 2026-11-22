-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:30.023589+00:00
-- url     : https://prove2.me/theorems/09ba5367-2cc0-41b2-8176-4b97aa38e6f8
-- title:
--   Heckebasic
-- statement:
--   Definitions and structural lemmas for Heckebasic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckebasic.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace Formalism.UG.P
open Formalism.UG
section Generic
variable {G : Type} [Group G]
end Generic
section Basis
variable {G : Type} [Group G]
theorem mk_out_dc (K : Subgroup G) (g : G) :
    ∃ a b : K, Quotient.out (DoubleCoset.mk K K g) = (a : G) * g * b := by
  obtain ⟨a, ha, b, hb, e⟩ := (DoubleCoset.eq K K g (Quotient.out (DoubleCoset.mk K K g))).1
    (DoubleCoset.out_eq' K K _).symm
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
theorem biInv_mk_out {k : Type} (K : Subgroup G) (f : G → k) (hf : IsBiInv K f) (g : G) :
    f (Quotient.out (DoubleCoset.mk K K g)) = f g := by
  obtain ⟨a, b, e⟩ := mk_out_dc K g
  rw [e]
  exact hf a b g
def toFs (k : Type) [CommRing k] (K : Subgroup G) (f : Hecke k K) : ClassSet K K →₀ k :=
  Finsupp.ofSupportFinite (fun c => (f : G → k) (Quotient.out c)) (by
    obtain ⟨S, hS⟩ := f.2.2
    refine (S.finite_toSet.image (DoubleCoset.mk K K)).subset ?_
    intro c hc
    obtain ⟨s, hs, a, b, e⟩ := hS (Quotient.out c) hc
    exact ⟨s, hs, ((DoubleCoset.eq K K s (Quotient.out c)).2 ⟨a, a.2, b, b.2, e⟩).trans
      (DoubleCoset.out_eq' K K c)⟩)
theorem toFs_apply (k : Type) [CommRing k] (K : Subgroup G) (f : Hecke k K) (c : ClassSet K K) :
    toFs k K f c = (f : G → k) (Quotient.out c) := rfl
def ofFs (k : Type) [CommRing k] (K : Subgroup G) (c : ClassSet K K →₀ k) : Hecke k K :=
  ⟨fun g => c (DoubleCoset.mk K K g), by
    refine ⟨fun a b g => ?_, ?_⟩
    · exact congrArg c ((DoubleCoset.eq K K g ((a : G) * g * b)).2 ⟨a, a.2, b, b.2, rfl⟩).symm
    · refine ⟨c.support.image Quotient.out, fun g hg => ?_⟩
      refine ⟨Quotient.out (DoubleCoset.mk K K g),
        Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), ?_⟩
      obtain ⟨a, ha, b, hb, e⟩ := (DoubleCoset.eq K K (Quotient.out (DoubleCoset.mk K K g)) g).1
        (DoubleCoset.out_eq' K K (DoubleCoset.mk K K g))
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩
end Basis
def heckeEquiv {G : Type} [Group G] (K : Subgroup G) (k : Type) [CommRing k] :
    Hecke k K ≃ₗ[k] (ClassSet K K →₀ k) where
  toFun := toFs k K
  invFun := ofFs k K
  map_add' f f' := by
    ext c
    simp only [toFs_apply, Finsupp.add_apply, Submodule.coe_add, Pi.add_apply]
  map_smul' r f := by
    ext c
    simp only [toFs_apply, Finsupp.smul_apply, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv f := by
    apply Subtype.ext
    funext g
    exact biInv_mk_out K _ f.2.1 g
  right_inv c := by
    ext d
    show c (DoubleCoset.mk K K (Quotient.out d)) = c d
    rw [DoubleCoset.out_eq']
end Formalism.UG.P



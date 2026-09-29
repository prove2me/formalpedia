-- Prove2me | solution 1 for AddMonoidHom.natCard_ker_comp_eq_mul_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/cabe4c66-2c82-5ccd-a24e-7d6f4d7b8310

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective

set_option autoImplicit false

namespace P2mKerMul

variable {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]

def kerMap (f : A →+ B) (g : B →+ C) : (g.comp f).ker →+ g.ker :=
  (f.domRestrict (g.comp f).ker).codRestrict g.ker fun x => by
    rw [AddMonoidHom.domRestrict_apply, AddMonoidHom.mem_ker]
    have hx := x.2
    rwa [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply] at hx

@[scoped simp] theorem kerMap_apply (f : A →+ B) (g : B →+ C) (x : (g.comp f).ker) :
    (kerMap f g x : B) = f x := rfl

theorem kerMap_surjective (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Function.Surjective (kerMap f g) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ (g.comp f).ker := by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
    rwa [AddMonoidHom.mem_ker] at hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

theorem ker_le (f : A →+ B) (g : B →+ C) : f.ker ≤ (g.comp f).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx, map_zero]

theorem ker_kerMap (f : A →+ B) (g : B →+ C) :
    (kerMap f g).ker = f.ker.addSubgroupOf (g.comp f).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker,
    ← kerMap_apply]
  exact ⟨fun h => by rw [h, AddSubgroup.coe_zero], fun h => Subtype.ext h⟩

theorem natCard_ker_comp (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker := by
  calc Nat.card (g.comp f).ker
      = Nat.card ((g.comp f).ker ⧸ (kerMap f g).ker) * Nat.card (kerMap f g).ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card g.ker * Nat.card f.ker := by
        rw [Nat.card_congr
            (QuotientAddGroup.quotientKerEquivOfSurjective _ (kerMap_surjective f g hf)).toEquiv,
          ker_kerMap, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (ker_le f g)).toEquiv]

end P2mKerMul
p2m_reactivate "P2MW.S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective.P2mKerMul"

theorem solution {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker :=
  P2mKerMul.natCard_ker_comp f g hf

end S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective
end P2MW
export P2MW.S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective (solution)

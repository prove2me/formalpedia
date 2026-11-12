-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel
-- name    : OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:09.913671+00:00
-- url     : https://prove2.me/theorems/8e618377-010e-4e48-9e16-269a72043b9f
-- title:
--   Generic semilinear (9.7.b) field-model realization $F_{r^s}\rtimes V^*$
-- statement:
--   A module-level generic interface realizing the Frobenius group $F_{r^s}\rtimes V^*$ (Bender–Glauberman Appendix C) inside a group, via kernel and complement transport.
--
--   Main declarations: `kernelTransport` (Kernel transport); `complementEquiv` (The C ≃ normOneUnits r s equivalence packaged from an injective μ); `complementTransport` (Complement transport).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet

namespace OddOrder.RepresentationTheory.SemilinearFieldModel

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

/-- **Kernel transport** `additiveFieldGroup r s →* G` for a field iso `e : Additive ↥E ≃+ 𝔽_{r^s}`.
Coordinate-wise `m ↦ ↑(toMul (e.symm (toAdd m)))`. -/
noncomputable def kernelTransport {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) :
    additiveFieldGroup r s →* G where
  toFun := fun m => ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥E) : G)
  map_one' := by simp
  map_mul' := fun m n => by simp [toAdd_mul, map_add, toMul_add]

@[simp] theorem kernelTransport_apply {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) (m : additiveFieldGroup r s) :
    kernelTransport e m = ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥E) : G) :=
  rfl

/-- The `C ≃* normOneUnits r s` equivalence packaged from an injective `μ : ↥C →* 𝔽_{r^s}ˣ` with
`μ.range = normOneUnits r s`.  Its inverse, post-composed with `C ↪ G`, is `complementTransport`. -/
noncomputable def complementEquiv {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    ↥C ≃* ↥(normOneUnits r s) :=
  MulEquiv.ofBijective
    ({ toFun := fun c => ⟨μ c, hμ_range ▸ MonoidHom.mem_range.mpr ⟨c, rfl⟩⟩
       map_one' := by ext; simp
       map_mul' := fun a b => by ext; simp } : ↥C →* ↥(normOneUnits r s))
    ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
     fun u => by
       obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
       exact ⟨v, Subtype.ext hv⟩⟩

/-- **Complement transport** `normOneUnits r s →* G` inverting `μ` and including back into `G`. -/
noncomputable def complementTransport {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    ↥(normOneUnits r s) →* G :=
  C.subtype.comp (complementEquiv μ hμ_inj hμ_range).symm.toMonoidHom

end OddOrder.RepresentationTheory.SemilinearFieldModel



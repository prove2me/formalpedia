-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25Final
-- name    : OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25Final
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:09:12.645934+00:00
-- url     : https://prove2.me/theorems/c2658e9c-9f80-479b-bdb5-09c83f808029
-- title:
--   BG Theorem 2.5 at the group level, with $V_P$ irreducible discharged for extraspecial $P$
-- statement:
--   Combines the group-level divisibility and $C_V(H)$ conclusions of Theorem 2.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (stated conditionally on irreducibility of $V_P$, BG Proposition 2.2(a)) with the Clifford-theory result that discharges that hypothesis for an extraspecial $P$, giving the fully grounded group-level Theorem 2.5 for extraspecial $P\trianglelefteq G$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ExtraspecialThm25Final.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ExtraspecialThm25Final.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25Group
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordConjugateChar

namespace OddOrder.RepresentationTheory

open Representation Module EigenspaceUnderCyclicAction

variable {G : Type*} [Group G]

/-- The Clifford-side conjugation automorphism `conjNormalMulAut P x` (`CliffordAlgClosed.lean`) and
the eigenspace/keystone-side `conjAutOfNormal P x` (`ExtraspecialThm25Group.lean`) of a normal
subgroup `P` coincide: both are the automorphism `p ↦ x p x⁻¹`. -/
theorem conjNormalMulAut_eq_conjAutOfNormal (P : Subgroup G) [P.Normal] (x : G) :
    conjNormalMulAut P x = conjAutOfNormal P x :=
  MulEquiv.ext fun p =>
    Subtype.ext (by rw [conjNormalMulAut_apply_coe, conjAutOfNormal_apply_coe])

/-- **BG Theorem 2.5, `C_V(H)` part, for an extraspecial `P` (fully grounded).**
Same setup as `finrank_modEq_of_extraspecial`; in addition assume `dim V ≥ 2` and that `x` has no
nonzero fixed vector (`C_V(H) = C_V(x) = V₀ = 0`).  Then `dim V = h - 1`, i.e. `h = dim V + 1`.
Equivalently (contrapositive), `h ≠ dim V + 1 ⟹ C_V(H) ≠ 0` — the half of Theorem 2.5 feeding the
even/odd contradiction of Theorem 3.4. -/
theorem finrank_eq_sub_one_of_extraspecial
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) [ρ.IsIrreducible] (hρf : Function.Injective ρ)
    (hPe : OddOrder.GroupTheory.IsExtraspecial p ↥P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hcop : Nat.Coprime h (Nat.card P))
    (hgen : Subgroup.closure ((P : Set G) ∪ {x}) = ⊤)
    (hxZ : ∀ z : ↥P, z ∈ Subgroup.center ↥P → conjAutOfNormal P x z = z)
    (hCP : ∀ k : ZMod h, k ≠ 0 → ∀ q : ↥P,
        (conjAutOfNormal P x ^ k.val) q = q → q ∈ Subgroup.center ↥P)
    (hV2 : 2 ≤ Module.finrank F V)
    (hCV : cyclicEigenspaceFinDim ε (ρ.asGroupHom x : Module.End F V) (0 : Fin h) = 0) :
    (Module.finrank F V : ℤ) = (h : ℤ) - 1 := by
  have hVP : Representation.IsIrreducible (ρ.comp P.subtype) :=
    restriction_isIrreducible_of_extraspecial ρ hρf hPe x hgen
      (fun z hz => by rw [conjNormalMulAut_eq_conjAutOfNormal]; exact hxZ z hz)
  exact finrank_eq_sub_one_of_faithful_irreducible_of_centralizer P ρ hρf
    hPe.commutator_eq_center.le x hxh hh2 hprim hh hcop hVP hCP hV2 hCV

end OddOrder.RepresentationTheory



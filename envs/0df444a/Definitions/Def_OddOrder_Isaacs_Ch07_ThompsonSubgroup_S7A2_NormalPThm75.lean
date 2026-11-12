-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
-- name    : OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:58.160299+00:00
-- url     : https://prove2.me/theorems/9f6c9f16-1684-4681-9012-4ec08870104b
-- title:
--   Isaacs FGT Ch. 7 (Thompson subgroup), part S7A2: Lemma 7.3, Theorem 7.5 (normal $P$)
-- statement:
--   Isaacs, *Finite Group Theory*, Chapter 7, pp. 201-208: the formal proof of Lemma 7.3, Theorem 7.5 for normal $P$, and the supporting action infrastructure.
--
--   Main definitions: `actionCentralizer` ($C_V(P)$, the elements of $V$ fixed by $P$), `quotientActionHom` (the induced action on $V/U$ for an invariant normal subgroup $U$), `quotientActionKernel` (the kernel of that action, the subgroup $K$ of Theorem 7.5) and `quotientActionFaithfulHom` (the faithful action of $A/K$ on $V/U$).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The image of any subgroup normalizes the image of a normal subgroup.

This is the normalizer adapter used in the reduced `GL(2,p)` branch of Isaacs Thm 7.5:
`P` normalizes `O_{p'}(G)`, so its faithful image normalizes the image of `O_{p'}(G)`. -/
theorem map_le_normalizer_map_of_normal
    {A B : Type*} [Group A] [Group B] {φ : A →* B} {P L : Subgroup A} [L.Normal] :
    P.map φ ≤ Subgroup.normalizer ((L.map φ) : Set B) := by
  rintro _ ⟨p, _hpP, rfl⟩
  have hLnorm : L.Normal := inferInstance
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨l, hlL, rfl⟩
    refine ⟨p * l * p⁻¹, hLnorm.conj_mem l hlL p, ?_⟩
    simp [map_mul]
  · rintro ⟨l, hlL, hyl⟩
    have hconj : p⁻¹ * l * p ∈ L := by
      simpa using hLnorm.conj_mem l hlL p⁻¹
    refine ⟨p⁻¹ * l * p, hconj, ?_⟩
    calc
      φ (p⁻¹ * l * p) = (φ p)⁻¹ * φ l * φ p := by simp [map_mul]
      _ = y := by rw [hyl]; group

/-- Action-centralizer notation for `C_V(P)`: the elements of `V` fixed by every element of `P`
under `φ : A →* MulAut V`. -/
def actionCentralizer {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P : Subgroup A) : Subgroup V :=
  Subgroup.fixedPointsOfMulAut (φ.comp P.subtype)

@[simp]
theorem mem_actionCentralizer {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {P : Subgroup A} {v : V} :
    v ∈ actionCentralizer φ P ↔ ∀ p : P, (φ p) v = v :=
  Iff.rfl

@[simp]
theorem mem_actionCentralizer_top {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {v : V} :
    v ∈ actionCentralizer φ (⊤ : Subgroup A) ↔ ∀ a : A, (φ a) v = v := by
  constructor
  · intro hv a
    exact hv ⟨a, trivial⟩
  · intro hv a
    exact hv a

/-- If `P ≤ Q`, then `C_V(Q) ≤ C_V(P)`. -/
theorem actionCentralizer_antitone {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {P Q : Subgroup A} (hPQ : P ≤ Q) :
    actionCentralizer φ Q ≤ actionCentralizer φ P := by
  intro v hv p
  exact hv ⟨p, hPQ p.property⟩

/-- The fixed subgroup of a generated subgroup is the intersection of the fixed subgroups.

This is the formal version of the Theorem 7.5 step: if both `P` and `Q` act trivially on `U`,
then so does `⟨P, Q⟩`. -/
theorem actionCentralizer_sup {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) :
    actionCentralizer φ (P ⊔ Q) = actionCentralizer φ P ⊓ actionCentralizer φ Q := by
  ext v
  constructor
  · intro hv
    exact ⟨actionCentralizer_antitone (show P ≤ P ⊔ Q from le_sup_left) hv,
      actionCentralizer_antitone (show Q ≤ P ⊔ Q from le_sup_right) hv⟩
  · rintro ⟨hP, hQ⟩ x
    have hx : (x : A) ∈ Subgroup.closure ((P : Set A) ∪ (Q : Set A)) := by
      simpa [Subgroup.sup_eq_closure] using x.property
    refine Subgroup.closure_induction
      (p := fun a _ => (φ a) v = v) ?mem ?one ?mul ?inv hx
    · intro a ha
      rcases ha with ha | ha
      · exact hP ⟨a, ha⟩
      · exact hQ ⟨a, ha⟩
    · simp
    · intro a b _ _ ha hb
      simp [map_mul, hb, ha]
    · intro a _ ha
      calc
        (φ a⁻¹) v = (φ a)⁻¹ v := by rw [map_inv]
        _ = (φ a)⁻¹ ((φ a) v) := by rw [ha]
        _ = v := MulAut.inv_apply_self V (φ a) v

/-- Any subgroup fixed pointwise by the whole acting group is invariant under the action. -/
theorem isAInvariant_of_le_actionCentralizer_top {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V}
    (hU : U ≤ actionCentralizer φ (⊤ : Subgroup A)) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ U := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a u hu
  rw [(mem_actionCentralizer_top.mp (hU hu)) a]
  exact hu

/-- If `G = ⟨P, Q⟩`, then `U = C_V(P) ∩ C_V(Q)` is invariant under the whole action.

This is the invariant-subgroup bridge needed before passing to `V/U` in Isaacs Thm 7.5. -/
theorem actionCentralizer_inf_isAInvariant_of_sup_eq_top
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {P Q : Subgroup A} (hPQ : P ⊔ Q = ⊤) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ
      (actionCentralizer φ P ⊓ actionCentralizer φ Q) := by
  apply isAInvariant_of_le_actionCentralizer_top
  rw [← actionCentralizer_sup, hPQ]

/-- The induced action on `V/U` for an invariant normal subgroup `U`. -/
noncomputable def quotientActionHom {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) : A →* MulAut (V ⧸ U) :=
  OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU

@[simp]
theorem quotientActionHom_apply_mk' {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (a : A) (v : V) :
    (quotientActionHom φ hU a) (QuotientGroup.mk' U v) =
      QuotientGroup.mk' U ((φ a) v) :=
  OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
    hU a v

/-- Kernel of the induced action on `V/U`. In Isaacs Thm 7.5 this is the subgroup `K`
acting trivially on `V/U`. -/
noncomputable def quotientActionKernel {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) : Subgroup A :=
  (quotientActionHom φ hU).ker

/-- The kernel of the induced quotient action is normal in the acting group. -/
instance quotientActionKernel_normal {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    (quotientActionKernel φ hU).Normal := by
  change (quotientActionHom φ hU).ker.Normal
  infer_instance

/-- The faithful action of `A/K` on `V/U`, where `K` is the kernel of the induced action.

This is the formal version of the Thm 7.5 step "the quotient group `G/K` acts faithfully on
`V/U`". -/
noncomputable def quotientActionFaithfulHom {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    A ⧸ quotientActionKernel φ hU →* MulAut (V ⧸ U) :=
  QuotientGroup.kerLift (quotientActionHom φ hU)

@[simp]
theorem quotientActionFaithfulHom_mk' {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (a : A) :
    quotientActionFaithfulHom φ hU
        (QuotientGroup.mk' (quotientActionKernel φ hU) a) =
      quotientActionHom φ hU a :=
  rfl

end OddOrder.Isaacs.Ch07



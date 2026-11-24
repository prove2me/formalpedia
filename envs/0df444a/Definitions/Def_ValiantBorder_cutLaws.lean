-- Prove2me | Definitions.Def_ValiantBorder_cutLaws
-- name    : ValiantBorder_cutLaws
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:02:35.638082+00:00
-- url     : https://prove2.me/theorems/a0b7647b-2137-4800-a665-f433852256cb
-- title:
--   Exchange laws on chambers of a unitriangular group
-- statement:
--   The chambers are upper unitriangular binary matrices; a near pair joins a chamber to its translate by a simple transvection. An exchange law expresses a product of slot-equality constraints as a finite sum of products of local tables. A family of such laws specifies which loads it covers and bounds the lengths of strings communicated along its channels.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Laws.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Laws.lean.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_fieldCases

/-! Claude (Anthropic), *VP ≠ VNP over every field*, section on exchange identities.
Adapted from the public Lean release at revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
The gate model for this project is in the mission's public statement file. -/
namespace Nc.Tower
open Matrix Finset

/-- The group SL_h(F₂) = GL_h(F₂). -/
abbrev SL2 (h : ℕ) : Type := Matrix.SpecialLinearGroup (Fin h) (ZMod 2)

theorem sl_pow_mem {G : Type*} [Group G] [Finite G] (S : Submonoid G) {a : G} (ha : a ∈ S) : a⁻¹ ∈ S := by
  have h : a⁻¹ = a ^ (orderOf a - 1) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
  rw [h]
  exact S.pow_mem ha _

/-- Upper unitriangular matrices. -/
def U (h : ℕ) : Subgroup (SL2 h) where
  carrier := {A | ∀ i j, (j < i → A.1 i j = 0) ∧ A.1 i i = 1}
  one_mem' := fun i j => ⟨fun hij => Matrix.one_apply_ne hij.ne', Matrix.one_apply_eq i⟩
  mul_mem' := by
    intro A B hA hB i j
    have h1 : ∀ i j k, j < i → A.1 i k * B.1 k j = 0 := by
      intro i j k hij
      rcases lt_or_ge k i with hk | hk
      · rw [(hA i k).1 hk, zero_mul]
      · rw [(hB k j).1 (lt_of_lt_of_le hij hk), mul_zero]
    refine ⟨fun hij => ?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun k _ => h1 i j k hij
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [(hA i i).2, (hB i i).2, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [(hA i k).1 h, zero_mul]
        · rw [(hB k i).1 h, mul_zero]
      · simp
  inv_mem' := by
    intro A hA
    let S : Submonoid (SL2 h) :=
      { carrier := {A | ∀ i j, (j < i → A.1 i j = 0) ∧ A.1 i i = 1}
        one_mem' := fun i j => ⟨fun hij => Matrix.one_apply_ne hij.ne', Matrix.one_apply_eq i⟩
        mul_mem' := by
          intro A B hA hB i j
          have h1 : ∀ i j k, j < i → A.1 i k * B.1 k j = 0 := by
            intro i j k hij
            rcases lt_or_ge k i with hk | hk
            · rw [(hA i k).1 hk, zero_mul]
            · rw [(hB k j).1 (lt_of_lt_of_le hij hk), mul_zero]
          refine ⟨fun hij => ?_, ?_⟩
          · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
            exact Finset.sum_eq_zero fun k _ => h1 i j k hij
          · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
            · rw [(hA i i).2, (hB i i).2, one_mul]
            · intro k _ hk
              rcases lt_or_gt_of_ne hk with h | h
              · rw [(hA i k).1 h, zero_mul]
              · rw [(hB k i).1 h, mul_zero]
            · simp }
    exact sl_pow_mem S hA

/-- The index j as a row. -/
def lo {h : ℕ} (j : Fin (h - 1)) : Fin h := ⟨j.1, by omega⟩

/-- The index j + 1 as a column. -/
def hi {h : ℕ} (j : Fin (h - 1)) : Fin h := ⟨j.1 + 1, by omega⟩

theorem lo_lt_hi {h : ℕ} (j : Fin (h - 1)) : lo j < hi j := by
  rw [Fin.lt_def]; simp [lo, hi]

theorem lo_ne_hi {h : ℕ} (j : Fin (h - 1)) : lo j ≠ hi j := (lo_lt_hi j).ne

/-- The simple root elements 1 + E_{j,j+1}. -/
def x (h : ℕ) (j : Fin (h - 1)) : U h :=
  ⟨⟨Matrix.transvection (lo j) (hi j) 1, Matrix.det_transvection_of_ne _ _ (lo_ne_hi j) 1⟩, by
    intro a b
    refine ⟨fun hab => ?_, ?_⟩
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_ne hab.ne', Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (lo_lt_hi j).not_gt
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨h1, h2⟩
      exact lo_ne_hi j (h1.trans h2.symm)⟩

theorem x_val (h : ℕ) (j : Fin (h - 1)) :
    ((x h j : SL2 h) : Matrix (Fin h) (Fin h) (ZMod 2)) = 1 + Matrix.single (lo j) (hi j) 1 := rfl


noncomputable instance (h : ℕ) : Fintype (U h) := Fintype.ofFinite _


/-- One element of every pair of a free involution. -/
theorem exists_first {Q : Type*} [Finite Q] (i : Q → Q) (hi : ∀ q, i (i q) = q) (hne : ∀ q, i q ≠ q) :
    ∃ F : Q → Prop, ∀ q, F (i q) ↔ ¬ F q := by
  obtain ⟨N, ⟨φ⟩⟩ := Finite.exists_equiv_fin Q
  refine ⟨fun q => φ q < φ (i q), fun q => ?_⟩
  simp only [hi, not_lt]
  constructor
  · exact fun h => h.le
  · exact fun h => lt_of_le_of_ne h fun e => hne q (φ.injective e)


variable {h : ℕ} [NeZero h]

theorem x_ne_one (l : Fin (h - 1)) : x h l ≠ 1 := by
  intro e
  have h1 := congrFun (congrFun (congrArg (fun u : U h => u.1.1) e) (lo l)) (hi l)
  simp only [x_val] at h1
  rw [Matrix.add_apply, Matrix.single_apply_same] at h1
  have h2 : ((1 : U h).1.1 : Matrix (Fin h) (Fin h) (ZMod 2)) (lo l) (hi l) = 0 :=
    Matrix.one_apply_ne (lo_ne_hi l)
  rw [h2, Matrix.one_apply_ne (lo_ne_hi l)] at h1
  exact absurd h1 (by decide)

theorem x_mul_self (l : Fin (h - 1)) : x h l * x h l = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  refine (Matrix.transvection_mul_transvection_same _ _ (lo_ne_hi l) (1 : ZMod 2) 1).trans ?_
  rw [show (1 : ZMod 2) + 1 = 0 from rfl, Matrix.transvection_zero]
  rfl


theorem exists_firstU (l : Fin (h - 1)) : ∃ F : U h → Prop, ∀ u, F (x h l * u) ↔ ¬ F u := by
  refine exists_first _ (fun u => ?_) fun u e => ?_
  · rw [← mul_assoc, x_mul_self, one_mul]
  · exact x_ne_one l (by simpa using e)

/-- The first elements of the pairs {u, x_l u}. -/
def FU (l : Fin (h - 1)) : U h → Prop := (exists_firstU l).choose


/-- Near pairs of the unitriangular group. -/
abbrev NN (h : ℕ) [NeZero h] : Type := {p : Fin (h - 1) × U h // FU p.1 p.2}

noncomputable instance instFintypeNN : Fintype (NN h) := Fintype.ofFinite _

noncomputable instance instDecNN : DecidableEq (NN h) := Classical.decEq _

noncomputable instance instDecU : DecidableEq (U h) := Classical.decEq _


def ee (h : ℕ) : ℕ := h * (h - 1) / 2
end Nc.Tower

namespace Nc.G
open Finset

/-- A law. -/
structure Law (F : Type) [CommRing F] where
  /-- roles -/
  Ro : Type
  /-- slots -/
  Sl : Type
  /-- channels -/
  Cn : Type
  /-- indices -/
  I : Type
  [fRo : Fintype Ro]
  [dRo : DecidableEq Ro]
  [fSl : Fintype Sl]
  [dSl : DecidableEq Sl]
  [fCn : Fintype Cn]
  [dCn : DecidableEq Cn]
  [fI : Fintype I]
  [dI : DecidableEq I]
  /-- one end of a slot -/
  a : Sl → Ro
  /-- the other end of a slot -/
  b : Sl → Ro
  ab : ∀ e, a e ≠ b e
  /-- one end of a channel -/
  c : Cn → Ro
  /-- the other end of a channel -/
  d : Cn → Ro
  cd : ∀ ν, c ν ≠ d ν
  /-- length of labels -/
  lam : ℕ
  /-- labels -/
  lab : I → Fin lam → Bool
  lab_inj : Function.Injective lab
  /-- lengths of strings -/
  len : I → Cn → ℕ
  /-- the tables: a role sees the bits of its slots and the strings of its channels -/
  tab : (p : Ro) → (i : I) → ({e // a e = p ∨ b e = p} → Bool) →
    ((ν : {ν // c ν = p ∨ d ν = p}) → Fin (len i ν) → Bool) → F
  /-- the identity -/
  law : ∀ X : Ro → Sl → Bool, (if ∀ e, X (a e) e = X (b e) e then (1 : F) else 0) =
    ∑ i, ∑ g : ∀ ν, Fin (len i ν) → Bool, ∏ p, tab p i (fun e => X p e) (fun ν => g ν)
  /-- indices that agree along channels are equal -/
  conn : ∀ ι : Ro → I, (∀ ν, ι (c ν) = ι (d ν)) → ∀ p q, ι p = ι q

attribute [instance] Law.fRo Law.dRo Law.fSl Law.dSl Law.fCn Law.dCn Law.fI Law.dI


end Nc.G

namespace Nc.Tow
open Finset Nc.G Nc.Price

/-- The norm of loads on pairs of chambers at a vertex. -/
noncomputable def vN2 {Fl : Type} [Fintype Fl] [DecidableEq Fl] (b : ℕ) (n : Sym2 Fl → ℕ) : ℝ :=
  ((b : ℝ) * (b - 1) / 2) * ∑ q : Sym2 Fl, if q.IsDiag then 0 else (n q : ℝ) ^ 2

/-- The laws for one local structure: chambers `Fl`, near pairs `Nr`. -/
structure VLaws (F : Type) [CommRing F] {Fl Nr : Type} [Fintype Fl] [DecidableEq Fl] [Fintype Nr]
    [DecidableEq Nr] (cN dN : Nr → Fl) (r b : ℕ) where
  /-- kinds of laws -/
  Di : Type
  [fD : Fintype Di]
  [dD : DecidableEq Di]
  /-- the laws -/
  L : Di → Law F
  /-- roles are the chambers -/
  ro : ∀ d, (L d).Ro ≃ Fl
  /-- channels are the near pairs -/
  cn : ∀ d, (L d).Cn ≃ Nr
  ends : ∀ d ν, s(ro d ((L d).c ν), ro d ((L d).d ν)) = s(cN (cn d ν), dN (cn d ν))
  lam_pos : ∀ d, 1 ≤ (L d).lam
  nonempty : ∀ d, Nonempty (L d).I
  /-- the scale -/
  a₁ : ℕ
  a₁_pos : 0 < a₁
  /-- the constant of the contraction -/
  C₁ : ℝ
  C₁_nonneg : 0 ≤ C₁
  /-- its integer form -/
  G₁ : ℕ
  G₁_le : (G₁ : ℝ) ≤ 2 * C₁ * (a₁ : ℝ) ^ 2
  /-- every load is below one of finitely many -/
  L1 : ∀ (n : Sym2 Fl → ℕ) (t : ℕ), √(vN2 b n) ≤ (a₁ : ℝ) * t → ∃ d, ∀ q : Sym2 Fl, ¬ q.IsDiag →
    n q ≤ (univ.filter fun e : (L d).Sl => s(ro d ((L d).a e), ro d ((L d).b e)) = q).card * t
  /-- the strings are short -/
  L2 : ∀ d i, r * b * ∑ ν, ((L d).lam + (L d).len i ν) ^ 2 ≤ G₁

attribute [instance] VLaws.fD VLaws.dD


end Nc.Tow

namespace Nc.Vp
open Nc.Tower

/-- One end of a near pair of U h. -/
abbrev cNear {h : ℕ} [NeZero h] (ν : NN h) : U h := ν.1.2

/-- The other end of a near pair of U h. -/
abbrev dNear {h : ℕ} [NeZero h] (ν : NN h) : U h := x h ν.1.1 * ν.1.2


end Nc.Vp



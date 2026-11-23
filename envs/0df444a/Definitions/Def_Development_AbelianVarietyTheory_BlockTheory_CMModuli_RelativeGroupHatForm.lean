-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_RelativeGroupHatForm
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_RelativeGroupHatForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:10.904807+00:00
-- url     : https://prove2.me/theorems/ee5e2795-c4e6-47f8-89e6-79a5fcadd46d
-- title:
--   Relative Group Hat Form
-- statement:
--   Definitions and structural lemmas for Relative Group Hat Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/RelativeGroupHatForm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
def zhatSubring : Subring (∀ n : ℕ+, ZMod n) where
  carrier := {f | ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (f n) = f m}
  mul_mem' {a b} ha hb m n h := by rw [Pi.mul_apply, map_mul, ha m n h, hb m n h, Pi.mul_apply]
  one_mem' m n h := by rw [Pi.one_apply, map_one, Pi.one_apply]
  add_mem' {a b} ha hb m n h := by rw [Pi.add_apply, map_add, ha m n h, hb m n h, Pi.add_apply]
  zero_mem' m n h := by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  neg_mem' {a} ha m n h := by rw [Pi.neg_apply, map_neg, ha m n h, Pi.neg_apply]
abbrev Zhat : Type := zhatSubring
def Zhat.red (n : ℕ+) : Zhat →+* ZMod n := (Pi.evalRingHom (fun m : ℕ+ => ZMod m) n).comp zhatSubring.subtype
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
abbrev Lhat (D : Datum H) : Type := Zhat ⊗[ℤ] D.La
def hatMul (D : Datum H) (c : 𝓞 E) : Lhat D →ₗ[Zhat] Lhat D :=
  (DistribMulAction.toLinearMap ℤ D.La c).baseChange Zhat
def hatForm (D : Datum H) : LinearMap.BilinForm Zhat (Lhat D) := D.EF.baseChange Zhat
def hatSub (D : Datum H) (𝔞 : Ideal (𝓞 E)) : Submodule Zhat (Lhat D) :=
  Submodule.span Zhat ((fun a : D.La => (1 : Zhat) ⊗ₜ[ℤ] a) '' (𝔞 • (⊤ : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La))
def simGroup (D : Datum H) (l : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) where
  carrier := {g | (∀ c x, g (hatMul D c x) = hatMul D c (g x)) ∧
    ∃ ν : Zhatˣ, Zhat.red ⟨l.A, l.A_pos⟩ ν = 1 ∧ ∀ x y, hatForm D (g x) (g y) = ν * hatForm D x y}
  mul_mem' := by
    rintro g h ⟨hg, ν, hν, eg⟩ ⟨hh, ν', hν', eh⟩
    refine ⟨fun c x => ?_, ν * ν', by rw [Units.val_mul, map_mul, hν, hν', _root_.mul_one], fun x y => ?_⟩
    · show g (h _) = hatMul D c (g (h x))
      rw [hh, hg]
    · show hatForm D (g (h x)) (g (h y)) = _
      rw [eg, eh, Units.val_mul, _root_.mul_assoc]
  one_mem' := ⟨fun _ _ => rfl, 1, map_one _, fun x y => by simp⟩
  inv_mem' := by
    rintro g ⟨hg, ν, hν, eg⟩
    refine ⟨fun c x => ?_, ν⁻¹, ?_, fun x y => ?_⟩
    · apply g.injective
      show g (g.symm _) = g (hatMul D c (g.symm x))
      rw [hg, g.apply_symm_apply, g.apply_symm_apply]
    · have := congrArg (Zhat.red ⟨l.A, l.A_pos⟩) ν.inv_mul
      rwa [map_mul, hν, _root_.mul_one, map_one] at this
    · have := eg (g.symm x) (g.symm y)
      rw [g.apply_symm_apply, g.apply_symm_apply] at this
      show hatForm D (g.symm x) (g.symm y) = _
      rw [this, Units.inv_mul_cancel_left]
def congSub (D : Datum H) (𝔞 : Ideal (𝓞 E)) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) where
  carrier := {g | ∀ x, g x - x ∈ hatSub D 𝔞}
  mul_mem' {g h} hg hh x := by
    have := (hatSub D 𝔞).add_mem (hg (h x)) (hh x)
    rwa [sub_add_sub_cancel] at this
  one_mem' x := by simp
  inv_mem' {g} hg x := by
    have := (hatSub D 𝔞).neg_mem (hg (g.symm x))
    rwa [g.apply_symm_apply, neg_sub] at this
def trivAt (D : Datum H) (l : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) :=
  congSub D l.Mb ⊓ congSub D (Ideal.span {(l.A : 𝓞 E)})
def relGroup (D : Datum H) (l l₂ : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) := simGroup D l₂ ⊓ trivAt D l
example (D : Datum H) (l : Level H) : LinearEquiv.neg Zhat ∈ simGroup D l :=
  ⟨fun c x => by simp, 1, map_one _, fun x y => by simp⟩
theorem zeta_pow_div {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : zeta n ^ (n / m) = zeta m := by
  obtain ⟨k, rfl⟩ := h
  have hm : 0 < m := Nat.pos_of_mul_pos_right hn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left k hm]
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  field_simp
theorem KA_le {l l₂ : Level H} (h : l.Dvd l₂) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  · have hz : zeta l₂.A ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [SetLike.mem_coe, ← zeta_pow_div l₂.A_pos h.2.2]
    exact pow_mem hz _
def lowerCoeff {l l₂ : Level H} (h : l.Dvd l₂) (c : Coeff l₂) : Coeff l where
  F := c.F
  fin := c.fin
  conj := c.conj
  zeta_mem := by
    have hp : 0 < l₂.M' := Nat.lcm_pos (by have := l₂.three_le; omega) l₂.A_pos
    have hd : l.M' ∣ l₂.M' := Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))
    rw [← zeta_pow_div hp hd]
    exact pow_mem c.zeta_mem _
  le := (KA_le h).trans c.le
variable {D : Datum H} {l l₂ : Level H}
def IsOver (h : l.Dvd l₂) (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (π : Xo₂.X ⟶ Xo.X) : Prop :=
  π ≫ Xo.s = Xo₂.s ≫ spMap (IntermediateField.inclusion (KA_le h)).toRingHom
def PullsBack (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (π : Xo₂.X ⟶ Xo.X) : Prop :=
  ∃ m : SABMap Xo₂.univ.t Xo.univ.t π,
    (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (Xo.univ.eta a).left) ∧
    (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (Xo.univ.etaA a).left)
def ChangesLevelBy (Xo : Moduli D l) (g : Lhat D ≃ₗ[Zhat] Lhat D) (r : Xo.X ⟶ Xo.X) : Prop :=
  ∃ m : SABMap Xo.univ.t Xo.univ.t r,
    (∀ a b : D.La, g (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D l.Mb →
      (Xo.univ.eta b).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧
    (∀ a b : D.La, g (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D (Ideal.span {(l.A : 𝓞 E)}) →
      (Xo.univ.etaA b).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
theorem spMap_inclusion_comp {A B C : IntermediateField ℚ ℂ} (h₁ : A ≤ B) (h₂ : B ≤ C) :
    spMap (IntermediateField.inclusion h₂).toRingHom ≫ spMap (IntermediateField.inclusion h₁).toRingHom =
      spMap (IntermediateField.inclusion (h₁.trans h₂)).toRingHom := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl
def levelMapF (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X} (hπ : IsOver h Xo Xo₂ π)
    (c : Coeff l₂) : Xo₂.XF c ⟶ Xo.XF (lowerCoeff h c) :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, spMap_inclusion_comp]
    rfl)
def endF {Xo : Moduli D l} (r : Xo.X ⟶ Xo.X) (hr : r ≫ Xo.s = Xo.s) (c : Coeff l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc, hr, pullback.condition])
def IsLevelCovering (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X}
    (hπ : IsOver h Xo Xo₂ π) : Prop :=
  ∃ (ρ : relGroup D l l₂ → (Xo₂.X ≅ Xo₂.X)) (hρ : ∀ g, (ρ g).hom ≫ Xo₂.s = Xo₂.s),
    ρ 1 = Iso.refl _ ∧ (∀ g g', ρ (g * g') = ρ g ≪≫ ρ g') ∧
    (∀ g, ChangesLevelBy Xo₂ g.1 (ρ g).hom) ∧
    (∀ g, (ρ g).hom ≫ π = π) ∧
    ∀ c : Coeff l₂,
      IsFinite (levelMapF h hπ c) ∧ Etale (levelMapF h hπ c) ∧ Surjective (levelMapF h hπ c) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo₂.XF c),
        (∀ y : Sp k ⟶ Xo₂.XF c, y ≫ levelMapF h hπ c = x ≫ levelMapF h hπ c →
          ∃ g, x ≫ endF (ρ g).hom (hρ g) c = y) ∧
        ∀ g, x ≫ endF (ρ g).hom (hρ g) c = x ↔ g.1 ∈ trivAt D l₂
def ModuliExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ l : Level H, Nonempty (Moduli D l)
def LevelMapsAndAction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (l l₂ : Level H) (h : l.Dvd l₂) (Xo : Moduli D l) (Xo₂ : Moduli D l₂),
      ∃ (π : Xo₂.X ⟶ Xo.X) (hπ : IsOver h Xo Xo₂ π), PullsBack Xo Xo₂ π ∧
        (∀ π' : Xo₂.X ⟶ Xo.X, IsOver h Xo Xo₂ π' → PullsBack Xo Xo₂ π' → π' = π) ∧
        IsLevelCovering h hπ
def ModuliAndLevels : Prop := ModuliExists ∧ LevelMapsAndAction
def WholeGroupActs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (l : Level H) (Xo : Moduli D l),
      ∃ ρ : simGroup D l → (Xo.X ≅ Xo.X), (∀ g, (ρ g).hom ≫ Xo.s = Xo.s) ∧
        ρ 1 = Iso.refl _ ∧ (∀ g g', ρ (g * g') = ρ g ≪≫ ρ g') ∧
        (∀ g, ChangesLevelBy Xo g.1 (ρ g).hom) ∧ ∀ g, g.1 ∈ trivAt D l → ρ g = Iso.refl _
end GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm



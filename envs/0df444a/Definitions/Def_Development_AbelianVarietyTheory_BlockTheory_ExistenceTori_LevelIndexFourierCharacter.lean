-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:22.833724+00:00
-- url     : https://prove2.me/theorems/b0888b70-8e76-4575-98f4-773b2a0a18ce
-- title:
--   Level Index Fourier Character
-- statement:
--   Definitions and structural lemmas for Level Index Fourier Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LevelIndexFourierCharacter.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def conjHalf (l : Level H) : Ideal (𝓞 E) := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)
theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  have h1 := H.bar_eq (H.bar a)
  have h2 := H.bar_eq a
  rw [h1, h2, IsCMField.complexConj_apply_apply]
theorem bar_mem_of_mem_conjHalf (l : Level H) {a : 𝓞 E} (ha : a ∈ conjHalf l) : H.bar a ∈ l.Mb := by
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha
  have : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) b) = b := bar_bar H b
  rwa [this]
theorem mul_mem_span_level (l : Level H) {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ conjHalf l) :
    ∃ z : 𝓞 E, a * b = (l.M : 𝓞 E) * z := by
  have h : a * b ∈ Ideal.span {(l.M : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul ha hb
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨z, by rw [← hz, mul_comm]⟩
def IsSep (l : Level H) (c : 𝓞 E) : Prop := c ∈ conjHalf l ∧ c - 1 ∈ l.Mb
theorem exists_isSep (l : Level H) : ∃ c, IsSep l c := by
  have h : (1 : 𝓞 E) ∈ l.Mb ⊔ conjHalf l := by
    rw [conjHalf, l.coprime]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
  refine ⟨b, hb, ?_⟩
  have : b - 1 = -a := by rw [← hab]; ring
  rw [this]; exact neg_mem ha
def sep (l : Level H) : 𝓞 E := (exists_isSep l).choose
theorem sep_spec (l : Level H) : IsSep l (sep l) := (exists_isSep l).choose_spec
variable (D : Datum H) (l : Level H)
abbrev NamedCl : Type := D.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) D.La))
abbrev ConjCl : Type := D.La ⧸ (conjHalf l • (⊤ : Submodule (𝓞 E) D.La))
theorem finite_quot (I : Ideal (𝓞 E)) (hI : (l.M : 𝓞 E) ∈ I) :
    Finite (D.La ⧸ (I • (⊤ : Submodule (𝓞 E) D.La))) := by
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have hM : (l.M : ℤ) ≠ 0 := by have := l.three_le; omega
  refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(l.M : ℤ), mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (l.M : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ (I • (⊤ : Submodule (𝓞 E) D.La))) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, natCast_zsmul,
    ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hI Submodule.mem_top
theorem level_mem_mul : (l.M : 𝓞 E) ∈ l.Mb * conjHalf l := by
  rw [conjHalf, l.prod]; exact Ideal.mem_span_singleton_self _
instance finite_namedCl : Finite (NamedCl D l) := finite_quot D l _
  (Ideal.mul_le_inf (level_mem_mul l)).1
instance finite_conjCl : Finite (ConjCl D l) := finite_quot D l _
  (Ideal.mul_le_inf (level_mem_mul l)).2
theorem ef_smul_eq_zero {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ conjHalf l) (u v : D.La) :
    ((D.EF u ((a * b) • v) : ℤ) : ZMod l.M) = 0 := by
  obtain ⟨z, hz⟩ := mul_mem_span_level l ha hb
  rw [hz, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul]
  simp
theorem ef_left_zero {c : 𝓞 E} (hc : c ∈ conjHalf l) {u : D.La}
    (hu : u ∈ conjHalf l • (⊤ : Submodule (𝓞 E) D.La)) (v : D.La) :
    ((D.EF u (c • v) : ℤ) : ZMod l.M) = 0 := by
  refine Submodule.smul_induction_on hu (fun m hm w _ => ?_) (fun x y hx hy => ?_)
  · rw [D.adj, ← mul_smul]
    exact ef_smul_eq_zero D l (bar_mem_of_mem_conjHalf l hm) hc w v
  · rw [map_add, LinearMap.add_apply, Int.cast_add, hx, hy, add_zero]
theorem ef_right_zero {c : 𝓞 E} (hc : c ∈ conjHalf l) (u : D.La) {v : D.La}
    (hv : v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ((D.EF u (c • v) : ℤ) : ZMod l.M) = 0 := by
  refine Submodule.smul_induction_on hv (fun m hm w _ => ?_) (fun x y hx hy => ?_)
  · rw [← mul_smul, mul_comm]
    exact ef_smul_eq_zero D l hm hc u w
  · rw [smul_add, map_add, Int.cast_add, hx, hy, add_zero]
def pairOne (a : ConjCl D l) (x : NamedCl D l) : ZMod l.M :=
  Quotient.liftOn₂' a x (fun u v => ((D.EF u (sep l • v) : ℤ) : ZMod l.M)) (by
    intro u v u' v' hu hv
    have hu' := (Submodule.quotientRel_def _).1 hu
    have hv' := (Submodule.quotientRel_def _).1 hv
    have h1 := ef_left_zero D l (sep_spec l).1 hu' v
    have h2 := ef_right_zero D l (sep_spec l).1 u' hv'
    rw [map_sub, LinearMap.sub_apply, Int.cast_sub, sub_eq_zero] at h1
    rw [smul_sub, map_sub, Int.cast_sub, sub_eq_zero] at h2
    exact h1.trans h2)
def pairing {n : ℕ} (a : Fin n → ConjCl D l) (t : Fin n → NamedCl D l) : ZMod l.M :=
  ∑ b, pairOne D l (a b) (t b)
theorem zeta_level_mem (c : Coeff l) : zeta l.M ∈ c.F := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hM' hk
  have : zeta l.M = zeta l.M' ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul, hk]
    congr 1
    have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0
    have : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
    push_cast
    field_simp
  rw [this]
  exact pow_mem c.zeta_mem k
variable {l} in

def zetaM (c : Coeff l) : c.F := ⟨zeta l.M, zeta_level_mem l c⟩
variable {l} in
theorem zetaM_prim (c : Coeff l) : IsPrimitiveRoot (zetaM c) l.M :=
  IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.M (by have := l.three_le; omega)) Subtype.val_injective
variable {l} in

def zetaU (c : Coeff l) : (c.F)ˣ :=
  Units.mk0 (zetaM c) ((zetaM_prim c).ne_zero (by have := l.three_le; omega))
variable {l}
def eChar (c : Coeff l) {n : ℕ} (a : Fin n → ConjCl D l) (t : Fin n → NamedCl D l) : c.F :=
  zetaM c ^ (pairing D l a t).val
variable {D}
def levPtCl (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (x : NamedCl D l) :
    ptO Xo x0 ⟶ Xo.univ.t.G :=
  Quotient.liftOn' x (fun u => levPt Xo x0 u) (by
    intro u v huv
    have h := (Submodule.quotientRel_def _).1 huv
    have : Xo.univ.eta u = Xo.univ.eta v := by
      have h2 := Xo.univ.eta_add (u - v) v
      rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h2
      exact h2
    simp only [levPt, this])
def levelPoints (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) :
    Set (Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) :=
  Set.range fun (t : Fin n → NamedCl D l) (b : Fin n) => levPtCl Xo x0 (t b)
variable (D l) in

def levelIndex (n : ℕ) : Finset (Fin n → NamedCl D l) := (Set.finite_univ).toFinset
def IsConjPt (Xo : Moduli D l) (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] (x0 : Sp S ⟶ Xo.X)
    (a : ConjCl D l) (u : ptO Xo x0 ⟶ Xo.univ.t.G) : Prop :=
  KilledBy Xo (conjHalf l) u ∧ ∀ x : NamedCl D l,
    Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L (l.M : ℤ) u (levPtCl Xo x0 x)
      (unitOn (Units.map (algebraMap c.F S).toMonoidHom (zetaU c ^ (pairOne D l a x).val)))
def SpansAtEvery {n : ℕ} (s : Set (Fin n)) (x₀ : Fin n → ConjCl D l) : Prop :=
  ∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsMaximal → conjHalf l ≤ 𝔭 →
    Submodule.span (𝓞 E) (x₀ '' s) ⊔ 𝔭 • (⊤ : Submodule (𝓞 E) (ConjCl D l)) = ⊤
def FirstInv {n : ℕ} (x₀ : Fin n → ConjCl D l) : Prop :=
  D.p + D.q ≤ n ∧ SpansAtEvery {b : Fin n | (b : ℕ) < D.p + D.q} x₀
def RankFull {n : ℕ} (x₀ : Fin n → ConjCl D l) : Prop := SpansAtEvery Set.univ x₀
open Classical in

def Admissible (nV : ℕ) {n : ℕ} (x₀ : Fin n → ConjCl D l) : Prop :=
  if n = nV then RankFull x₀ else FirstInv x₀
def fourier (c : Coeff l) {n : ℕ} (φ : (Fin n → ConjCl D l) → c.F) (t : Fin n → NamedCl D l) : c.F :=
  (Nat.card (Fin n → NamedCl D l) : c.F)⁻¹ *
    ∑ a ∈ (Set.finite_univ : (Set.univ : Set (Fin n → ConjCl D l)).Finite).toFinset, φ a * (eChar D c a t)⁻¹
def indicatorCl (c : Coeff l) {n : ℕ} (x₀ : Fin n → ConjCl D l) : (Fin n → ConjCl D l) → c.F :=
  Set.indicator {x₀} 1
def indCoeff (c : Coeff l) {n : ℕ} (x₀ : Fin n → ConjCl D l) (t : Fin n → NamedCl D l) : c.F :=
  fourier c (indicatorCl c x₀) t
variable (D l) in

def PairingPerfect (n : ℕ) : Prop :=
  (∀ a : Fin n → ConjCl D l, (∀ t, pairing D l a t = 0) → a = 0) ∧
    ∀ t : Fin n → NamedCl D l, (∀ a, pairing D l a t = 0) → t = 0
variable (D) in

def FourierInversion (c : Coeff l) (n : ℕ) : Prop :=
  (∀ (φ : (Fin n → ConjCl D l) → c.F) (a : Fin n → ConjCl D l),
      φ a = ∑ t ∈ levelIndex D l n, fourier c φ t * eChar D c a t) ∧
    ∀ t₀ : Fin n → NamedCl D l, fourier c (fun a => eChar D c a t₀) = Set.indicator {t₀} 1
variable (D l) in

def AdmissibleStable (n : ℕ) : Prop :=
  ∀ u : 𝓞 E, Ideal.span {u} ⊔ conjHalf l = ⊤ → ∀ x₀ : Fin n → ConjCl D l,
    (FirstInv x₀ → FirstInv (u • x₀)) ∧ (RankFull x₀ → RankFull (u • x₀))
def HalvesNamed (Xo : Moduli D l) (c : Coeff l) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (x0 : Sp k ⟶ Xo.X), x0 ≫ Xo.s = sOf c k →
    (Function.Injective (levPtCl Xo x0) ∧ ∀ u, KilledBy Xo l.Mb u ↔ u ∈ Set.range (levPtCl Xo x0)) ∧
    (∀ a, ∃! u, IsConjPt Xo c x0 a u) ∧ ∀ u, KilledBy Xo (conjHalf l) u → ∃! a, IsConjPt Xo c x0 a u
end GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation



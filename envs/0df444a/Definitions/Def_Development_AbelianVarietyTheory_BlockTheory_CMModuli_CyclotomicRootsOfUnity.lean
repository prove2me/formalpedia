-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CyclotomicRootsOfUnity
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_CyclotomicRootsOfUnity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:05.770875+00:00
-- url     : https://prove2.me/theorems/2832a239-7c4c-44cf-8afd-9afe14b14d08
-- title:
--   Cyclotomic Roots Of Unity
-- statement:
--   Definitions and structural lemmas for Cyclotomic Roots Of Unity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CyclotomicRootsOfUnity.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SiegelFamilyZetaUnit
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_AbelianLocusModels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels
def LiesOver (W : ValuationSubring ℂ) (p : ℕ) : Prop := (p : ℂ) ∈ W.nonunits
example (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, LiesOver W p := by
  have hI : Ideal.span {((p : ℕ) : (⊥ : Subring ℂ))} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    obtain ⟨⟨x, hx⟩, h1⟩ := h.exists_right_inv
    obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hx
    have h2 : ((p : ℤ) : ℂ) * (m : ℂ) = 1 := by simpa using congrArg Subtype.val h1
    have h3 : (p : ℤ) * m = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ 1 := ⟨m, h3.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast h4))
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨W, hW ⟨_, Ideal.subset_span rfl, by simp⟩⟩
abbrev locRing (W : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) : ValuationSubring F :=
  W.comap F.val.toRingHom
abbrev locIncl (W : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) : locRing W F →+* F :=
  (locRing W F).subtype
def locMap (W : ValuationSubring ℂ) {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') :
    locRing W F →+* locRing W F' :=
  ((IntermediateField.inclusion h).toRingHom.comp (locIncl W F)).codRestrict (locRing W F') fun x => x.2
theorem inv_natCast_mem {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {d : ℕ}
    (hd : ¬ p ∣ d) : (d : ℂ)⁻¹ ∈ W := by
  by_contra h
  have hdn : (d : ℂ) ∈ W.nonunits := (W.mem_nonunits_iff_or).mpr (Or.inr h)
  have hc : IsCoprime (p : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : ℂ) * p + (b : ℂ) * d = 1 := by exact_mod_cast hab
  have hv : ∀ (m : ℤ) (x : ℂ), W.valuation x < 1 → W.valuation ((m : ℂ) * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((W.valuation_le_one_iff _).mpr (intCast_mem W m))) hx
  have := Valuation.map_add_lt W.valuation (hv a _ (W.mem_nonunits_iff.mp hW)) (hv b _ (W.mem_nonunits_iff.mp hdn))
  rw [h1, map_one] at this
  exact lt_irrefl _ this
theorem zeta_mem_valuationSubring (W : ValuationSubring ℂ) {M : ℕ} (hM : M ≠ 0) : zeta M ∈ W := by
  have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
  rw [← W.valuation_le_one_iff]
  have h2 : W.valuation (zeta M) ^ M = 1 := by rw [← map_pow, h1, map_one]
  exact ((pow_eq_one_iff_of_nonneg zero_le' hM).mp h2).le
theorem cycloLocal_le {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {M : ℕ} (hM : M ≠ 0)
    {F : IntermediateField ℚ ℂ} (hF : zeta M ∈ F) : cycloLocal p M ≤ W.toSubring ⊓ F.toSubfield.toSubring := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨q, hq, rfl⟩ | hx)
  · refine ⟨?_, SubfieldClass.ratCast_mem F q⟩
    change (q : ℂ) ∈ W
    rw [Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem W _) (inv_natCast_mem hp hW hq)
  · obtain rfl : x = zeta M := hx
    exact ⟨zeta_mem_valuationSubring W hM, hF⟩
def cycloMap {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {M : ℕ} (hM : M ≠ 0)
    {F : IntermediateField ℚ ℂ} (hF : zeta M ∈ F) : cycloLocal p M →+* locRing W F :=
  ((cycloLocal p M).subtype.codRestrict F fun x => (cycloLocal_le hp hW hM hF x.2).2).codRestrict
    (locRing W F) fun x => (cycloLocal_le hp hW hM hF x.2).1
theorem zeta_mem_of_dvd {F : IntermediateField ℚ ℂ} {a N : ℕ} (hN : N ≠ 0) (h : a ∣ N) (hF : zeta N ∈ F) :
    zeta a ∈ F := by
  obtain ⟨k, rfl⟩ := h
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hN)
  have : zeta a = zeta (a * k) ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem hF k
theorem zeta_lcm_mem {F : IntermediateField ℚ ℂ} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h₁ : zeta a ∈ F)
    (h₂ : zeta b ∈ F) : zeta (Nat.lcm a b) ∈ F := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hl : ((Nat.lcm a b : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero ha hb)
  have e1 : ((Nat.gcd a b : ℕ) : ℂ) * (Nat.lcm a b : ℕ) = a * b := by exact_mod_cast Nat.gcd_mul_lcm a b
  have e2 : ((Nat.gcd a b : ℕ) : ℂ) = a * (Nat.gcdA a b : ℂ) + b * (Nat.gcdB a b : ℂ) := by
    exact_mod_cast Nat.gcd_eq_gcd_ab a b
  have : zeta (Nat.lcm a b) = zeta a ^ Nat.gcdB a b * zeta b ^ Nat.gcdA a b := by
    rw [zeta, zeta, zeta, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    field_simp
    linear_combination (-1 : ℂ) * e1 + (Nat.lcm a b : ℂ) * e2
  rw [this]
  exact mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
abbrev Idx (H : Host E) (p : ℕ) : Type := Σ l : {l : Level H // l.GoodAt p}, Coeff l.1
abbrev Idx.l {p : ℕ} (i : Idx H p) : Level H := i.1.1
abbrev Idx.F {p : ℕ} (i : Idx H p) : IntermediateField ℚ ℂ := i.2.F
def Idx.Le {p : ℕ} (i j : Idx H p) : Prop := i.l.Dvd j.l ∧ i.F ≤ j.F
theorem Idx.Le.refl {p : ℕ} (i : Idx H p) : i.Le i := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl⟩
theorem Idx.Le.trans {p : ℕ} {i j k : Idx H p} (h : i.Le j) (h' : j.Le k) : i.Le k :=
  ⟨⟨h.1.1.trans h'.1.1, h'.1.2.1.trans h.1.2.1, h.1.2.2.trans h'.1.2.2⟩, h.2.trans h'.2⟩
def addLevel (l : Level H) {N : ℕ} (hN : N ≠ 0) : Level H :=
  { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos (Nat.pos_of_ne_zero hN) }
theorem zeta_mem_sup (F : IntermediateField ℚ ℂ) (N : ℕ) :
    zeta N ∈ F ⊔ IntermediateField.adjoin ℚ {zeta N} :=
  (le_sup_right : _ ≤ F ⊔ _) (IntermediateField.subset_adjoin _ _ rfl)
def addCoeff {l : Level H} (c : Coeff l) {N : ℕ} (hN : N ≠ 0) : Coeff (addLevel l hN) :=
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hz : zeta (addLevel l hN).M' ∈ c.F ⊔ IntermediateField.adjoin ℚ {zeta N} := by
    have : (addLevel l hN).M' = Nat.lcm l.M' N := (Nat.lcm_assoc _ _ _).symm
    rw [this]
    exact zeta_lcm_mem hM' hN ((le_sup_left : c.F ≤ _) c.zeta_mem) (zeta_mem_sup _ _)
  { F := c.F ⊔ IntermediateField.adjoin ℚ {zeta N}
    fin := by
      have := c.fin
      have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta N}) :=
        IntermediateField.adjoin.finiteDimensional
          (((Complex.isPrimitiveRoot_exp N hN).isIntegral (Nat.pos_of_ne_zero hN)).tower_top)
      infer_instance
    conj := fun τ a => (le_sup_left : c.F ≤ _) (c.conj τ a)
    zeta_mem := hz
    le := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x (rfl | hx)
      · exact (le_sup_left : c.F ≤ _) (c.le (IntermediateField.subset_adjoin _ _ (by simp)))
      · obtain rfl : x = _ := hx
        exact zeta_mem_of_dvd
          (Nat.lcm_ne_zero (by have := l.three_le; change l.M ≠ 0; omega) (addLevel l hN).A_pos.ne')
          (Nat.dvd_lcm_right _ _) hz }
def Idx.add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : Idx H p :=
  ⟨⟨addLevel i.l hN, i.1.2⟩, addCoeff i.2 hN⟩
theorem Idx.le_add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : i.Le (i.add hN) :=
  ⟨⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩, le_sup_left⟩
theorem Idx.zeta_mem_add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : zeta N ∈ (i.add hN).F :=
  zeta_mem_sup _ _
def abOpen {S : Scheme.{0}} (G : Over S) : S.Opens := ⟨interior (abLocus G), isOpen_interior⟩
def IsBirational {X Z : Scheme.{0}} (h : X ⟶ Z) : Prop :=
  ∃ V : Z.Opens, Dense (V : Set Z) ∧ Dense ((h ⁻¹ᵁ V : X.Opens) : Set X) ∧ IsIso (h ∣_ V)
example (X : Scheme.{0}) : IsBirational (𝟙 X) :=
  ⟨⊤, dense_univ, dense_univ, inferInstance⟩
def IsSymplecticFrame (D : Datum H) {g N : ℕ} (ρ : D.La →+ Std g N) : Prop :=
  Function.Surjective ρ ∧ (∀ a, ρ a = 0 ↔ ∃ b, a = N • b) ∧
    ∀ a b, stdForm (ρ a) (ρ b) = (D.EF a b : ZMod N)
def genus (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * (D.p + D.q)
section Compare
variable {D : Datum H} {l l₁ : Level H} {Xo : Moduli D l} {Xo₁ : Moduli D l₁} {c : Coeff l} {c₁ : Coeff l₁}
  {O O₁ : Type} [CommRing O] [CommRing O₁] {β : O →+* c.F} {β₁ : O₁ →+* c₁.F}
def IsEtaleCoverOnAb (Y : Model Xo c β) (Y₁ : Model Xo₁ c₁ β₁) (b : O →+* O₁) (π : Y₁.X ⟶ Y.X) : Prop :=
  ∃ q : (abOpen Y₁.t.G).toScheme ⟶ pullback ((abOpen Y.t.G).ι ≫ Y.s) (spMap b),
    q ≫ pullback.fst _ _ ≫ (abOpen Y.t.G).ι = (abOpen Y₁.t.G).ι ≫ π ∧
    q ≫ pullback.snd _ _ = (abOpen Y₁.t.G).ι ≫ Y₁.s ∧
    IsFinite q ∧ Etale q ∧ Surjective q
def IsClassified (Y₁ : Model Xo₁ c₁ β₁) {g N : ℕ} (ρ : D.La →+ Std g N) {R : Type} [CommRing R] (κ : R →+* O₁)
    {𝒜 : Scheme.{0}} (s : 𝒜 ⟶ Sp R) (A : Over 𝒜) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std g N → (𝟙_ (Over 𝒜) ⟶ A)) (good : Prop) : Prop :=
  ∃ (t : SAB H (abOpen Y₁.t.G).toScheme) (m : SABMap t Y₁.t (abOpen Y₁.t.G).ι)
    (j : Xo₁.XF c₁ ⟶ (abOpen Y₁.t.G).toScheme) (ψ : Y₁.oF.t.G.left ⟶ t.G.left)
    (lv₁ : Std g N → (𝟙_ (Over (abOpen Y₁.t.G).toScheme) ⟶ t.G))
    (f : (abOpen Y₁.t.G).toScheme ⟶ pullback s (spMap κ)),

    j ≫ (abOpen Y₁.t.G).ι = Y₁.j ∧ ψ ≫ m.φ = Y₁.m.φ ∧

    (∀ a, j ≫ (lv₁ (ρ a)).left = (Y₁.oF.etaA a ^ (l₁.A / N)).left ≫ ψ) ∧

    f ≫ pullback.snd _ _ = (abOpen Y₁.t.G).ι ≫ Y₁.s ∧ IsFinite f ∧
    IsPullbackTriple t.G (abelian₂ t.G t.PP.L) lv₁ A P lv (f ≫ pullback.fst _ _) ∧

    (good → ∃ (Z : Scheme.{0}) (h : (abOpen Y₁.t.G).toScheme ⟶ Z) (w : Z ⟶ pullback s (spMap κ))
      (tZ : SAB H Z) (mZ : SABMap t tZ h) (eZ eA : D.La → (𝟙_ (Over Z) ⟶ tZ.G))
      (lvZ : Std g N → (𝟙_ (Over Z) ⟶ tZ.G)),
      h ≫ w = f ∧ IsFinite h ∧ IsBirational h ∧ Surjective h ∧
      IsReduced Z ∧ Flat (w ≫ pullback.snd _ _) ∧ IsFinite w ∧ FormallyUnramified w ∧
      (∀ a, j ≫ h ≫ (eZ a).left = (Y₁.oF.eta a).left ≫ ψ ≫ mZ.φ) ∧
      (∀ a, j ≫ h ≫ (eA a).left = (Y₁.oF.etaA a).left ≫ ψ ≫ mZ.φ) ∧
      (∀ a, lvZ (ρ a) = eA a ^ (l₁.A / N)) ∧
      IsPullbackTriple tZ.G (abelian₂ tZ.G tZ.PP.L) lvZ A P lv (w ≫ pullback.fst _ _))
end Compare
abbrev Models {D : Datum H} (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) : Type 1 :=
  ∀ i : Idx H p, Model (Xo i.l) i.2 (locIncl W i.F)
abbrev Transitions {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} {W : ValuationSubring ℂ}
    (Y : Models Xo p W) : Type :=
  ∀ i j : Idx H p, i.Le j → ((Y j).X ⟶ (Y i).X)
def SiegelComparison {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} (hp : p.Prime)
    {W : ValuationSubring ℂ} (hW : LiesOver W p) (Y : Models Xo p W) (π : Transitions Y) : Prop :=
  ∃ n : ℕ, n.Prime ∧ Odd n ∧ n ≠ p ∧ (∀ i : Idx H p, n.Coprime i.l.M) ∧
    ∃ (M₁ : ℕ) (hM : M₁ ≠ 0), 3 ≤ M₁ ∧ (∃ e : ℕ, M₁ = n ^ e) ∧
      ∃ (𝒜 : Scheme.{0}) (s : 𝒜 ⟶ Sp (cycloLocal p M₁)) (A : Over 𝒜) (_ : GrpObj A) (P : LB (A ⊗ A).left)
        (lv : Std (genus D) M₁ → (𝟙_ (Over 𝒜) ⟶ A)) (ρ : D.La →+ Std (genus D) M₁),
        IsSiegelFamily (genus D) p hM 𝒜 s A P lv ∧ IsSymplecticFrame D ρ ∧
        ∀ i : Idx H p,
          IsEtaleCoverOnAb (Y i) (Y (i.add hM)) (locMap W (i.le_add hM).2) (π i (i.add hM) (i.le_add hM)) ∧
          IsClassified (Y (i.add hM)) ρ (cycloMap hp hW hM (i.zeta_mem_add hM)) s A P lv (¬ p ∣ i.l.M')
def IsLocalSystem {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} (hp : p.Prime)
    {W : ValuationSubring ℂ} (hW : LiesOver W p) (Y : Models Xo p W) (π : Transitions Y) : Prop :=

  (∀ (i j : Idx H p) (h : i.Le j), IsTransition (Y i) (Y j) (locMap W h.2) (π i j h)) ∧

  (∀ i : Idx H p, π i i (Idx.Le.refl i) = 𝟙 _) ∧
  (∀ (i j k : Idx H p) (h : i.Le j) (h' : j.Le k), π j k h' ≫ π i j h = π i k (h.trans h')) ∧

  (∀ i : Idx H p, OneModel p (Y i)) ∧

  SiegelComparison hp hW Y π
def LocalSystemExists (H : Host E) : Prop :=
  ∀ (D : Datum H), 1 ≤ D.p + D.q → ∀ (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (hp : p.Prime)
    (W : ValuationSubring ℂ) (hW : LiesOver W p), ∃ (Y : Models Xo p W) (π : Transitions Y), IsLocalSystem hp hW Y π
end GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:25.013787+00:00
-- url     : https://prove2.me/theorems/9b6d579a-0139-4cc7-a542-ae6848c432ea
-- title:
--   Level Action Transitions
-- statement:
--   Definitions and structural lemmas for Level Action Transitions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenModelSections_Model_incl_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Group
variable (D : Datum H)
def nLa (n : ℕ) : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
theorem mem_nLa {n : ℕ} {x : D.La} : x ∈ nLa D n ↔ ∃ y, x = n • y := by
  simp only [nLa, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, eq_comm]
abbrev LaMod (n : ℕ+) : Type := D.La ⧸ nLa D n
abbrev cls (n : ℕ+) (a : D.La) : LaMod D n := Submodule.Quotient.mk a
theorem cls_eq {n : ℕ+} {a b : D.La} : cls D n a = cls D n b ↔ ∃ y, a = b + (n : ℕ) • y := by
  rw [Submodule.Quotient.eq, mem_nLa]
  exact exists_congr fun y => by rw [sub_eq_iff_eq_add']
def KMax : Subgroup (∀ n : ℕ+, LaMod D n ≃ₗ[𝓞 E] LaMod D n) where
  carrier := {g | (∀ (n m : ℕ+) (a b : D.La), g (n * m) (cls D _ a) = cls D _ b → g n (cls D n a) = cls D n b) ∧
    ∀ (n : ℕ+) (a b a' b' : D.La), g n (cls D n a) = cls D n a' → g n (cls D n b) = cls D n b' →
      D.EF a' b' ≡ D.EF a b [ZMOD (n : ℕ)]}
  one_mem' := by
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · obtain ⟨y, hy⟩ := (cls_eq D).mp h
      exact (cls_eq D).mpr ⟨(m : ℕ) • y, by rw [hy, PNat.mul_coe, mul_smul]⟩
    · obtain ⟨y, rfl⟩ := (cls_eq D).mp ha
      obtain ⟨z, rfl⟩ := (cls_eq D).mp hb
      refine Int.modEq_iff_dvd.mpr ⟨D.EF a' z + D.EF y b' + (n : ℕ) * D.EF y z, ?_⟩
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      ring
  mul_mem' := by
    rintro g g' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (g' (n * m) (cls D _ a))
      change g (n * m) (g' (n * m) (cls D _ a)) = _ at h
      change g n (g' n (cls D _ a)) = _
      rw [h1' n m a c hc.symm]
      exact h1 n m c b (by rw [← h, ← hc])
    · obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (g' n (cls D _ a))
      obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (g' n (cls D _ b))
      change g n (g' n (cls D _ a)) = _ at ha
      change g n (g' n (cls D _ b)) = _ at hb
      exact (h2 n c d a' b' (by rw [← ha, ← hc]) (by rw [← hb, ← hd])).trans (h2' n a b c d hc.symm hd.symm)
  inv_mem' := by
    rintro g ⟨h1, h2⟩
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · change (g (n * m)).symm (cls D _ a) = _ at h
      change (g n).symm (cls D _ a) = _
      rw [LinearEquiv.symm_apply_eq] at h ⊢
      exact (h1 n m b a h.symm).symm
    · change (g n).symm (cls D _ a) = _ at ha
      change (g n).symm (cls D _ b) = _ at hb
      rw [LinearEquiv.symm_apply_eq] at ha hb
      exact (h2 n a' b' a b ha.symm hb.symm).symm
variable {D}
def modulus (l : Level H) : ℕ+ := ⟨l.M', Nat.lcm_pos (by have := l.three_le; omega) l.A_pos⟩
def Sends (l : Level H) (g : KMax D) (a b : D.La) : Prop :=
  g.1 (modulus l) (cls D _ a) = cls D _ b
def FixesLevel (l : Level H) (g : KMax D) : Prop :=
  ∀ a b, Sends l g a b → a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ∧ a - b ∈ nLa D l.A
end Group
def IsNormalisation {U Z Y : Scheme.{0}} (i : U ⟶ Z) (p : Z ⟶ Y) : Prop :=
  ∃ (_ : QuasiCompact (i ≫ p)) (_ : QuasiSeparated (i ≫ p)) (e : Z ≅ (i ≫ p).normalization),
    i ≫ e.hom = (i ≫ p).toNormalization ∧ e.hom ≫ (i ≫ p).fromNormalization = p
section OneLevel
variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀}
def etaMap (m : Model univ h φ) (a : D.La) : baseChange str h ⟶ m.t.G.left := m.secMap (toUnit _ ≫ univ.eta a)
def etaAMap (m : Model univ h φ) (a : D.La) : baseChange str h ⟶ m.t.G.left := m.secMap (toUnit _ ≫ univ.etaA a)
def Descends (m : Model univ h φ) : Prop :=
  ∃ (Y : Scheme.{0}) (sY : Y ⟶ Sp (KA l)) (i : X₀ ⟶ Y) (p : pullback m.s (spMap φ) ⟶ Y)
    (tY : SAB H Y) (tQ : SAB H (pullback m.s (spMap φ)))
    (u : SABMap univ.t tY i) (qX : SABMap tQ m.t (pullback.fst m.s (spMap φ))) (qY : SABMap tQ tY p),
    IsOpenImmersion i ∧ i ≫ sY = str ∧
    IsPullback p (pullback.snd m.s (spMap φ)) sY (spMap h.incl) ∧
    m.j ≫ p = baseChangeFst str h ≫ i ∧
    qX.cart.1.lift m.toModel.φ (m.t₀.G.hom ≫ m.j) (by rw [Category.assoc]; exact m.toModel.cart.1.w) ≫ qY.φ =
      m.toUniv.φ ≫ u.φ
structure IsLevelAction (m : Model univ h φ) (act : KMax D → (m.X ⟶ m.X)) (lift : ∀ g, SABMap m.t m.t (act g))
    (act₀ : KMax D → (baseChange str h ⟶ baseChange str h)) : Prop where
  act_over : ∀ g, act g ≫ m.s = m.s
  act_one : act 1 = 𝟙 _
  act_mul : ∀ g g', act (g * g') = act g ≫ act g'
  lift_one : (lift 1).φ = 𝟙 _
  lift_mul : ∀ g g', (lift (g * g')).φ = (lift g).φ ≫ (lift g').φ
  act_fix : ∀ g, FixesLevel l g → act g = 𝟙 _
  lift_fix : ∀ g, FixesLevel l g → (lift g).φ = 𝟙 _
  act₀_over : ∀ g, act₀ g ≫ baseChangeStr str h = baseChangeStr str h
  act₀_incl : ∀ g, act₀ g ≫ m.incl = m.incl ≫ act g
  eta : ∀ g a b, Sends l g a b → etaMap m b ≫ (lift g).φ = act₀ g ≫ etaMap m a
  etaA : ∀ g a b, Sends l g a b → etaAMap m b ≫ (lift g).φ = act₀ g ≫ etaAMap m a
def LevelActs (m : Model univ h φ) : Prop := ∃ act lift act₀, IsLevelAction m act lift act₀
variable {O' : Type} [CommRing O'] {φ' : O' →+* F₀}
def inclBase (m' : Model univ h φ') (ψ : O' →+* O) (hψ : φ.comp ψ = φ') :
    baseChange str h ⟶ pullback m'.s (spMap ψ) :=
  pullback.lift m'.incl (baseChangeStr str h ≫ spMap φ) (by
    rw [m'.incl_over, Category.assoc, ← Spec.map_comp, ← hψ]; rfl)
def compare (m' : Model univ h φ') (m : Model univ h φ) : m'.t₀.G.left ⟶ m.t₀.G.left :=
  m.toUniv.cart.1.lift m'.toUniv.φ m'.t₀.G.hom m'.toUniv.cart.1.w
def Dominates (m' : Model univ h φ') (m : Model univ h φ) (ψ : O' →+* O) (hψ : φ.comp ψ = φ') : Prop :=
  ∃ (δ : pullback m'.s (spMap ψ) ⟶ m.X) (t : SAB H (pullback m'.s (spMap ψ)))
    (q' : SABMap t m'.t (pullback.fst m'.s (spMap ψ))) (q : SABMap t m.t δ),
    δ ≫ m.s = pullback.snd m'.s (spMap ψ) ∧
    inclBase m' ψ hψ ≫ δ = m.incl ∧
    q'.cart.1.lift m'.toModel.φ (m'.t₀.G.hom ≫ inclBase m' ψ hψ)
        (by rw [Category.assoc, inclBase, pullback.lift_fst]; exact m'.toModel.cart.1.w) ≫ q.φ =
      compare m' m ≫ m.toModel.φ
end OneLevel
section TwoLevels
variable {D : Datum H} {l l₂ : Level H} {X₀ X₂ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)} {str₂ : X₂ ⟶ Sp (KA l₂)}
  {univ : Obj D l (baseKA l) str} {univ₂ : Obj D l₂ (baseKA l₂) str₂} {F₀ F₂ : IntermediateField ℚ ℂ}
  {h : IsCoeffField l F₀} {h₂ : IsCoeffField l₂ F₂}
  {O O₂ : Type} [CommRing O] [CommRing O₂] {φ : O →+* F₀} {φ₂ : O₂ →+* F₂}
structure IsTransition (m₂ : Model univ₂ h₂ φ₂) (m : Model univ h φ) (hl : l.Dvd l₂) (hF : F₀ ≤ F₂) (ψ : O →+* O₂)
    (hψ : φ₂.comp ψ = (IntermediateField.inclusion hF).toRingHom.comp φ) (π : m₂.X ⟶ m.X) : Prop where
  map_over : π ≫ m.s = m₂.s ≫ spMap ψ
  normalisation : IsNormalisation m₂.incl (pullback.lift π m₂.s map_over : m₂.X ⟶ pullback m.s (spMap ψ))
  compat : ∃ (π₀ : baseChange str₂ h₂ ⟶ baseChange str h) (q : SABMap m₂.t m.t π),
    π₀ ≫ baseChangeStr str h = baseChangeStr str₂ h₂ ≫ spMap (IntermediateField.inclusion hF).toRingHom ∧
    π₀ ≫ m.incl = m₂.incl ≫ π ∧
    (∀ a, etaMap m₂ ((l₂.M / l.M) • a) ≫ q.φ = π₀ ≫ etaMap m a) ∧
    (∀ a, etaAMap m₂ ((l₂.A / l.A) • a) ≫ q.φ = π₀ ≫ etaAMap m a)
end TwoLevels
end GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Slopes
-- name    : GroundTheory_HeightsAndTheta_Heights_Slopes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:55.235497+00:00
-- url     : https://prove2.me/theorems/15e58bae-a911-4048-ba5f-6e09d05d426b
-- title:
--   Slopes
-- statement:
--   Definitions and structural lemmas for Slopes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Slopes.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_bot_8fbec8549ade
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
namespace HermitianBundle
variable {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K)
def bundleSlope : ℝ := E.deg / Module.finrank (𝓞 K) E.carrier
def relSlope (F G : Submodule (𝓞 K) E.carrier) : ℝ :=
  (E.normDegree G - E.normDegree F) / ((E.rank G : ℝ) - E.rank F)
def slopeMin : EReal :=
  ⨅ (F : Submodule (𝓞 K) E.carrier) (hF : E.Saturated F) (_ : F ≠ ⊤),
    (((E.quot F hF).bundleSlope : ℝ) : EReal)
def Semistable : Prop :=
  0 < Module.finrank (𝓞 K) E.carrier ∧
    ∀ F : Submodule (𝓞 K) E.carrier, F ≠ ⊥ → E.slope F ≤ E.slope ⊤
structure IsCanonicalFiltration {m : ℕ} (f : Fin (m + 1) → Submodule (𝓞 K) E.carrier) : Prop where
  bot : f 0 = ⊥
  top : f (Fin.last m) = ⊤
  strictMono : StrictMono f
  saturated : ∀ i, E.Saturated (f i)
  semistable : ∀ (i : Fin m) (G : Submodule (𝓞 K) E.carrier), f i.castSucc < G → G ≤ f i.succ →
    E.relSlope (f i.castSucc) G ≤ E.relSlope (f i.castSucc) (f i.succ)
  anti : StrictAnti fun i : Fin m ↦ E.relSlope (f i.castSucc) (f i.succ)
def supNorm (v : E.carrier) : ℝ := ⨆ σ : K →+* ℂ, E.normAt σ v
def firstMin : ℝ := ⨅ v : {v : E.carrier // v ≠ 0}, E.supNorm v
theorem saturated_bot : E.Saturated ⊥ := by
  intro a x ha hx
  rw [Submodule.mem_bot] at hx ⊢
  exact (smul_eq_zero.mp hx).resolve_left ha
theorem saturated_top : E.Saturated ⊤ := fun _ _ _ _ ↦ Submodule.mem_top
end HermitianBundle
def ratLine (a : ℝ) : HermitianBundle ℚ :=
  ⟨𝓞 ℚ, (HermitianMetric.integers ℚ).scale (Real.exp (-a)) (Real.exp_pos _)⟩
def ratPlane (a b : ℝ) : HermitianBundle ℚ := (ratLine a).prod (ratLine b)
def ratPlaneFlag (a b : ℝ) : Fin 3 → Submodule (𝓞 ℚ) (ratPlane a b).carrier :=
  ![⊥, LinearMap.range (LinearMap.inl (𝓞 ℚ) (𝓞 ℚ) (𝓞 ℚ)), ⊤]
def trivialFlag {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K) :
    Fin 2 → Submodule (𝓞 K) E.carrier :=
  ![⊥, ⊤]
def RelSlopeQuot.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (F G : Submodule (𝓞 K) E.carrier) (hF : E.Saturated F), F < G →
    E.relSlope F G = ((E.sub G).quot (F.comap G.subtype) (hF.comap_subtype G)).bundleSlope
def DegreeBoundedFinite.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (c : ℝ),
    {F : Submodule (𝓞 K) E.carrier | c ≤ E.degree F}.Finite
def SlopeBoundedFinite.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (c : ℝ),
    {F : Submodule (𝓞 K) E.carrier | F ≠ ⊥ ∧ c ≤ E.slope F}.Finite
def MaxDestabilizing.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K),
    0 < Module.finrank (𝓞 K) E.carrier →
    ∃ F : Submodule (𝓞 K) E.carrier, F ≠ ⊥ ∧ ((E.slope F : ℝ) : EReal) = E.slopeMax ∧
      ∀ G : Submodule (𝓞 K) E.carrier, G ≠ ⊥ → ((E.slope G : ℝ) : EReal) = E.slopeMax → G ≤ F
def CanonicalFiltration.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K),
    ∃ (m : ℕ) (f : Fin (m + 1) → Submodule (𝓞 K) E.carrier), E.IsCanonicalFiltration f ∧
      ∀ (m' : ℕ) (g : Fin (m' + 1) → Submodule (𝓞 K) E.carrier), E.IsCanonicalFiltration g →
        Set.range g = Set.range f
def CanonicalFiltrationSlopes.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (n : ℕ)
    (f : Fin (n + 2) → Submodule (𝓞 K) E.carrier), E.IsCanonicalFiltration f →
    E.slopeMax = ((E.relSlope (f 0) (f 1) : ℝ) : EReal) ∧
      E.slopeMin = ((E.relSlope (f (Fin.last n).castSucc) (f (Fin.last (n + 1))) : ℝ) : EReal)
def SlopeBounds.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K),
    0 < Module.finrank (𝓞 K) E.carrier →
    E.slopeMin ≤ ((E.bundleSlope : ℝ) : EReal) ∧ ((E.bundleSlope : ℝ) : EReal) ≤ E.slopeMax
def SemistableIff.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K),
    0 < Module.finrank (𝓞 K) E.carrier → (E.Semistable ↔ E.slopeMax = E.slopeMin)
def FirstMinAttained.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K),
    0 < Module.finrank (𝓞 K) E.carrier →
    0 < E.firstMin ∧ ∃ v : E.carrier, v ≠ 0 ∧ E.supNorm v = E.firstMin
def FirstMinSlopeLower.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K),
    0 < Module.finrank (𝓞 K) E.carrier → ((-Real.log E.firstMin : ℝ) : EReal) ≤ E.slopeMax
def FirstMinSlopeUpper.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K),
    0 < Module.finrank (𝓞 K) E.carrier →
    E.slopeMax ≤ ((-Real.log E.firstMin +
      Real.log ((Module.finrank (𝓞 K) E.carrier : ℝ) * Module.finrank ℚ K) / 2 +
      Real.log |(discr K : ℝ)| / (2 * Module.finrank ℚ K) : ℝ) : EReal)
def RankTwoSplit.Statement : Prop :=
  ∀ a b : ℝ, b < a →
    (ratPlane a b).IsCanonicalFiltration (ratPlaneFlag a b) ∧
      (ratPlane a b).slopeMax = ((a : ℝ) : EReal) ∧ (ratPlane a b).slopeMin = ((b : ℝ) : EReal) ∧
      (ratPlane a b).bundleSlope = (a + b) / 2 ∧ (ratPlane a b).firstMin = Real.exp (-a)
def RankTwoEqual.Statement : Prop :=
  ∀ a : ℝ,
    (ratPlane a a).Semistable ∧ (ratPlane a a).IsCanonicalFiltration (trivialFlag (ratPlane a a)) ∧
      (ratPlane a a).slopeMax = ((a : ℝ) : EReal) ∧ (ratPlane a a).slopeMin = ((a : ℝ) : EReal) ∧
      (ratPlane a a).bundleSlope = a ∧ (ratPlane a a).firstMin = Real.exp (-a)
namespace HermitianBundle
variable {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
theorem rank_eq_one_of_ne_bot (h1 : Module.finrank (𝓞 K) E.carrier = 1)
    {G : Submodule (𝓞 K) E.carrier} (hG : G ≠ ⊥) : E.rank G = 1 := by
  unfold HermitianBundle.rank
  have hle : Module.finrank (𝓞 K) G ≤ 1 := h1 ▸ Submodule.finrank_le G
  have hpos : Module.finrank (𝓞 K) G ≠ 0 := fun h ↦ hG (Submodule.finrank_eq_zero.mp h)
  omega
theorem degree_le_degree_top (h1 : Module.finrank (𝓞 K) E.carrier = 1)
    {G : Submodule (𝓞 K) E.carrier} (hG : G ≠ ⊥) : E.degree G ≤ E.degree ⊤ := by
  obtain ⟨g, hgG, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG
  let s : Fin 1 → G := fun _ ↦ ⟨g, hgG⟩
  let t : Fin 1 → (⊤ : Submodule (𝓞 K) E.carrier) := fun _ ↦ ⟨g, Submodule.mem_top⟩
  have hs : LinearIndependent (𝓞 K) s :=
    linearIndependent_unique_iff.mpr (fun h ↦ hg0 (congrArg Subtype.val h))
  have ht : LinearIndependent (𝓞 K) t :=
    linearIndependent_unique_iff.mpr (fun h ↦ hg0 (congrArg Subtype.val h))
  have hrt : E.rank ⊤ = 1 := E.rank_eq_one_of_ne_bot h1 (by
    intro h
    have : Nontrivial E.carrier := Module.nontrivial_of_finrank_eq_succ h1
    exact top_ne_bot h)
  rw [E.degree_eq_of_linearIndependent G hs (by rw [Fintype.card_fin, E.rank_eq_one_of_ne_bot h1 hG]),
    E.degree_eq_of_linearIndependent ⊤ ht (by rw [Fintype.card_fin, hrt])]
  refine sub_le_sub_right ?_ _
  have hfin : Finite ((⊤ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range t)) :=
    finite_quotient_span ht (by rw [Fintype.card_fin, finrank_top, h1])
  have hle : Submodule.span (𝓞 K) (Set.range s) ≤
      (Submodule.span (𝓞 K) (Set.range t)).comap (Submodule.inclusion le_top) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  let φ := Submodule.mapQ _ _ (Submodule.inclusion (le_top : G ≤ ⊤)) hle
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hrt' : Set.range t = {⟨g, Submodule.mem_top⟩} := Set.range_const
    have hrs : Set.range s = {⟨g, hgG⟩} := Set.range_const
    rw [hrt', Submodule.mem_span_singleton] at hm
    rw [hrs, Submodule.mem_span_singleton]
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, Subtype.ext ?_⟩
    have := congrArg Subtype.val ha
    simpa using this
  have hfin' : Finite (G ⧸ Submodule.span (𝓞 K) (Set.range s)) := Finite.of_injective φ hinj
  have hcard := Nat.card_le_card_of_injective φ hinj
  have hpos : 0 < Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range s)) := Nat.card_pos
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)
theorem isCanonicalFiltration_of_finrank_one (h1 : Module.finrank (𝓞 K) E.carrier = 1) :
    E.IsCanonicalFiltration (trivialFlag E) := by
  have : Nontrivial E.carrier := Module.nontrivial_of_finrank_eq_succ h1
  refine ⟨rfl, rfl, ?_, ?_, ?_, Subsingleton.strictAnti _⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
    fin_cases i
    exact bot_lt_top
  · intro i
    fin_cases i
    · exact E.saturated_bot
    · exact E.saturated_top
  · intro i G hG _
    fin_cases i
    have hG' : G ≠ ⊥ := ne_bot_of_gt hG
    have hrt : E.rank ⊤ = 1 := E.rank_eq_one_of_ne_bot h1 top_ne_bot
    have hrb : E.rank ⊥ = 0 := by simp [HermitianBundle.rank]
    have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    change E.relSlope ⊥ G ≤ E.relSlope ⊥ ⊤
    simp only [relSlope, normDegree, E.rank_eq_one_of_ne_bot h1 hG', hrt, hrb, degree_bot]
    simp only [Nat.cast_one, Nat.cast_zero, sub_zero, zero_div, div_one]
    exact div_le_div_of_nonneg_right (E.degree_le_degree_top h1 hG') hd.le
theorem semistable_of_finrank_one (h1 : Module.finrank (𝓞 K) E.carrier = 1) : E.Semistable := by
  have : Nontrivial E.carrier := Module.nontrivial_of_finrank_eq_succ h1
  refine ⟨by omega, fun G hG ↦ ?_⟩
  simp only [slope, normDegree, E.rank_eq_one_of_ne_bot h1 hG, E.rank_eq_one_of_ne_bot h1 top_ne_bot,
    Nat.cast_one, div_one]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  exact div_le_div_of_nonneg_right (E.degree_le_degree_top h1 hG) hd.le
end HermitianBundle
example : ratIntegers.Semistable :=
  HermitianBundle.semistable_of_finrank_one _ (Module.finrank_self (𝓞 ℚ))
theorem isCanonicalFiltration_integers (K : Type) [Field K] [NumberField K] :
    (HermitianBundle.integers K).IsCanonicalFiltration (trivialFlag (HermitianBundle.integers K)) :=
  HermitianBundle.isCanonicalFiltration_of_finrank_one _ (Module.finrank_self (𝓞 K))
example : ratIntegers.IsCanonicalFiltration (trivialFlag ratIntegers) :=
  isCanonicalFiltration_integers ℚ
example : ratIntegers.IsCanonicalFiltration (m := 0 + 1) (trivialFlag ratIntegers) :=
  isCanonicalFiltration_integers ℚ
example : (0 : ℝ) < 1 := one_pos
end
end GroundTheory.Heights₂.Heights



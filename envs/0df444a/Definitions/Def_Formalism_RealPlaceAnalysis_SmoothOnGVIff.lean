-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
-- name    : Formalism_RealPlaceAnalysis_SmoothOnGVIff
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:22:53.398148+00:00
-- url     : https://prove2.me/theorems/ba878e2d-a715-4e24-8f09-e3443ada2574
-- title:
--   Smooth On GVIff
-- statement:
--   Definitions and structural lemmas for Smooth On GVIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/SmoothOnGVIff.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementD
import Theorems.Thm_Formalism_REAL_exp_indefinite_unitary_holds
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix
import Theorems.Thm_Formalism_REAL_maximal_compact_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
namespace Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical in

def expG {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : UJ ε :=
  if h : inG ε X then
    ⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, exp_indefinite_unitary_holds n ε X h t⟩
  else 1
lemma toM_expG {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (h : inG ε X) :
    toM (expG ε X t) = NormedSpace.exp ((t : ℂ) • X) := by
  rw [expG, dif_pos h]
  exact IsUnit.unit_spec _
lemma Kset_mul {n : ℕ} (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hh : h ∈ Kset ε) : g * h ∈ Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]
lemma Kset_star {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    star g ∈ Kset ε := by
  have hJ : star (Jm ε) = Jm ε := by
    rw [Jm, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext a; by_cases ha : ε a <;> simp [ha]
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  have h := congrArg star hg.2
  rw [star_mul, star_mul, hJ] at h
  exact h.symm
def KG {n : ℕ} (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | toM g ∈ Kset ε}
  mul_mem' := by
    intro g h hg hh
    show toM g * toM h ∈ Kset ε
    exact Kset_mul ε hg hh
  one_mem' := by
    show (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε
    refine ⟨Submonoid.one_mem _, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro g hg
    have hinv : ((((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) =
        star (toM g) := by
      show (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = _
      exact Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem hg.1)
    have h2 : toM g⁻¹ = star (toM g) := hinv
    show toM g⁻¹ ∈ Kset ε
    rw [h2]
    exact Kset_star ε hg
abbrev toMK {n : ℕ} {ε : Fin n → Bool} (k : KG ε) : Matrix (Fin n) (Fin n) ℂ := toM (k : UJ ε)
lemma range_toMK {n : ℕ} (ε : Fin n → Bool) :
    Set.range (fun k : KG ε => toMK k) = Kset ε := by
  ext M
  constructor
  · rintro ⟨k, rfl⟩
    exact k.2
  · intro hM
    have hu : M * star M = 1 := Unitary.mul_star_self_of_mem hM.1
    have hu' : star M * M = 1 := Unitary.star_mul_self_of_mem hM.1
    have hUJ : inUJ ε M := by
      show Mᴴ * Jm ε * M = Jm ε
      rw [Matrix.mul_assoc, ← hM.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu',
        Matrix.one_mul]
    exact ⟨⟨⟨⟨M, star M, hu, hu'⟩, hUJ⟩, hM⟩, rfl⟩
instance instCompactKG (n : ℕ) (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  rw [← isCompact_univ_iff, hemb.isCompact_iff, Set.image_univ, range_toMK]
  exact (maximal_compact_facts n ε).2.1
def muK {n : ℕ} (ε : Fin n → Bool) : Measure (KG ε) := Measure.haarMeasure ⊤
instance instIsHaarMuK (n : ℕ) (ε : Fin n → Bool) : (muK ε).IsHaarMeasure := by
  unfold muK; infer_instance
lemma inK_smul_real {n : ℕ} (ε : Fin n → Bool) {Z : Matrix (Fin n) (Fin n) ℂ} (h : inK ε Z) (t : ℝ) :
    inK ε ((t : ℂ) • Z) := by
  obtain ⟨hG, hJ⟩ := h
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  refine ⟨?_, ?_⟩
  · unfold inG at hG ⊢
    rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hG, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hJ]
open Classical in

def expK {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : KG ε :=
  if h : inK ε Z then
    ⟨expG ε Z t, by
      show toM (expG ε Z t) ∈ Kset ε
      rw [toM_expG ε Z t h.1]
      exact (maximal_compact_facts n ε).2.2.2.1 _ (inK_smul_real ε h t)⟩
  else 1
def ExpGFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ), inG ε X →
    expG ε X 0 = 1 ∧ (∀ s t : ℝ, expG ε X (s + t) = expG ε X s * expG ε X t) ∧
    Continuous (fun t : ℝ => expG ε X t) ∧
    (inK ε X → (∀ t : ℝ, ((expK ε X t : KG ε) : UJ ε) = expG ε X t) ∧ Continuous (fun t : ℝ => expK ε X t))
def KHaar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    IsProbabilityMeasure (muK ε) ∧
    (∀ k : KG ε, Measure.map (fun x => k * x) (muK ε) = muK ε) ∧
    (∀ k : KG ε, Measure.map (fun x => x * k) (muK ε) = muK ε) ∧
    Measure.map (fun x : KG ε => x⁻¹) (muK ε) = muK ε
def KExp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ), k ∈ Kset ε →
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ NormedSpace.exp Y = k ∧ hs Y ≤ 3 * hs (k - 1)
def GenExp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
    ∃ Z X : Matrix (Fin n) (Fin n) ℂ, inK ε Z ∧ inP ε X ∧
      g = NormedSpace.exp Z * NormedSpace.exp X
def KByParts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F D : KG ε → E) (Z : Matrix (Fin n) (Fin n) ℂ),
    inK ε Z → Continuous F → Continuous D →
    (∀ k : KG ε, HasDerivAt (fun t : ℝ => F (k * expK ε Z t)) (D k) 0) →
    ∫ k, D k ∂(muK ε) = 0
def LamDom : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam →
    (∀ a, ∃ z : ℤ, lam a - rhoS n a = z) →
    (∀ a, ∃ z : ℤ, lam a + rhoN ε a - rhoC ε a = z) ∧
    (∀ a, ∃ z : ℤ, lam a + rhoS n a = z) ∧
    ∀ a b : Fin n, a < b → ε a = ε b →
      lam b + rhoN ε b - rhoC ε b ≤ lam a + rhoN ε a - rhoC ε a
def EabConj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n)
    (g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → inUJ ε g →
    Eab ε a b (fun x => starRingEnd ℂ (f x)) g = -(sgn ε a b : ℂ) * starRingEnd ℂ (Eab ε b a f g)
def SmoothOnGV {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUJ ε g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g
def RdV {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
def EcV {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (ε : Fin n → Bool)
    (Z : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (cpart1 ε Z) f g + Complex.I • RdV (cpart2 ε Z) f g
def EabV {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (ε : Fin n → Bool) (a b : Fin n)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  EcV ε (Matrix.single a b 1) f
def EwordV {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (ε : Fin n → Bool) :
    List (Fin n × Fin n) → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)
  | [] => id
  | p :: w => fun f => EabV ε p.1 p.2 (EwordV ε w f)
def RdExtV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ)) (g X : Matrix (Fin n) (Fin n) ℂ),
    IsOpen U → g ∈ U → inUJ ε g → ContDiffOn ℝ ∞ F U → (∀ h ∈ U, inUJ ε h → f h = F h) →
    inG ε X → RdV X f g = fderiv ℝ F g (g * X)
def RdSmoothV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (X : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnGV ε f → inG ε X → SmoothOnGV ε (RdV X f)
def RdLinV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f f' : Matrix (Fin n) (Fin n) ℂ → E) (X Y : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (c : ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnGV ε f → SmoothOnGV ε f' → inG ε X → inG ε Y → inUJ ε g →
    RdV (X + Y) f g = RdV X f g + RdV Y f g ∧ RdV ((r : ℂ) • X) f g = (r : ℂ) • RdV X f g ∧
    RdV X (fun h => f h + c • f' h) g = RdV X f g + c • RdV X f' g
def RdBracketV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (X Y g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnGV ε f → inG ε X → inG ε Y → inUJ ε g →
    RdV X (RdV Y f) g - RdV Y (RdV X f) g = RdV (X * Y - Y * X) f g
def EabGlV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b c d : Fin n) (g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnGV ε f → inUJ ε g →
    EabV ε a b (EabV ε c d f) g - EabV ε c d (EabV ε a b f) g =
      (if b = c then EabV ε a d f g else 0) - (if d = a then EabV ε c b f g else 0)
def RdLeftV : Prop :=
  ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (X h g : Matrix (Fin n) (Fin n) ℂ),
    RdV X (fun x => f (h * x)) g = RdV X f (h * g)
def RdVPair : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (φ : E →L[ℂ] E')
    (f : Matrix (Fin n) (Fin n) ℂ → E) (X g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnGV ε f → inG ε X → inUJ ε g →
    SmoothOnGV ε (fun x => φ (f x)) ∧ φ (RdV X f g) = RdV X (fun x => φ (f x)) g
def EcSumV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (Z g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnGV ε f → inUJ ε g →
    EcV ε Z f g = ∑ a, ∑ b, Z a b • EabV ε a b f g
end Formalism.REAL



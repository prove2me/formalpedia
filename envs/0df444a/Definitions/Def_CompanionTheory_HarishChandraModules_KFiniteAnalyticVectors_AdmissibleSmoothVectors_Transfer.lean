-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:38.844316+00:00
-- url     : https://prove2.me/theorems/b8e70b62-acf7-4ef3-88bd-514895e77871
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
namespace CompanionTheory.D.gk.admitted
namespace PrismTransfer
section Closure
variable {G : Type} [Group G] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
def sumRep (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix ι' ι' ℂ) : G →* Matrix (ι ⊕ ι') (ι ⊕ ι') ℂ where
  toFun x := fromBlocks (ρ x) 0 0 (ρ' x)
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]
def tensRep (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix ι' ι' ℂ) : G →* Matrix (ι × ι') (ι × ι') ℂ where
  toFun x := ρ x ⊗ₖ ρ' x
  map_one' := by simp
  map_mul' x y := by simp [mul_kronecker_mul]
def conjRep (ρ : G →* Matrix ι ι ℂ) : G →* Matrix ι ι ℂ where
  toFun x := (ρ x).map (starRingEnd ℂ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.map_mul]
variable [TopologicalSpace G] {st : G → G} {S : Set G} {ρ : G →* Matrix ι ι ℂ} {ρ' : G →* Matrix ι' ι' ℂ}
theorem isGood_sum (h : IsGood st S ρ) (h' : IsGood st S ρ') : IsGood st S (sumRep ρ ρ') where
  cont := Continuous.matrix_fromBlocks h.cont continuous_const continuous_const h'.cont
  adj g := by
    change fromBlocks (ρ (st g)) 0 0 (ρ' (st g)) = (fromBlocks (ρ g) 0 0 (ρ' g))ᴴ
    simp [fromBlocks_conjTranspose, h.adj, h'.adj]
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    obtain ⟨b, hb, hb'⟩ := h'.tri
    refine ⟨Sum.elim (fun i => 2 * a i) (fun j => 2 * b j + 1), ?_, ?_⟩
    · rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
      · rw [ha (show a i = a j by omega)]
      · omega
      · omega
      · rw [hb (show b i = b j by omega)]
    · intro s hs
      change (fromBlocks (ρ s) 0 0 (ρ' s)).BlockTriangular _
      rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
      · exact ha' s hs (show a j < a i by omega)
      · rfl
      · rfl
      · exact hb' s hs (show b j < b i by omega)
theorem pair_mono {a b c d : ℕ} (h : a ≤ c) (h' : b ≤ d) : Nat.pair a b ≤ Nat.pair c d := by
  have h1 : Nat.pair a b ≤ Nat.pair c b := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (Nat.pair_lt_pair_left b h).le
  have h2 : Nat.pair c b ≤ Nat.pair c d := by
    rcases h'.eq_or_lt with rfl | h'
    · exact le_rfl
    · exact (Nat.pair_lt_pair_right c h').le
  exact h1.trans h2
theorem isGood_tens (h : IsGood st S ρ) (h' : IsGood st S ρ') : IsGood st S (tensRep ρ ρ') where
  cont := by
    refine continuous_matrix fun i j => ?_
    exact (h.cont.matrix_elem i.1 j.1).mul (h'.cont.matrix_elem i.2 j.2)
  adj g := by
    change ρ (st g) ⊗ₖ ρ' (st g) = (ρ g ⊗ₖ ρ' g)ᴴ
    rw [conjTranspose_kronecker, h.adj, h'.adj]
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    obtain ⟨b, hb, hb'⟩ := h'.tri
    refine ⟨fun p => Nat.pair (a p.1) (b p.2), ?_, ?_⟩
    · intro p q hpq
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 hpq
      exact Prod.ext (ha h1) (hb h2)
    · intro s hs p q hpq
      change ρ s p.1 q.1 * ρ' s p.2 q.2 = 0
      by_cases h1 : a q.1 < a p.1
      · rw [ha' s hs h1, zero_mul]
      by_cases h2 : b q.2 < b p.2
      · rw [hb' s hs h2, mul_zero]
      exact absurd (pair_mono (not_lt.1 h1) (not_lt.1 h2)) (not_le.2 hpq)
theorem isGood_conj (h : IsGood st S ρ) : IsGood st S (conjRep ρ) where
  cont := by
    refine continuous_matrix fun i j => ?_
    exact Complex.continuous_conj.comp (h.cont.matrix_elem i j)
  adj g := by
    change (ρ (st g)).map (starRingEnd ℂ) = ((ρ g).map (starRingEnd ℂ))ᴴ
    rw [h.adj]
    ext i j
    simp
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    refine ⟨a, ha, fun s hs i j hij => ?_⟩
    change starRingEnd ℂ (ρ s i j) = 0
    rw [ha' s hs hij, map_zero]
theorem isGood_one : IsGood st S (1 : G →* Matrix Unit Unit ℂ) where
  cont := continuous_const
  adj g := by simp
  tri := ⟨fun _ => 0, fun _ _ _ => rfl, fun _ _ _ _ h => absurd h (lt_irrefl _)⟩
omit [DecidableEq ι] [DecidableEq ι'] in
theorem coef_kronecker (A : Matrix ι ι ℂ) (B : Matrix ι' ι' ℂ) (a b : ι → ℂ) (a' b' : ι' → ℂ) :
    (fun p : ι × ι' => a p.1 * a' p.2) ⬝ᵥ ((A ⊗ₖ B) *ᵥ fun p : ι × ι' => b p.1 * b' p.2) =
      (a ⬝ᵥ (A *ᵥ b)) * (a' ⬝ᵥ (B *ᵥ b')) := by
  have : ((A ⊗ₖ B) *ᵥ fun p : ι × ι' => b p.1 * b' p.2) = fun p => (A *ᵥ b) p.1 * (B *ᵥ b') p.2 := by
    funext p
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum, kroneckerMap_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
def coefAlg (st : G → G) (S : Set G) (C : Set G) : StarSubalgebra ℂ C(C, ℂ) where
  carrier := {f | ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ) (a b : κ → ℂ),
    IsGood st S τ ∧ ∀ x : C, f x = a ⬝ᵥ (τ x *ᵥ b)}
  mul_mem' := by
    rintro f g ⟨κ, _, _, τ, a, b, h, hf⟩ ⟨κ', _, _, τ', a', b', h', hg⟩
    refine ⟨κ × κ', inferInstance, inferInstance, tensRep τ τ', fun p => a p.1 * a' p.2,
      fun p => b p.1 * b' p.2, isGood_tens h h', fun x => ?_⟩
    rw [ContinuousMap.mul_apply, hf, hg]
    exact (coef_kronecker _ _ _ _ _ _).symm
  add_mem' := by
    rintro f g ⟨κ, _, _, τ, a, b, h, hf⟩ ⟨κ', _, _, τ', a', b', h', hg⟩
    refine ⟨κ ⊕ κ', inferInstance, inferInstance, sumRep τ τ', Sum.elim a a', Sum.elim b b',
      isGood_sum h h', fun x => ?_⟩
    rw [ContinuousMap.add_apply, hf, hg]
    change _ = Sum.elim a a' ⬝ᵥ (fromBlocks (τ x) 0 0 (τ' x) *ᵥ Sum.elim b b')
    simp [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  algebraMap_mem' c := by
    refine ⟨Unit, inferInstance, inferInstance, 1, fun _ => c, fun _ => 1, isGood_one, fun x => ?_⟩
    simp [dotProduct]
  star_mem' := by
    rintro f ⟨κ, _, _, τ, a, b, h, hf⟩
    refine ⟨κ, inferInstance, inferInstance, conjRep τ, star a, star b, isGood_conj h, fun x => ?_⟩
    rw [ContinuousMap.star_apply, hf]
    change _ = star a ⬝ᵥ ((τ x).map (starRingEnd ℂ) *ᵥ star b)
    simp [dotProduct, mulVec, mul_comm]
end Closure
section Bound
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (e : K → ℂ)
structure IsFam (Φ : G → ℂ) (F : List G → G → ℂ) : Prop where
  cont₀ : Continuous Φ
  cont : ∀ l, Continuous (F l)
  nil : ∀ x, F [] x = ∫ k : K, e k * Φ (x * k) ∂μ
  cons : ∀ a l x, F (a :: l) x = ∫ k : K, e k * F l (x * k * a) ∂μ
variable {μ e}
end Bound
end PrismTransfer
open PrismTransfer
end CompanionTheory.D.gk.admitted



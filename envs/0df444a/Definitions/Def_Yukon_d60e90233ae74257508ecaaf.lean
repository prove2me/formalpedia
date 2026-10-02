-- Prove2me | Definitions.Def_Yukon_d60e90233ae74257508ecaaf
-- name    : Yukon_d60e90233ae74257508ecaaf
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:26:49.891989+00:00
-- url     : https://prove2.me/theorems/1e725195-fd12-4f41-852a-0bff1ffb7406
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.FoldChainGeometry6813.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.FoldChainGeometry6813.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/FoldChainGeometry6813.lean
--
--   yukon-proof-operation:foundation-direct-82448096e2bc90c2d86c1dbd0c611aeb763a6ef999ea85e6fca412d6521eb673
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODFmMDk2ODhhZTZlOTI5OWU3MjUwZjk3Y2ExN2FhMjQ5MDRkNTAyYmQ1NGEwNzk1NjRiNzZiMjgzNDczNDcxMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTgyNDQ4MDk2ZTJiYzkwYzJkODZjMWRiZDBjNjExYWViNzYzYTZlZjk5OWVhODVlNmZjYTQxMmQ2NTIxZWI2NzMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kNjBlOTAyMzNhZTc0MjU3NTA4ZWNhYWYiLCJ2IjoyfQ]

import Definitions.Def_Yukon_0e3496485be9a551c983331b









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
Fold-chain accounting. A seed at which both `F` and `F_R` vanish, and at
which the `R`-free end of the derivative chain does not vanish, lies on the
fold curve `V(g, F_R)` for a geometric factor `g` of `F`. On each component
`C` of that curve take the first derivative `dR m F` outside `C`; then
`m ≥ 2`, and every seed on `C` is either a regular solution of the carrier
`dR (m-1) F` or a zero of `dR m F` on `C`. The first kind is counted by the
sharp prime incidence bound, the second by the zero-point box bound. Both use
the degree of `C`, so the fold curve is paid once for the whole chain rather
than once per derivative stage.
-/

namespace ProximityPrize.SubmissionLower.FoldChain6813
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174
  RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
  RCN264 RCN007 RCN004 RCN072
  LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K] {ι : Type*}
local instance  _root_.ProximityPrize.SubmissionLower.FoldChain6813.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.FoldChain6813.instDecidableEq_proximityPrize_1 : DecidableEq ι := Classical.decEq ι

/-- Seeds on the fold curve of `F` that are not `R`-free tail seeds. -/
def foldSeeds (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ F = 0 ∧
    specialization K (selected γ) γ (dR 1 F) = 0 ∧
    specialization K (selected γ) γ (dR (chainLength F) F) ≠ 0

theorem foldSeeds_subset (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) : foldSeeds F selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem dR_one (F : MvPolynomial (Fin 4) K) :
    dR 1 F = MvPolynomial.pderiv (2 : Fin 4) F := dR_succ 0 F

/-- A seed of `F` and `F_R` is a fold seed or a tail seed. -/
theorem mem_fold_or_tail (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) (γ : K) (hγ : γ ∈ Gamma)
    (h0 : specialization K (selected γ) γ F = 0)
    (h1 : specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) F) = 0) :
    γ ∈ foldSeeds F selected Gamma ∪ tailSeeds F selected Gamma := by
  by_cases hL : specialization K (selected γ) γ (dR (chainLength F) F) = 0
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hL⟩)
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hγ, h0, by rw [dR_one]; exact h1, hL⟩)

/-- A factor of `R`-degree one has no fold seeds. -/
theorem foldSeeds_eq_empty_of_degree_one (F : MvPolynomial (Fin 4) K)
    (hF : F.degreeOf 2 = 1) (selected : K → Polynomial K) (Gamma : Finset K) :
    foldSeeds F selected Gamma = ∅ := by
  have hL : chainLength F = 1 := by
    have h1 := chainLength_pos F (by omega)
    have h2 := chainLength_le F
    omega
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro γ hγ
  obtain ⟨_, _, h1, hne⟩ := Finset.mem_filter.mp hγ
  rw [hL] at hne
  exact hne h1

/-- Every seed of `Q` lies in the regular pair seeds, the fold seeds, the tail
seeds or the `R`-free seeds. -/
theorem cover_fold (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0) :
    Gamma ⊆
      (Finset.univ.biUnion fun F : RegularIndex Q =>
          regularPairSeeds Q T selected Gamma F) ∪
        ((positiveRFactors Q).biUnion fun F => foldSeeds F selected Gamma) ∪
        ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma) ∪
        rfreeSeeds Q selected Gamma := by
  intro γ hγ
  obtain ⟨F, hFactive, hFzero⟩ :=
    exists_active_factor_of_solution Q hQ (selected γ) γ (hQsolution γ hγ)
  by_cases hRfree : F.degreeOf 2 = 0
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr ⟨hγ, ?_⟩
    have hdiv : F ∣ rfreeProduct Q := by
      unfold rfreeProduct
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hFactive, hRfree⟩)
    obtain ⟨c, hc⟩ := hdiv
    rw [hc, map_mul, hFzero, zero_mul]
  · have hFpos : F ∈ positiveRFactors Q := by
      unfold positiveRFactors
      exact Finset.mem_filter.mpr ⟨hFactive, Nat.pos_of_ne_zero hRfree⟩
    by_cases hreg : specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) F) = 0
    · rcases Finset.mem_union.mp (mem_fold_or_tail F selected Gamma γ hγ hFzero hreg) with
        hfold | htail
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨F, hFpos, hfold⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨F, hFpos, htail⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr ⟨⟨F, hFpos⟩, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hγ, ⟨hFzero, hreg⟩, hTsolution γ hγ⟩

section Components

variable (K)

/-- A seed on a component vanishes on every polynomial whose surface lies in it. -/
theorem specialization_zero_of_component
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) (selected : K → Polynomial K) (γ : K)
    (hC : C ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) selected γ)).toRingHom)
    (Q : MvPolynomial (Fin 4) K) (hQ : surfaceMap (polynomialEmbedding K) Q ∈ C) :
    specialization K (selected γ) γ Q = 0 := by
  have h := RingHom.mem_ker.mp (hC hQ)
  change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
    (surfaceMap (polynomialEmbedding K) Q) = 0 at h
  rw [selectedPoint_surface_evaluation] at h
  exact (polynomialEmbedding_eq_zero_iff K _).mp h

/-- One component of the fold curve: its seeds are regular seeds of one
derivative carrier or zeros of the next derivative on the component. -/
theorem fold_component_count
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) (GenericField K))
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hproper : ¬ G ∣ surfaceMap (polynomialEmbedding K) (dR 1 F))
    (C : RegularComponent (GenericField K) G (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1)
    (p : ℕ) [CharP K p]
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf j * G.degreeOf k +
        G.degreeOf j * (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf k < p)
    (y r z : ℕ) (hr : 1 ≤ r) (hY : F.degreeOf 1 ≤ y) (hR : F.degreeOf 2 - 1 ≤ r)
    (hZ : F.degreeOf 3 ≤ z)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (w a e : ℕ) (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (htail : ∀ γ ∈ Γ, specialization K (selected γ) γ (dR (chainLength F) F) ≠ 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    (componentSeeds (GenericField K) G (surfaceMap (polynomialEmbedding K) (dR 1 F)) 1 Γ
        (selectedPoint (polynomialEmbedding K) selected) C).card * (a - w) ≤
      (nodes.card - w) * (∑ i, capAt (agreementCaps y r z w) i *
          actualCoordinateDegree (GenericField K) C.1 i) +
        (e + 1) * (a - w) * actualCoordinateDegree (GenericField K) C.1 2 +
        (a - w) * (∑ i, capAt ⟨y, r, z⟩ i * actualCoordinateDegree (GenericField K) C.1 i) := by
  classical
  letI : CharP (GenericField K) p := genericField_charP K p
  let phi := polynomialEmbedding K
  let T := surfaceMap phi (dR 1 F)
  let S := componentSeeds (GenericField K) G T 1 Γ (selectedPoint phi selected) C
  show S.card * (a - w) ≤ _
  have hsub : S ⊆ Γ := componentSeeds_subset _ G T 1 Γ _ C
  have hon : ∀ γ ∈ S, C.1 ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi selected γ)).toRingHom :=
    fun γ hγ => componentSeeds_on_prime _ G T 1 Γ _ C γ hγ
  have hgmem := regularComponent_G_mem _ G T 1 C
  have htmem := regularComponent_T_mem _ G T 1 C
  have hFmem : surfaceMap phi (dR 0 F) ∈ C.1 :=
    ((Ideal.span_singleton_le_iff_mem (I := C.1)).mpr hgmem)
      (Ideal.mem_span_singleton.mpr hdiv)
  by_cases hex : ∃ m, surfaceMap phi (dR m F) ∉ C.1
  · obtain ⟨m, hmout, hmin⟩ : ∃ m, surfaceMap phi (dR m F) ∉ C.1 ∧
        ∀ k < m, surfaceMap phi (dR k F) ∈ C.1 :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_not.mp (Nat.find_min hex hk)⟩
    have hm2 : 2 ≤ m := by
      by_contra hlt
      interval_cases m
      · exact hmout hFmem
      · exact hmout htmem
    have hcarrier : surfaceMap phi (dR (m - 1) F) ∈ C.1 := hmin (m - 1) (by omega)
    have hderiv : MvPolynomial.pderiv (2 : Fin 4) (dR (m - 1) F) = dR m F := by
      rw [← dR_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    have hproj : ProjectionsFiniteSeparable (GenericField K) C.1 :=
      all_transcendental_coordinates_finite_separable _ C.1 p G T hG hgmem htmem
        hproper hGdegree hcutDegree
    have hnonpoint := regularComponent_ne_point _ G T 1 C
    let S₁ := S.filter fun γ => specialization K (selected γ) γ (dR m F) ≠ 0
    let S₂ := S.filter fun γ => ¬ specialization K (selected γ) γ (dR m F) ≠ 0
    have hsplit : S₁.card + S₂.card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have hS₁ : S₁ ⊆ S := Finset.filter_subset _ _
    have hS₂ : S₂ ⊆ S := Finset.filter_subset _ _
    -- regular seeds of the carrier `dR (m-1) F`
    have hcap : ∀ i ∈ nodes, ∀ j,
        (agreementPolynomial phi (dR (m - 1) F) w (x i) (u₀ i) (u₁ i)).degreeOf j ≤
          capAt (agreementCaps y r z w) j := by
      intro i _ j
      have h := surface_agreement_caps phi (dR (m - 1) F) y r z hr
        ((dR_degree_le (m - 1) F 1).trans hY)
        ((dR_R_degree_le (m - 1) F).trans (by omega))
        ((dR_degree_le (m - 1) F 3).trans hZ) w (fun j => (j.factorial : K)⁻¹)
        (x i) (u₀ i) (u₁ i)
      simpa [agreementPolynomial] using h j
    have hreg := prime_seed_incidence_sharp phi C.1 hproj hnonpoint (dR (m - 1) F) hcarrier
      (by rw [hderiv]; exact hmout) selected S₁ nodes x u₀ u₁ hinj p w a e hw hchar hwa han
      (fun γ hγ => hdegree γ (hsub (hS₁ hγ)))
      (fun γ hγ => specialization_zero_of_component K C.1 selected γ (hon γ (hS₁ hγ)) _
        hcarrier)
      (fun γ hγ => selectedPoint_regular_of_specialization K (dR (m - 1) F) selected γ
        (by rw [hderiv]; exact (Finset.mem_filter.mp hγ).2))
      (fun γ hγ => hon γ (hS₁ hγ))
      (fun γ hγ => hagreement γ (hsub (hS₁ hγ)))
      (noLargeSelectedPencil_mono selected Γ S₁ w e (hS₁.trans hsub) hnoPencil)
      (capAt (agreementCaps y r z w)) hcap
    -- zeros of `dR m F` on the component
    let points := S₂.image (selectedPoint phi selected)
    have hjcap : ∀ i, (surfaceMap phi (dR m F)).degreeOf i ≤ capAt ⟨y, r, z⟩ i := by
      intro i
      have h := surfaceMap_degreeOf_le phi (dR m F) i
      fin_cases i
      · exact h.trans ((dR_degree_le m F 1).trans hY)
      · exact h.trans ((dR_R_degree_le m F).trans (by change F.degreeOf 2 - m ≤ r; omega))
      · exact h.trans ((dR_degree_le m F 3).trans hZ)
    have hjump := finite_zero_points_le_box (GenericField K) C.1 hproj hnonpoint
      (surfaceMap phi (dR m F)) hmout (capAt ⟨y, r, z⟩) hjcap points
      (by
        intro v hv
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
        exact hon γ (hS₂ hγ))
      (by
        intro v hv
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
        have hz : specialization K (selected γ) γ (dR m F) = 0 :=
          not_not.mp (Finset.mem_filter.mp hγ).2
        change MvPolynomial.eval (selectedPoint phi selected γ) (surfaceMap phi (dR m F)) = 0
        rw [selectedPoint_surface_evaluation, hz, map_zero])
    have hpoints : points.card = S₂.card :=
      Finset.card_image_of_injective _ (selectedPoint_injective phi selected)
    rw [hpoints] at hjump
    have hjump' : S₂.card ≤ ∑ i, capAt ⟨y, r, z⟩ i *
        actualCoordinateDegree (GenericField K) C.1 i := by
      exact_mod_cast hjump
    have hreg' : S₁.card * (a - w) ≤ (nodes.card - w) * (∑ i, capAt (agreementCaps y r z w) i *
          actualCoordinateDegree (GenericField K) C.1 i) +
        (e + 1) * (a - w) * actualCoordinateDegree (GenericField K) C.1 2 := hreg
    calc
      S.card * (a - w) = S₁.card * (a - w) + S₂.card * (a - w) := by
        rw [← hsplit, Nat.add_mul]
      _ ≤ _ := by
        have := Nat.mul_le_mul_left (a - w) hjump'
        nlinarith
  · have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      apply htail γ (hsub hγ)
      exact specialization_zero_of_component K C.1 selected γ (hon γ hγ) _
        (not_not.mp (fun h => hex ⟨chainLength F, h⟩))
    rw [hempty, Finset.card_empty, Nat.zero_mul]
    exact Nat.zero_le _

/-- All fold seeds on one geometric factor `G` of `F`. -/
theorem fold_factor_count
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) (GenericField K))
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hproper : ¬ G ∣ surfaceMap (polynomialEmbedding K) (dR 1 F))
    (p : ℕ) [CharP K p]
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf j * G.degreeOf k +
        G.degreeOf j * (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf k < p)
    (y r z : ℕ) (hr : 1 ≤ r) (hY : F.degreeOf 1 ≤ y) (hR : F.degreeOf 2 - 1 ≤ r)
    (hZ : F.degreeOf 3 ≤ z)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (w a e : ℕ) (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hGpoint : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ) G = 0)
    (hfold : ∀ γ ∈ Γ, specialization K (selected γ) γ (dR 1 F) = 0)
    (htail : ∀ γ ∈ Γ, specialization K (selected γ) γ (dR (chainLength F) F) ≠ 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    Γ.card * (a - w) ≤
      1 * (∑ i, ((nodes.card - w) * capAt (agreementCaps y r z w) i +
          (a - w) * capAt ⟨y, r, z⟩ i) *
        coordinateMixedDegree (GenericField K) G (surfaceMap (polynomialEmbedding K) (dR 1 F)) i) +
      (e + 1) * (a - w) *
        coordinateMixedDegree (GenericField K) G (surfaceMap (polynomialEmbedding K) (dR 1 F)) 2 := by
  classical
  letI : CharP (GenericField K) p := genericField_charP K p
  let T := surfaceMap (polynomialEmbedding K) (dR 1 F)
  letI : ∀ C : RegularComponent (GenericField K) G T 1, C.1.IsPrime :=
    fun C => regularComponent_isPrime (GenericField K) G T 1 C
  have hTpoint : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ) T = 0 := by
    intro γ hγ
    change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
      (surfaceMap (polynomialEmbedding K) (dR 1 F)) = 0
    rw [selectedPoint_surface_evaluation, hfold γ hγ, map_zero]
  have hbudget : ∀ i, (∑ C : RegularComponent (GenericField K) G T 1,
      actualCoordinateDegree (GenericField K) C.1 i) ≤
        coordinateMixedDegree (GenericField K) G T i := by
    intro i
    have hneq : (Equiv.swap (0 : Fin 3) i) 1 ≠ (Equiv.swap (0 : Fin 3) i) 2 :=
      (Equiv.swap (0 : Fin 3) i).injective.ne (by decide)
    exact sum_actualCoordinateDegree_at_le (GenericField K)
      (fun C : RegularComponent (GenericField K) G T 1 => C.1)
      Subtype.val_injective i p G T hG
      (regularComponent_G_mem (GenericField K) G T 1)
      (regularComponent_T_mem (GenericField K) G T 1)
      hproper hGdegree (hcutDegree _ _ hneq)
  apply aggregate_component_incidence (GenericField K) G T 1 Γ
    (selectedPoint (polynomialEmbedding K) selected) hGpoint hTpoint (fun _ _ => by simp)
    (a - w) 1 (e + 1) _ (coordinateMixedDegree (GenericField K) G T)
    (fun C i => actualCoordinateDegree (GenericField K) C.1 i) _ hbudget
  intro C
  have h := fold_component_count K F G hG hdiv hproper C p hGdegree hcutDegree y r z hr hY hR hZ
    selected Γ nodes x u₀ u₁ hinj w a e hw hchar hwa han hdegree htail hagreement hnoPencil
  have heq : (∑ i, ((nodes.card - w) * capAt (agreementCaps y r z w) i +
      (a - w) * capAt ⟨y, r, z⟩ i) * actualCoordinateDegree (GenericField K) C.1 i) =
      (nodes.card - w) * (∑ i, capAt (agreementCaps y r z w) i *
        actualCoordinateDegree (GenericField K) C.1 i) +
      (a - w) * (∑ i, capAt ⟨y, r, z⟩ i * actualCoordinateDegree (GenericField K) C.1 i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  show _ ≤ 1 * (∑ i, ((nodes.card - w) * capAt (agreementCaps y r z w) i +
      (a - w) * capAt ⟨y, r, z⟩ i) * actualCoordinateDegree (GenericField K) C.1 i) +
    (e + 1) * (a - w) * actualCoordinateDegree (GenericField K) C.1 2
  rw [Nat.one_mul, heq]
  exact h.trans (le_of_eq (by ring))

end Components

/-- **Fold-chain bound.** All fold seeds of an irreducible `F` pay the fold
curve `V(F, F_R)` once: the agreement numerator of the first derivative stage,
plus the zero-point cost of the jump seeds. -/
theorem foldSeeds_card_le_left
    (P : UnequalParameters) (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (hY : F.degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 - 1 ≤ P.leftR)
    (hZ : F.degreeOf 3 ≤ P.leftZ)
    (hY' : F.degreeOf 1 ≤ P.rightY) (hR' : F.degreeOf 2 ≤ P.rightR)
    (hZ' : F.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hrightYSmall : P.rightY < p) (hrightRSmall : P.rightR < p) (hrightZSmall : P.rightZ < p)
    (hmixedYSmall : P.mixedCost.y < p) (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n) (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (hdegree : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ P.w)
    (hagreement : ∀ γ ∈ Gamma, P.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hno : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (foldSeeds F selected Gamma).card * P.gap ≤
      leftRegularNumerator P + P.gap * dot ⟨P.leftY, P.leftR, P.leftZ⟩ P.mixedCost := by
  classical
  letI : CharP (GenericField K) p := genericField_charP K p
  let phi := polynomialEmbedding K
  let Δ := foldSeeds F selected Gamma
  have hFne : F ≠ 0 := hF.ne_zero
  have hΔ : Δ ⊆ Gamma := foldSeeds_subset F selected Gamma
  have hΔdata : ∀ γ ∈ Δ, specialization K (selected γ) γ F = 0 ∧
      specialization K (selected γ) γ (dR 1 F) = 0 ∧
      specialization K (selected γ) γ (dR (chainLength F) F) ≠ 0 :=
    fun γ hγ => (Finset.mem_filter.mp hγ).2
  have hnotdvd : ¬ F ∣ dR 1 F :=
    irreducible_not_dvd_dR F hF p hpos hsmall 1 le_rfl (chainLength_pos F hpos)
  have hcover := card_le_sum_geometricSeeds K F hFne selected Δ (fun γ hγ => (hΔdata γ hγ).1)
  let rightCap : RCN051.DegreeVector := ⟨P.rightY, P.rightR, P.rightZ⟩
  let leftCap : RCN051.DegreeVector := ⟨P.leftY, P.leftR, P.leftZ⟩
  let capF : Fin 3 → ℕ := fun i =>
    (P.n - P.w) * capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) i +
      (P.a - P.w) * capAt ⟨P.leftY, P.leftR, P.leftZ⟩ i
  have hsingle (g : GeometricFactor K F) :
      (geometricSeeds K F selected Δ g).card * P.gap ≤
        (∑ i, capF i * coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i) +
          (P.errors + 1) * P.gap *
            coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) 2 := by
    have hgSpec := surfaceFactors_spec phi F g.1 g.2
    have hsub := geometricSeeds_subset K F selected Δ g
    have hproper : ¬ g.1 ∣ surfaceMap phi (dR 1 F) := by
      intro hgT
      apply hnotdvd
      have hpos' : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 := by omega
      have hgeo : g.1 ∣ geometricSurfaceMap K (GenericField K) F := by
        simpa only [canonical_geometricSurfaceMap] using hgSpec.2
      exact (geometric_factor_dvd_iff K (GenericField K) F (dR 1 F) hF hpos'
        g.1 hgSpec.1 hgeo).mp (by simpa only [canonical_geometricSurfaceMap] using hgT)
    have hgCaps : HasCaps g.1 rightCap := by
      intro i
      have hi := geometricFactor_degree_le K F hFne g i
      fin_cases i
      · exact hi.trans hY'
      · exact hi.trans hR'
      · exact hi.trans hZ'
    have hTCaps : HasCaps (surfaceMap phi (dR 1 F)) leftCap := by
      intro i
      fin_cases i
      · exact (surfaceMap_degreeOf_le phi (dR 1 F) 0).trans ((dR_degree_le 1 F 1).trans hY)
      · exact (surfaceMap_degreeOf_le phi (dR 1 F) 1).trans ((dR_R_degree_le 1 F).trans hR)
      · exact (surfaceMap_degreeOf_le phi (dR 1 F) 2).trans ((dR_degree_le 1 F 3).trans hZ)
    have hrightSmall : ∀ i, capAt rightCap i < p := by
      intro i
      fin_cases i
      · exact hrightYSmall
      · exact hrightRSmall
      · exact hrightZSmall
    have hgates := actual_characteristic_gates g.1 (surfaceMap phi (dR 1 F))
      rightCap leftCap p hgCaps hTCaps hrightSmall
      (by
        have h : RCN051.mixed rightCap leftCap RCN051.unitY = P.mixedCost.y := by
          simp only [rightCap, leftCap, RCN051.mixed, RCN051.unitY,
            UnequalParameters.mixedCost]
          ring
        rw [h]
        exact hmixedYSmall)
      (by
        have h : RCN051.mixed rightCap leftCap RCN051.unitR = P.mixedCost.r := by
          simp only [rightCap, leftCap, RCN051.mixed, RCN051.unitR,
            UnequalParameters.mixedCost]
          ring
        rw [h]
        exact hmixedRSmall)
      (by
        have h : RCN051.mixed rightCap leftCap RCN051.unitZ = P.mixedCost.z := by
          simp only [rightCap, leftCap, RCN051.mixed, RCN051.unitZ,
            UnequalParameters.mixedCost]
          ring
        rw [h]
        exact hmixedZSmall)
    have h := fold_factor_count K F g.1 hgSpec.1 hgSpec.2 hproper p hgates.1 hgates.2
      P.leftY P.leftR P.leftZ hleftR hY hR hZ selected (geometricSeeds K F selected Δ g)
      nodes x u₀ u₁ hinj P.w P.a P.errors hw hchar hwa (by rw [hnodes]; exact han)
      (fun γ hγ => hdegree γ (hΔ (hsub hγ)))
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => (hΔdata γ (hsub hγ)).2.1)
      (fun γ hγ => (hΔdata γ (hsub hγ)).2.2)
      (fun γ hγ => hagreement γ (hΔ (hsub hγ)))
      (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
        (fun _ hγ => hΔ (hsub hγ)) hno)
    rw [hnodes, Nat.one_mul] at h
    exact h
  let P' : UnequalParameters :=
    ⟨P.n, P.w, P.a, P.rightY, P.rightR, P.rightZ, P.leftY, P.leftR, P.leftZ⟩
  have hbudget (i : Fin 3) :
      (∑ g : GeometricFactor K F,
        coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i) ≤
        regularCapAt P.mixedCost i := by
    have h := sum_coordinateMixedDegree_geometricFactors_le P' F (dR 1 F) hFne
      ((dR_degree_le 1 F 1).trans hY) ((dR_R_degree_le 1 F).trans hR)
      ((dR_degree_le 1 F 3).trans hZ) i
    refine h.trans ?_
    have h1 := Nat.mul_le_mul_right P.leftZ hR'
    have h2 := Nat.mul_le_mul_right P.leftR hZ'
    have h3 := Nat.mul_le_mul_right P.leftZ hY'
    have h4 := Nat.mul_le_mul_right P.leftY hZ'
    have h5 := Nat.mul_le_mul_right P.leftR hY'
    have h6 := Nat.mul_le_mul_right P.leftY hR'
    fin_cases i <;>
      simp only [regularCapAt, regularVector, P', UnequalParameters.mixedCost,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      nlinarith
  have hfubini : (∑ g : GeometricFactor K F, ∑ i : Fin 3,
      capF i * coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i) =
      ∑ i : Fin 3, capF i * (∑ g : GeometricFactor K F,
        coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Δ.card * P.gap ≤ (∑ g : GeometricFactor K F,
        (geometricSeeds K F selected Δ g).card) * P.gap :=
      Nat.mul_le_mul_right P.gap hcover
    _ = ∑ g : GeometricFactor K F, (geometricSeeds K F selected Δ g).card * P.gap := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K F,
        ((∑ i, capF i * coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i) +
          (P.errors + 1) * P.gap *
            coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) 2) :=
      Finset.sum_le_sum fun g _ => hsingle g
    _ = (∑ i : Fin 3, capF i * (∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) i)) +
        (P.errors + 1) * P.gap * (∑ g : GeometricFactor K F,
          coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi (dR 1 F)) 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfubini]
    _ ≤ (∑ i : Fin 3, capF i * regularCapAt P.mixedCost i) +
        (P.errors + 1) * P.gap * regularCapAt P.mixedCost 2 :=
      Nat.add_le_add
        (Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hbudget i))
        (Nat.mul_le_mul_left _ (hbudget 2))
    _ = _ := by
      simp only [capF, Fin.sum_univ_three, capAt, regularCapAt, agreementCaps,
        leftRegularNumerator, UnequalParameters.leftAgreement, dot, UnequalParameters.gap,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring

end
end ProximityPrize.SubmissionLower.FoldChain6813



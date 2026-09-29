-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.cutrk_submodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:26:18.021324+00:00
-- url     : https://prove2.me/submissions/f2fae171-167e-46d2-a249-90948c5b51e6

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

open Module

set_option linter.unusedSectionVars false

section aux_cs

variable {K : Type*} [Field K]

/-- Rank–nullity for a subspace containing the kernel. -/
lemma aux_cs_finrank_map_add_ker {E F : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [AddCommGroup F] [Module K F]
    (f : E →ₗ[K] F) (U : Submodule K E) (hU : LinearMap.ker f ≤ U) :
    finrank K (U.map f) + finrank K (LinearMap.ker f) = finrank K U := by
  have h := (f ∘ₗ U.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  rw [← h, (Submodule.comapSubtypeEquivOfLe hU).finrank_eq]

lemma aux_cs_finrank_map_add_ker' {E F : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [AddCommGroup F] [Module K F]
    (f : E →ₗ[K] F) (W : Submodule K E) :
    finrank K (W.map f) + finrank K (LinearMap.ker f) = finrank K ↥(W ⊔ LinearMap.ker f) := by
  have h := aux_cs_finrank_map_add_ker f (W ⊔ LinearMap.ker f) le_sup_right
  have hm : (W ⊔ LinearMap.ker f).map f = W.map f := by
    rw [Submodule.map_sup, LinearMap.ker, Submodule.map_comap_eq, inf_bot_eq, sup_bot_eq]
  rw [hm] at h
  exact h

variable {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- restriction of a vector to the coordinates in `X` -/
noncomputable def aux_cs_P (X : Finset R) : (R → K) →ₗ[K] (X → K) :=
  LinearMap.funLeft K K (fun x : X => (x : R))

/-- span of the columns indexed by `Y` -/
noncomputable def aux_cs_W (M : Matrix R C K) (Y : Finset C) : Submodule K (R → K) :=
  Submodule.span K (M.col '' (Y : Set C))

/-- vectors vanishing on `X` -/
noncomputable def aux_cs_K (X : Finset R) : Submodule K (R → K) :=
  LinearMap.ker (aux_cs_P (K := K) X)

lemma aux_cs_mem_ker (X : Finset R) (v : R → K) :
    v ∈ aux_cs_K (K := K) X ↔ ∀ x ∈ X, v x = 0 := by
  rw [aux_cs_K, LinearMap.mem_ker]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa [aux_cs_P, LinearMap.funLeft] using this
  · intro h
    funext ⟨x, hx⟩
    simp [aux_cs_P, LinearMap.funLeft, h x hx]

lemma aux_cs_finrank_ker (X : Finset R) :
    (finrank K (LinearMap.ker (aux_cs_P (K := K) X)) : ℤ) = Fintype.card R - X.card := by
  have h := (aux_cs_P (K := K) X).finrank_range_add_finrank_ker
  have hs : LinearMap.range (aux_cs_P (K := K) X) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ _
      Subtype.val_injective)
  rw [hs, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at h
  omega

lemma aux_cs_rank_eq (M : Matrix R C K) (X : Finset R) (Y : Finset C) :
    ((M.submatrix (fun x : X => (x : R)) (fun y : Y => (y : C))).rank : ℤ) =
      finrank K ↥(aux_cs_W M Y ⊔ aux_cs_K (K := K) X) -
        (Fintype.card R - X.card) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hrange : Set.range (M.submatrix (fun x : X => (x : R)) (fun y : Y => (y : C))).col =
      (aux_cs_P (K := K) X) '' (M.col '' (Y : Set C)) := by
    ext v
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      refine ⟨M.col y, ⟨y, hy, rfl⟩, ?_⟩
      funext x
      simp [aux_cs_P, LinearMap.funLeft, Matrix.col]
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      funext x
      simp [aux_cs_P, LinearMap.funLeft, Matrix.col]
  rw [hrange, ← Submodule.map_span, ← aux_cs_finrank_ker (K := K) X]
  have := aux_cs_finrank_map_add_ker' (aux_cs_P (K := K) X) (aux_cs_W M Y)
  unfold aux_cs_W at this ⊢
  unfold aux_cs_K
  omega

lemma aux_cs_rank_submod (M : Matrix R C K) (X₁ X₂ : Finset R) (Y₁ Y₂ : Finset C) :
    ((M.submatrix (fun x : ↥(X₁ ∩ X₂) => (x : R)) (fun y : ↥(Y₁ ∪ Y₂) => (y : C))).rank : ℤ) +
      ((M.submatrix (fun x : ↥(X₁ ∪ X₂) => (x : R)) (fun y : ↥(Y₁ ∩ Y₂) => (y : C))).rank : ℤ) ≤
    ((M.submatrix (fun x : X₁ => (x : R)) (fun y : Y₁ => (y : C))).rank : ℤ) +
      ((M.submatrix (fun x : X₂ => (x : R)) (fun y : Y₂ => (y : C))).rank : ℤ) := by
  rw [aux_cs_rank_eq, aux_cs_rank_eq, aux_cs_rank_eq, aux_cs_rank_eq]
  have hK1 : aux_cs_K (K := K) (X₁ ∩ X₂) ≤ aux_cs_K (K := K) X₁ ⊔ aux_cs_K (K := K) X₂ := by
    intro v hv
    simp only [aux_cs_mem_ker] at hv
    rw [Submodule.mem_sup]
    refine ⟨fun i => if i ∈ X₁ then 0 else v i, ?_, fun i => if i ∈ X₁ then v i else 0, ?_, ?_⟩
    · simp only [aux_cs_mem_ker]
      intro x hx
      simp [hx]
    · simp only [aux_cs_mem_ker]
      intro x hx
      by_cases h1 : x ∈ X₁
      · simp [h1, hv x (Finset.mem_inter.mpr ⟨h1, hx⟩)]
      · simp [h1]
    · funext i
      by_cases h1 : i ∈ X₁ <;> simp [h1]
  have hKanti : ∀ X X' : Finset R, X ⊆ X' → aux_cs_K (K := K) X' ≤ aux_cs_K (K := K) X := by
    intro X X' hXX' v hv
    simp only [aux_cs_mem_ker] at hv ⊢
    intro x hx
    exact hv x (hXX' hx)
  have hWmono : ∀ Y Y' : Finset C, Y ⊆ Y' → aux_cs_W M Y ≤ aux_cs_W M Y' := by
    intro Y Y' h
    unfold aux_cs_W
    apply Submodule.span_mono
    apply Set.image_mono
    exact_mod_cast h
  have hW1 : aux_cs_W M (Y₁ ∪ Y₂) ≤ aux_cs_W M Y₁ ⊔ aux_cs_W M Y₂ := by
    unfold aux_cs_W
    rw [Finset.coe_union, Set.image_union, Submodule.span_union]
  set S₁ := aux_cs_W M Y₁ ⊔ aux_cs_K (K := K) X₁ with hS₁
  set S₂ := aux_cs_W M Y₂ ⊔ aux_cs_K (K := K) X₂ with hS₂
  have hT1 : aux_cs_W M (Y₁ ∪ Y₂) ⊔ aux_cs_K (K := K) (X₁ ∩ X₂) ≤ S₁ ⊔ S₂ := by
    apply sup_le
    · exact hW1.trans (sup_le_sup le_sup_left le_sup_left)
    · exact hK1.trans (sup_le_sup le_sup_right le_sup_right)
  have hT2 : aux_cs_W M (Y₁ ∩ Y₂) ⊔ aux_cs_K (K := K) (X₁ ∪ X₂) ≤ S₁ ⊓ S₂ := by
    apply sup_le
    · exact le_inf ((hWmono _ _ Finset.inter_subset_left).trans le_sup_left)
        ((hWmono _ _ Finset.inter_subset_right).trans le_sup_left)
    · exact le_inf ((hKanti _ _ Finset.subset_union_left).trans le_sup_right)
        ((hKanti _ _ Finset.subset_union_right).trans le_sup_right)
  have h1 := Submodule.finrank_mono hT1
  have h2 := Submodule.finrank_mono hT2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq S₁ S₂
  have h4 := Finset.card_union_add_card_inter X₁ X₂

  omega

end aux_cs

end ApproxCliqueWidth.Certificate

open ApproxCliqueWidth.Certificate

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ X₁ Y₁ X₂ Y₂ : Finset V, Disjoint X₁ Y₁ → Disjoint X₂ Y₂ →
        cutrkStar G (X₁ ∩ X₂) (Y₁ ∪ Y₂) + cutrkStar G (X₁ ∪ X₂) (Y₁ ∩ Y₂) ≤
          cutrkStar G X₁ Y₁ + cutrkStar G X₂ Y₂) ∧
    IsSubmodular (cutrk G) := by
  refine ⟨?_, ?_⟩
  · intro X₁ Y₁ X₂ Y₂ _ _
    exact aux_cs_rank_submod (G.adjMatrix (ZMod 2)) X₁ X₂ Y₁ Y₂
  · intro X Y
    unfold cutrk
    rw [Finset.compl_inter, Finset.compl_union]
    exact aux_cs_rank_submod (G.adjMatrix (ZMod 2)) X Y Xᶜ Yᶜ

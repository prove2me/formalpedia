-- Prove2me | Definitions.Def_OAIQWUCS002
-- name    : OAIQWUCS002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:55:21.160671+00:00
-- url     : https://prove2.me/theorems/b98ffa34-d246-4252-ab3d-37a540c56fff
-- title:
--   Product charts, holomorphic boxes and global projections (OpenAI universal-cover splitting)
-- statement:
--   The main definitions bundle of the split of OpenAI's proof of `OAI.UniversalCoverSplitting.main`: if a compact connected Kähler manifold $X$ of dimension $n \ge 2$ has a holomorphic splitting $TX = E_1 \oplus E_2$ into integrable subbundles of positive ranks, then its universal cover is biholomorphic to a product $Y_1 \times Y_2$ of connected, simply connected complex manifolds, and the biholomorphism carries the lifts of $E_1$ and $E_2$ to the tangent bundles of the factors. This is the two-summand form of Beauville's compatible splitting conjecture.
--
--   The bundle holds OpenAI's Lean definitions, structures and predicates from `lean/OAI/Geometry/KahlerSplitting` (OpenAI, *Universal-cover splitting for compact Kähler manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. Following the paper's Sections 2–6, among them:
--   - simultaneous product charts of the splitting (`SplittingChart`, `splittingAtlas`, `ProductChart`) and holomorphic boxes, the maps of two parameters whose first and second derivatives lie in $E_1$ and $E_2$ (`IsBox`, `IsMixedBox`, `IsBlockBox`, `IsHorizontalMap`, `IsVerticalMap`, `Polydisk`, `IsDiskTile`);
--   - metrics in charts, curve speed and area (`continuousMetricInChart`, `metricNorm`, `curveSpeed`, `curveArea`, `compactManifoldMetric`, `pullbackMetric`), used for the paper's area estimate (Section 4);
--   - Hartogs shells and their fillings (`complexAnnulus`, `MixedFillable`, `superPotential`, `superDomain`), for the paper's extension results (Sections 3 and 4);
--   - étale spaces of holomorphic germs (`Total`, `Germs`, `sectionOf`);
--   - global projections of the universal cover onto the leaves, and the charts built from them (`GlobalProjection`, `RetractChart`, `Fixed`, `fixedChart`, `CoverProductChart`), and the swap of the two summands (`HolomorphicSplitting.swap`).
--
--   Simultaneous product charts come from the holomorphic Frobenius theorem, applied to each summand. Here the lemma `holomorphic_frobenius` is a short bridge from the published standalone statement `OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem`, which the bundle imports. So that statement, and its proof, must be live before this bundle is published. The definitions of the published goal (`ComplexManifold`, `KahlerMetric`, `HolomorphicSplitting`, `Integrable`, `OrdinaryUniversalCover`, `CompatibleProduct` and the others) come from the published bundle `Def_KahlerSplitting`.
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Universal-cover splitting for compact Kähler manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/KahlerSplitting at commit adc7f12

import Mathlib
import Definitions.Def_KahlerSplitting
import Definitions.Def_OAIQWUCS001
import Theorems.Thm_OAI_UniversalCoverSplitting_holomorphic_frobenius_theorem

section
-- module Solutions.OAIQW_UniversalCover.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_UniversalCover.Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace RectangleGrid
variable {P Q X : Type*}

def band (k i j : ℕ) : Prop := i ≤ j+k ∧ j ≤ i+k

structure Band (T : Set (P × Q → X)) (D : ℕ → P × Q → X)
    (lo hi : ℕ → P) (bot top : ℕ → Q) (k : ℕ) where
  tile : ℕ → ℕ → P × Q → X
  member : ∀ i j, band k i j → tile i j ∈ T
  diagonal : ∀ i, tile i i=D i
  hseam : ∀ i j, band k i j → band k (i+1) j →
    ∀ y, tile i j (hi i,y)=tile (i+1) j (lo (i+1),y)
  vseam : ∀ i j, band k i j → band k i (j+1) →
    ∀ x, tile i j (x,top j)=tile i (j+1) (x,bot (j+1))

theorem band_extend (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (horizontal : ∀ f ∈ T, ∀ q, (fun p ↦ f (p,q)) ∈ H)
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (D : ℕ → P × Q → X) (lo hi : ℕ → P) (bot top : ℕ → Q)
    (join : ∀ i, D i (hi i,top i)=D (i+1) (lo (i+1),bot (i+1)))
    (k : ℕ) (G : Band T D lo hi bot top k) :
    ∃ F : Band T D lo hi bot top (k+1), ∀ i j, band k i j → F.tile i j=G.tile i j := by
  classical
  have up (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : i < j) :
      ∃ f ∈ T, (∀ x, f (x,bot j)=G.tile i (j-1) (x,top (j-1))) ∧
        (∀ y, f (hi i,y)=G.tile (i+1) j (lo (i+1),y)) := by
    have b₁ : band k i (j-1) := by unfold band at *; omega
    have b₂ : band k (i+1) j := by unfold band at *; omega
    apply fill _ (horizontal _ (G.member _ _ b₁) _) _ (vertical _ (G.member _ _ b₂) _)
    by_cases he : j=i+1
    · subst j
      simpa only [Nat.add_sub_cancel,G.diagonal] using join i
    · have b₃ : band k (i+1) (j-1) := by unfold band at *; omega
      have e₁ := G.hseam i (j-1) b₁ b₃ (top (j-1))
      have e₂ := G.vseam (i+1) (j-1) b₃ (by simpa only [Nat.sub_add_cancel (by omega : 1≤ j)] using b₂) (lo (i+1))
      exact e₁.trans (by simpa only [Nat.sub_add_cancel (by omega : 1≤ j)] using e₂)
  have down (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : j < i) :
      ∃ f ∈ T, (∀ x, f (x,top j)=G.tile i (j+1) (x,bot (j+1))) ∧
        (∀ y, f (lo i,y)=G.tile (i-1) j (hi (i-1),y)) := by
    have b₁ : band k i (j+1) := by unfold band at *; omega
    have b₂ : band k (i-1) j := by unfold band at *; omega
    apply fill _ (horizontal _ (G.member _ _ b₁) _) _ (vertical _ (G.member _ _ b₂) _)
    by_cases he : i=j+1
    · subst i
      simpa only [Nat.add_sub_cancel,G.diagonal] using (join j).symm
    · have b₃ : band k (i-1) (j+1) := by unfold band at *; omega
      have e₁ := G.hseam (i-1) (j+1) b₃ (by simpa only [Nat.sub_add_cancel (by omega : 1≤ i)] using b₁) (bot (j+1))
      have e₂ := G.vseam (i-1) j b₂ b₃ (hi (i-1))
      simp only [Nat.sub_add_cancel (by omega : 1≤ i)] at e₁
      exact e₁.symm.trans e₂.symm
  let f (i j : ℕ) : P × Q → X :=
    if h : band k i j then G.tile i j else
    if hb : band (k+1) i j then
      if hij : i < j then (up i j hb h hij).choose
      else (down i j hb h (by unfold band at *; omega)).choose
    else D 0
  have old (i j : ℕ) (h : band k i j) : f i j=G.tile i j := by simp only [f,dite_eq_left h]
  have upper (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : i < j) :
      f i j ∈ T ∧ (∀ x, f i j (x,bot j)=G.tile i (j-1) (x,top (j-1))) ∧
        (∀ y, f i j (hi i,y)=G.tile (i+1) j (lo (i+1),y)) := by
    simpa only [f,dite_eq_right hn,dite_eq_left h,dite_eq_left hij] using (up i j h hn hij).choose_spec
  have lower (i j : ℕ) (h : band (k+1) i j) (hn : ¬band k i j) (hij : j < i) :
      f i j ∈ T ∧ (∀ x, f i j (x,top j)=G.tile i (j+1) (x,bot (j+1))) ∧
        (∀ y, f i j (lo i,y)=G.tile (i-1) j (hi (i-1),y)) := by
    simpa only [f,dite_eq_right hn,dite_eq_left h,dite_eq_right (not_lt.mpr (Nat.le_of_lt hij))] using
      (down i j h hn hij).choose_spec
  refine ⟨⟨f,?_,?_,?_,?_⟩,old⟩
  · intro i j h
    by_cases ho : band k i j
    · rw [old i j ho]; exact G.member i j ho
    · by_cases hij : i < j
      · exact (upper i j h ho hij).1
      · exact (lower i j h ho (by unfold band at *; omega)).1
  · intro i
    rw [old i i (by unfold band; omega),G.diagonal]
  · intro i j ha hb y
    by_cases hA : band k i j
    · rw [old i j hA]
      by_cases hB : band k (i+1) j
      · rw [old (i+1) j hB]; exact G.hseam i j hA hB y
      · have e := (lower (i+1) j hb hB (by unfold band at *; omega)).2.2 y
        simpa only [Nat.add_sub_cancel] using e.symm
    · have hB : band k (i+1) j := by unfold band at *; omega
      rw [old (i+1) j hB]
      exact (upper i j ha hA (by unfold band at *; omega)).2.2 y
  · intro i j ha hb x
    by_cases hA : band k i j
    · rw [old i j hA]
      by_cases hB : band k i (j+1)
      · rw [old i (j+1) hB]; exact G.vseam i j hA hB x
      · have e := (upper i (j+1) hb hB (by unfold band at *; omega)).2.1 x
        simpa only [Nat.add_sub_cancel] using e.symm
    · have hB : band k i (j+1) := by unfold band at *; omega
      rw [old i (j+1) hB]
      exact (lower i j ha hA (by unfold band at *; omega)).2.1 x

theorem diagonal_grid (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (horizontal : ∀ f ∈ T, ∀ q, (fun p ↦ f (p,q)) ∈ H)
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (D : ℕ → P × Q → X) (hD : ∀ i, D i ∈ T)
    (lo hi : ℕ → P) (bot top : ℕ → Q)
    (join : ∀ i, D i (hi i,top i)=D (i+1) (lo (i+1),bot (i+1))) :
    ∃ f : ℕ → ℕ → P × Q → X, (∀ i j, f i j ∈ T) ∧
      (∀ i, f i i=D i) ∧
      (∀ i j y, f i j (hi i,y)=f (i+1) j (lo (i+1),y)) ∧
      (∀ i j x, f i j (x,top j)=f i (j+1) (x,bot (j+1))) := by
  classical
  let seed : Band T D lo hi bot top 0 :=
    ⟨fun i _ ↦ D i,fun i _ _ ↦ hD i,fun _ ↦ rfl,
      fun i j ha hb ↦ by unfold band at ha hb; omega,
      fun i j ha hb ↦ by unfold band at ha hb; omega⟩
  have ext := band_extend H V T horizontal vertical fill D lo hi bot top join
  let seq : (k : ℕ) → Band T D lo hi bot top k :=
    Nat.rec seed (fun k G ↦ (ext k G).choose)
  have stable (k i j : ℕ) (h : band k i j) :
      (seq (k+1)).tile i j=(seq k).tile i j := (ext k (seq k)).choose_spec i j h
  have stable' (k l : ℕ) (hkl : k≤ l) (i j : ℕ) (h : band k i j) :
      (seq l).tile i j=(seq k).tile i j := by
    induction l, hkl using Nat.le_induction with
    | base => rfl
    | succ l hkl ih =>
      exact (stable l i j (by unfold band at *; omega)).trans ih
  let f (i j : ℕ) := (seq (i+j)).tile i j
  have atBand (k i j : ℕ) (h : i+j≤ k) : f i j=(seq k).tile i j :=
    (stable' (i+j) k h i j (by unfold band; omega)).symm
  refine ⟨f,fun i j ↦ (seq (i+j)).member i j (by unfold band; omega),
    fun i ↦ (seq (i+i)).diagonal i,?_,?_⟩
  · intro i j y
    rw [atBand (i+j+1) i j (by omega),atBand (i+j+1) (i+1) j (by omega)]
    exact (seq (i+j+1)).hseam i j (by unfold band; omega) (by unfold band; omega) y
  · intro i j x
    rw [atBand (i+j+1) i j (by omega),atBand (i+j+1) i (j+1) (by omega)]
    exact (seq (i+j+1)).vseam i j (by unfold band; omega) (by unfold band; omega) x

end RectangleGrid
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace IntervalChain
variable {X : Type*}

def cell (t : ℕ → I) (i : ℕ) := Icc (t i) (t (i+1))

lemma overlap (t : ℕ → I) (ht : Monotone t)
    (f : ∀ i, cell t i → X)
    (seam : ∀ i, f i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩ =
      f (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩)
    (i j : ℕ) (x : I) (hi : x ∈ cell t i) (hj : x ∈ cell t j) :
    f i ⟨x,hi⟩=f j ⟨x,hj⟩ := by
  have half : ∀ j i, i ≤ j → ∀ (x : I) (hi : x ∈ cell t i) (hj : x ∈ cell t j),
      f i ⟨x,hi⟩=f j ⟨x,hj⟩ := by
    intro j
    induction j with
    | zero => intro i hij x hi hj; have he : i=0 := Nat.eq_zero_of_le_zero hij; subst i; rfl
    | succ j ih =>
      intro i hij x hi hj
      by_cases he : i=j+1
      · subst i; rfl
      have hij' : i ≤ j := by omega
      have hx : x=t (j+1) := le_antisymm (hi.2.trans (ht (by omega))) hj.1
      subst x
      exact (ih i hij' _ hi ⟨ht (Nat.le_succ j),le_rfl⟩).trans (seam j)
  rcases le_total i j with h|h
  · exact half j i h x hi hj
  · exact (half i j h x hj hi).symm

lemma covers (t : ℕ → I) (ht0 : t 0=0) (ht : Monotone t)
    (N : ℕ) (hN : t N=1) (x : I) : ∃ i ≤ N, x ∈ cell t i := by
  by_cases hx : x=1
  · subst x
    refine ⟨N,le_rfl,?_,?_⟩
    · simp only [hN,le_refl]
    · exact (hN ▸ ht (Nat.le_succ N))
  have hx1 : x < 1 := lt_of_le_of_ne le_top hx
  have hm : ∃ i, x < t (i+1) := ⟨N,lt_of_lt_of_le hx1 (hN ▸ ht (Nat.le_succ N))⟩
  let i := Nat.find hm
  have hiN : i ≤ N := Nat.find_min' hm (lt_of_lt_of_le hx1 (hN ▸ ht (Nat.le_succ N)))
  refine ⟨i,hiN,?_,(Nat.find_spec hm).le⟩
  cases hi : i with
  | zero => simp [ht0]
  | succ j =>
    have hn := Nat.find_min hm (show j < i from by omega)
    exact le_of_not_gt (by simpa only [hi] using hn)

end IntervalChain
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace PathSubdivision
variable {P X : Type*} [TopologicalSpace P]

theorem parameterize (α : I → X) (Q : (P → X) → Prop)
    (local_param : ∀ x : I, ∃ U : Set I, IsOpen U ∧ x ∈ U ∧
      ∃ f : P → X, Q f ∧ ∃ a : U → P, Continuous a ∧ ∀ y, f (a y)=α y) :
    ∃ t : ℕ → I, t 0=0 ∧ Monotone t ∧ (∃ N, ∀ m ≥ N, t m=1) ∧
      ∃ f : ℕ → P → X, (∀ i, Q (f i)) ∧
      ∃ a : ∀ i, IntervalChain.cell t i → P, (∀ i, Continuous (a i)) ∧
        ∀ i y, f i (a i y)=α y := by
  classical
  choose U hU hx f hf a ha he using local_param
  have cover : univ ⊆ ⋃ x, U x := fun x _ ↦ mem_iUnion.mpr ⟨x,hx x⟩
  obtain ⟨t,ht0,ht,hN,hsub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval hU cover
  choose k hk using hsub
  refine ⟨t,ht0,ht,hN,fun i ↦ f (k i),fun i ↦ hf (k i),
    fun i y ↦ a (k i) ⟨y,hk i y.property⟩,?_,?_⟩
  · intro i
    exact (ha (k i)).comp (continuous_subtype_val.subtype_mk _)
  · intro i y
    exact he (k i) _

end PathSubdivision
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Boxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Manifold ContDiff
open Set
namespace UniversalCoverSplitting
open scoped Manifold ContDiff
open Set

def IsBox {n r₁ r₂ : ℕ} {X : ComplexManifold n}
    (S : HolomorphicSplitting X r₁ r₂) (U : Set (ℂ × ℂ))
    (f : ℂ × ℂ → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U ∧
  ∀ z ∈ U,
    S.projection (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1, 0)) =
      mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1, 0) ∧
    S.projection (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (0, 1)) = 0

end UniversalCoverSplitting

noncomputable section
open Set Topology Filter Metric
namespace UniversalCoverSplitting
section CompactQuadratic
variable {B E : Type*} [TopologicalSpace B] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_quadratic_operator_bound {K : Set B} (hK : IsCompact K)
    (Q : B → E → ℝ) (P : B → E →L[ℝ] E)
    (hQ : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) (K ×ˢ univ))
    (hP : ContinuousOn P K)
    (hpos : ∀ x ∈ K, ∀ u, u ≠ 0 → 0 < Q x u)
    (hhom : ∀ x ∈ K, ∀ (r : ℝ) u, Q x (r • u) = r ^ 2 * Q x u) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ u, Q x (P x u) ≤ C * Q x u := by
  let L : Set (B × E) := K ×ˢ sphere 0 1
  have hL : IsCompact L := hK.prod (isCompact_sphere 0 1)
  have hQL : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) L :=
    hQ.mono (prod_mono_right (subset_univ _))
  have hnum : ContinuousOn (fun p : B × E ↦ Q p.1 (P p.1 p.2)) L := by
    apply hQ.comp
      (continuousOn_fst.prodMk ((hP.comp continuousOn_fst (fun _ h ↦ h.1)).clm_apply
        continuousOn_snd))
    exact fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have hden : ∀ p ∈ L, Q p.1 p.2 ≠ 0 := by
    intro p hp
    apply ne_of_gt (hpos p.1 hp.1 p.2 _)
    intro he
    have hn : ‖p.2‖ = (1:ℝ) := by simpa using hp.2
    simp [he] at hn
  obtain ⟨C,hC⟩ := hL.bddAbove_image (hnum.div hQL hden)
  refine ⟨max C 1, by positivity, fun x hx u ↦ ?_⟩
  have hzero : Q x 0 = 0 := by simpa using hhom x hx 0 (0:E)
  by_cases hu : u = 0
  · simp [hu,hzero]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let v := ‖u‖⁻¹ • u
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hv : v ∈ sphere (0:E) 1 := by simpa using hvnorm
  have hb : Q x (P x v) / Q x v ≤ max C 1 :=
    (hC ⟨(x,v),⟨hx,hv⟩,rfl⟩).trans (le_max_left _ _)
  have hvpos : 0 < Q x v := hpos x hx v (by intro hh; simp [hh] at hvnorm)
  have hquad : Q x (P x v) ≤ max C 1 * Q x v := (div_le_iff₀ hvpos).mp hb
  have huv : ‖u‖ • v = u := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  calc
    Q x (P x u) = ‖u‖ ^ 2 * Q x (P x v) := by
      conv_lhs => rw [← huv, map_smul]
      exact hhom x hx ‖u‖ (P x v)
    _ ≤ ‖u‖ ^ 2 * (max C 1 * Q x v) := mul_le_mul_of_nonneg_left hquad (sq_nonneg _)
    _ = max C 1 * Q x u := by
      have hs : Q x u = ‖u‖ ^ 2 * Q x v := by rw [← hhom x hx ‖u‖ v, huv]
      rw [hs]
      ring

end CompactQuadratic
end UniversalCoverSplitting
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.MetricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Manifold ContDiff
open Set
noncomputable section
open Set Topology Filter Metric

namespace UniversalCoverSplitting
section MetricCharts
variable {n : ℕ} {X : ComplexManifold n}

def continuousMetricInChart (g : RealMetricField X) (c : X.Carrier) (z : Model n) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  let e := extChartAt (model n) c
  let q := (mfderiv (model n) (model n) e.symm z).restrictScalars ℝ
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((g (e.symm z)).compl₁₂ q.toLinearMap q.toLinearMap))

@[simp] theorem continuousMetricInChart_apply (g : RealMetricField X) (c : X.Carrier)
    (z u v : Model n) : continuousMetricInChart g c z u v = metricInChart g c z u v := rfl

theorem KahlerMetric.continuous_metricInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContinuousOn (continuousMetricInChart g.metric c) (extChartAt (model n) c).target := by
  apply continuousOn_clm_apply.mpr
  intro u
  apply continuousOn_clm_apply.mpr
  intro v
  exact (g.smooth c u v).continuousOn

theorem KahlerMetric.continuous_quadraticInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContinuousOn (fun p : Model n × Model n ↦ metricInChart g.metric c p.1 p.2 p.2)
      ((extChartAt (model n) c).target ×ˢ univ) := by
  exact ((g.continuous_metricInChart c).comp continuousOn_fst (fun _ hp ↦ hp.1)).clm_apply
    continuousOn_snd |>.clm_apply continuousOn_snd

theorem metricInChart_smul (g : RealMetricField X) (c : X.Carrier)
    (z u : Model n) (r : ℝ) :
    metricInChart g c z (r • u) (r • u) = r ^ 2 * metricInChart g c z u u := by
  change continuousMetricInChart g c z (r • u) (r • u) =
    r ^ 2 * continuousMetricInChart g c z u u
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem chart_inverse_derivative_injective (c : X.Carrier) {z : Model n}
    (hz : z ∈ (extChartAt (model n) c).target) :
    Function.Injective (mfderiv (model n) (model n) (extChartAt (model n) c).symm z) := by
  let e := extChartAt (model n) c
  have hsource : e.symm z ∈ e.source := e.map_target hz
  have heq := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hsource
  change (mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderivWithin (model n) (model n) e.symm (Set.range (model n)) (e (e.symm z))) =
      ContinuousLinearMap.id ℂ (Model n) at heq
  have heq' : (mfderiv (model n) (model n) e (e.symm z)).comp
      (mfderiv (model n) (model n) e.symm z) = ContinuousLinearMap.id ℂ _ := by
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at heq
    erw [e.right_inv hz] at heq
    exact heq
  intro u v huv
  have hv := congrArg (mfderiv (model n) (model n) e (e.symm z)) huv
  change ((mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderiv (model n) (model n) e.symm z)) u =
    ((mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderiv (model n) (model n) e.symm z)) v at hv
  rw [heq'] at hv
  exact hv

theorem KahlerMetric.positive_quadraticInChart (g : KahlerMetric X) (c : X.Carrier)
    {z u : Model n} (hz : z ∈ (extChartAt (model n) c).target) (hu : u ≠ 0) :
    0 < metricInChart g.metric c z u u := by
  apply g.positive
  intro hzero
  apply hu
  exact chart_inverse_derivative_injective c hz (hzero.trans (map_zero _).symm)

theorem metricInChart_forward (g : RealMetricField X) (c : X.Carrier)
    {x : X.Carrier} (hx : x ∈ (extChartAt (model n) c).source) (u v : Tangent X x) :
    metricInChart g c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) v) = g x u v := by
  let e := extChartAt (model n) c
  let p := mfderiv (model n) (model n) e x
  let q := mfderiv (model n) (model n) e.symm (e x)
  have hi : q.comp p = ContinuousLinearMap.id ℂ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
  have hu : q (p u) = u := congrArg (fun L : Tangent X x →L[ℂ] Tangent X x ↦ L u) hi
  have hv : q (p v) = v := congrArg (fun L : Tangent X x →L[ℂ] Tangent X x ↦ L v) hi
  change g (e.symm (e x)) (q (p u)) (q (p v)) = g x u v
  rw [e.left_inv hx]
  change g x (q (p u)) (q (p v)) = g x u v
  rw [hu,hv]

theorem projectionInChart_forward (P : ProjectionField X) (c : X.Carrier)
    {x : X.Carrier} (hx : x ∈ (extChartAt (model n) c).source) (u : Tangent X x) :
    projectionInChart P c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u) =
    (mfderiv (model n) (model n) (extChartAt (model n) c) x) (P x u) := by
  let e := extChartAt (model n) c
  let p := mfderiv (model n) (model n) e x
  let q := mfderiv (model n) (model n) e.symm (e x)
  have hi : q.comp p = ContinuousLinearMap.id ℂ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
  have hu : q (p u) = u := congrArg (fun L : Tangent X x →L[ℂ] Tangent X x ↦ L u) hi
  change (mfderiv (model n) (model n) e (e.symm (e x))) (P (e.symm (e x))
    (q (p u))) = p (P x u)
  rw [e.left_inv hx]
  change p (P x (q (p u))) = p (P x u)
  rw [hu]

theorem KahlerMetric.nonnegative (g : KahlerMetric X) (x : X.Carrier) (u : Tangent X x) :
    0 ≤ g.metric x u u := by
  by_cases hu : u = 0
  · simp [hu]
  · exact (g.positive x u hu).le

def metricNorm (g : KahlerMetric X) (x : X.Carrier) (u : Tangent X x) : ℝ :=
  Real.sqrt (g.metric x u u)

@[instance_reducible]
def KahlerMetric.realInnerCore (g : KahlerMetric X) (x : X.Carrier) :
    PreInnerProductSpace.Core ℝ (Tangent X x) where
  inner u v := g.metric x u v
  conj_inner_symm u v := by simpa using g.symmetric x v u
  re_inner_nonneg u := g.nonnegative x u
  add_left u v w := by simp only [map_add, LinearMap.add_apply]
  smul_left u v r := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, conj_trivial]

theorem metricNorm_add_le (g : KahlerMetric X) (x : X.Carrier) (u v : Tangent X x) :
    metricNorm g x (u + v) ≤ metricNorm g x u + metricNorm g x v := by
  let := g.realInnerCore x
  let := InnerProductSpace.Core.toNorm (𝕜 := ℝ) (F := Tangent X x)
  exact (InnerProductSpace.Core.toSeminormedSpaceCore (g.realInnerCore x)).norm_triangle u v

theorem KahlerMetric.orthogonal_I (g : KahlerMetric X) (x : X.Carrier) (u : Tangent X x) :
    g.metric x (Complex.I • u) u = 0 := by
  have hh := g.hermitian x (Complex.I • u) u
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, LinearMap.neg_apply] at hh
  rw [g.symmetric x u (Complex.I • u)] at hh
  linarith

theorem KahlerMetric.quadratic_complex_smul (g : KahlerMetric X) (x : X.Carrier)
    (u : Tangent X x) (z : ℂ) :
    g.metric x (z • u) (z • u) = ‖z‖ ^ 2 * g.metric x u u := by
  have hzu : z • u = z.re • u + z.im • (Complex.I • u) := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
  have hui : g.metric x u (Complex.I • u) = 0 := by
    rw [g.symmetric x u (Complex.I • u)]
    exact g.orthogonal_I x u
  rw [hzu]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hui,g.orthogonal_I x u,g.hermitian x u u,Complex.sq_norm,Complex.normSq_apply]
  ring

theorem metricNorm_complex_smul (g : KahlerMetric X) (x : X.Carrier)
    (u : Tangent X x) (z : ℂ) :
    metricNorm g x (z • u) = ‖z‖ * metricNorm g x u := by
  dsimp [metricNorm]
  rw [g.quadratic_complex_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end MetricCharts
end UniversalCoverSplitting
namespace UniversalCoverSplitting
section ComplementProjection
universe u
variable {n r₁ r₂ : ℕ}
variable {X : ComplexManifold.{u} n}

theorem projectionInChart_sub_id (P : ProjectionField X) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) :
    projectionInChart (fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x) - P x) c z =
      ContinuousLinearMap.id ℂ (Model n) - projectionInChart P c z := by
  let e := extChartAt (model n) c
  have heq := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (e.map_target hz)
  change (mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderivWithin (model n) (model n) e.symm (Set.range (model n)) (e (e.symm z))) =
      ContinuousLinearMap.id ℂ (Model n) at heq
  have heq' : (mfderiv (model n) (model n) e (e.symm z)).comp
      (mfderiv (model n) (model n) e.symm z) = ContinuousLinearMap.id ℂ _ := by
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at heq
    erw [e.right_inv hz] at heq
    exact heq
  ext u : 1
  change (mfderiv (model n) (model n) e (e.symm z))
    (((ContinuousLinearMap.id ℂ (Tangent X (e.symm z)) - P (e.symm z)))
      ((mfderiv (model n) (model n) e.symm z) u)) = _
  simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub]
  have hh := congrArg (fun L : Model n →L[ℂ] Model n ↦ L u) heq'
  change (mfderiv (model n) (model n) e (e.symm z))
    ((mfderiv (model n) (model n) e.symm z) u) = u at hh
  rw [hh]
  rfl

theorem HolomorphicProjection.complement {P : ProjectionField X}
    (hP : HolomorphicProjection P) :
    HolomorphicProjection (fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x) - P x) := by
  intro c
  apply ((differentiableOn_const (c := ContinuousLinearMap.id ℂ (Model n))).sub (hP c)).congr
  intro z hz
  exact projectionInChart_sub_id P c hz

theorem HolomorphicSplitting.complement_holomorphic (S : HolomorphicSplitting X r₁ r₂) :
    HolomorphicProjection (complementaryProjection S) := S.holomorphic.complement

theorem mixed_direction_metric_norm_le (g : KahlerMetric X) (x : X.Carrier)
    (P : Tangent X x →L[ℂ] Tangent X x) (D : (ℂ × ℂ) →L[ℂ] Tangent X x)
    (h₁ : P (D (1, 0)) = D (1, 0)) (h₂ : P (D (0, 1)) = 0)
    (C₁ C₂ : ℝ)
    (hC₁ : ∀ u, metricNorm g x (P u) ≤ C₁ * metricNorm g x u)
    (hC₂ : ∀ u, metricNorm g x ((ContinuousLinearMap.id ℂ (Tangent X x) - P) u) ≤
      C₂ * metricNorm g x u)
    (a₁ a₂ b₁ b₂ : ℂ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    metricNorm g x (D (a₁, a₂)) ≤
      (‖a₁/b₁‖ * C₁ + ‖a₂/b₂‖ * C₂) * metricNorm g x (D (b₁,b₂)) := by
  have split (c₁ c₂ : ℂ) : D (c₁, c₂) = c₁ • D (1, 0) + c₂ • D (0, 1) := by
    calc
      D (c₁, c₂) = D (c₁ • (1, 0) + c₂ • (0, 1)) := by congr 1; ext <;> simp
      _ = c₁ • D (1, 0) + c₂ • D (0, 1) := by rw [map_add, map_smul, map_smul]
  have hid : D (a₁,a₂) = (a₁/b₁) • P (D (b₁,b₂)) +
      (a₂/b₂) • ((ContinuousLinearMap.id ℂ (Tangent X x) - P) (D (b₁,b₂))) := by
    rw [split a₁ a₂, split b₁ b₂]
    simp only [map_add, map_smul, h₁, h₂, smul_zero, add_zero,
      sub_apply, ContinuousLinearMap.id_apply]
    simp only [sub_self, sub_zero, smul_zero, zero_add, smul_smul,
      div_mul_cancel₀ _ hb₁, div_mul_cancel₀ _ hb₂]
  rw [hid]
  calc
    _ ≤ metricNorm g x ((a₁/b₁) • P (D (b₁,b₂))) +
        metricNorm g x ((a₂/b₂) • ((ContinuousLinearMap.id ℂ (Tangent X x) - P) (D (b₁,b₂)))) :=
      metricNorm_add_le g x _ _
    _ = ‖a₁/b₁‖ * metricNorm g x (P (D (b₁,b₂))) +
        ‖a₂/b₂‖ * metricNorm g x ((ContinuousLinearMap.id ℂ (Tangent X x) - P) (D (b₁,b₂))) := by
      rw [metricNorm_complex_smul, metricNorm_complex_smul]
    _ ≤ ‖a₁/b₁‖ * (C₁ * metricNorm g x (D (b₁,b₂))) +
        ‖a₂/b₂‖ * (C₂ * metricNorm g x (D (b₁,b₂))) :=
      add_le_add (mul_le_mul_of_nonneg_left (hC₁ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hC₂ _) (norm_nonneg _))
    _ = _ := by ring

end ComplementProjection
end UniversalCoverSplitting

noncomputable section
open Set Metric

namespace UniversalCoverSplitting
open Filter Topology Metric MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

def curveSpeed (g : KahlerMetric X) (f : ℂ → X.Carrier) (z : ℂ) : ℝ :=
  metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ) (model n) f z (1 : ℂ))

def curveArea (g : KahlerMetric X) (f : ℂ → X.Carrier) (U : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (curveSpeed g f z ^ 2)

end UniversalCoverSplitting
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.SmallArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set Metric Filter Topology
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

noncomputable abbrev compactManifoldMetric (X : ComplexManifold n)
    [CompactSpace X.Carrier] : MetricSpace X.Carrier := by
  letI : TopologicalSpace.MetrizableSpace X.Carrier :=
    Manifold.metrizableSpace 𝓘(ℝ, Model n) X.Carrier
  exact TopologicalSpace.metrizableSpaceMetric X.Carrier

local instance instMetricSpaceCarrierOfCompactSpace [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

end UniversalCoverSplitting

open Set Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.CompactCurves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance instMetricSpaceCarrierOfCompactSpace_1 [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance instMetricSpaceCarrierOfCompactSpace_2 [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance instMetricSpaceCarrierOfCompactSpace_3 [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open Complex

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PathDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

theorem chart_mfderiv_inverses (c : X.Carrier) {z : Model n}
    (hz : z ∈ (extChartAt (model n) c).target) :
    (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)).comp
      (mfderiv (model n) (model n) (extChartAt (model n) c).symm z) =
      ContinuousLinearMap.id ℂ (Model n) ∧
    (mfderiv (model n) (model n) (extChartAt (model n) c).symm z).comp
      (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)) =
      ContinuousLinearMap.id ℂ (Model n) := by
  constructor
  · have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz
    change (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)).comp
      (mfderivWithin (model n) (model n) (extChartAt (model n) c).symm (range (model n)) z) =
      ContinuousLinearMap.id ℂ (Model n) at h
    simpa only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] using h
  · have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz
    change (mfderivWithin (model n) (model n) (extChartAt (model n) c).symm (range (model n)) z).comp
      (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)) =
      ContinuousLinearMap.id ℂ (Model n) at h
    simpa only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] using h

lemma projectionInChart_self (P : ProjectionField X) (c : X.Carrier) :
    projectionInChart P c (extChartAt (model n) c c) = P c := by
  let e := extChartAt (model n) c
  let A : X.Carrier → Model n →L[ℂ] Model n := fun x ↦ mfderiv (model n) (model n) e x
  let B : Model n → Model n →L[ℂ] Model n := fun z ↦ mfderiv (model n) (model n) e.symm z
  let T : X.Carrier → Model n →L[ℂ] Model n := fun x ↦ P x
  have hA : A c = ContinuousLinearMap.id ℂ (Model n) := mfderiv_extChartAt_self
  have hB : B (e c) = ContinuousLinearMap.id ℂ (Model n) := by
    have h := mfderivWithin_range_extChartAt_symm (I := model n) (x := c)
    change (mfderivWithin (model n) (model n) e.symm (range (model n)) (e c) :
      Model n →L[ℂ] Model n) = ContinuousLinearMap.id ℂ (Model n) at h
    simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
    exact h
  change (A (e.symm (e c))).comp ((T (e.symm (e c))).comp (B (e c))) = T c
  rw [e.left_inv (mem_extChartAt_source c),hA,hB]
  simp

lemma projectionInChart_idempotent (S : HolomorphicSplitting X r s) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) (v : Model n) :
    projectionInChart S.projection c z (projectionInChart S.projection c z v) =
      projectionInChart S.projection c z v := by
  let e := extChartAt (model n) c
  let a : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e (e.symm z)
  let b : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e.symm z
  have hba : b.comp a = ContinuousLinearMap.id ℂ (Model n) := (chart_mfderiv_inverses c hz).2
  have hba' (u : Model n) : b (a u) = u := congrArg (fun L : Model n →L[ℂ] Model n ↦ L u) hba
  let T : Model n →L[ℂ] Model n := S.projection (e.symm z)
  have hT (u : Model n) : T (T u) = T u := S.idempotent (e.symm z) u
  change a (T (b (a (T (b v))))) = a (T (b v))
  rw [hba',hT]

lemma projectionInChart_complement (P : ProjectionField X) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) :
    projectionInChart (fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x)-P x) c z =
      ContinuousLinearMap.id ℂ (Model n)-projectionInChart P c z := by
  let e := extChartAt (model n) c
  let a : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e (e.symm z)
  let b : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e.symm z
  have hab : a.comp b = ContinuousLinearMap.id ℂ (Model n) := (chart_mfderiv_inverses c hz).1
  have hab' (u : Model n) : a (b u) = u := congrArg (fun L : Model n →L[ℂ] Model n ↦ L u) hab
  let T : Model n →L[ℂ] Model n := P (e.symm z)
  apply ContinuousLinearMap.ext
  intro v
  change a (b v-T (b v)) = v-a (T (b v))
  rw [map_sub,hab']

end UniversalCoverSplitting

open Set Metric Filter Topology Asymptotics

open Set Metric Filter Topology Asymptotics

open Set Metric Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ProductCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open Set Metric Filter Topology
open scoped ContDiff
open Set
open Set Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem holomorphic_frobenius {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt : ∀ O : Set E, IsOpen O → O ⊆ U → InvolutiveProjectionOn P O)
    {p : E} (hp : p ∈ U) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range (P p).toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker (P p).toLinearMap) = s) :
    ∃ e : OpenPartialHomeomorph ((Fin r → ℂ) × (Fin s → ℂ)) E,
      (0 : (Fin r → ℂ) × (Fin s → ℂ)) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.target, ∀ v, P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 :=
  holomorphic_frobenius_theorem hU P hP hid hInt hp hr hs

end UniversalCoverSplitting

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma projection_complement_idempotent (P : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) (v : E) :
    (ContinuousLinearMap.id ℂ E-P) ((ContinuousLinearMap.id ℂ E-P) v) =
      (ContinuousLinearMap.id ℂ E-P) v := by
  simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,hP,sub_self,sub_zero]

lemma projection_complement_range (P : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) :
    LinearMap.range (ContinuousLinearMap.id ℂ E-P).toLinearMap = LinearMap.ker P.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change P (w-P w) = 0
    rw [map_sub,hP,sub_self]
  · intro hv
    refine ⟨v,?_⟩
    change v-P v = v
    rw [show P v = 0 from hv,sub_zero]

lemma projection_complement_ker (P : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) :
    LinearMap.ker (ContinuousLinearMap.id ℂ E-P).toLinearMap = LinearMap.range P.toLinearMap := by
  ext v
  constructor
  · intro hv
    refine ⟨v,?_⟩
    exact (sub_eq_zero.mp (show v-P v = 0 from hv)).symm
  · rintro ⟨w,rfl⟩
    change P w-P (P w) = 0
    rw [hP,sub_self]

lemma complement_fixed_iff_zero (P : E →L[ℂ] E) (v : E) :
    (ContinuousLinearMap.id ℂ E-P) v = v ↔ P v = 0 := by
  change v-P v = v ↔ P v = 0
  exact sub_eq_self

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E R S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]

theorem combine_foliation_charts (P : E → E →L[ℂ] E)
    (e₁ : OpenPartialHomeomorph (R × S) E) (e₂ : OpenPartialHomeomorph (S × R) E)
    (h₁ : ContDiffOn ℂ 1 e₁.symm e₁.target) (h₂ : ContDiffOn ℂ 1 e₂.symm e₂.target)
    (hk₁ : ∀ y ∈ e₁.target, ∀ v, P y v = v ↔ (fderiv ℂ e₁.symm y v).2 = 0)
    (hk₂ : ∀ y ∈ e₂.target, ∀ v, P y v = 0 ↔ (fderiv ℂ e₂.symm y v).2 = 0)
    {p : E} (hp₁ : p ∈ e₁.target) (hp₂ : p ∈ e₂.target)
    (h0₁ : e₁.symm p = 0) (h0₂ : e₂.symm p = 0)
    (L : (R × S) ≃L[ℂ] E) :
    ∃ e : OpenPartialHomeomorph E (R × S), p ∈ e.source ∧ e p = 0 ∧
      e.source ⊆ e₁.target ∩ e₂.target ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.source, ∀ v,
        (P y v = v ↔ (fderiv ℂ e y v).2 = 0) ∧
        (P y v = 0 ↔ (fderiv ℂ e y v).1 = 0) := by
  let U := e₁.target ∩ e₂.target
  have hU : IsOpen U := e₁.open_target.inter e₂.open_target
  let f : E → R × S := fun y ↦ ((e₂.symm y).2,(e₁.symm y).2)
  have hf : ContDiffOn ℂ 1 f U :=
    ((contDiff_snd.comp_contDiffOn h₂).mono inter_subset_right).prodMk
      ((contDiff_snd.comp_contDiffOn h₁).mono inter_subset_left)
  let D : E → E →L[ℂ] (R × S) := fun y ↦
    ((ContinuousLinearMap.snd ℂ S R).comp (fderiv ℂ e₂.symm y)).prod
      ((ContinuousLinearMap.snd ℂ R S).comp (fderiv ℂ e₁.symm y))
  have hd (y : E) (hy : y ∈ U) : HasFDerivAt f (D y) y := by
    exact ((h₂.contDiffAt (e₂.open_target.mem_nhds hy.2)).differentiableAt
      (by norm_num)).hasFDerivAt.snd.prodMk
      (((h₁.contDiffAt (e₁.open_target.mem_nhds hy.1)).differentiableAt
      (by norm_num)).hasFDerivAt.snd)
  have hDin : Function.Injective (D p) := by
    intro v w hvw
    have hv : D p (v-w) = 0 := by rw [map_sub,hvw,sub_self]
    have ha : P p (v-w) = 0 := (hk₂ p hp₂ (v-w)).mpr (congrArg Prod.fst hv)
    have hb : P p (v-w) = v-w := (hk₁ p hp₁ (v-w)).mpr (congrArg Prod.snd hv)
    exact sub_eq_zero.mp (hb.symm.trans ha)
  let A := ((D p).toLinearMap.linearEquivOfInjective hDin L.symm.toLinearEquiv.finrank_eq).toContinuousLinearEquiv
  obtain ⟨e,he,hep,heU,hee,hei⟩ := exists_holomorphic_ift_chart hU hf ⟨hp₁,hp₂⟩ A
    (hd p ⟨hp₁,hp₂⟩)
  refine ⟨e,hep,?_,heU,hee,hei,?_⟩
  · rw [he]
    simp [f,h0₁,h0₂]
  · intro y hy v
    rw [he,(hd y (heU hy)).fderiv]
    exact ⟨hk₁ y (heU hy).1 v,hk₂ y (heU hy).2 v⟩

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem holomorphic_product_coordinates {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt₁ : ∀ O : Set E, IsOpen O → O ⊆ U → InvolutiveProjectionOn P O)
    (hInt₂ : ∀ O : Set E, IsOpen O → O ⊆ U →
      InvolutiveProjectionOn (fun x ↦ ContinuousLinearMap.id ℂ E-P x) O)
    {p : E} (hp : p ∈ U) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range (P p).toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker (P p).toLinearMap) = s) :
    ∃ e : OpenPartialHomeomorph E ((Fin r → ℂ) × (Fin s → ℂ)),
      p ∈ e.source ∧ e p = 0 ∧ e.source ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.source, ∀ v,
        (P y v = v ↔ (fderiv ℂ e y v).2 = 0) ∧
        (P y v = 0 ↔ (fderiv ℂ e y v).1 = 0) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨e₁,h0₁,he₁,hU₁,_,hi₁,hk₁⟩ := holomorphic_frobenius hU P hP hid hInt₁ hp hr hs
  let Q := fun x ↦ ContinuousLinearMap.id ℂ E-P x
  have hQ : DifferentiableOn ℂ Q U := (differentiableOn_const (c := ContinuousLinearMap.id ℂ E)).sub hP
  have hidQ (x : E) (hx : x ∈ U) (v : E) : Q x (Q x v) = Q x v :=
    projection_complement_idempotent (P x) (hid x hx) v
  have hrQ : Module.finrank ℂ (LinearMap.range (Q p).toLinearMap) = s := by
    rw [projection_complement_range (P p) (hid p hp)]
    exact hs
  have hsQ : Module.finrank ℂ (LinearMap.ker (Q p).toLinearMap) = r := by
    rw [projection_complement_ker (P p) (hid p hp)]
    exact hr
  obtain ⟨e₂,h0₂,he₂,_,_,hi₂,hk₂⟩ := holomorphic_frobenius hU Q hQ hidQ hInt₂ hp hrQ hsQ
  have hp₁ : p ∈ e₁.target := he₁ ▸ e₁.map_source h0₁
  have hp₂ : p ∈ e₂.target := he₂ ▸ e₂.map_source h0₂
  have hi0₁ : e₁.symm p = 0 := by rw [← he₁,e₁.left_inv h0₁]
  have hi0₂ : e₂.symm p = 0 := by rw [← he₂,e₂.left_inv h0₂]
  obtain ⟨L,_⟩ := exists_projection_coordinates (P p) (hid p hp) hr hs
  obtain ⟨e,hep,he0,heU,he,hei,hker⟩ := combine_foliation_charts P e₁ e₂ hi₁ hi₂ hk₁
    (fun y hy v ↦ (complement_fixed_iff_zero (P y) v).symm.trans (hk₂ y hy v))
    hp₁ hp₂ hi0₁ hi0₂ L
  exact ⟨e,hep,he0,fun y hy ↦ hU₁ (heU hy).1,he,hei,hker⟩

end UniversalCoverSplitting
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

theorem local_product_chart (S : HolomorphicSplitting X r s)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (c : X.Carrier) :
    ∃ e : OpenPartialHomeomorph X.Carrier (Model r × Model s),
      c ∈ e.source ∧ e c = 0 ∧
      MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) e e.source ∧
      MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) e.symm e.target ∧
      ∀ y ∈ e.source, ∀ v : Tangent X y,
        (S.projection y v = v ↔
          (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).2 = 0) ∧
        (S.projection y v = 0 ↔
          (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).1 = 0) := by
  let a := extChartAt (model n) c
  let P := projectionInChart S.projection c
  have hInt₁ (O : Set (Model n)) (hO : IsOpen O) (hOU : O ⊆ a.target) :
      InvolutiveProjectionOn P O := h₁ c O hO hOU
  have hInt₂ (O : Set (Model n)) (hO : IsOpen O) (hOU : O ⊆ a.target) :
      InvolutiveProjectionOn (fun z ↦ ContinuousLinearMap.id ℂ (Model n)-P z) O := by
    intro V W hV hW hVP hWP z hz
    have heq (y : Model n) (hy : y ∈ O) :=
      projectionInChart_complement S.projection c (hOU hy)
    have H := h₂ c O hO hOU V W hV hW
      (fun y hy ↦ (congrArg (fun L : Model n →L[ℂ] Model n ↦ L (V y)) (heq y hy)).trans (hVP y hy))
      (fun y hy ↦ (congrArg (fun L : Model n →L[ℂ] Model n ↦ L (W y)) (heq y hy)).trans (hWP y hy)) z hz
    exact (congrArg (fun L : Model n →L[ℂ] Model n ↦ L (VectorField.lieBracket ℂ V W z))
      (heq z hz)).symm.trans H
  have hr : Module.finrank ℂ (LinearMap.range (P (a c)).toLinearMap) = r := by
    have H : P (a c) = (S.projection c : Model n →L[ℂ] Model n) := projectionInChart_self S.projection c
    rw [H]
    exact S.first_rank c
  have hs : Module.finrank ℂ (LinearMap.ker (P (a c)).toLinearMap) = s := by
    have H : P (a c) = (S.projection c : Model n →L[ℂ] Model n) := projectionInChart_self S.projection c
    rw [H]
    exact S.second_rank c
  obtain ⟨b,hbc,hb0,hbU,hb,hbi,hbk⟩ := holomorphic_product_coordinates
    (isOpen_extChartAt_target c) P (S.holomorphic c)
    (fun z hz v ↦ projectionInChart_idempotent S c hz v) hInt₁ hInt₂
    (mem_extChartAt_target c) hr hs
  let d := chartAt (Model n) c
  have ha : (a : X.Carrier → Model n) = d := by
    ext x; simp [a,d,model]
  have hai : (a.symm : Model n → X.Carrier) = d.symm := by
    ext x; simp [a,d,model]
  have has : a.source = d.source := extChartAt_source (model n) c
  have hat : a.target = d.target := by
    simp [a,d,model]
  let e := d.trans b
  have hec : c ∈ e.source := ⟨mem_chart_source (Model n) c,ha ▸ hbc⟩
  have he0 : e c = 0 := by change b (d c) = 0; rw [← ha]; exact hb0
  have hd : MDifferentiableOn (model n) (model n) d d.source := by
    rw [← ha]
    exact mdifferentiableOn_extChartAt (I := model n) (x := c)
  have hdi : MDifferentiableOn (model n) (model n) d.symm d.target := by
    rw [← hai,← hat]
    exact mdifferentiableOn_extChartAt_symm
  have hbd : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) b b.source :=
    mdifferentiableOn_iff_differentiableOn.mpr (hb.differentiableOn (by norm_num))
  have hbid : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) b.symm b.target :=
    mdifferentiableOn_iff_differentiableOn.mpr (hbi.differentiableOn (by norm_num))
  have he : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) e e.source :=
    hbd.comp (hd.mono inter_subset_left) inter_subset_right
  have hei : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) e.symm e.target :=
    hdi.comp (hbid.mono inter_subset_left) inter_subset_right
  refine ⟨e,hec,he0,he,hei,?_⟩
  intro y hy v
  change Model n at v
  have hdy : y ∈ d.source := hy.1
  have hby : d y ∈ b.source := hy.2
  have hay : a y ∈ a.target := a.map_source (has ▸ hdy)
  let A : Model n →L[ℂ] Model n := mfderiv (model n) (model n) d y
  let B : Model n →L[ℂ] Model n := mfderiv (model n) (model n) d.symm (d y)
  let T : Model n →L[ℂ] Model n := S.projection y
  have hBA : B.comp A = ContinuousLinearMap.id ℂ (Model n) := by
    have H := (chart_mfderiv_inverses c hay).2
    rw [ha,hai,d.left_inv hdy] at H
    exact H
  have hAB : A.comp B = ContinuousLinearMap.id ℂ (Model n) := by
    have H := (chart_mfderiv_inverses c hay).1
    rw [ha,hai,d.left_inv hdy] at H
    exact H
  have hBA' (w : Model n) : B (A w) = w := congrArg (fun L : Model n →L[ℂ] Model n ↦ L w) hBA
  have hAinj : Function.Injective A := by
    intro x z hxz
    simpa only [hBA'] using congrArg B hxz
  have hPA (w : Model n) : P (d y) (A w) = A (T w) := by
    change projectionInChart S.projection c (d y) (A w) = A (T w)
    dsimp only [projectionInChart]
    rw [ha,hai,d.left_inv hdy]
    change A (T (B (A w))) = A (T w)
    rw [hBA']
  have hD : (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y :
      Model n →L[ℂ] (Model r × Model s)) = (fderiv ℂ b (d y)).comp A := by
    have H := mfderiv_comp (I := model n) (I' := model n)
      (I'' := 𝓘(ℂ, Model r × Model s)) y
      (hbd.mdifferentiableAt (b.open_source.mem_nhds hby))
      (hd.mdifferentiableAt (d.open_source.mem_nhds hdy))
    change (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y :
      Model n →L[ℂ] (Model r × Model s)) =
      (mfderiv (model n) 𝓘(ℂ, Model r × Model s) b (d y)).comp A at H
    simp only [mfderiv_eq_fderiv] at H
    exact H
  have hfin := hbk (d y) hby (A v)
  rw [hPA v] at hfin
  constructor
  · change T v = v ↔ _
    rw [hD]
    exact (hAinj.eq_iff).symm.trans hfin.1
  · change T v = 0 ↔ _
    rw [hD]
    have ha0 : A (T v) = 0 ↔ T v = 0 := by
      simpa only [map_zero] using (hAinj.eq_iff (a := T v) (b := 0))
    exact ha0.symm.trans hfin.2

end UniversalCoverSplitting
open Set Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

structure SplittingChart (S : HolomorphicSplitting X r s) where
  chart : OpenPartialHomeomorph X.Carrier (Model r × Model s)
  radius : ℝ
  radius_pos : 0 < radius
  product_range : chart.target = ball 0 radius ×ˢ ball 0 radius
  holomorphic : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) chart chart.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) chart.symm chart.target
  horizontal : ∀ y ∈ chart.source, ∀ v : Tangent X y,
    S.projection y v = v ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) chart y v).2 = 0
  vertical : ∀ y ∈ chart.source, ∀ v : Tangent X y,
    S.projection y v = 0 ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) chart y v).1 = 0

theorem restrict_product_chart (S : HolomorphicSplitting X r s)
    (e : OpenPartialHomeomorph X.Carrier (Model r × Model s))
    (he : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) e e.source)
    (hei : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) e.symm e.target)
    (hk : ∀ y ∈ e.source, ∀ v : Tangent X y,
      (S.projection y v = v ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).2 = 0) ∧
      (S.projection y v = 0 ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).1 = 0))
    {c : X.Carrier} (hc : c ∈ e.source) (h0 : e c = 0) :
    ∃ b : SplittingChart S, c ∈ b.chart.source ∧ b.chart c = 0 := by
  have h0t : (0 : Model r × Model s) ∈ e.target := h0 ▸ e.map_source hc
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds h0t)
  let V : Set (Model r × Model s) := ball 0 ε ×ˢ ball 0 ε
  have hV : IsOpen V := isOpen_ball.prod isOpen_ball
  have hVU : V ⊆ e.target := by
    rw [show V = ball (0 : Model r × Model s) ε from ball_prod_same _ _ _]
    exact hball
  let b := (e.symm.restrOpen V hV).symm
  have hbt : b.target = V := inter_eq_right.mpr hVU
  have hbc : c ∈ b.source := by
    change c ∈ e.source ∧ e c ∈ V
    refine ⟨hc,?_⟩
    rw [h0]
    exact ⟨mem_ball_self hε,mem_ball_self hε⟩
  let B : SplittingChart S :=
    { chart := b
      radius := ε
      radius_pos := hε
      product_range := hbt
      holomorphic := he.mono inter_subset_left
      inverse_holomorphic := hei.mono inter_subset_left
      horizontal := fun y hy v ↦ (hk y hy.1 v).1
      vertical := fun y hy v ↦ (hk y hy.1 v).2 }
  exact ⟨B,hbc,h0⟩

end UniversalCoverSplitting

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

theorem exists_splittingChart (S : HolomorphicSplitting X r s)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (c : X.Carrier) :
    ∃ b : SplittingChart S, c ∈ b.chart.source ∧ b.chart c = 0 := by
  obtain ⟨e,hc,h0,he,hei,hk⟩ := local_product_chart S h₁ h₂ c
  exact restrict_product_chart S e he hei hk hc h0
end UniversalCoverSplitting
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma SplittingChart.inverse_derivative (e : SplittingChart S)
    {z : Model r × Model s} (hz : z ∈ e.chart.target) (w : Model r × Model s) :
    mfderiv (model n) 𝓘(ℂ, Model r × Model s) e.chart (e.chart.symm z)
      (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm z w) = w := by
  have hdi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds hz)
  have hd := e.holomorphic.mdifferentiableAt
    (e.chart.open_source.mem_nhds (e.chart.map_target hz))
  have hEq : (e.chart ∘ e.chart.symm : (Model r × Model s) → Model r × Model s) =ᶠ[𝓝 z] id := by
    filter_upwards [e.chart.open_target.mem_nhds hz] with y hy
    exact e.chart.right_inv hy
  have h := mfderiv_comp z hd hdi
  change (mfderiv 𝓘(ℂ, Model r × Model s) 𝓘(ℂ, Model r × Model s)
    (e.chart ∘ e.chart.symm) z : (Model r × Model s) →L[ℂ] (Model r × Model s)) =
    (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e.chart (e.chart.symm z)).comp
      (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm z) at h
  have hid := hEq.mfderiv_eq (I := 𝓘(ℂ, Model r × Model s)) (I' := 𝓘(ℂ, Model r × Model s))
  simp only [mfderiv_id] at hid
  have h' := h.symm.trans hid
  exact congrArg (fun A : (Model r × Model s) →L[ℂ] (Model r × Model s) ↦ A w) h'

theorem SplittingChart.box_coordinates (e : SplittingChart S)
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) (hmap : MapsTo f U e.chart.source) :
    DifferentiableOn ℂ (e.chart ∘ f) U ∧
      ∀ z ∈ U,
        (fderiv ℂ (e.chart ∘ f) z (1,0)).2 = 0 ∧
        (fderiv ℂ (e.chart ∘ f) z (0,1)).1 = 0 := by
  refine ⟨mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hf.1 hmap),?_⟩
  intro z hz
  have h := mfderiv_comp z
    (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (hmap hz)))
    (hf.1.mdifferentiableAt (hU.mem_nhds hz))
  change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, Model r × Model s) (e.chart ∘ f) z :
    (ℂ × ℂ) →L[ℂ] (Model r × Model s)) =
    (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e.chart (f z)).comp
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z) at h
  simp only [mfderiv_eq_fderiv] at h
  rw [h]
  exact ⟨(e.horizontal _ (hmap hz) _).mp (hf.2 z hz).1,
    (e.vertical _ (hmap hz) _).mp (hf.2 z hz).2⟩

theorem SplittingChart.box_of_coordinate_tangencies (e : SplittingChart S)
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {g : ℂ × ℂ → Model r × Model s}
    (hg : DifferentiableOn ℂ g U) (hmap : MapsTo g U e.chart.target)
    (ht : ∀ z ∈ U, (fderiv ℂ g z (1,0)).2 = 0 ∧ (fderiv ℂ g z (0,1)).1 = 0) :
    IsBox S U (e.chart.symm ∘ g) := by
  refine ⟨e.inverse_holomorphic.comp (mdifferentiableOn_iff_differentiableOn.mpr hg) hmap,?_⟩
  intro z hz
  have h := mfderiv_comp z
    (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hg.differentiableAt (hU.mem_nhds hz)))
  change (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) (e.chart.symm ∘ g) z : (ℂ × ℂ) →L[ℂ] Model n) =
    (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm (g z)).comp
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, Model r × Model s) g z) at h
  simp only [mfderiv_eq_fderiv] at h
  have hp (v : ℂ × ℂ) :
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) (e.chart.symm ∘ g) z : (ℂ × ℂ) →L[ℂ] Model n) v =
      (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm (g z) :
        (Model r × Model s) →L[ℂ] Model n) (fderiv ℂ g z v) := by
    exact congrArg (fun A : (ℂ × ℂ) →L[ℂ] Model n ↦ A v) h
  constructor
  · apply (e.horizontal _ (e.chart.map_target (hmap hz)) _).mpr
    rw [hp]
    rw [e.inverse_derivative (hmap hz)]
    exact (ht z hz).1
  · apply (e.vertical _ (e.chart.map_target (hmap hz)) _).mpr
    rw [hp]
    rw [e.inverse_derivative (hmap hz)]
    exact (ht z hz).2

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.HolomorphicIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open Set Metric Filter Topology
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set Metric
open Set Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
section ComplexIdentity
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_eqOn_of_convex_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : Convex ℝ U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  intro y hy
  let l : ℂ →ᴬ[ℂ] E := ContinuousAffineMap.lineMap x y
  let L : ℂ →L[ℝ] E := ((ContinuousLinearMap.id ℂ ℂ).smulRight (y - x)).restrictScalars ℝ
  have he : ∀ z : ℂ, l z = L z + x := fun z ↦ rfl
  have hl0 : l 0 = x := by simp [l, ContinuousAffineMap.coe_lineMap_eq]
  have hl1 : l 1 = y := by simp [l, ContinuousAffineMap.coe_lineMap_eq]
  have hopen : IsOpen (l ⁻¹' U) := hU.preimage l.continuous
  have hconv : Convex ℝ (l ⁻¹' U) := by
    change Convex ℝ ((fun z ↦ L z + x) ⁻¹' U)
    exact (hc.translate_preimage_left x).linear_preimage L.toLinearMap
  have hf' : DifferentiableOn ℂ (f ∘ l) (l ⁻¹' U) :=
    hf.comp l.differentiableOn (mapsTo_preimage _ _)
  have hg' : DifferentiableOn ℂ (g ∘ l) (l ⁻¹' U) :=
    hg.comp l.differentiableOn (mapsTo_preimage _ _)
  have hlocal : (f ∘ l) =ᶠ[𝓝 0] (g ∘ l) :=
    hfg.comp_tendsto (hl0 ▸ l.continuous.continuousAt)
  have hzero : (0 : ℂ) ∈ l ⁻¹' U := by simpa only [mem_preimage, hl0] using hx
  have hone : (1 : ℂ) ∈ l ⁻¹' U := by simpa only [mem_preimage, hl1] using hy
  have h := (hf'.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hg'.analyticOnNhd hopen) hconv.isPreconnected hzero hlocal hone
  simpa only [Function.comp_apply, hl1] using h

end ComplexIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section ManifoldIdentity
open Filter Topology
open scoped Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {n : ℕ} {X : ComplexManifold n}

theorem holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f g : E → X.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, E) (model n) f U)
    (hg : MDifferentiableOn 𝓘(ℂ, E) (model n) g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : E | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz.2)).continuousAt
    have hcg : ContinuousAt g z := (hg.mdifferentiableAt (hU.mem_nhds hz.2)).continuousAt
    have : (𝓝[V] z).NeBot := mem_closure_iff_clusterPt.mp hz.1
    have heq : f z = g z := tendsto_nhds_unique_of_eventuallyEq
      hcf.continuousWithinAt hcg.continuousWithinAt
      (Filter.mem_of_superset self_mem_nhdsWithin fun w (hw : w ∈ V) ↦ hw.eq_of_nhds)
    let c := extChartAt (model n) (f z)
    have hsrc : c.source ∈ 𝓝 (f z) := extChartAt_source_mem_nhds (I := model n) (f z)
    have hN : U ∩ (f ⁻¹' c.source ∩ g ⁻¹' c.source) ∈ 𝓝 z :=
      inter_mem (hU.mem_nhds hz.2) (inter_mem (hcf hsrc) (hcg (heq ▸ hsrc)))
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.mp hN
    have hfc : DifferentiableOn ℂ (c ∘ f) (Metric.ball z r) := by
      intro a ha
      have hm : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Model n) (c ∘ f) a :=
        (mdifferentiableAt_extChartAt (I := model n) (by
          simpa only [mem_preimage, c, extChartAt_source] using (hrN ha).2.1)).comp a
          (hf.mdifferentiableAt (hU.mem_nhds (hrN ha).1))
      exact hm.differentiableAt.differentiableWithinAt
    have hgc : DifferentiableOn ℂ (c ∘ g) (Metric.ball z r) := by
      intro a ha
      have hm : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Model n) (c ∘ g) a :=
        (mdifferentiableAt_extChartAt (I := model n) (by
          simpa only [mem_preimage, c, extChartAt_source] using (hrN ha).2.2)).comp a
          (hg.mdifferentiableAt (hU.mem_nhds (hrN ha).1))
      exact hm.differentiableAt.differentiableWithinAt
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff.mp hz.1 (Metric.ball z r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hchart : EqOn (c ∘ f) (c ∘ g) (Metric.ball z r) :=
      holomorphic_eqOn_of_convex_of_eventuallyEq Metric.isOpen_ball (convex_ball z r)
        hfc hgc hwB (hwV.mono fun a ha ↦ congrArg c ha)
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z hr) fun a ha ↦
      c.injOn (hrN ha).2.1 (hrN ha).2.2 (hchart ha)
  intro z hz
  exact (hVU hz).eq_of_nhds

end ManifoldIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section ManifoldSourceIdentity
open Filter Topology
open scoped Manifold
variable {m n : ℕ} {M : ComplexManifold m} {X : ComplexManifold n}

theorem holomorphic_manifolds_eqOn_of_preconnected_of_eventuallyEq
    {U : Set M.Carrier} (hU : IsOpen U) (hc : IsPreconnected U)
    {f g : M.Carrier → X.Carrier}
    (hf : MDifferentiableOn (model m) (model n) f U)
    (hg : MDifferentiableOn (model m) (model n) g U)
    {x : M.Carrier} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : M.Carrier | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    let e := chartAt (Model m) z
    have hzs : z ∈ e.source := mem_chart_source _ _
    have hzt : e z ∈ e.target := e.map_source hzs
    have hcz : ContinuousAt e z := e.continuousAt hzs
    have hcs : ContinuousAt e.symm (e z) := e.symm.continuousAt hzt
    have hN : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e z) := by
      refine inter_mem (e.open_target.mem_nhds hzt) (hcs ?_)
      simpa only [e.left_inv hzs] using hU.mem_nhds hz.2
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.mp hN
    have hfc : MDifferentiableOn 𝓘(ℂ, Model m) (model n) (f ∘ e.symm) (Metric.ball (e z) r) := by
      intro a ha
      exact ((hf.mdifferentiableAt (hU.mem_nhds (hrN ha).2)).comp a
        (mdifferentiableAt_atlas_symm (I := model m)
          (ChartedSpace.chart_mem_atlas z) (hrN ha).1)).mdifferentiableWithinAt
    have hgc : MDifferentiableOn 𝓘(ℂ, Model m) (model n) (g ∘ e.symm) (Metric.ball (e z) r) := by
      intro a ha
      exact ((hg.mdifferentiableAt (hU.mem_nhds (hrN ha).2)).comp a
        (mdifferentiableAt_atlas_symm (I := model m)
          (ChartedSpace.chart_mem_atlas z) (hrN ha).1)).mdifferentiableWithinAt
    have hB : e.source ∩ e ⁻¹' Metric.ball (e z) r ∈ 𝓝 z :=
      inter_mem (e.open_source.mem_nhds hzs) (hcz (Metric.ball_mem_nhds _ hr))
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff_nhds.mp hz.1 _ hB
    have hwgerm : (f ∘ e.symm) =ᶠ[𝓝 (e w)] (g ∘ e.symm) := by
      apply hwV.comp_tendsto
      have h := e.symm.continuousAt (e.map_source hwB.1)
      change Tendsto e.symm (𝓝 (e w)) (𝓝 (e.symm (e w))) at h
      simpa only [e.left_inv hwB.1] using h
    have heq := holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
      Metric.isOpen_ball (convex_ball (e z) r).isPreconnected hfc hgc hwB.2 hwgerm
    exact Filter.mem_of_superset hB fun a ha ↦ by
      change f a = g a
      simpa only [Function.comp_apply, e.left_inv ha.1] using heq ha.2
  intro z hz
  exact (hVU hz).eq_of_nhds

end ManifoldSourceIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section LocalProductSeparation
variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem independent_second_of_fderiv_zero
    {U : Set E₁} {V : Set E₂} (hU : IsOpen U) (hV : IsOpen V)
    (hVc : IsPreconnected V) {f : E₁ × E₂ → F}
    (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (hzero : ∀ p ∈ U ×ˢ V, ∀ v : E₂, fderiv ℂ f p (0, v) = 0)
    {a : E₁} (ha : a ∈ U) {b c : E₂} (hb : b ∈ V) (hc : c ∈ V) :
    f (a, b) = f (a, c) := by
  have hd (y : E₂) (hy : y ∈ V) :
      HasFDerivAt (fun t : E₂ ↦ f (a, t)) (0 : E₂ →L[ℂ] F) y := by
    have hp : HasFDerivAt (fun t : E₂ ↦ (a, t))
        (ContinuousLinearMap.inr ℂ E₁ E₂) y := by
      have hh := (hasFDerivAt_const (𝕜 := ℂ) a y).prodMk (hasFDerivAt_id (𝕜 := ℂ) y)
      have he : (ContinuousLinearMap.prod (0 : E₂ →L[ℂ] E₁)
          (ContinuousLinearMap.id ℂ E₂)) = ContinuousLinearMap.inr ℂ E₁ E₂ := by
        ext v <;> rfl
      rw [he] at hh
      exact hh
    have hh := ((hf (a, y) ⟨ha, hy⟩).differentiableAt
      ((hU.prod hV).mem_nhds ⟨ha, hy⟩)).hasFDerivAt.comp y hp
    have he : fderiv ℂ f (a, y) ∘L ContinuousLinearMap.inr ℂ E₁ E₂ = 0 := by
      ext v
      exact hzero (a, y) ⟨ha, hy⟩ v
    rw [he] at hh
    exact hh
  exact hV.is_const_of_fderiv_eq_zero hVc
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hd y hy).fderiv) hb hc

end LocalProductSeparation
end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.BoxGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set Metric
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting

section Separation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem separated_eq_diagonal {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℂ × ℂ → E × F} (hf : DifferentiableOn ℂ f (U ×ˢ U))
    (ht : ∀ z ∈ U ×ˢ U, (fderiv ℂ f z (1,0)).2 = 0 ∧
      (fderiv ℂ f z (0,1)).1 = 0) {u v : ℂ} (hu : u ∈ U) (hv : v ∈ U) :
    f (u,v) = ((f (u,u)).1,(f (v,v)).2) := by
  have h₁ (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hU).mem_nhds (show (u,z) ∈ U ×ˢ U from ⟨hu,hz⟩))).hasFDerivAt
    have hh := hd.fst.comp_hasDerivAt z ((hasDerivAt_const z u).prodMk (hasDerivAt_id z))
    change HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) ((fderiv ℂ f (u,z) (0,1)).1) z at hh
    rwa [(ht (u,z) ⟨hu,hz⟩).2] at hh
  have h₂ (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hU).mem_nhds (show (z,v) ∈ U ×ˢ U from ⟨hz,hv⟩))).hasFDerivAt
    have hh := hd.snd.comp_hasDerivAt z ((hasDerivAt_id z).prodMk (hasDerivAt_const z v))
    change HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) ((fderiv ℂ f (z,v) (1,0)).2) z at hh
    rwa [(ht (z,v) ⟨hz,hv⟩).1] at hh
  apply Prod.ext
  · exact hU.is_const_of_deriv_eq_zero hUc
      (fun z hz ↦ (h₁ z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (h₁ z hz).deriv) hv hu
  · exact hU.is_const_of_deriv_eq_zero hUc
      (fun z hz ↦ (h₂ z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (h₂ z hz).deriv) hu hv
end Separation

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem box_diagonal_germ_unique (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsBox S (U ×ˢ U) f) (hg : IsBox S (U ×ˢ U) g)
    (heq : ∀ z ∈ U, f (z,z) = g (z,z)) {p : ℂ} (hp : p ∈ U) :
    f =ᶠ[𝓝 (p,p)] g := by
  obtain ⟨e,het,_⟩ := exists_splittingChart S h₁ h₂ (f (p,p))
  have hpp : (p,p) ∈ U ×ˢ U := ⟨hp,hp⟩
  have hfn := (hf.1.continuousOn.continuousAt ((hU.prod hU).mem_nhds hpp))
    (e.chart.open_source.mem_nhds het)
  have hgn := (hg.1.continuousOn.continuousAt ((hU.prod hU).mem_nhds hpp))
    (e.chart.open_source.mem_nhds ((heq p hp) ▸ het))
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp (inter_mem ((hU.prod hU).mem_nhds hpp) (inter_mem hfn hgn))
  have hprod : ball p a ×ˢ ball p a = ball (p,p) a := ball_prod_same _ _ _
  have hsub : ball p a ⊆ U := by
    intro z hz
    exact (hasub (hprod ▸ (show (z,p) ∈ ball p a ×ˢ ball p a from ⟨hz,mem_ball_self ha⟩))).1.1
  have hm (z : ℂ × ℂ) (hz : z ∈ ball p a ×ˢ ball p a) :
      f z ∈ e.chart.source ∧ g z ∈ e.chart.source := (hasub (hprod ▸ hz)).2
  have hbsub : ball p a ×ˢ ball p a ⊆ U ×ˢ U := prod_mono hsub hsub
  have hfb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball p a) f from ⟨hf.1.mono hbsub,fun z hz ↦ hf.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).1)
  have hgb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball p a) g from ⟨hg.1.mono hbsub,fun z hz ↦ hg.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).2)
  filter_upwards [ball_mem_nhds (p,p) ha] with z hz
  have hzz : z ∈ ball p a ×ˢ ball p a := hprod.symm ▸ hz
  apply e.chart.injOn (hm z hzz).1 (hm z hzz).2
  have hfe := separated_eq_diagonal isOpen_ball (convex_ball p a).isPreconnected hfb.1 hfb.2 hzz.1 hzz.2
  have hge := separated_eq_diagonal isOpen_ball (convex_ball p a).isPreconnected hgb.1 hgb.2 hzz.1 hzz.2
  change (e.chart ∘ f) z = (e.chart ∘ g) z
  rw [hfe,hge]
  simp only [Function.comp_apply,heq z.1 (hsub hzz.1),heq z.2 (hsub hzz.2)]

theorem SplittingChart.diagonal_box (e : SplittingChart S) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f U)
    (hmap : MapsTo f U e.chart.source) :
    IsBox S (U ×ˢ U) (fun z : ℂ × ℂ ↦ e.chart.symm ((e.chart (f z.1)).1,(e.chart (f z.2)).2)) ∧
      ∀ z ∈ U, e.chart.symm ((e.chart (f z)).1,(e.chart (f z)).2) = f z := by
  let q := e.chart ∘ f
  have hq : DifferentiableOn ℂ q U :=
    mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hf hmap)
  let G : ℂ × ℂ → Model r × Model s := fun z ↦ ((q z.1).1,(q z.2).2)
  have hd (z : ℂ × ℂ) (hz : z ∈ U ×ˢ U) :
      HasFDerivAt G ((((ContinuousLinearMap.fst ℂ (Model r) (Model s)).comp (fderiv ℂ q z.1)).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)).prod
        (((ContinuousLinearMap.snd ℂ (Model r) (Model s)).comp (fderiv ℂ q z.2)).comp (ContinuousLinearMap.snd ℂ ℂ ℂ))) z := by
    exact ((hq.differentiableAt (hU.mem_nhds hz.1)).hasFDerivAt.fst.comp z hasFDerivAt_fst).prodMk
      ((hq.differentiableAt (hU.mem_nhds hz.2)).hasFDerivAt.snd.comp z hasFDerivAt_snd)
  have hG : DifferentiableOn ℂ G (U ×ˢ U) := fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt
  have hGmap : MapsTo G (U ×ˢ U) e.chart.target := by
    intro z hz
    have h₁' := e.chart.map_source (hmap hz.1)
    have h₂' := e.chart.map_source (hmap hz.2)
    rw [e.product_range] at h₁' h₂' ⊢
    exact ⟨h₁'.1,h₂'.2⟩
  have ht : ∀ z ∈ U ×ˢ U, (fderiv ℂ G z (1,0)).2 = 0 ∧ (fderiv ℂ G z (0,1)).1 = 0 := by
    intro z hz
    rw [(hd z hz).fderiv]
    simp
  refine ⟨e.box_of_coordinate_tangencies (hU.prod hU) hG hGmap ht,?_⟩
  intro z hz
  exact e.chart.left_inv (hmap hz)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.mono {U V : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) (hV : V ⊆ U) : IsBox S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

theorem glue_boxes {ι : Type*} (U : ι → Set (ℂ × ℂ)) (hU : ∀ i, IsOpen (U i))
    (f : ι → ℂ × ℂ → X.Carrier) (hf : ∀ i, IsBox S (U i) (f i))
    (heq : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) (d : X.Carrier) :
    ∃ F : ℂ × ℂ → X.Carrier, IsBox S (⋃ i, U i) F ∧ ∀ i, EqOn F (f i) (U i) := by
  classical
  let F : ℂ × ℂ → X.Carrier := fun z ↦ if hz : z ∈ ⋃ i, U i then
    f (mem_iUnion.mp hz).choose z else d
  have hF (i : ι) : EqOn F (f i) (U i) := by
    intro z hz
    have hzU : z ∈ ⋃ i, U i := mem_iUnion.mpr ⟨i,hz⟩
    dsimp only [F]
    rw [dite_eq_left hzU]
    exact heq _ i ⟨(mem_iUnion.mp hzU).choose_spec,hz⟩
  have hlocal (z : ℂ × ℂ) (hz : z ∈ ⋃ i, U i) :
      ∃ i, z ∈ U i ∧ F =ᶠ[𝓝 z] f i := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨i,hi,Filter.mem_of_superset ((hU i).mem_nhds hi) (hF i)⟩
  refine ⟨F,⟨?_,?_⟩,hF⟩
  · intro z hz
    obtain ⟨i,hi,he⟩ := hlocal z hz
    exact (((hf i).1.mdifferentiableAt ((hU i).mem_nhds hi)).congr_of_eventuallyEq he).mdifferentiableWithinAt
  · intro z hz
    obtain ⟨i,hi,he⟩ := hlocal z hz
    have hd := he.mfderiv_eq (I := 𝓘(ℂ,ℂ × ℂ)) (I' := model n)
    rw [he.eq_of_nhds,hd]
    exact (hf i).2 z hi

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def separatedAffine (p b : ℂ × ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 + b.1 * z.1,p.2 + b.2 * z.2)

def separatedLinear (b : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (b.1 • ContinuousLinearMap.fst ℂ ℂ ℂ).prod (b.2 • ContinuousLinearMap.snd ℂ ℂ ℂ)

lemma separatedAffine_hasFDerivAt (p b z : ℂ × ℂ) :
    HasFDerivAt (separatedAffine p b) (separatedLinear b) z := by
  exact ((hasFDerivAt_fst.const_mul b.1).const_add p.1).prodMk
    ((hasFDerivAt_snd.const_mul b.2).const_add p.2)

lemma IsBox.comp_separatedAffine {U V : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hU : IsOpen U) (hf : IsBox S U f) (p b : ℂ × ℂ)
    (hmap : MapsTo (separatedAffine p b) V U) :
    IsBox S V (f ∘ separatedAffine p b) := by
  have hd : ∀ z, MDifferentiableAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,ℂ × ℂ)
      (separatedAffine p b) z := fun z ↦ (separatedAffine_hasFDerivAt p b z).differentiableAt.mdifferentiableAt
  refine ⟨hf.1.comp (fun z _ ↦ (hd z).mdifferentiableWithinAt) hmap,?_⟩
  intro z hz
  have hmf := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap hz))) (hd z)
  rw [hmf,mfderiv_eq_fderiv,(separatedAffine_hasFDerivAt p b z).fderiv]
  have h₁ : separatedLinear b (1,0) = b.1 • (1,0) := by ext <;> simp [separatedLinear]
  have h₂ : separatedLinear b (0,1) = b.2 • (0,1) := by ext <;> simp [separatedLinear]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (separatedAffine p b z)) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (separatedAffine p b z)
  change S.projection (f (separatedAffine p b z)) (D (separatedLinear b (1,0))) =
      D (separatedLinear b (1,0)) ∧
    S.projection (f (separatedAffine p b z)) (D (separatedLinear b (0,1))) = 0
  have ht : S.projection (f (separatedAffine p b z)) (D (1,0)) = D (1,0) ∧
      S.projection (f (separatedAffine p b z)) (D (0,1)) = 0 := hf.2 _ (hmap hz)
  simp only [h₁,h₂,map_smul,ht.1,ht.2,smul_zero,and_self]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

def mixedLinear (c : ℂ × ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun q := (q.2+c.1*q.1,q.2+c.2*q.1)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' a x := by ext <;> dsimp <;> ring

@[simp] lemma mixedLinear_apply (c q : ℂ × ℂ) :
    mixedLinear c q = (q.2+c.1*q.1,q.2+c.2*q.1) := rfl

def mixedLinearEquiv (c : ℂ × ℂ) (hc : c.1 ≠ c.2) : (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) :=
  { mixedLinear c with
    invFun := fun z ↦ ((z.1-z.2)/(c.1-c.2),(c.1*z.2-c.2*z.1)/(c.1-c.2))
    left_inv := by
      intro z
      have h : c.1-c.2 ≠ 0 := sub_ne_zero.mpr hc
      ext <;> dsimp <;> field_simp <;> ring
    right_inv := by
      intro z
      have h : c.1-c.2 ≠ 0 := sub_ne_zero.mpr hc
      ext <;> dsimp <;> field_simp <;> ring }

def mixedEquiv (c : ℂ × ℂ) (hc : c.1 ≠ c.2) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (mixedLinearEquiv c hc).toContinuousLinearEquiv

@[simp] lemma mixedEquiv_apply (c : ℂ × ℂ) (hc : c.1 ≠ c.2) (q : ℂ × ℂ) :
    mixedEquiv c hc q = (q.2+c.1*q.1,q.2+c.2*q.1) := rfl

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def IsMixedBox (c : ℂ × ℂ) (hc : c.1 ≠ c.2) (U : Set (ℂ × ℂ))
    (f : ℂ × ℂ → X.Carrier) : Prop :=
  IsBox S (mixedEquiv c hc '' U) (f ∘ (mixedEquiv c hc).symm)

lemma IsMixedBox.mono {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {U V : Set (ℂ × ℂ)}
    {f : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f) (hV : V ⊆ U) :
    IsMixedBox (S := S) c hc V f := IsBox.mono hf (image_mono hV)

lemma IsMixedBox.holomorphic {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {U : Set (ℂ × ℂ)}
    {f : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f) :
    MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f U := by
  have hh := hf.1.comp ((mixedEquiv c hc).differentiable.mdifferentiable.mdifferentiableOn)
    (mapsTo_image (mixedEquiv c hc) U)
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh

lemma isMixedBox_iff {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {U : Set (ℂ × ℂ)}
    {f : ℂ × ℂ → X.Carrier} :
    IsMixedBox (S := S) c hc U (f ∘ mixedEquiv c hc) ↔ IsBox S (mixedEquiv c hc '' U) f := by
  simp only [IsMixedBox,Function.comp_def,ContinuousLinearEquiv.apply_symm_apply]

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.FormDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open scoped Interval
open Set Filter Topology Metric
open scoped ContDiff
open Set Metric
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open scoped Manifold ContDiff
open Set
open Set Filter Topology Metric Complex
open scoped Real

open scoped ContDiff
open Set

open scoped Manifold ContDiff
open Set Filter Topology
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

def pullbackMetric (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (z : ℂ × ℂ) :
    (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) →L[ℝ] ℝ :=
  let D := (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z).restrictScalars ℝ
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp
    ((g.metric (f z)).compl₁₂ D.toLinearMap D.toLinearMap))

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set Filter Topology

open scoped Manifold ContDiff
open Set Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.DiskArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set MeasureTheory

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
open scoped Manifold
variable {n : ℕ} {X : ComplexManifold n}

def sliceDensity (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (s z : ℂ) : ℝ :=
  pullbackMetric g f (s,z) (0,1) (0,1)

theorem sliceDensity_nonneg (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (s z : ℂ) :
    0 ≤ sliceDensity g f s z := g.nonnegative _ _

theorem curveSpeed_slice_sq (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {s z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f (s,z)) :
    curveSpeed g (fun w ↦ f (s,w)) z ^ 2 = sliceDensity g f s z := by
  have hp : HasFDerivAt (fun w : ℂ ↦ (s,w))
      (ContinuousLinearMap.inr ℂ ℂ ℂ) z := hasFDerivAt_prodMk_right s z
  have hc : (fun w ↦ f (s,w)) = f ∘ (fun w : ℂ ↦ (s,w)) := rfl
  unfold curveSpeed
  rw [hc, mfderiv_comp z hf hp.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv,
    hp.fderiv]
  change metricNorm g (f (s,z))
    (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (s,z) (0,1)) ^ 2 = _
  exact Real.sq_sqrt (g.nonnegative _ _)

end UniversalCoverSplitting

open Set Metric
open scoped ContDiff

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.MixedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open Set Metric Filter Topology

namespace UniversalCoverSplitting

def complexAnnulus (a b : ℝ) : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}

lemma isOpen_complexAnnulus (a b : ℝ) : IsOpen (complexAnnulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma complexAnnulus_subset_ball (a b : ℝ) : complexAnnulus a b ⊆ ball 0 b :=
  fun _ hz ↦ by simpa using hz.2

lemma complexAnnulus_nonempty {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (complexAnnulus a b).Nonempty := by
  obtain ⟨r,har,hrb⟩ := exists_between hab
  refine ⟨(r:ℂ),?_⟩
  simpa [complexAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ha.trans_lt har)] using And.intro har hrb

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma box_shifted_diagonal_germ_unique (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {D : Set ℂ} (hD : IsOpen D) {f g : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) (hg : IsBox S U g) (p : ℂ × ℂ) {v : ℂ} (hv : v ∈ D)
    (hmap : ∀ z ∈ D, separatedAffine p (1,1) (z,z) ∈ U)
    (he : ∀ z ∈ D, f (separatedAffine p (1,1) (z,z)) = g (separatedAffine p (1,1) (z,z))) :
    f =ᶠ[𝓝 (separatedAffine p (1,1) (v,v))] g := by
  let T := separatedAffine p (1,1)
  have hT : Continuous T := continuous_iff_continuousAt.mpr fun z ↦ (separatedAffine_hasFDerivAt p (1,1) z).continuousAt
  let V := (D ×ˢ D) ∩ T ⁻¹' U
  have hVo : IsOpen V := (hD.prod hD).inter (hU.preimage hT)
  have hvV : (v,v) ∈ V := ⟨⟨hv,hv⟩,hmap v hv⟩
  obtain ⟨e,hepos,hesub⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hvV)
  have hprod : ball v e ×ˢ ball v e = ball (v,v) e := ball_prod_same _ _ _
  have hTU : MapsTo T (ball v e ×ˢ ball v e) U := fun z hz ↦ (hesub (hprod ▸ hz)).2
  have hf' := hf.comp_separatedAffine hU p (1,1) hTU
  have hg' := hg.comp_separatedAffine hU p (1,1) hTU
  have hdiag : ∀ z ∈ ball v e, (f ∘ T) (z,z) = (g ∘ T) (z,z) := by
    intro z hz
    exact he z (hesub (hprod ▸ (show (z,z) ∈ ball v e ×ˢ ball v e from ⟨hz,hz⟩))).1.1
  have hfg := box_diagonal_germ_unique h₁ h₂ isOpen_ball hf' hg' hdiag (mem_ball_self hepos)
  let B : ℂ × ℂ → ℂ × ℂ := separatedAffine (-p.1,-p.2) (1,1)
  have hB : Continuous B := continuous_iff_continuousAt.mpr fun z ↦ (separatedAffine_hasFDerivAt (-p.1,-p.2) (1,1) z).continuousAt
  have hBT (z : ℂ × ℂ) : B (T z) = z := by ext <;> simp [B,T,separatedAffine]
  have hTB (z : ℂ × ℂ) : T (B z) = z := by ext <;> simp [B,T,separatedAffine]
  have hlim : Tendsto B (𝓝 (T (v,v))) (𝓝 (v,v)) := by
    have h := hB.continuousAt (x := T (v,v))
    change Tendsto B _ (𝓝 (B (T (v,v)))) at h
    rw [hBT] at h
    exact h
  have hh := hfg.comp_tendsto hlim
  change (fun x ↦ f (T (B x))) =ᶠ[𝓝 (T (v,v))] (fun x ↦ g (T (B x))) at hh
  simpa only [hTB] using hh

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma glue_mixed_boxes {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {ι : Type*}
    (U : ι → Set (ℂ × ℂ)) (hU : ∀ i, IsOpen (U i))
    (f : ι → ℂ × ℂ → X.Carrier) (hf : ∀ i, IsMixedBox (S := S) c hc (U i) (f i))
    (he : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) (d : X.Carrier) :
    ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (⋃ i, U i) F ∧
      ∀ i, EqOn F (f i) (U i) := by
  let M := mixedEquiv c hc
  have hV (i : ι) : IsOpen (M '' U i) := M.toHomeomorph.isOpenMap _ (hU i)
  have hcompat (i j : ι) : EqOn (f i ∘ M.symm) (f j ∘ M.symm) ((M '' U i) ∩ (M '' U j)) := by
    intro z hz
    apply he i j
    constructor
    · rcases hz.1 with ⟨x,hx,rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
    · rcases hz.2 with ⟨x,hx,rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  obtain ⟨G,hG,hGF⟩ := glue_boxes (fun i ↦ M '' U i) hV (fun i ↦ f i ∘ M.symm) hf hcompat d
  have hd : IsBox S (M '' (⋃ i, U i)) G := by
    rw [image_iUnion]
    exact hG
  refine ⟨G ∘ M,isMixedBox_iff.mpr hd,?_⟩
  intro i z hz
  have h := hGF i (mem_image_of_mem M hz)
  simpa only [Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using h

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.mixed_slope_bound (g : KahlerMetric X) {U : Set (ℂ × ℂ)}
    (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (c : ℂ × ℂ) (hc : c.1 ≠ c.2) (C₁ C₂ : ℝ)
    (hC₁ : ∀ x (u : Tangent X x), metricNorm g x (S.projection x u) ≤ C₁ * metricNorm g x u)
    (hC₂ : ∀ x (u : Tangent X x), metricNorm g x (complementaryProjection S x u) ≤ C₂ * metricNorm g x u)
    {z : ℂ × ℂ} (hz : mixedEquiv c hc z ∈ U) :
    metricNorm g ((f ∘ mixedEquiv c hc) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ mixedEquiv c hc) z (1,0)) ≤
    (‖c.1‖ * C₁ + ‖c.2‖ * C₂) * metricNorm g ((f ∘ mixedEquiv c hc) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ mixedEquiv c hc) z (0,1)) := by
  let M := mixedEquiv c hc
  have hm := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds hz)) M.differentiableAt.mdifferentiableAt
  rw [hm,mfderiv_eq_fderiv,M.hasFDerivAt.fderiv]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (M z)) := mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (M z)
  change metricNorm g (f (M z)) (D (M (1,0))) ≤
    (‖c.1‖ * C₁ + ‖c.2‖ * C₂) * metricNorm g (f (M z)) (D (M (0,1)))
  have ht : S.projection (f (M z)) (D (1,0)) = D (1,0) ∧
      S.projection (f (M z)) (D (0,1)) = 0 := hf.2 _ hz
  simpa only [M,mixedEquiv_apply,mul_one,zero_add,mul_zero,add_zero,div_one] using
    mixed_direction_metric_norm_le g (f (M z)) (S.projection (f (M z))) D ht.1 ht.2 C₁ C₂
      (hC₁ _) (hC₂ _) c.1 c.2 1 1 one_ne_zero one_ne_zero

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ShellFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsMixedBox.slice_holomorphic {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W D : Set ℂ} {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc (W ×ˢ D) f) {w : ℂ} (hw : w ∈ W) :
    MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun v ↦ f (w,v)) D :=
  hf.holomorphic.comp
    (fun z _ ↦ (hasFDerivAt_prodMk_right w z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt)
    (fun _ hv ↦ ⟨hw,hv⟩)

lemma IsMixedBox.fibre_eq_of_shell {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set ℂ} {f g Fs : ℂ × ℂ → X.Carrier} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hf : IsMixedBox (S := S) c hc (U ×ˢ ball 0 b) f)
    (hg : IsMixedBox (S := S) c hc (V ×ˢ ball 0 b) g)
    (hfs : EqOn f Fs (U ×ˢ complexAnnulus a b))
    (hgs : EqOn g Fs (V ×ˢ complexAnnulus a b))
    {w v : ℂ} (hwU : w ∈ U) (hwV : w ∈ V) (hv : v ∈ ball 0 b) : f (w,v) = g (w,v) := by
  obtain ⟨z,hz⟩ := complexAnnulus_nonempty ha hab
  have he : (fun v ↦ f (w,v)) =ᶠ[𝓝 z] (fun v ↦ g (w,v)) :=
    Filter.mem_of_superset ((isOpen_complexAnnulus a b).mem_nhds hz)
      (fun y hy ↦ (hfs ⟨hwU,hy⟩).trans (hgs ⟨hwV,hy⟩).symm)
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq isOpen_ball
    (convex_ball (0:ℂ) b).isPreconnected (hf.slice_holomorphic hwU) (hg.slice_holomorphic hwV)
    (complexAnnulus_subset_ball a b hz) he hv

def MixedFillable (S : HolomorphicSplitting X r s) (c : ℂ × ℂ) (hc : c.1 ≠ c.2)
    (W : Set ℂ) (Fs : ℂ × ℂ → X.Carrier) (a b : ℝ) : Set ℂ :=
  {w | ∃ e : ℝ, 0 < e ∧ ball w e ⊆ W ∧ ∃ F : ℂ × ℂ → X.Carrier,
    IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F ∧
    EqOn F Fs (ball w e ×ˢ complexAnnulus a b)}

lemma mixedFillable_subset {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs : ℂ × ℂ → X.Carrier} {a b : ℝ} :
    MixedFillable S c hc W Fs a b ⊆ W := by
  rintro w ⟨e,he,heW,F,hF,heq⟩
  exact heW (mem_ball_self he)

lemma ball_subset_mixedFillable {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs F : ℂ × ℂ → X.Carrier} {a b e : ℝ} {w : ℂ}
    (hW : ball w e ⊆ W) (hF : IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F)
    (heq : EqOn F Fs (ball w e ×ˢ complexAnnulus a b)) :
    ball w e ⊆ MixedFillable S c hc W Fs a b := by
  intro x hx
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
  exact ⟨d,hd,hdsub.trans hW,F,hF.mono (prod_mono hdsub subset_rfl),
    heq.mono (prod_mono hdsub subset_rfl)⟩

lemma isOpen_mixedFillable {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs : ℂ × ℂ → X.Carrier} {a b : ℝ} :
    IsOpen (MixedFillable S c hc W Fs a b) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro w ⟨e,he,heW,F,hF,heq⟩
  exact Filter.mem_of_superset (ball_mem_nhds w he) (ball_subset_mixedFillable heW hF heq)

theorem glue_all_mixed_fillings {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} {Fs : ℂ × ℂ → X.Carrier} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (MixedFillable S c hc W Fs a b ×ˢ ball 0 b) F ∧
      EqOn F Fs (MixedFillable S c hc W Fs a b ×ˢ complexAnnulus a b) := by
  classical
  let A := MixedFillable S c hc W Fs a b
  choose e he heW f hf heq using (fun w : A ↦ w.property)
  let U : A → Set (ℂ × ℂ) := fun w ↦ ball (w:ℂ) (e w) ×ˢ ball 0 b
  have hU (w : A) : IsOpen (U w) := isOpen_ball.prod isOpen_ball
  have hcompat (u v : A) : EqOn (f u) (f v) (U u ∩ U v) := by
    intro z hz
    exact (hf u).fibre_eq_of_shell ha hab (hf v) (heq u) (heq v) hz.1.1 hz.2.1 hz.1.2
  obtain ⟨F,hF,hFeq⟩ := glue_mixed_boxes U hU f hf hcompat (Fs 0)
  have hUnion : (⋃ w, U w) = A ×ˢ ball 0 b := by
    ext z
    constructor
    · rintro ⟨_,⟨w,rfl⟩,hz⟩
      exact ⟨ball_subset_mixedFillable (heW w) (hf w) (heq w) hz.1,hz.2⟩
    · intro hz
      exact mem_iUnion.mpr ⟨⟨z.1,hz.1⟩,mem_ball_self (he ⟨z.1,hz.1⟩),hz.2⟩
  refine ⟨F,hUnion ▸ hF,?_⟩
  intro z hz
  let w : A := ⟨z.1,hz.1⟩
  exact (hFeq w ⟨mem_ball_self (he w),complexAnnulus_subset_ball _ _ hz.2⟩).trans
    (heq w ⟨mem_ball_self (he w),hz.2⟩)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal

open Set Metric Filter Topology
namespace UniversalCoverSplitting

theorem ball_subset_of_closedBall_continuation {E : Type*} [MetricSpace E] [ProperSpace E]
    {A : Set E} (hA : IsOpen A) {x : E} (hx : x ∈ A) {e : ℝ}
    (hfill : ∀ ρ : ℝ, 0 < ρ → ρ < e → ball x ρ ⊆ A → closedBall x ρ ⊆ A) :
    ball x e ⊆ A := by
  by_contra h
  obtain ⟨y,hy,hny⟩ := not_subset.mp h
  obtain ⟨z,hz,hd⟩ := hA.isClosed_compl.exists_infDist_eq_dist ⟨y,hny⟩ x
  have hpos : 0 < infDist x Aᶜ := by
    rw [hd]
    exact dist_pos.mpr (ne_of_mem_of_not_mem hx hz)
  have hlt : infDist x Aᶜ < e :=
    (infDist_le_dist_of_mem hny).trans_lt (mem_ball'.mp hy)
  apply hz
  apply hfill _ hpos hlt ball_infDist_compl_subset
  rw [mem_closedBall,dist_comm,← hd]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.SmallAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.toMixed {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (hV : MapsTo (mixedEquiv c hc) V U) :
    IsMixedBox (S := S) c hc V (f ∘ mixedEquiv c hc) := by
  have he : (f ∘ mixedEquiv c hc) ∘ (mixedEquiv c hc).symm = f := by
    funext q
    exact congrArg f ((mixedEquiv c hc).apply_symm_apply q)
  unfold IsMixedBox
  rw [he]
  exact hf.mono (image_subset_iff.mpr hV)

lemma IsMixedBox.comp_translation {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc U f) (p : ℂ × ℂ)
    (hp : MapsTo (fun q ↦ p+q) V U) :
    IsMixedBox (S := S) c hc V (fun q ↦ f (p+q)) := by
  let M := mixedEquiv c hc
  have hm : MapsTo (separatedAffine (M p) (1,1)) (M '' V) (M '' U) := by
    rintro z ⟨q,hq,rfl⟩
    refine ⟨p+q,hp hq,?_⟩
    simp only [map_add,separatedAffine,one_mul]
    rfl
  have h := IsBox.comp_separatedAffine (M.toHomeomorph.isOpenMap _ hU) hf (M p) (1,1) hm
  have he : (f ∘ M.symm) ∘ separatedAffine (M p) (1,1) = (fun q ↦ f (p+q)) ∘ M.symm := by
    funext z
    simp only [Function.comp_apply,separatedAffine,one_mul]
    change f (M.symm (M p+z)) = f (p+M.symm z)
    rw [map_add,M.symm_apply_apply]
  rw [he] at h
  exact h

lemma IsMixedBox.slice_holomorphic_on {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc U f) (w : ℂ) {D : Set ℂ}
    (hD : MapsTo (fun v ↦ (w,v)) D U) :
    MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun v ↦ f (w,v)) D :=
  hf.holomorphic.comp
    (fun z _ ↦ (hasFDerivAt_prodMk_right w z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt) hD

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric

open Set Metric

open Set MeasureTheory Filter Topology
open scoped ENNReal

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.BoundaryExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsMixedBox.eqOn_of_slice_in_domain (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {D : Set ℂ} (hD : IsOpen D) {v w : ℂ} (hv : v ∈ D)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f)
    (hg : IsMixedBox (S := S) c hc U g)
    (hmap : ∀ z ∈ D, (w,z) ∈ U) (he : ∀ z ∈ D, f (w,z) = g (w,z)) : EqOn f g U := by
  let M := mixedEquiv c hc
  let p : ℂ × ℂ := (c.1*w,c.2*w)
  have hcalc (z : ℂ) : separatedAffine p (1,1) (z,z) = M (w,z) := by
    ext <;> simp [p,M,separatedAffine,mixedEquiv_apply,add_comm]
  have hmo : IsOpen (M '' U) := M.toHomeomorph.isOpenMap _ hU
  have hh : (f ∘ M.symm) =ᶠ[𝓝 (M (w,v))] (g ∘ M.symm) := by
    rw [← hcalc]
    apply box_shifted_diagonal_germ_unique h₁ h₂ hmo hD hf hg p hv
    · intro z hz
      rw [hcalc]
      exact mem_image_of_mem M (hmap z hz)
    · intro z hz
      change f (M.symm (separatedAffine p (1,1) (z,z))) = g (M.symm (separatedAffine p (1,1) (z,z)))
      rw [hcalc,M.symm_apply_apply]
      exact he z hz
  have hevent : f =ᶠ[𝓝 (w,v)] g := by
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh.comp_tendsto M.continuous.continuousAt
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq hU hUc
    hf.holomorphic hg.holomorphic (hmap v hv) hevent

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

def separatedHomeomorph (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) where
  toFun := separatedAffine p b
  invFun := separatedAffine (-p.1/b.1,-p.2/b.2) (b.1⁻¹,b.2⁻¹)
  left_inv z := by
    ext <;> dsimp [separatedAffine] <;> field_simp <;> ring
  right_inv z := by
    ext <;> dsimp [separatedAffine] <;> field_simp <;> ring
  continuous_toFun := by unfold separatedAffine; fun_prop
  continuous_invFun := by unfold separatedAffine; fun_prop

@[simp] lemma separatedHomeomorph_apply (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (z : ℂ × ℂ) :
    separatedHomeomorph p b hb₁ hb₂ z = separatedAffine p b z := rfl

@[simp] lemma separatedHomeomorph_symm_apply (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (z : ℂ × ℂ) :
    (separatedHomeomorph p b hb₁ hb₂).symm z =
      separatedAffine (-p.1/b.1,-p.2/b.2) (b.1⁻¹,b.2⁻¹) z := rfl

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.comp_separatedHomeomorph_symm {U V : Set (ℂ × ℂ)} (hU : IsOpen U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0)
    (hmap : MapsTo (separatedHomeomorph p b hb₁ hb₂).symm V U) :
    IsBox S V (f ∘ (separatedHomeomorph p b hb₁ hb₂).symm) :=
  hf.comp_separatedAffine hU (-p.1/b.1,-p.2/b.2) (b.1⁻¹,b.2⁻¹) hmap

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_quadratic_remainder {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ z ∈ ball (0:E) r,
      |f z-f 0-fderiv ℝ f 0 z| ≤ M*‖z‖^2 := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K,T,hT,hLip⟩ := hdf.exists_lipschitzOnWith
  have hdiff : ∀ᶠ z in 𝓝 (0:E), DifferentiableAt ℝ f z :=
    (hf.eventually (by norm_num)).mono (fun z h ↦ h.differentiableAt (by norm_num))
  obtain ⟨r,hr,hrT⟩ := Metric.mem_nhds_iff.mp (inter_mem hT hdiff)
  have h0T : (0:E) ∈ T := (hrT (mem_ball_self hr)).1
  let D := fderiv ℝ f 0
  let R : E → ℝ := fun z ↦ f z-f 0-D z
  have hD (z : E) (hz : z ∈ ball (0:E) r) : HasFDerivAt R (fderiv ℝ f z-D) z :=
    ((hrT hz).2.hasFDerivAt.sub_const (f 0)).sub D.hasFDerivAt
  refine ⟨r,(K:ℝ)+1,hr,by positivity,?_⟩
  intro z hz
  have hsub : closedBall (0:E) ‖z‖ ⊆ ball 0 r := closedBall_subset_ball (by simpa using hz)
  have hb (u : E) (hu : u ∈ closedBall (0:E) ‖z‖) : ‖fderiv ℝ f u-D‖ ≤ (K:ℝ)*‖z‖ := by
    have h := hLip.dist_le_mul u ((hrT (hsub hu)).1) 0 h0T
    rw [dist_eq_norm,dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa using hu) K.coe_nonneg)
  have h := (convex_closedBall (0:E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u hu ↦ (hD u (hsub hu)).hasFDerivWithinAt) hb
    (mem_closedBall_self (norm_nonneg z)) (by simp : z ∈ closedBall (0:E) ‖z‖)
  have h' : |f z-f 0-D z| ≤ (K:ℝ)*‖z‖*‖z‖ := by
    simpa only [R,map_zero,sub_self,sub_zero,Real.norm_eq_abs] using h
  dsimp [D] at h'
  nlinarith [sq_nonneg ‖z‖]

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma exists_parabolic_interior_disks {ρ : ℂ × ℂ → ℝ} {U : Set (ℂ × ℂ)}
    (hρ : ContDiffAt ℝ 2 ρ 0) (hρ0 : ρ 0 = 0) {c e : ℝ} (hc : 0 < c) (he : 0 < e)
    (hD : ∀ (x : ℝ) (v : ℂ), fderiv ℝ ρ 0 ((x:ℂ),v) = c*x)
    (hU : ∀ z ∈ ball (0:ℂ × ℂ) e, ρ z < 0 → z ∈ U) :
    ∃ a k : ℝ, a < 0 ∧ 0 < k ∧ ∀ x ∈ Ico a 0,
      MapsTo (fun z : ℂ ↦ ((x:ℂ),z)) (closedBall 0 (k*Real.sqrt (-x))) U := by
  obtain ⟨r,M,hr,hM,hrem⟩ := contDiffAt_quadratic_remainder hρ
  let R := min r e
  have hR : 0 < R := lt_min hr he
  let k := Real.sqrt (c/(4*M))
  have hk : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hk2 : k^2 = c/(4*M) := Real.sq_sqrt (by positivity)
  have hkM : M*k^2 = c/4 := by rw [hk2]; field_simp
  have hm : 0 < min R (min (c/(4*M)) (R^2/(k^2+1))) := by positivity
  obtain ⟨d,hd,hdm⟩ := exists_between hm
  have hdR : d < R := hdm.trans_le (min_le_left _ _)
  have hdM : d < c/(4*M) := hdm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdk : d < R^2/(k^2+1) := hdm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨-d,k,neg_neg_of_pos hd,hk,?_⟩
  intro x hx v hv
  have hs : 0 < -x := neg_pos.mpr hx.2
  have hsd : -x ≤ d := by linarith [hx.1]
  have hvn : ‖v‖ ≤ k*Real.sqrt (-x) := by simpa using hv
  have hvsq : ‖v‖^2 ≤ k^2*(-x) := by
    have h := sq_le_sq₀ (norm_nonneg v) (mul_nonneg hk.le (Real.sqrt_nonneg _)) |>.mpr hvn
    rw [mul_pow,Real.sq_sqrt hs.le] at h
    exact h
  have hvr : ‖v‖ < R := by
    have hdk' := (lt_div_iff₀ (by positivity : 0 < k^2+1)).mp hdk
    have hks := mul_le_mul_of_nonneg_left hsd (sq_nonneg k)
    nlinarith [norm_nonneg v]
  have hzR : ((x:ℂ),v) ∈ ball (0:ℂ × ℂ) R := by
    rw [mem_ball_zero_iff,Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hx.2]
    exact max_lt (hsd.trans_lt hdR) hvr
  have hzNorm : ‖((x:ℂ),v)‖^2 ≤ x^2+‖v‖^2 := by
    rw [Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hx.2]
    rcases le_total (-x) ‖v‖ with h|h
    · rw [max_eq_right h]; nlinarith [sq_nonneg x]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖v‖]
  have hsM : M*(-x) ≤ c/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*M)).mp (hsd.trans hdM.le)
    nlinarith
  have hquad : M*‖((x:ℂ),v)‖^2 ≤ c*(-x)/2 := by
    have h₁ := mul_le_mul_of_nonneg_left hzNorm hM.le
    have h₂ := mul_le_mul_of_nonneg_left hvsq hM.le
    have h₃ := mul_le_mul_of_nonneg_right hsM hs.le
    have h₄ : M*(k^2*(-x)) = c/4*(-x) := by rw [← mul_assoc,hkM]
    nlinarith
  have hbound := hrem ((x:ℂ),v) ((ball_subset_ball (min_le_left r e)) hzR)
  rw [hρ0,sub_zero,hD] at hbound
  have hupper := (le_abs_self (ρ ((x:ℂ),v)-c*x)).trans hbound
  apply hU _ ((ball_subset_ball (min_le_right r e)) hzR)
  nlinarith [mul_pos hc hs]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

def mixedSource (p b c : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (hc : c.1 ≠ c.2) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) :=
  (mixedEquiv c hc).toHomeomorph.trans (separatedHomeomorph p b hb₁ hb₂)

@[simp] lemma mixedSource_zero (p b c : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (hc : c.1 ≠ c.2) :
    mixedSource p b c hb₁ hb₂ hc 0 = p := by
  ext <;> simp [mixedSource,separatedAffine]

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Superellipsoids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold
open Set Metric Filter Topology

namespace UniversalCoverSplitting

def superPotential (m : ℕ) (z : ℂ × ℂ) : ℝ :=
  Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m

def superDomain (m : ℕ) (a : ℝ) : Set (ℂ × ℂ) := {z | superPotential m z < a}

lemma normSq_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k Complex.normSq := by
  change ContDiff ℝ k (fun z : ℂ ↦ z.re*z.re+z.im*z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

lemma superPotential_contDiff (m : ℕ) {k : WithTop ℕ∞} : ContDiff ℝ k (superPotential m) :=
  ((normSq_contDiff.comp contDiff_fst).pow m).add ((normSq_contDiff.comp contDiff_snd).pow m)

lemma superDomain_open (m : ℕ) (a : ℝ) : IsOpen (superDomain m a) :=
  isOpen_lt (superPotential_contDiff m (k := 0)).continuous continuous_const

lemma superPotential_convex (m : ℕ) : ConvexOn ℝ univ (superPotential m) := by
  have h : ConvexOn ℝ (univ : Set ℂ) (fun z : ℂ ↦ ‖z‖^(2*m)) :=
    (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) _
  have h₁ := h.comp_linearMap (LinearMap.fst ℝ ℂ ℂ)
  have h₂ := h.comp_linearMap (LinearMap.snd ℝ ℂ ℂ)
  have hh := h₁.add h₂
  change ConvexOn ℝ univ (fun z : ℂ × ℂ ↦ ‖z.1‖^(2*m)+‖z.2‖^(2*m)) at hh
  change ConvexOn ℝ univ (fun z : ℂ × ℂ ↦ Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m)
  simpa only [Complex.normSq_eq_norm_sq,pow_mul] using hh

lemma superDomain_convex (m : ℕ) (a : ℝ) : Convex ℝ (superDomain m a) := by
  have h := (superPotential_convex m).convex_lt a
  simp only [mem_univ,true_and] at h
  exact h

lemma superPotential_zero {m : ℕ} (hm : 0 < m) : superPotential m 0 = 0 := by
  simp [superPotential,zero_pow hm.ne']

lemma superDomain_zero {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) : (0:ℂ × ℂ) ∈ superDomain m a := by
  simpa only [superDomain,mem_ofPred_eq,superPotential_zero hm] using ha

lemma superPotential_smul (m : ℕ) (t : ℝ) (z : ℂ × ℂ) :
    superPotential m (t • z) = t^(2*m) * superPotential m z := by
  simp only [superPotential,Prod.smul_fst,Prod.smul_snd,Complex.real_smul,Complex.normSq_mul,Complex.normSq_ofReal,
    mul_pow,pow_mul,mul_add]
  ring

lemma superDomain_subset_bidisk {m : ℕ} (_hm : 0 < m) {a : ℝ} (ha : a ≤ 1) :
    superDomain m a ⊆ ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 := by
  intro z hz
  have h₁ : Complex.normSq z.1 ^ m < 1 := lt_of_lt_of_le (lt_of_le_of_lt (le_add_of_nonneg_right
    (pow_nonneg (Complex.normSq_nonneg z.2) m)) hz) ha
  have h₂ : Complex.normSq z.2 ^ m < 1 := lt_of_lt_of_le (lt_of_le_of_lt (le_add_of_nonneg_left
    (pow_nonneg (Complex.normSq_nonneg z.1) m)) hz) ha
  have hnorm : ∀ w : ℂ, Complex.normSq w ^ m < 1 → w ∈ ball (0:ℂ) 1 := by
    intro w hw
    rw [mem_ball,dist_zero_right]
    by_contra hh
    have hn : 1 ≤ ‖w‖ := le_of_not_gt hh
    have hn₂ : 1 ≤ Complex.normSq w := by rw [Complex.normSq_eq_norm_sq]; nlinarith
    exact not_lt_of_ge (one_le_pow₀ hn₂) hw
  exact ⟨hnorm z.1 h₁,hnorm z.2 h₂⟩

end UniversalCoverSplitting

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def IsHorizontalCurve (S : HolomorphicSplitting X r s) (U : Set ℂ) (f : ℂ → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f U ∧ ∀ z ∈ U,
    S.projection (f z) (mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ)) = mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ)

def IsVerticalCurve (S : HolomorphicSplitting X r s) (U : Set ℂ) (f : ℂ → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f U ∧ ∀ z ∈ U,
    S.projection (f z) (mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ)) = 0

lemma IsHorizontalCurve.mono {U V : Set ℂ} {f : ℂ → X.Carrier}
    (hf : IsHorizontalCurve S U f) (hV : V ⊆ U) : IsHorizontalCurve S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

lemma IsVerticalCurve.mono {U V : Set ℂ} {f : ℂ → X.Carrier}
    (hf : IsVerticalCurve S U f) (hV : V ⊆ U) : IsVerticalCurve S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

lemma SplittingChart.horizontal_coordinate_constant (e : SplittingChart S) {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) {f : ℂ → X.Carrier}
    (hf : IsHorizontalCurve S U f) (he : MapsTo f U e.chart.source)
    {u v : ℂ} (hu : u ∈ U) (hv : v ∈ U) : (e.chart (f u)).2 = (e.chart (f v)).2 := by
  have hd (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun z ↦ (e.chart (f z)).2) 0 z := by
    have h := mfderiv_comp z (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz)))
      (hf.1.mdifferentiableAt (hU.mem_nhds hz))
    have hh : DifferentiableAt ℂ (e.chart ∘ f) z := mdifferentiableAt_iff_differentiableAt.mp
      ((e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz))).comp z
        (hf.1.mdifferentiableAt (hU.mem_nhds hz)))
    have ht := (e.horizontal _ (he hz) _).mp (hf.2 z hz)
    have hh' := hh.hasFDerivAt.snd.hasDerivAt
    change HasDerivAt (fun z ↦ (e.chart (f z)).2) ((fderiv ℂ (e.chart ∘ f) z (1:ℂ)).2) z at hh'
    simp only [mfderiv_eq_fderiv] at h
    have hz0 : (fderiv ℂ (e.chart ∘ f) z (1:ℂ)).2 = 0 := by rw [h]; exact ht
    rwa [hz0] at hh'
  exact hU.is_const_of_deriv_eq_zero hUc
    (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hd z hz).deriv) hu hv

lemma SplittingChart.vertical_coordinate_constant (e : SplittingChart S) {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) {f : ℂ → X.Carrier}
    (hf : IsVerticalCurve S U f) (he : MapsTo f U e.chart.source)
    {u v : ℂ} (hu : u ∈ U) (hv : v ∈ U) : (e.chart (f u)).1 = (e.chart (f v)).1 := by
  have hd (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun z ↦ (e.chart (f z)).1) 0 z := by
    have h := mfderiv_comp z (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz)))
      (hf.1.mdifferentiableAt (hU.mem_nhds hz))
    have hh : DifferentiableAt ℂ (e.chart ∘ f) z := mdifferentiableAt_iff_differentiableAt.mp
      ((e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz))).comp z
        (hf.1.mdifferentiableAt (hU.mem_nhds hz)))
    have ht := (e.vertical _ (he hz) _).mp (hf.2 z hz)
    have hh' := hh.hasFDerivAt.fst.hasDerivAt
    change HasDerivAt (fun z ↦ (e.chart (f z)).1) ((fderiv ℂ (e.chart ∘ f) z (1:ℂ)).1) z at hh'
    simp only [mfderiv_eq_fderiv] at h
    have hz0 : (fderiv ℂ (e.chart ∘ f) z (1:ℂ)).1 = 0 := by rw [h]; exact ht
    rwa [hz0] at hh'
  exact hU.is_const_of_deriv_eq_zero hUc
    (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hd z hz).deriv) hu hv

lemma SplittingChart.mix_curves (e : SplittingChart S) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {α β : ℂ → X.Carrier}
    (hα : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) α U)
    (hβ : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) β V)
    (hαe : MapsTo α U e.chart.source) (hβe : MapsTo β V e.chart.source) :
    IsBox S (U ×ˢ V) (fun z ↦ e.chart.symm ((e.chart (α z.1)).1,(e.chart (β z.2)).2)) := by
  let A := e.chart ∘ α
  let B := e.chart ∘ β
  have hA : DifferentiableOn ℂ A U := mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hα hαe)
  have hB : DifferentiableOn ℂ B V := mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hβ hβe)
  let G : ℂ × ℂ → Model r × Model s := fun z ↦ ((A z.1).1,(B z.2).2)
  have hd (z : ℂ × ℂ) (hz : z ∈ U ×ˢ V) :
      HasFDerivAt G ((((ContinuousLinearMap.fst ℂ (Model r) (Model s)).comp (fderiv ℂ A z.1)).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)).prod
        (((ContinuousLinearMap.snd ℂ (Model r) (Model s)).comp (fderiv ℂ B z.2)).comp (ContinuousLinearMap.snd ℂ ℂ ℂ))) z := by
    exact ((hA.differentiableAt (hU.mem_nhds hz.1)).hasFDerivAt.fst.comp z hasFDerivAt_fst).prodMk
      ((hB.differentiableAt (hV.mem_nhds hz.2)).hasFDerivAt.snd.comp z hasFDerivAt_snd)
  apply e.box_of_coordinate_tangencies (hU.prod hV) (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
  · intro z hz
    have ha := e.chart.map_source (hαe hz.1)
    have hb := e.chart.map_source (hβe hz.2)
    rw [e.product_range] at ha hb ⊢
    exact ⟨ha.1,hb.2⟩
  · intro z hz
    rw [(hd z hz).fderiv]
    simp

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

section Separation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
lemma separated_eq_axes {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    {f : ℂ × ℂ → E × F} (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (ht : ∀ z ∈ U ×ˢ V, (fderiv ℂ f z (1,0)).2 = 0 ∧ (fderiv ℂ f z (0,1)).1 = 0)
    {u u₀ v v₀ : ℂ} (hu : u ∈ U) (hu₀ : u₀ ∈ U) (hv : v ∈ V) (hv₀ : v₀ ∈ V) :
    f (u,v) = ((f (u,v₀)).1,(f (u₀,v)).2) := by
  have h₁ (z : ℂ) (hz : z ∈ V) : HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hV).mem_nhds (show (u,z) ∈ U ×ˢ V from ⟨hu,hz⟩))).hasFDerivAt
    have hh := hd.fst.comp_hasDerivAt z ((hasDerivAt_const z u).prodMk (hasDerivAt_id z))
    change HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) ((fderiv ℂ f (u,z) (0,1)).1) z at hh
    rwa [(ht (u,z) ⟨hu,hz⟩).2] at hh
  have h₂ (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hV).mem_nhds (show (z,v) ∈ U ×ˢ V from ⟨hz,hv⟩))).hasFDerivAt
    have hh := hd.snd.comp_hasDerivAt z ((hasDerivAt_id z).prodMk (hasDerivAt_const z v))
    change HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) ((fderiv ℂ f (z,v) (1,0)).2) z at hh
    rwa [(ht (z,v) ⟨hz,hv⟩).1] at hh
  exact Prod.ext (hV.is_const_of_deriv_eq_zero hVc
      (fun z hz ↦ (h₁ z hz).differentiableAt.differentiableWithinAt) (fun z hz ↦ (h₁ z hz).deriv) hv hv₀)
    (hU.is_const_of_deriv_eq_zero hUc
      (fun z hz ↦ (h₂ z hz).differentiableAt.differentiableWithinAt) (fun z hz ↦ (h₂ z hz).deriv) hu hu₀)
end Separation

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma SplittingChart.mix_curves_axes (e : SplittingChart S) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S U α) (hβ : IsVerticalCurve S V β)
    (hαe : MapsTo α U e.chart.source) (hβe : MapsTo β V e.chart.source)
    {u₀ v₀ : ℂ} (hu₀ : u₀ ∈ U) (hv₀ : v₀ ∈ V) (hbase : α u₀ = β v₀) :
    (∀ u ∈ U, e.chart.symm ((e.chart (α u)).1,(e.chart (β v₀)).2) = α u) ∧
    (∀ v ∈ V, e.chart.symm ((e.chart (α u₀)).1,(e.chart (β v)).2) = β v) := by
  constructor
  · intro u hu
    rw [← hbase,← e.horizontal_coordinate_constant hU hUc hα hαe hu hu₀]
    exact e.chart.left_inv (hαe hu)
  · intro v hv
    rw [hbase,← e.vertical_coordinate_constant hV hVc hβ hβe hv hv₀]
    exact e.chart.left_inv (hβe hv)

lemma exists_axis_box_germ (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {u₀ v₀ : ℂ} (hu₀ : u₀ ∈ U) (hv₀ : v₀ ∈ V)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S U α) (hβ : IsVerticalCurve S V β)
    (hbase : α u₀ = β v₀) :
    ∃ d : ℝ, 0 < d ∧ ball u₀ d ⊆ U ∧ ball v₀ d ⊆ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S (ball u₀ d ×ˢ ball v₀ d) F ∧
        (∀ u ∈ ball u₀ d, F (u,v₀) = α u) ∧ (∀ v ∈ ball v₀ d, F (u₀,v) = β v) := by
  obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (α u₀)
  have hαn := (hα.1.continuousOn.continuousAt (hU.mem_nhds hu₀)) (e.chart.open_source.mem_nhds he)
  have hβn := (hβ.1.continuousOn.continuousAt (hV.mem_nhds hv₀))
    (e.chart.open_source.mem_nhds (hbase ▸ he))
  obtain ⟨a,ha,haU⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hu₀) hαn)
  obtain ⟨b,hb,hbV⟩ := Metric.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hv₀) hβn)
  let d := min a b
  have hd : 0 < d := lt_min ha hb
  have hdU : ball u₀ d ⊆ U := fun _ hz ↦ (haU ((ball_subset_ball (min_le_left _ _)) hz)).1
  have hdV : ball v₀ d ⊆ V := fun _ hz ↦ (hbV ((ball_subset_ball (min_le_right _ _)) hz)).1
  have hdae : MapsTo α (ball u₀ d) e.chart.source := fun _ hz ↦ (haU ((ball_subset_ball (min_le_left _ _)) hz)).2
  have hdbe : MapsTo β (ball v₀ d) e.chart.source := fun _ hz ↦ (hbV ((ball_subset_ball (min_le_right _ _)) hz)).2
  refine ⟨d,hd,hdU,hdV,_,e.mix_curves isOpen_ball isOpen_ball (hα.1.mono hdU) (hβ.1.mono hdV) hdae hdbe,?_⟩
  exact e.mix_curves_axes isOpen_ball isOpen_ball (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected
    (hα.mono hdU) (hβ.mono hdV) hdae hdbe (mem_ball_self hd) (mem_ball_self hd) hbase

lemma IsBox.horizontal_slice {U : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) {D : Set ℂ} (v : ℂ) (hmap : ∀ z ∈ D, (z,v) ∈ U) :
    IsHorizontalCurve S D (fun z ↦ f (z,v)) := by
  have hd (z : ℂ) : HasFDerivAt (fun z : ℂ ↦ (z,v))
      ((ContinuousLinearMap.id ℂ ℂ).prod (0:ℂ →L[ℂ] ℂ)) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const v z)
  refine ⟨hf.1.comp (fun z _ ↦ (hd z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt) hmap,?_⟩
  intro z hz
  have hh := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap z hz))) (hd z).differentiableAt.mdifferentiableAt
  simp only [mfderiv_eq_fderiv,(hd z).fderiv] at hh
  change S.projection (f (z,v)) ((mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (z,v)) z) (1:ℂ)) = _
  have he : (mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (z,v)) z : ℂ →L[ℂ] Model n) (1:ℂ) =
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (z,v) : (ℂ × ℂ) →L[ℂ] Model n) (1,0) :=
    congrArg (fun D : ℂ →L[ℂ] Model n ↦ D (1:ℂ)) hh
  rw [he]
  exact (hf.2 (z,v) (hmap z hz)).1

lemma IsBox.vertical_slice {U : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) {D : Set ℂ} (u : ℂ) (hmap : ∀ z ∈ D, (u,z) ∈ U) :
    IsVerticalCurve S D (fun z ↦ f (u,z)) := by
  have hd (z : ℂ) : HasFDerivAt (fun z : ℂ ↦ (u,z))
      ((0:ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) z :=
    (hasFDerivAt_const u z).prodMk (hasFDerivAt_id z)
  refine ⟨hf.1.comp (fun z _ ↦ (hd z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt) hmap,?_⟩
  intro z hz
  have hh := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap z hz))) (hd z).differentiableAt.mdifferentiableAt
  simp only [mfderiv_eq_fderiv,(hd z).fderiv] at hh
  change S.projection (f (u,z)) ((mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (u,z)) z) (1:ℂ)) = 0
  have he : (mfderiv 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (u,z)) z : ℂ →L[ℂ] Model n) (1:ℂ) =
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (u,z) : (ℂ × ℂ) →L[ℂ] Model n) (0,1) :=
    congrArg (fun D : ℂ →L[ℂ] Model n ↦ D (1:ℂ)) hh
  rw [he]
  exact (hf.2 (u,z) (hmap z hz)).2

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.AxisContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem box_axes_germ_unique (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsBox S (U ×ˢ V) f) (hg : IsBox S (U ×ˢ V) g)
    (p q : ℂ) (hp : p ∈ U) (hq : q ∈ V)
    (heq₁ : ∀ z ∈ U, f (z,q) = g (z,q)) (heq₂ : ∀ z ∈ V, f (p,z) = g (p,z)) :
    f =ᶠ[𝓝 (p,q)] g := by
  obtain ⟨e,het,_⟩ := exists_splittingChart S h₁ h₂ (f (p,q))
  have hpp : (p,q) ∈ U ×ˢ V := ⟨hp,hq⟩
  have hfn := (hf.1.continuousOn.continuousAt ((hU.prod hV).mem_nhds hpp))
    (e.chart.open_source.mem_nhds het)
  have hgn := (hg.1.continuousOn.continuousAt ((hU.prod hV).mem_nhds hpp))
    (e.chart.open_source.mem_nhds ((heq₁ p hp) ▸ het))
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp (inter_mem ((hU.prod hV).mem_nhds hpp) (inter_mem hfn hgn))
  have hprod : ball p a ×ˢ ball q a = ball (p,q) a := ball_prod_same _ _ _
  have hsub₁ : ball p a ⊆ U := by
    intro z hz
    exact (hasub (hprod ▸ (show (z,q) ∈ ball p a ×ˢ ball q a from ⟨hz,mem_ball_self ha⟩))).1.1
  have hsub₂ : ball q a ⊆ V := by
    intro z hz
    exact (hasub (hprod ▸ (show (p,z) ∈ ball p a ×ˢ ball q a from ⟨mem_ball_self ha,hz⟩))).1.2
  have hm (z : ℂ × ℂ) (hz : z ∈ ball p a ×ˢ ball q a) :
      f z ∈ e.chart.source ∧ g z ∈ e.chart.source := (hasub (hprod ▸ hz)).2
  have hbsub : ball p a ×ˢ ball q a ⊆ U ×ˢ V := prod_mono hsub₁ hsub₂
  have hfb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball q a) f from ⟨hf.1.mono hbsub,fun z hz ↦ hf.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).1)
  have hgb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball q a) g from ⟨hg.1.mono hbsub,fun z hz ↦ hg.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).2)
  filter_upwards [ball_mem_nhds (p,q) ha] with z hz
  have hzz : z ∈ ball p a ×ˢ ball q a := hprod.symm ▸ hz
  apply e.chart.injOn (hm z hzz).1 (hm z hzz).2
  have hfe := separated_eq_axes isOpen_ball isOpen_ball (convex_ball p a).isPreconnected
    (convex_ball q a).isPreconnected hfb.1 hfb.2 hzz.1 (mem_ball_self ha) hzz.2 (mem_ball_self ha)
  have hge := separated_eq_axes isOpen_ball isOpen_ball (convex_ball p a).isPreconnected
    (convex_ball q a).isPreconnected hgb.1 hgb.2 hzz.1 (mem_ball_self ha) hzz.2 (mem_ball_self ha)
  change (e.chart ∘ f) z = (e.chart ∘ g) z
  rw [hfe,hge]
  simp only [Function.comp_apply,heq₁ z.1 (hsub₁ hzz.1),heq₂ z.2 (hsub₂ hzz.2)]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma horizontal_axis_boundary_extension (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S))
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    {O : Set ℂ} (hO : IsOpen O) {α : ℂ → X.Carrier} (hα : IsHorizontalCurve S O α)
    {p : ℂ} (hp : p ∈ O) (hpc : p ∈ closure {z : ℂ | (z,0) ∈ U})
    (haxis : ∀ z ∈ O, (z,0) ∈ U → f (z,0) = α z) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ (p,0) ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ U) := by
  obtain ⟨e,hep,_⟩ := exists_splittingChart S h₁ h₂ (α p)
  have hαn := (hα.1.continuousOn.continuousAt (hO.mem_nhds hp)) (e.chart.open_source.mem_nhds hep)
  obtain ⟨d,hd,hdO⟩ := Metric.mem_nhds_iff.mp (inter_mem (hO.mem_nhds hp) hαn)
  have hdsub : ball p d ⊆ O := fun _ hz ↦ (hdO hz).1
  have hdae : MapsTo α (ball p d) e.chart.source := fun _ hz ↦ (hdO hz).2
  obtain ⟨q,hq,hqp⟩ := mem_closure_iff_nhds.mp hpc (ball p d) (ball_mem_nhds p hd)
  have hqe : f (q,0) ∈ e.chart.source := (haxis q (hdsub hq) hqp) ▸ hdae hq
  have hfn := (hf.1.continuousOn.continuousAt (hU.mem_nhds hqp)) (e.chart.open_source.mem_nhds hqe)
  obtain ⟨a,ha,haV⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hqp) hfn)
  have hβmap (z : ℂ) (hz : z ∈ ball (0:ℂ) a) : (q,z) ∈ U ∧ f (q,z) ∈ e.chart.source := by
    apply haV
    rw [← ball_prod_same]
    exact ⟨mem_ball_self ha,hz⟩
  let β : ℂ → X.Carrier := fun z ↦ f (q,z)
  have hβ : IsVerticalCurve S (ball 0 a) β := hf.vertical_slice hU q (fun z hz ↦ (hβmap z hz).1)
  let V := ball p d ×ˢ ball (0:ℂ) a
  let F : ℂ × ℂ → X.Carrier := fun z ↦ e.chart.symm ((e.chart (α z.1)).1,(e.chart (β z.2)).2)
  have hF : IsBox S V F := e.mix_curves isOpen_ball isOpen_ball (hα.1.mono hdsub)
    hβ.1 hdae (fun z hz ↦ (hβmap z hz).2)
  have haxes := e.mix_curves_axes isOpen_ball isOpen_ball (convex_ball p d).isPreconnected
    (convex_ball (0:ℂ) a).isPreconnected (hα.mono hdsub) hβ hdae (fun z hz ↦ (hβmap z hz).2)
    hq (mem_ball_self ha) (haxis q (hdsub hq) hqp).symm
  have hVo : IsOpen V := isOpen_ball.prod isOpen_ball
  have hqc : (q,0) ∈ V ∩ U := ⟨⟨hq,mem_ball_self ha⟩,hqp⟩
  obtain ⟨b,hb,hbV⟩ := Metric.mem_nhds_iff.mp ((hVo.inter hU).mem_nhds hqc)
  have hbsub : ball q b ×ˢ ball (0:ℂ) b ⊆ V ∩ U := by rwa [ball_prod_same]
  have hFg : F =ᶠ[𝓝 (q,0)] f := by
    apply box_axes_germ_unique h₁ h₂ isOpen_ball isOpen_ball
      (hF.mono (hbsub.trans inter_subset_left)) (hf.mono (hbsub.trans inter_subset_right)) q 0
      (mem_ball_self hb) (mem_ball_self hb)
    · intro z hz
      have hm := hbsub (show (z,0) ∈ ball q b ×ˢ ball (0:ℂ) b from ⟨hz,mem_ball_self hb⟩)
      exact (haxes.1 z hm.1.1).trans (haxis z (hdsub hm.1.1) hm.2).symm
    · intro z hz
      have hm := hbsub (show (q,z) ∈ ball q b ×ˢ ball (0:ℂ) b from ⟨mem_ball_self hb,hz⟩)
      exact haxes.2 z hm.1.2
  refine ⟨V,hVo,⟨mem_ball_self hd,mem_ball_self ha⟩,F,hF,?_⟩
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hVo.inter hU)
    (((convex_ball p d).prod (convex_ball (0:ℂ) a)).inter hUc).isPreconnected
    (hF.1.mono inter_subset_left) (hf.1.mono inter_subset_right) hqc hFg

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma superPotential_radial_lt {m : ℕ} (hm : 0 < m) {a t : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (ht1 : t < 1) {z : ℂ × ℂ} (hz : superPotential m z ≤ a) :
    t • z ∈ superDomain m a := by
  change superPotential m (t • z) < a
  rw [superPotential_smul]
  have htP : t^(2*m) < 1 := pow_lt_one₀ ht ht1 (by omega)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz (pow_nonneg ht _)) (by nlinarith)

lemma superDomain_closure {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    closure (superDomain m a) = {z | superPotential m z ≤ a} := by
  apply Subset.antisymm
  · exact closure_minimal (fun z (h : superPotential m z < a) ↦ h.le)
      (isClosed_le (superPotential_contDiff m (k := 0)).continuous continuous_const)
  intro z hz
  have ht : Tendsto (fun t : ℝ ↦ t • z) (𝓝[<] 1) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ ↦ t • (z : ℂ × ℂ)) := continuous_id.smul continuous_const
    have hh := hc.continuousAt (x := (1:ℝ)) |>.tendsto
    rw [one_smul] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with t ht ht0
  exact superPotential_radial_lt hm ha ht0.le ht hz

lemma superDomain_frontier {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    frontier (superDomain m a) = {z | superPotential m z = a} := by
  rw [frontier, (superDomain_open m a).interior_eq, superDomain_closure hm ha]
  ext z
  change (superPotential m z ≤ a ∧ ¬superPotential m z < a) ↔ superPotential m z = a
  rw [not_lt]
  exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le,h.ge⟩⟩

lemma superDomain_axis_closure {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a)
    {p : ℂ} (hp : superPotential m (p,0) ≤ a) :
    p ∈ closure {z : ℂ | (z,0) ∈ superDomain m a} := by
  have ht : Tendsto (fun t : ℝ ↦ t • p) (𝓝[<] 1) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ ↦ t • (p : ℂ)) := continuous_id.smul continuous_const
    have hh := hc.continuousAt (x := (1:ℝ)) |>.tendsto
    rw [one_smul] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with t ht ht0
  simpa only [Prod.smul_mk,smul_zero] using superPotential_radial_lt hm ha ht0.le ht hp

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma segment_meets_inter_balls {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : E} {r s : ℝ} (hi : (ball p r ∩ ball q s).Nonempty) :
    (segment ℝ p q ∩ (ball p r ∩ ball q s)).Nonempty := by
  obtain ⟨x,hxp,hxq⟩ := hi
  have hr : 0 < r := (dist_nonneg : 0 ≤ dist x p).trans_lt hxp
  have hs : 0 < s := (dist_nonneg : 0 ≤ dist x q).trans_lt hxq
  have hd : dist p q < r+s := lt_of_le_of_lt (dist_triangle p x q)
    (add_lt_add (by simpa only [mem_ball,dist_comm] using hxp) hxq)
  have hrs : 0 < r+s := add_pos hr hs
  let t : ℝ := r/(r+s)
  have ht : 0 < t := div_pos hr hrs
  have ht1 : t < 1 := (div_lt_one hrs).mpr (by linarith)
  have heq : 1-t = s/(r+s) := by dsimp [t]; field_simp; ring
  refine ⟨AffineMap.lineMap p q t,lineMap_mem_segment ℝ p q ⟨ht.le,ht1.le⟩,?_,?_⟩
  · rw [mem_ball,dist_lineMap_left,Real.norm_eq_abs,abs_of_pos ht]
    have h := mul_lt_mul_of_pos_left hd ht
    have he : t*(r+s)=r := by dsimp [t]; field_simp
    rwa [he] at h
  · rw [mem_ball,dist_lineMap_right,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ht1),heq]
    have h := mul_lt_mul_of_pos_left hd (div_pos hs hrs)
    have he : s/(r+s)*(r+s)=s := by field_simp
    rwa [he] at h

lemma convex_boundary_ball_overlap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) {p q : E} (hp : p ∈ closure U) (hq : q ∈ closure U)
    {r s : ℝ} (hi : (ball p r ∩ ball q s).Nonempty) :
    ((ball p r ∩ ball q s) ∩ U).Nonempty := by
  obtain ⟨x,hxs,hxi⟩ := segment_meets_inter_balls hi
  have hxc := hU.closure.segment_subset hp hq hxs
  obtain ⟨y,hyi,hyU⟩ := mem_closure_iff_nhds.mp hxc (ball p r ∩ ball q s)
    ((isOpen_ball.inter isOpen_ball).mem_nhds hxi)
  exact ⟨y,hyi,hyU⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma box_extend_closure {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (hext : ∀ p ∈ frontier U, ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ U)) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ closure U ⊆ W ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S W F ∧ EqOn F f U := by
  classical
  have hb (p : frontier U) : ∃ a : ℝ, 0 < a ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S (ball (p:ℂ × ℂ) a) F ∧
        EqOn F f (ball (p:ℂ × ℂ) a ∩ U) := by
    obtain ⟨V,hV,hp,F,hF,he⟩ := hext p p.property
    obtain ⟨a,ha,haV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hp)
    exact ⟨a,ha,F,hF.mono haV,he.mono (inter_subset_inter_left U haV)⟩
  choose a ha G hG hGf using hb
  have hGG (p q : frontier U) : EqOn (G p) (G q) (ball (p:ℂ × ℂ) (a p) ∩ ball (q:ℂ × ℂ) (a q)) := by
    by_cases hne : (ball (p:ℂ × ℂ) (a p) ∩ ball (q:ℂ × ℂ) (a q)).Nonempty
    · obtain ⟨z,hzi,hzU⟩ := convex_boundary_ball_overlap hUc
        (frontier_subset_closure p.property) (frontier_subset_closure q.property) hne
      apply holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
        (isOpen_ball.inter isOpen_ball) ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
        ((hG p).1.mono inter_subset_left) ((hG q).1.mono inter_subset_right) hzi
      filter_upwards [(isOpen_ball.inter isOpen_ball |>.inter hU).mem_nhds ⟨hzi,hzU⟩] with w hw
      exact (hGf p ⟨hw.1.1,hw.2⟩).trans (hGf q ⟨hw.1.2,hw.2⟩).symm
    · intro z hz
      exact (hne ⟨z,hz⟩).elim
  let V : Option (frontier U) → Set (ℂ × ℂ)
    | none => U
    | some p => ball (p:ℂ × ℂ) (a p)
  let G' : Option (frontier U) → ℂ × ℂ → X.Carrier
    | none => f
    | some p => G p
  have hVo : ∀ i, IsOpen (V i) := by intro i; cases i with
    | none => exact hU
    | some p => exact isOpen_ball
  have hGb : ∀ i, IsBox S (V i) (G' i) := by intro i; cases i with
    | none => exact hf
    | some p => exact hG p
  have hcompat : ∀ i j, EqOn (G' i) (G' j) (V i ∩ V j) := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact fun _ _ ↦ rfl
      | some q => exact fun z hz ↦ (hGf q ⟨hz.2,hz.1⟩).symm
    | some p =>
      cases j with
      | none => exact hGf p
      | some q => exact hGG p q
  obtain ⟨F,hF,he⟩ := glue_boxes V hVo G' hGb hcompat (f 0)
  refine ⟨⋃ i, V i,isOpen_iUnion hVo,?_,F,hF,he none⟩
  intro p hp
  by_cases hpU : p ∈ U
  · exact mem_iUnion.mpr ⟨none,hpU⟩
  · have hpf : p ∈ frontier U := ⟨hp,by simpa only [hU.interior_eq] using hpU⟩
    exact mem_iUnion.mpr ⟨some ⟨p,hpf⟩,mem_ball_self (ha ⟨p,hpf⟩)⟩

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.DiskAxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma superDomain_axes_of_eventually {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S (superDomain m a) f)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S (ball (0:ℂ) 1) α)
    (hβ : IsVerticalCurve S (ball (0:ℂ) 1) β)
    (he₁ : (fun z : ℂ ↦ f (z,0)) =ᶠ[𝓝 0] α)
    (he₂ : (fun z : ℂ ↦ f (0,z)) =ᶠ[𝓝 0] β) :
    (∀ z, (z,0) ∈ superDomain m a → f (z,0)=α z) ∧
    (∀ z, (0,z) ∈ superDomain m a → f (0,z)=β z) := by
  let L₁ : ℂ →L[ℝ] ℂ × ℂ := (ContinuousLinearMap.id ℝ ℂ).prod 0
  let L₂ : ℂ →L[ℝ] ℂ × ℂ := (0:ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)
  have hD₁ : IsOpen {z : ℂ | (z,0) ∈ superDomain m a} := (superDomain_open m a).preimage L₁.continuous
  have hD₂ : IsOpen {z : ℂ | (0,z) ∈ superDomain m a} := (superDomain_open m a).preimage L₂.continuous
  have hC₁ : Convex ℝ {z : ℂ | (z,0) ∈ superDomain m a} := (superDomain_convex m a).linear_preimage L₁.toLinearMap
  have hC₂ : Convex ℝ {z : ℂ | (0,z) ∈ superDomain m a} := (superDomain_convex m a).linear_preimage L₂.toLinearMap
  constructor
  · exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq hD₁ hC₁.isPreconnected
      (hf.horizontal_slice (superDomain_open m a) 0 (fun _ hz ↦ hz)).1
      (hα.1.mono (fun _ hz ↦ (superDomain_subset_bidisk hm ha1 hz).1))
      (show (0:ℂ) ∈ {z : ℂ | (z,0) ∈ superDomain m a} from superDomain_zero hm ha) he₁
  · exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq hD₂ hC₂.isPreconnected
      (hf.vertical_slice (superDomain_open m a) 0 (fun _ hz ↦ hz)).1
      (hβ.1.mono (fun _ hz ↦ (superDomain_subset_bidisk hm ha1 hz).2))
      (show (0:ℂ) ∈ {z : ℂ | (0,z) ∈ superDomain m a} from superDomain_zero hm ha) he₂

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma superDomain_exhaustion :
    (⋃ m : {m : ℕ // 0 < m}, superDomain m 1) = ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨m,hm⟩ := mem_iUnion.mp hz
    exact superDomain_subset_bidisk m.property (le_refl 1) hm
  intro z hz
  have hn₁ : Complex.normSq z.1 < 1 := by
    have hh : ‖z.1‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz.1
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z.1]
  have hn₂ : Complex.normSq z.2 < 1 := by
    have hh : ‖z.2‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz.2
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z.2]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Complex.normSq_nonneg z.1) hn₁).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one (Complex.normSq_nonneg z.2) hn₂)
  have hev : ∀ᶠ m : ℕ in atTop, superPotential m z < 1 :=
    ht (Iio_mem_nhds (show (0:ℝ)+0 < 1 by norm_num))
  obtain ⟨m,hm,hPm⟩ := (eventually_gt_atTop (0:ℕ) |>.and hev).exists
  exact mem_iUnion.mpr ⟨⟨m,hm⟩,hPm⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.BlockMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def IsBlockBox (S : HolomorphicSplitting X r s) (U : Set (E × F)) (f : E × F → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,E × F) (model n) f U ∧ ∀ z ∈ U,
    (∀ v : E, S.projection (f z) (mfderiv 𝓘(ℂ,E × F) (model n) f z (v,0)) =
      mfderiv 𝓘(ℂ,E × F) (model n) f z (v,0)) ∧
    (∀ w : F, S.projection (f z) (mfderiv 𝓘(ℂ,E × F) (model n) f z (0,w)) = 0)

lemma IsBlockBox.mono {U V : Set (E × F)} {f : E × F → X.Carrier}
    (hf : IsBlockBox S U f) (hV : V ⊆ U) : IsBlockBox S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

lemma SplittingChart.block_coordinates (e : SplittingChart S) {U : Set (E × F)}
    (hU : IsOpen U) {f : E × F → X.Carrier} (hf : IsBlockBox S U f)
    (he : MapsTo f U e.chart.source) :
    DifferentiableOn ℂ (e.chart ∘ f) U ∧ ∀ z ∈ U,
      (∀ v : E, (fderiv ℂ (e.chart ∘ f) z (v,0)).2=0) ∧
      (∀ w : F, (fderiv ℂ (e.chart ∘ f) z (0,w)).1=0) := by
  refine ⟨mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hf.1 he),?_⟩
  intro z hz
  have h := mfderiv_comp z (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (he hz)))
    (hf.1.mdifferentiableAt (hU.mem_nhds hz))
  change (mfderiv 𝓘(ℂ,E × F) 𝓘(ℂ,Model r × Model s) (e.chart ∘ f) z :
    (E × F) →L[ℂ] (Model r × Model s)) =
    (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart (f z)).comp
    (mfderiv 𝓘(ℂ,E × F) (model n) f z) at h
  simp only [mfderiv_eq_fderiv] at h
  rw [h]
  exact ⟨fun v ↦ (e.horizontal _ (he hz) _).mp ((hf.2 z hz).1 v),
    fun w ↦ (e.vertical _ (he hz) _).mp ((hf.2 z hz).2 w)⟩

lemma SplittingChart.block_of_coordinate_tangencies (e : SplittingChart S)
    {U : Set (E × F)} (hU : IsOpen U) {f : E × F → Model r × Model s}
    (hf : DifferentiableOn ℂ f U) (hmap : MapsTo f U e.chart.target)
    (ht : ∀ z ∈ U, (∀ v : E, (fderiv ℂ f z (v,0)).2=0) ∧
      (∀ w : F, (fderiv ℂ f z (0,w)).1=0)) : IsBlockBox S U (e.chart.symm ∘ f) := by
  refine ⟨e.inverse_holomorphic.comp (mdifferentiableOn_iff_differentiableOn.mpr hf) hmap,?_⟩
  intro z hz
  have h := mfderiv_comp z
    (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hf.differentiableAt (hU.mem_nhds hz)))
  change (mfderiv 𝓘(ℂ,E × F) (model n) (e.chart.symm ∘ f) z : (E × F) →L[ℂ] Model n) =
    (mfderiv 𝓘(ℂ,Model r × Model s) (model n) e.chart.symm (f z)).comp
      (mfderiv 𝓘(ℂ,E × F) 𝓘(ℂ,Model r × Model s) f z) at h
  simp only [mfderiv_eq_fderiv] at h
  constructor
  · intro v
    apply (e.horizontal _ (e.chart.map_target (hmap hz)) _).mpr
    rw [h]
    exact (e.inverse_derivative (hmap hz) (fderiv ℂ f z (v,0))) ▸ (ht z hz).1 v
  · intro w
    apply (e.vertical _ (e.chart.map_target (hmap hz)) _).mpr
    rw [h]
    exact (e.inverse_derivative (hmap hz) (fderiv ℂ f z (0,w))) ▸ (ht z hz).2 w

lemma SplittingChart.inverse_isBlockBox (e : SplittingChart S) :
    IsBlockBox S e.chart.target e.chart.symm := by
  simpa only [Function.comp_id] using e.block_of_coordinate_tangencies e.chart.open_target
    differentiable_id.differentiableOn (mapsTo_id _)
    (by intro z _; simp)

lemma SplittingChart.mix_block_maps (e : SplittingChart S) {U : Set (E × F)}
    (hU : IsOpen U) {f g : E × F → X.Carrier} (hf : IsBlockBox S U f) (hg : IsBlockBox S U g)
    (hfe : MapsTo f U e.chart.source) (hge : MapsTo g U e.chart.source) :
    IsBlockBox S U (fun z ↦ e.chart.symm ((e.chart (f z)).1,(e.chart (g z)).2)) := by
  have hfc := e.block_coordinates hU hf hfe
  have hgc := e.block_coordinates hU hg hge
  let k : E × F → Model r × Model s := fun z ↦ ((e.chart (f z)).1,(e.chart (g z)).2)
  have hk : DifferentiableOn ℂ k U := hfc.1.fst.prodMk hgc.1.snd
  apply e.block_of_coordinate_tangencies hU hk
  · intro z hz
    have hfT := e.chart.map_source (hfe hz)
    have hgT := e.chart.map_source (hge hz)
    rw [e.product_range] at hfT hgT ⊢
    exact ⟨hfT.1,hgT.2⟩
  · intro z hz
    have hd₁ := (hfc.1.differentiableAt (hU.mem_nhds hz)).hasFDerivAt.fst
    have hd₂ := (hgc.1.differentiableAt (hU.mem_nhds hz)).hasFDerivAt.snd
    have hd := (hd₁.prodMk hd₂).fderiv
    change fderiv ℂ k z = _ at hd
    rw [hd]
    exact ⟨fun v ↦ (hgc.2 z hz).1 v,fun w ↦ (hfc.2 z hz).2 w⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

def IsHorizontalMap (S : HolomorphicSplitting X r s) (U : Set E) (f : E → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,E) (model n) f U ∧ ∀ z ∈ U, ∀ v : E,
    S.projection (f z) (mfderiv 𝓘(ℂ,E) (model n) f z v) = mfderiv 𝓘(ℂ,E) (model n) f z v

def IsVerticalMap (S : HolomorphicSplitting X r s) (U : Set E) (f : E → X.Carrier) : Prop :=
  MDifferentiableOn 𝓘(ℂ,E) (model n) f U ∧ ∀ z ∈ U, ∀ v : E,
    S.projection (f z) (mfderiv 𝓘(ℂ,E) (model n) f z v) = 0

lemma IsHorizontalMap.comp {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → X.Carrier} (hf : IsHorizontalMap S U f) {q : F → E}
    (hq : DifferentiableOn ℂ q V) (hmap : MapsTo q V U) : IsHorizontalMap S V (f ∘ q) := by
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq) hmap,?_⟩
  intro z hz v
  rw [mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq.differentiableAt (hV.mem_nhds hz)))]
  exact hf.2 _ (hmap hz) _

lemma IsVerticalMap.comp {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → X.Carrier} (hf : IsVerticalMap S U f) {q : F → E}
    (hq : DifferentiableOn ℂ q V) (hmap : MapsTo q V U) : IsVerticalMap S V (f ∘ q) := by
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq) hmap,?_⟩
  intro z hz v
  rw [mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq.differentiableAt (hV.mem_nhds hz)))]
  exact hf.2 _ (hmap hz) _

lemma IsHorizontalMap.curve {U : Set ℂ} {f : ℂ → X.Carrier} (hf : IsHorizontalMap S U f) :
    IsHorizontalCurve S U f := ⟨hf.1,fun z hz ↦ hf.2 z hz 1⟩

lemma IsVerticalMap.curve {U : Set ℂ} {f : ℂ → X.Carrier} (hf : IsVerticalMap S U f) :
    IsVerticalCurve S U f := ⟨hf.1,fun z hz ↦ hf.2 z hz 1⟩

lemma IsHorizontalMap.block {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → X.Carrier} (hf : IsHorizontalMap S U f) :
    IsBlockBox S (U ×ˢ V) (fun z : E × F ↦ f z.1) := by
  have hc := hf.comp hU (hU.prod hV) differentiable_fst.differentiableOn
    (show MapsTo Prod.fst (U ×ˢ V) U from fun _ h ↦ h.1)
  refine ⟨hc.1,fun z hz ↦ ⟨fun v ↦ hc.2 z hz (v,0),fun w ↦ ?_⟩⟩
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds hz.1))
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst)
  change (mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.fst) z : (E × F) →L[ℂ] Model n) = _ at hd
  let P : Model n →L[ℂ] Model n := S.projection (f z.1)
  change P ((mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.fst) z : (E × F) →L[ℂ] Model n) (0,w)) = 0
  rw [hd]
  simp only [mfderiv_eq_fderiv,fderiv_fst]
  change P ((mfderiv 𝓘(ℂ,E) (model n) f z.1 : E →L[ℂ] Model n) 0) = 0
  rw [map_zero]
  exact P.map_zero

lemma IsVerticalMap.block {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : F → X.Carrier} (hf : IsVerticalMap S V f) :
    IsBlockBox S (U ×ˢ V) (fun z : E × F ↦ f z.2) := by
  have hc := hf.comp hV (hU.prod hV) differentiable_snd.differentiableOn
    (show MapsTo Prod.snd (U ×ˢ V) V from fun _ h ↦ h.2)
  refine ⟨hc.1,fun z hz ↦ ⟨fun v ↦ ?_,fun w ↦ hc.2 z hz (0,w)⟩⟩
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt (hV.mem_nhds hz.2))
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_snd)
  change (mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.snd) z : (E × F) →L[ℂ] Model n) = _ at hd
  let P : Model n →L[ℂ] Model n := S.projection (f z.2)
  change P ((mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.snd) z : (E × F) →L[ℂ] Model n) (v,0)) =
    (mfderiv 𝓘(ℂ,E × F) (model n) (f ∘ Prod.snd) z : (E × F) →L[ℂ] Model n) (v,0)
  rw [hd]
  simp only [mfderiv_eq_fderiv,fderiv_snd]
  change P ((mfderiv 𝓘(ℂ,F) (model n) f z.2 : F →L[ℂ] Model n) 0) =
    (mfderiv 𝓘(ℂ,F) (model n) f z.2 : F →L[ℂ] Model n) 0
  rw [map_zero]
  exact P.map_zero

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F A B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup A] [NormedSpace ℂ A]
 [NormedAddCommGroup B] [NormedSpace ℂ B]

lemma IsBlockBox.comp_parameters {U : Set E} {V : Set F} {W : Set A} {Z : Set B}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hZ : IsOpen Z)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f)
    {a : A → E} {b : B → F} (ha : DifferentiableOn ℂ a W) (hb : DifferentiableOn ℂ b Z)
    (hma : MapsTo a W U) (hmb : MapsTo b Z V) :
    IsBlockBox S (W ×ˢ Z) (f ∘ Prod.map a b) := by
  have hq : DifferentiableOn ℂ (Prod.map a b) (W ×ˢ Z) :=
    (ha.comp differentiable_fst.differentiableOn (fun _ h ↦ h.1)).prodMk
      (hb.comp differentiable_snd.differentiableOn (fun _ h ↦ h.2))
  have hqm : MapsTo (Prod.map a b) (W ×ˢ Z) (U ×ˢ V) := fun _ h ↦ ⟨hma h.1,hmb h.2⟩
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq) hqm,?_⟩
  intro z hz
  have had := ha.differentiableAt (hW.mem_nhds hz.1)
  have hbd := hb.differentiableAt (hZ.mem_nhds hz.2)
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt ((hU.prod hV).mem_nhds (hqm hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (HasFDerivAt.prodMap z had.hasFDerivAt hbd.hasFDerivAt).differentiableAt)
  let D : (E × F) →L[ℂ] Model n := mfderiv 𝓘(ℂ,E × F) (model n) f (a z.1,b z.2)
  let P : Model n →L[ℂ] Model n := S.projection (f (a z.1,b z.2))
  let M : (A × B) →L[ℂ] Model n := mfderiv 𝓘(ℂ,A × B) (model n) (f ∘ Prod.map a b) z
  have hM : M = D.comp ((fderiv ℂ a z.1).prodMap (fderiv ℂ b z.2)) := by
    change M = D.comp (mfderiv 𝓘(ℂ,A × B) 𝓘(ℂ,E × F) (Prod.map a b) z) at hd
    rw [mfderiv_eq_fderiv,(HasFDerivAt.prodMap z had.hasFDerivAt hbd.hasFDerivAt).fderiv] at hd
    exact hd
  change (∀ v : A, P (M (v,0))=M (v,0)) ∧ (∀ w : B, P (M (0,w))=0)
  rw [hM]
  constructor
  · intro v
    change P (D (fderiv ℂ a z.1 v,fderiv ℂ b z.2 0))=D (fderiv ℂ a z.1 v,fderiv ℂ b z.2 0)
    rw [map_zero]
    exact (hf.2 (a z.1,b z.2) (hqm hz)).1 _
  · intro w
    change P (D (fderiv ℂ a z.1 0,fderiv ℂ b z.2 w))=0
    rw [map_zero]
    exact (hf.2 (a z.1,b z.2) (hqm hz)).2 _

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma IsBlockBox.horizontal_slice {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f) {b : F} (hb : b ∈ V) :
    IsHorizontalMap S U (fun a ↦ f (a,b)) := by
  let q : E → E × F := fun a ↦ (a,b)
  have hq : Differentiable ℂ q := differentiable_id.prodMk (differentiable_const b)
  have hmap : MapsTo q U (U ×ˢ V) := fun _ h ↦ ⟨h,hb⟩
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq.differentiableOn) hmap,?_⟩
  intro z hz v
  let P : Model n →L[ℂ] Model n := S.projection (f (z,b))
  let D : (E × F) →L[ℂ] Model n := mfderiv 𝓘(ℂ,E × F) (model n) f (z,b)
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt ((hU.prod hV).mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq z))
  change (mfderiv 𝓘(ℂ,E) (model n) (f ∘ q) z : E →L[ℂ] Model n) =
    D.comp (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E × F) q z) at hd
  rw [mfderiv_eq_fderiv] at hd
  have hqd : fderiv ℂ q z=(ContinuousLinearMap.id ℂ E).prod 0 := by
    exact ((hasFDerivAt_id z).prodMk (hasFDerivAt_const b z)).fderiv
  rw [hqd] at hd
  change P ((mfderiv 𝓘(ℂ,E) (model n) (f ∘ q) z : E →L[ℂ] Model n) v)=
    (mfderiv 𝓘(ℂ,E) (model n) (f ∘ q) z : E →L[ℂ] Model n) v
  rw [hd]
  exact (hf.2 (z,b) ⟨hz,hb⟩).1 v

lemma IsBlockBox.vertical_slice {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f) {a : E} (ha : a ∈ U) :
    IsVerticalMap S V (fun b ↦ f (a,b)) := by
  let q : F → E × F := fun b ↦ (a,b)
  have hq : Differentiable ℂ q := (differentiable_const a).prodMk differentiable_id
  have hmap : MapsTo q V (U ×ˢ V) := fun _ h ↦ ⟨ha,h⟩
  refine ⟨hf.1.comp (mdifferentiableOn_iff_differentiableOn.mpr hq.differentiableOn) hmap,?_⟩
  intro z hz v
  let P : Model n →L[ℂ] Model n := S.projection (f (a,z))
  let D : (E × F) →L[ℂ] Model n := mfderiv 𝓘(ℂ,E × F) (model n) f (a,z)
  have hd := mfderiv_comp z (hf.1.mdifferentiableAt ((hU.prod hV).mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hq z))
  change (mfderiv 𝓘(ℂ,F) (model n) (f ∘ q) z : F →L[ℂ] Model n) =
    D.comp (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,E × F) q z) at hd
  rw [mfderiv_eq_fderiv] at hd
  have hqd : fderiv ℂ q z=(0 : F →L[ℂ] E).prod (ContinuousLinearMap.id ℂ F) := by
    exact ((hasFDerivAt_const a z).prodMk (hasFDerivAt_id z)).fderiv
  rw [hqd] at hd
  change P ((mfderiv 𝓘(ℂ,F) (model n) (f ∘ q) z : F →L[ℂ] Model n) v)=0
  rw [hd]
  exact (hf.2 (a,z) ⟨ha,hz⟩).2 v

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

abbrev Polydisk (d : ℕ) := ball (0 : Model d) (1 : ℝ)

def SplittingChart.unitMap (e : SplittingChart S) : Model r × Model s → X.Carrier :=
  fun z ↦ e.chart.symm ((e.radius : ℂ) • z.1,(e.radius : ℂ) • z.2)

lemma scale_mem_ball {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {z : Model d}
    (hz : z ∈ Polydisk d) : (ρ : ℂ) • z ∈ ball 0 ρ := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
  nlinarith

lemma unscale_mem_ball {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {z : Model d}
    (hz : z ∈ ball 0 ρ) : (ρ : ℂ)⁻¹ • z ∈ Polydisk d := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
  exact (inv_mul_lt_iff₀ hρ).mpr (by simpa using hz)

lemma SplittingChart.unitMap_block (e : SplittingChart S) :
    IsBlockBox S (Polydisk r ×ˢ Polydisk s) e.unitMap := by
  have he : IsBlockBox S (ball 0 e.radius ×ˢ ball 0 e.radius) e.chart.symm := by
    simpa only [e.product_range] using e.inverse_isBlockBox
  exact he.comp_parameters isOpen_ball isOpen_ball isOpen_ball isOpen_ball
    (differentiable_id.const_smul (e.radius : ℂ)).differentiableOn
    (differentiable_id.const_smul (e.radius : ℂ)).differentiableOn
    (fun _ h ↦ scale_mem_ball e.radius_pos h) (fun _ h ↦ scale_mem_ball e.radius_pos h)

lemma SplittingChart.unitMap_coordinates (e : SplittingChart S) {x : X.Carrier}
    (hx : x ∈ e.chart.source) :
    e.unitMap ((e.radius : ℂ)⁻¹ • (e.chart x).1,(e.radius : ℂ)⁻¹ • (e.chart x).2)=x := by
  have hr : (e.radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr e.radius_pos.ne'
  simpa only [SplittingChart.unitMap,smul_smul,mul_inv_cancel₀ hr,one_smul] using
    e.chart.left_inv hx

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ContinuousBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped unitInterval

namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

def IsBox (atlas : Set (OpenPartialHomeomorph X (C × D))) (F : A × B → X) : Prop :=
  Continuous F ∧ ∀ e ∈ atlas,
    (∀ a, IsLocallyConstant (fun b : {b : B // F (a,b) ∈ e.source} ↦ (e (F (a,b))).1)) ∧
    (∀ b, IsLocallyConstant (fun a : {a : A // F (a,b) ∈ e.source} ↦ (e (F (a,b))).2))

lemma IsBox.separated {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {F : A × B → X} (hF : IsBox atlas F) {e : OpenPartialHomeomorph X (C × D)}
    (he : e ∈ atlas) {U : Set A} {V : Set B} (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hmap : MapsTo F (U ×ˢ V) e.source) {a a₀ : A} {b b₀ : B}
    (ha : a ∈ U) (ha₀ : a₀ ∈ U) (hb : b ∈ V) (hb₀ : b₀ ∈ V) :
    e (F (a,b)) = ((e (F (a,b₀))).1,(e (F (a₀,b))).2) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hV
  have h₁ : IsLocallyConstant (fun b : V ↦ (e (F (a,b))).1) :=
    ((hF.2 e he).1 a).comp_continuous (continuous_subtype_val.subtype_mk
      (fun b ↦ hmap ⟨ha,b.property⟩))
  have h₂ : IsLocallyConstant (fun a : U ↦ (e (F (a,b))).2) :=
    ((hF.2 e he).2 b).comp_continuous (continuous_subtype_val.subtype_mk
      (fun a ↦ hmap ⟨a.property,hb⟩))
  exact Prod.ext (h₁.apply_eq_of_preconnectedSpace ⟨b,hb⟩ ⟨b₀,hb₀⟩)
    (h₂.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨a₀,ha₀⟩)

theorem unique [T2Space X] (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source)
    {F G : I × I → X} (hF : IsBox atlas F) (hG : IsBox atlas G)
    (hbottom : ∀ a, F (a,0)=G (a,0)) (hleft : ∀ b, F (0,b)=G (0,b)) : F = G := by
  classical
  let c : Option atlas → Set (I × I)
    | none => {p | F p ≠ G p}
    | some e => F ⁻¹' e.val.source ∩ G ⁻¹' e.val.source
  have hc : ∀ i, IsOpen (c i) := by
    rintro (_|e)
    · exact (isClosed_eq hF.1 hG.1).isOpen_compl
    · exact (e.val.open_source.preimage hF.1).inter (e.val.open_source.preimage hG.1)
  have hcU : univ ⊆ ⋃ i, c i := by
    intro p _
    by_cases hp : F p = G p
    · obtain ⟨e,he,hpe⟩ := hcover (F p)
      exact mem_iUnion.mpr ⟨some ⟨e,he⟩,hpe,show G p ∈ e.source from hp ▸ hpe⟩
    · exact mem_iUnion.mpr ⟨none,hp⟩
  obtain ⟨t,ht0,htmono,⟨N,hN⟩,ht⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc hcU
  have hprefix : ∀ i j, EqOn F G (Icc 0 (t i) ×ˢ Icc 0 (t j)) := by
    intro i
    induction i with
    | zero =>
      intro j p hp
      have hp0 : p.1 = 0 := le_antisymm (ht0 ▸ hp.1.2) hp.1.1
      change F (p.1,p.2)=G (p.1,p.2)
      rw [hp0]
      exact hleft p.2
    | succ i hi =>
      intro j
      induction j with
      | zero =>
        intro p hp
        have hp0 : p.2 = 0 := le_antisymm (ht0 ▸ hp.2.2) hp.2.1
        change F (p.1,p.2)=G (p.1,p.2)
        rw [hp0]
        exact hbottom p.1
      | succ j hj =>
        intro p hp
        by_cases hpi : p.1 ≤ t i
        · exact hi (j+1) ⟨⟨hp.1.1,hpi⟩,hp.2⟩
        by_cases hpj : p.2 ≤ t j
        · exact hj ⟨hp.1,⟨hp.2.1,hpj⟩⟩
        have hti : t i ≤ t (i+1) := htmono (Nat.le_succ i)
        have htj : t j ≤ t (j+1) := htmono (Nat.le_succ j)
        have hcorner : F (t i,t j)=G (t i,t j) := hi j ⟨⟨bot_le,le_rfl⟩,⟨bot_le,le_rfl⟩⟩
        obtain ⟨k,hk⟩ := ht i j
        cases k with
        | none => exact False.elim ((hk ⟨⟨le_rfl,hti⟩,⟨le_rfl,htj⟩⟩) hcorner)
        | some e =>
          have hmapF : MapsTo F (Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1))) e.val.source :=
            fun _ h ↦ (hk h).1
          have hmapG : MapsTo G (Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1))) e.val.source :=
            fun _ h ↦ (hk h).2
          have hpa : p.1 ∈ Icc (t i) (t (i+1)) := ⟨(not_le.mp hpi).le,hp.1.2⟩
          have hpb : p.2 ∈ Icc (t j) (t (j+1)) := ⟨(not_le.mp hpj).le,hp.2.2⟩
          have ha0 : t i ∈ Icc (t i) (t (i+1)) := ⟨le_rfl,hti⟩
          have hb0 : t j ∈ Icc (t j) (t (j+1)) := ⟨le_rfl,htj⟩
          apply e.val.injOn (hmapF ⟨hpa,hpb⟩) (hmapG ⟨hpa,hpb⟩)
          rw [hF.separated e.property isPreconnected_Icc isPreconnected_Icc hmapF hpa ha0 hpb hb0,
            hG.separated e.property isPreconnected_Icc isPreconnected_Icc hmapG hpa ha0 hpb hb0]
          have hbEq : F (p.1,t j)=G (p.1,t j) := hj ⟨hp.1,⟨bot_le,le_rfl⟩⟩
          have hlEq : F (t i,p.2)=G (t i,p.2) := hi (j+1) ⟨⟨bot_le,le_rfl⟩,hp.2⟩
          rw [hbEq,hlEq]
  funext p
  exact hprefix N N (by simpa only [hN N le_rfl] using
    (show p ∈ Icc (0:I) 1 ×ˢ Icc (0:I) 1 from ⟨⟨bot_le,le_top⟩,⟨bot_le,le_top⟩⟩))

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

lemma locallyConstant_of_finite_closed_cover {ι Y : Type*} [Finite ι]
    (U : ι → Set A) (hU : ∀ i, IsClosed (U i)) (hcover : ∀ a, ∃ i, a ∈ U i)
    {f : A → Y} (hf : ∀ i, IsLocallyConstant (fun a : U i ↦ f a)) : IsLocallyConstant f := by
  intro W
  have heq : (f ⁻¹' W)ᶜ = ⋃ i, Subtype.val '' ((fun a : U i ↦ f a) ⁻¹' Wᶜ) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,hi⟩ := hcover a
      exact mem_iUnion.mpr ⟨i,⟨⟨a,hi⟩,ha,rfl⟩⟩
    · rintro ⟨_,⟨i,rfl⟩,⟨a,ha,rfl⟩⟩
      exact ha
  rw [← isClosed_compl_iff,heq]
  apply isClosed_iUnion_of_finite
  intro i
  exact (hU i).isClosedMap_subtype_val _ ((hf i W).isClosed_compl)

lemma locallyConstant_source_of_finite_closed_cover {ι Y : Type*} [Finite ι]
    (U : ι → Set A) (hU : ∀ i, IsClosed (U i)) (hcover : ∀ a, ∃ i, a ∈ U i)
    (p : A → Prop) {f : A → Y}
    (hf : ∀ i, IsLocallyConstant (fun a : {a : U i // p a} ↦ f a)) :
    IsLocallyConstant (fun a : {a : A // p a} ↦ f a) := by
  apply locallyConstant_of_finite_closed_cover
    (fun i ↦ Subtype.val ⁻¹' U i) (fun i ↦ (hU i).preimage continuous_subtype_val)
    (fun a ↦ hcover a)
  intro i
  let g : {a : {a : A // p a} // a.val ∈ U i} → {a : U i // p a} :=
    fun a ↦ ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  have hg : Continuous g := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  exact (hf i).comp_continuous hg

lemma IsBox.precomp {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {F : A × B → X} (hF : IsBox atlas F) {A' B' : Type*}
    [TopologicalSpace A'] [TopologicalSpace B'] {a : A' → A} {b : B' → B}
    (ha : Continuous a) (hb : Continuous b) :
    IsBox atlas (fun p : A' × B' ↦ F (a p.1,b p.2)) := by
  refine ⟨hF.1.comp (ha.prodMap hb),?_⟩
  intro e he
  constructor
  · intro x
    exact ((hF.2 e he).1 (a x)).comp_continuous
      ((hb.comp continuous_subtype_val).subtype_mk (fun y ↦ y.property))
  · intro y
    exact ((hF.2 e he).2 (b y)).comp_continuous
      ((ha.comp continuous_subtype_val).subtype_mk (fun x ↦ x.property))

lemma IsBox.of_closed_rectangles {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {F : A × B → X} (hF : Continuous F) {ι : Type*} [Finite ι]
    (U : ι → Set A) (V : ι → Set B) (hU : ∀ i, IsClosed (U i)) (hV : ∀ i, IsClosed (V i))
    (hcover : ∀ p : A × B, ∃ i, p ∈ U i ×ˢ V i)
    (hf : ∀ i, IsBox atlas (fun p : U i × V i ↦ F (p.1,p.2))) : IsBox atlas F := by
  refine ⟨hF,fun e he ↦ ⟨?_,?_⟩⟩
  · intro a
    apply locallyConstant_source_of_finite_closed_cover (f := fun b ↦ (e (F (a,b))).1)
      (fun i : {i : ι // a ∈ U i} ↦ V i) (fun i ↦ hV i)
      (fun b ↦ by obtain ⟨i,hi⟩ := hcover (a,b); exact ⟨⟨i,hi.1⟩,hi.2⟩)
      (fun b ↦ F (a,b) ∈ e.source)
    intro i
    exact ((hf i).2 e he).1 ⟨a,i.property⟩
  · intro b
    apply locallyConstant_source_of_finite_closed_cover (f := fun a ↦ (e (F (a,b))).2)
      (fun i : {i : ι // b ∈ V i} ↦ U i) (fun i ↦ hU i)
      (fun a ↦ by obtain ⟨i,hi⟩ := hcover (a,b); exact ⟨⟨i,hi.2⟩,hi.1⟩)
      (fun a ↦ F (a,b) ∈ e.source)
    intro i
    exact ((hf i).2 e he).2 ⟨b,i.property⟩

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma locallyConstant_restrict_of_fderiv_zero {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup K] [NormedSpace ℂ K]
    {U : Set H} (hU : IsOpen U) {f : H → K} (hf : DifferentiableOn ℂ f U)
    (hd : ∀ x ∈ U, fderiv ℂ f x = 0) : IsLocallyConstant (fun x : U ↦ f x) := by
  intro W
  have hW := hU.isOpen_inter_preimage_of_fderiv_eq_zero hf hd W
  convert hW.preimage (continuous_subtype_val : Continuous (Subtype.val : U → H)) using 1
  ext x
  simp

def splittingAtlas (S : HolomorphicSplitting X r s) :
    Set (OpenPartialHomeomorph X.Carrier (Model r × Model s)) :=
  Set.range (fun e : SplittingChart S ↦ e.chart)

lemma IsBlockBox.plaqueBox {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {f : E × F → X.Carrier} (hf : IsBlockBox S (U ×ˢ V) f) :
    ProductBoxTopology.IsBox (splittingAtlas S) (fun p : U × V ↦ f (p.1,p.2)) := by
  have hcont : ContinuousOn f (U ×ˢ V) := hf.1.continuousOn
  refine ⟨hcont.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)
    (fun p ↦ ⟨p.1.property,p.2.property⟩),?_⟩
  rintro _ ⟨e,rfl⟩
  let W : Set (E × F) := (U ×ˢ V) ∩ f ⁻¹' e.chart.source
  have hW : IsOpen W := hcont.isOpen_inter_preimage (hU.prod hV) e.chart.open_source
  have hc := e.block_coordinates hW (hf.mono inter_subset_left)
    (show MapsTo f W e.chart.source from fun _ h ↦ h.2)
  constructor
  · intro a
    let T : Set F := V ∩ (fun b ↦ f (a,b)) ⁻¹' e.chart.source
    have hT : IsOpen T := (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ h ↦ ⟨a.property,h⟩)).isOpen_inter_preimage hV e.chart.open_source
    have hd (b : F) (hb : b ∈ T) : HasFDerivAt (fun b ↦ (e.chart (f (a,b))).1) (0 : F →L[ℂ] Model r) b := by
      have hab : ((a:E),b) ∈ W := ⟨⟨a.property,hb.1⟩,hb.2⟩
      have hg := (hc.1.differentiableAt (hW.mem_nhds hab)).hasFDerivAt.fst.comp b
        ((hasFDerivAt_const (𝕜 := ℂ) (a:E) b).prodMk (hasFDerivAt_id (𝕜 := ℂ) b))
      have heq : ((ContinuousLinearMap.fst ℂ (Model r) (Model s)).comp
          (fderiv ℂ (e.chart ∘ f) ((a:E),b))).comp
          ((0 : F →L[ℂ] E).prod (ContinuousLinearMap.id ℂ F)) = 0 := by
        apply ContinuousLinearMap.ext
        intro w
        exact (hc.2 _ hab).2 w
      rw [heq] at hg
      exact hg
    have hl := locallyConstant_restrict_of_fderiv_zero hT
      (fun b hb ↦ (hd b hb).differentiableAt.differentiableWithinAt) (fun b hb ↦ (hd b hb).fderiv)
    exact hl.comp_continuous ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun b ↦ ⟨b.val.property,b.property⟩))
  · intro b
    let T : Set E := U ∩ (fun a ↦ f (a,b)) ⁻¹' e.chart.source
    have hT : IsOpen T := (hcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ h ↦ ⟨h,b.property⟩)).isOpen_inter_preimage hU e.chart.open_source
    have hd (a : E) (ha : a ∈ T) : HasFDerivAt (fun a ↦ (e.chart (f (a,b))).2) (0 : E →L[ℂ] Model s) a := by
      have hab : (a,(b:F)) ∈ W := ⟨⟨ha.1,b.property⟩,ha.2⟩
      have hg := (hc.1.differentiableAt (hW.mem_nhds hab)).hasFDerivAt.snd.comp a
        ((hasFDerivAt_id (𝕜 := ℂ) a).prodMk (hasFDerivAt_const (𝕜 := ℂ) (b:F) a))
      have heq : ((ContinuousLinearMap.snd ℂ (Model r) (Model s)).comp
          (fderiv ℂ (e.chart ∘ f) (a,(b:F)))).comp
          ((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] F)) = 0 := by
        apply ContinuousLinearMap.ext
        intro v
        exact (hc.2 _ hab).1 v
      rw [heq] at hg
      exact hg
    have hl := locallyConstant_restrict_of_fderiv_zero hT
      (fun a ha ↦ (hd a ha).differentiableAt.differentiableWithinAt) (fun a ha ↦ (hd a ha).fderiv)
    exact hl.comp_continuous ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun a ↦ ⟨a.val.property,a.property⟩))

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

lemma unique_paths [T2Space X] (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source)
    {F G : A × B → X} (hF : IsBox atlas F) (hG : IsBox atlas G)
    {a₀ a : A} {b₀ b : B} (α : Path a₀ a) (β : Path b₀ b)
    (hbottom : ∀ a, F (a,b₀)=G (a,b₀)) (hleft : ∀ b, F (a₀,b)=G (a₀,b)) :
    F (a,b)=G (a,b) := by
  have h := unique atlas hcover (hF.precomp α.continuous β.continuous)
    (hG.precomp α.continuous β.continuous)
    (fun s ↦ by simpa using hbottom (α s))
    (fun t ↦ by simpa using hleft (β t))
  simpa using congrFun h (1,1)

lemma unique_connected [T2Space X] [PathConnectedSpace A] [PathConnectedSpace B]
    (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source)
    {F G : A × B → X} (hF : IsBox atlas F) (hG : IsBox atlas G)
    (a₀ : A) (b₀ : B)
    (hbottom : ∀ a, F (a,b₀)=G (a,b₀)) (hleft : ∀ b, F (a₀,b)=G (a₀,b)) : F=G := by
  funext p
  exact unique_paths atlas hcover hF hG (PathConnectedSpace.somePath a₀ p.1)
    (PathConnectedSpace.somePath b₀ p.2) hbottom hleft

lemma pathConnected_Icc_unit {a b : I} (hab : a ≤ b) : PathConnectedSpace (Icc a b) := by
  refine ⟨⟨⟨a,le_rfl,hab⟩⟩,fun x y ↦ ?_⟩
  have hm (t : I) : Icc.convexComb x.val y.val t ∈ Icc a b := by
    constructor
    · change (a:ℝ) ≤ (1-(t:ℝ))*(x.val:ℝ)+(t:ℝ)*(y.val:ℝ)
      have hx : (a:ℝ) ≤ (x.val:ℝ) := x.property.1
      have hy : (a:ℝ) ≤ (y.val:ℝ) := y.property.1
      nlinarith [t.property.1,t.property.2]
    · change (1-(t:ℝ))*(x.val:ℝ)+(t:ℝ)*(y.val:ℝ) ≤ (b:ℝ)
      have hx : (x.val:ℝ) ≤ (b:ℝ) := x.property.2
      have hy : (y.val:ℝ) ≤ (b:ℝ) := y.property.2
      nlinarith [t.property.1,t.property.2]
  exact ⟨⟨⟨fun t ↦ ⟨Icc.convexComb x.val y.val t,hm t⟩,
    (Icc.continuous_convexComb x.val y.val).subtype_mk _⟩,
    by ext; simp,by ext; simp⟩⟩

end ProductBoxTopology
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PlaqueCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {P A B X C D : Type*} [TopologicalSpace P] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

structure ProductChart (atlas : Set (OpenPartialHomeomorph X (C × D))) where
  chart : OpenPartialHomeomorph X (C × D)
  mem_atlas : chart ∈ atlas
  first : Set C
  second : Set D
  product_range : chart.target = first ×ˢ second
  inverse_box : IsBox atlas (fun p : first × second ↦ chart.symm (p.1,p.2))

lemma ProductChart.parameter_tile [T2Space X] [CompactSpace A] [CompactSpace B]
    [PathConnectedSpace A] [PathConnectedSpace B]
    {atlas : Set (OpenPartialHomeomorph X (C × D))}
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source) (e : ProductChart atlas)
    {R : P → A × B → X} (hR : ∀ p, IsBox atlas (R p)) (p₀ : P) (a₀ : A) (b₀ : B)
    (hbottom : Continuous (fun z : P × A ↦ R z.1 (z.2,b₀)))
    (hleft : Continuous (fun z : P × B ↦ R z.1 (a₀,z.2)))
    (he : ∀ w, R p₀ w ∈ e.chart.source) :
    ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧
      Continuous (fun z : U × (A × B) ↦ R z.1 z.2) := by
  have hb : ∀ᶠ p in 𝓝 p₀, ∀ a, R p (a,b₀) ∈ e.chart.source := by
    simpa only [mem_univ,forall_true_left] using
      isCompact_univ.eventually_forall_of_forall_eventually
        (fun a _ ↦ hbottom.continuousAt.eventually (e.chart.open_source.mem_nhds (he (a,b₀))))
  have hl : ∀ᶠ p in 𝓝 p₀, ∀ b, R p (a₀,b) ∈ e.chart.source := by
    simpa only [mem_univ,forall_true_left] using
      isCompact_univ.eventually_forall_of_forall_eventually
        (fun b _ ↦ hleft.continuousAt.eventually (e.chart.open_source.mem_nhds (he (a₀,b))))
  obtain ⟨U,hUsub,hU,hpU⟩ := mem_nhds_iff.mp (hb.and hl)
  have hbU (p : U) (a : A) : R p (a,b₀) ∈ e.chart.source := (hUsub p.property).1 a
  have hlU (p : U) (b : B) : R p (a₀,b) ∈ e.chart.source := (hUsub p.property).2 b
  let f : U × A → C := fun z ↦ (e.chart (R z.1 (z.2,b₀))).1
  let g : U × B → D := fun z ↦ (e.chart (R z.1 (a₀,z.2))).2
  have hf : Continuous f := (e.chart.continuousOn.comp_continuous
    (hbottom.comp (continuous_subtype_val.prodMap continuous_id)) (fun z ↦ hbU z.1 z.2)).fst
  have hg : Continuous g := (e.chart.continuousOn.comp_continuous
    (hleft.comp (continuous_subtype_val.prodMap continuous_id)) (fun z ↦ hlU z.1 z.2)).snd
  have hfmem (z : U × A) : f z ∈ e.first := by
    have h := e.chart.map_source (hbU z.1 z.2)
    rw [e.product_range] at h
    exact h.1
  have hgmem (z : U × B) : g z ∈ e.second := by
    have h := e.chart.map_source (hlU z.1 z.2)
    rw [e.product_range] at h
    exact h.2
  let M : U → A × B → X := fun p w ↦ e.chart.symm (f (p,w.1),g (p,w.2))
  have hM : ∀ p, IsBox atlas (M p) := by
    intro p
    exact e.inverse_box.precomp
      ((hf.comp (continuous_const.prodMk continuous_id)).subtype_mk (fun a ↦ hfmem (p,a)))
      ((hg.comp (continuous_const.prodMk continuous_id)).subtype_mk (fun b ↦ hgmem (p,b)))
  have hEq (p : U) : R p = M p := by
    apply unique_connected atlas hcover (hR p) (hM p) a₀ b₀
    · intro a
      have hs := (hR p).separated e.mem_atlas isPreconnected_univ isPreconnected_singleton
        (U := univ) (V := {b₀})
        (fun w hw ↦ by rcases w with ⟨a,b⟩; have h : b=b₀ := hw.2; subst b; exact hbU p a)
        (a := a) (a₀ := a₀) (b := b₀) (b₀ := b₀) trivial trivial rfl rfl
      change R p (a,b₀)=e.chart.symm ((e.chart (R p (a,b₀))).1,(e.chart (R p (a₀,b₀))).2)
      rw [← hs,e.chart.left_inv (hbU p a)]
    · intro b
      have hs := (hR p).separated e.mem_atlas isPreconnected_singleton isPreconnected_univ
        (U := {a₀}) (V := univ)
        (fun w hw ↦ by rcases w with ⟨a,b⟩; have h : a=a₀ := hw.1; subst a; exact hlU p b)
        (a := a₀) (a₀ := a₀) (b := b) (b₀ := b₀) rfl rfl trivial trivial
      change R p (a₀,b)=e.chart.symm ((e.chart (R p (a₀,b₀))).1,(e.chart (R p (a₀,b))).2)
      rw [← hs,e.chart.left_inv (hlU p b)]
  refine ⟨U,hU,hpU,?_⟩
  have hMc : Continuous (fun z : U × (A × B) ↦ M z.1 z.2) :=
    e.chart.continuousOn_symm.comp_continuous
      ((hf.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
        (hg.comp (continuous_fst.prodMk continuous_snd.snd)))
      (fun z ↦ e.product_range ▸ ⟨hfmem (z.1,z.2.1),hgmem (z.1,z.2.2)⟩)
  exact hMc.congr (fun z ↦ congrFun (hEq z.1).symm z.2)

end ProductBoxTopology
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.isBlockBox {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) : IsBlockBox S U f := by
  refine ⟨hf.1,fun z hz ↦ ⟨?_,?_⟩⟩
  · intro v
    let D : (ℂ × ℂ) →L[ℂ] Model n := mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z
    let P : Model n →L[ℂ] Model n := S.projection (f z)
    change P (D (v,0)) = D (v,0)
    have hd : D (v,0) = v • D (1,0) := by
      simpa only [Prod.smul_mk,smul_eq_mul,mul_one,mul_zero,smul_zero] using D.map_smul v (1,0)
    rw [hd,P.map_smul]
    exact congrArg (fun x ↦ v • x) (hf.2 z hz).1
  · intro w
    let D : (ℂ × ℂ) →L[ℂ] Model n := mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z
    let P : Model n →L[ℂ] Model n := S.projection (f z)
    change P (D (0,w)) = 0
    have hd : D (0,w) = w • D (0,1) := by
      simpa only [Prod.smul_mk,smul_eq_mul,mul_one,mul_zero,smul_zero] using D.map_smul w (0,1)
    rw [hd,P.map_smul]
    have hzero : P (D (0,1)) = 0 := (hf.2 z hz).2
    rw [hzero,smul_zero]

section BlockLocal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma IsBlockBox.of_local {U : Set (E × F)} {f : E × F → X.Carrier}
    (hl : ∀ z ∈ U, ∃ V : Set (E × F), IsOpen V ∧ z ∈ V ∧ IsBlockBox S V f) :
    IsBlockBox S U f := by
  constructor
  · intro z hz
    obtain ⟨V,hV,hzV,hf⟩ := hl z hz
    exact (hf.1.mdifferentiableAt (hV.mem_nhds hzV)).mdifferentiableWithinAt
  · intro z hz
    obtain ⟨V,_,hzV,hf⟩ := hl z hz
    exact hf.2 z hzV

lemma IsBlockBox.congr {U : Set (E × F)} (hU : IsOpen U)
    {f g : E × F → X.Carrier} (hf : IsBlockBox S U f) (hfg : EqOn g f U) :
    IsBlockBox S U g := by
  refine ⟨hf.1.congr hfg,?_⟩
  intro z hz
  have he : g =ᶠ[𝓝 z] f := Filter.eventually_of_mem (hU.mem_nhds hz) hfg
  have hd := he.mfderiv_eq (I := 𝓘(ℂ,E × F)) (I' := model n)
  rw [hfg hz,hd]
  exact hf.2 z hz

end BlockLocal
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

abbrev unitComplex (t : I) : ℂ := ((t:ℝ):ℂ)

lemma continuous_unitComplex : Continuous unitComplex :=
  Complex.continuous_ofReal.comp continuous_subtype_val

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem block_endpoint_of_family (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S))
    {U : Set (E × F)} (hU : IsOpen U) {R : (E × F) → I × I → X.Carrier}
    (hR : ∀ p ∈ U, ProductBoxTopology.IsBox (splittingAtlas S) (R p))
    (hc : ContinuousOn (Function.uncurry R) (U ×ˢ univ))
    (hb : ∀ t : I, IsBlockBox S U (fun p ↦ R p (t,0)))
    (hl : ∀ t : I, IsBlockBox S U (fun p ↦ R p (0,t))) :
    IsBlockBox S U (fun p ↦ R p (1,1)) := by
  classical
  apply IsBlockBox.of_local
  intro p₀ hp₀
  let c : SplittingChart S → Set (I × I) := fun e ↦ R p₀ ⁻¹' e.chart.source
  have hco : ∀ e, IsOpen (c e) := fun e ↦ e.chart.open_source.preimage (hR p₀ hp₀).1
  have hcov : univ ⊆ ⋃ e, c e := by
    intro w _
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (R p₀ w)
    exact mem_iUnion.mpr ⟨e,he⟩
  obtain ⟨t,ht0,htmono,⟨N,hN⟩,ht⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hco hcov
  have hnode : ∀ i j, ∃ V : Set (E × F), IsOpen V ∧ p₀ ∈ V ∧
      IsBlockBox S V (fun p ↦ R p (t i,t j)) := by
    intro i
    induction i with
    | zero => intro j; simpa only [ht0] using ⟨U,hU,hp₀,hl (t j)⟩
    | succ i hi =>
      intro j
      induction j with
      | zero => simpa only [ht0] using ⟨U,hU,hp₀,hb (t (i+1))⟩
      | succ j hj =>
        have hti : t i ≤ t (i+1) := htmono (Nat.le_succ i)
        have htj : t j ≤ t (j+1) := htmono (Nat.le_succ j)
        obtain ⟨e,he⟩ := ht i j
        let K := Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1))
        have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
        have hmap : ∀ᶠ p in 𝓝 p₀, ∀ w ∈ K, R p w ∈ e.chart.source :=
          hK.eventually_forall_of_forall_eventually fun w hw ↦
            (hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hp₀,trivial⟩)).eventually
              (e.chart.open_source.mem_nhds (he hw))
        obtain ⟨O,hOsub,hO,hpO⟩ := _root_.mem_nhds_iff.mp hmap
        obtain ⟨V,hV,hpV,hbV⟩ := hj
        obtain ⟨W,hW,hpW,hlW⟩ := hi (j+1)
        let L := ((U ∩ O) ∩ V) ∩ W
        have hL : IsOpen L := ((hU.inter hO).inter hV).inter hW
        have hpL : p₀ ∈ L := ⟨⟨⟨hp₀,hpO⟩,hpV⟩,hpW⟩
        have hbL : IsBlockBox S L (fun p ↦ R p (t (i+1),t j)) :=
          hbV.mono (fun _ h ↦ h.1.2)
        have hlL : IsBlockBox S L (fun p ↦ R p (t i,t (j+1))) :=
          hlW.mono (fun _ h ↦ h.2)
        have hmi (p : E × F) (hp : p ∈ L) : MapsTo (R p) K e.chart.source :=
          hOsub hp.1.1.2
        have himem : t (i+1) ∈ Icc (t i) (t (i+1)) := ⟨hti,le_rfl⟩
        have hjmem : t (j+1) ∈ Icc (t j) (t (j+1)) := ⟨htj,le_rfl⟩
        have hi0 : t i ∈ Icc (t i) (t (i+1)) := ⟨le_rfl,hti⟩
        have hj0 : t j ∈ Icc (t j) (t (j+1)) := ⟨le_rfl,htj⟩
        have hm := e.mix_block_maps hL hbL hlL
          (fun p hp ↦ hmi p hp ⟨himem,hj0⟩) (fun p hp ↦ hmi p hp ⟨hi0,hjmem⟩)
        refine ⟨L,hL,hpL,hm.congr hL ?_⟩
        intro p hp
        have hs := (hR p hp.1.1.1).separated (show e.chart ∈ splittingAtlas S from ⟨e,rfl⟩)
          isPreconnected_Icc isPreconnected_Icc (hmi p hp) himem hi0 hjmem hj0
        change R p (t (i+1),t (j+1)) =
          e.chart.symm ((e.chart (R p (t (i+1),t j))).1,(e.chart (R p (t i,t (j+1)))).2)
        rw [← hs,e.chart.left_inv (hmi p hp ⟨himem,hjmem⟩)]
  simpa only [hN N le_rfl] using hnode N N

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ParameterGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {P A X : Type*} [TopologicalSpace P] [TopologicalSpace A] [TopologicalSpace X]

lemma continuousOn_prod_iff {f : P × A → X} {U : Set P} {V : Set A} :
    ContinuousOn f (U ×ˢ V) ↔ Continuous (fun z : U × V ↦ f (z.1,z.2)) := by
  constructor
  · intro h
    exact h.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)
      (fun z ↦ ⟨z.1.property,z.2.property⟩)
  · intro h
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact h.comp (Homeomorph.Set.prod U V).continuous

lemma continuousOn_prod_union {f : P × A → X} {U : Set P} {V W : Set A}
    (hV : IsClosed V) (hW : IsClosed W)
    (hfV : ContinuousOn f (U ×ˢ V)) (hfW : ContinuousOn f (U ×ˢ W)) :
    ContinuousOn f (U ×ˢ (V ∪ W)) := by
  let g : U × A → X := fun z ↦ f (z.1,z.2)
  have hgV : ContinuousOn g (univ ×ˢ V) := hfV.comp
    (continuous_subtype_val.prodMap continuous_id).continuousOn
    (fun z hz ↦ ⟨z.1.property,hz.2⟩)
  have hgW : ContinuousOn g (univ ×ˢ W) := hfW.comp
    (continuous_subtype_val.prodMap continuous_id).continuousOn
    (fun z hz ↦ ⟨z.1.property,hz.2⟩)
  have hg : ContinuousOn g (univ ×ˢ (V ∪ W)) := by
    rw [prod_union]
    exact hgV.union_of_isClosed hgW (isClosed_univ.prod hV) (isClosed_univ.prod hW)
  apply continuousOn_prod_iff.mpr
  exact hg.comp_continuous (continuous_id.prodMap continuous_subtype_val)
    (fun z ↦ ⟨trivial,z.2.property⟩)

def LocalFamilyContinuous (R : P → A → X) (p : P) (K : Set A) : Prop :=
  ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ContinuousOn (Function.uncurry R) (U ×ˢ K)

lemma LocalFamilyContinuous.mono {R : P → A → X} {p : P} {K L : Set A}
    (h : LocalFamilyContinuous R p K) (hLK : L ⊆ K) : LocalFamilyContinuous R p L := by
  obtain ⟨U,hU,hp,hR⟩ := h
  exact ⟨U,hU,hp,hR.mono (prod_mono_right hLK)⟩

lemma LocalFamilyContinuous.union {R : P → A → X} {p : P} {K L : Set A}
    (hK : IsClosed K) (hL : IsClosed L)
    (hR : LocalFamilyContinuous R p K) (hS : LocalFamilyContinuous R p L) :
    LocalFamilyContinuous R p (K ∪ L) := by
  obtain ⟨U,hU,hp,hRu⟩ := hR
  obtain ⟨V,hV,hpv,hRv⟩ := hS
  exact ⟨U ∩ V,hU.inter hV,⟨hp,hpv⟩,continuousOn_prod_union hK hL
    (hRu.mono (prod_mono_left inter_subset_left))
    (hRv.mono (prod_mono_left inter_subset_right))⟩

lemma LocalFamilyContinuous.subtype_parameter {R : P → A → X} {p : P} {K : Set A}
    {U : Set P} (hU : IsOpen U) (hp : p ∈ U)
    (h : LocalFamilyContinuous (fun q : U ↦ R q) ⟨p,hp⟩ K) :
    LocalFamilyContinuous R p K := by
  obtain ⟨W,hW,hpW,hRW⟩ := h
  obtain ⟨V,hV,hVe⟩ := isOpen_induced_iff.mp hW
  have hpV : p ∈ V := by change (⟨p,hp⟩ : U) ∈ Subtype.val ⁻¹' V; rwa [hVe]
  refine ⟨U ∩ V,hU.inter hV,⟨hp,hpV⟩,continuousOn_prod_iff.mpr ?_⟩
  have hc := continuousOn_prod_iff.mp hRW
  let k : ↥(U ∩ V) → W := fun q ↦ ⟨⟨q.val,q.property.1⟩,by rw [← hVe]; exact q.property.2⟩
  have hk : Continuous k := (continuous_subtype_val.subtype_mk _).subtype_mk _
  exact hc.comp (hk.prodMap continuous_id)

lemma LocalFamilyContinuous.precomp {B : Type*} [TopologicalSpace B]
    {R : P → A → X} {p : P} {K : Set A} {L : Set B}
    (h : LocalFamilyContinuous R p K) {f : B → A} (hf : Continuous f)
    (hmap : MapsTo f L K) : LocalFamilyContinuous (fun p b ↦ R p (f b)) p L := by
  obtain ⟨U,hU,hp,hR⟩ := h
  exact ⟨U,hU,hp,hR.comp (continuous_id.prodMap hf).continuousOn
    (fun z hz ↦ ⟨hz.1,hmap hz.2⟩)⟩

lemma LocalFamilyContinuous.of_restrict {R : P → A → X} {p : P} {K : Set A}
    (h : LocalFamilyContinuous (fun q (a : K) ↦ R q a) p univ) :
    LocalFamilyContinuous R p K := by
  obtain ⟨U,hU,hp,hR⟩ := h
  refine ⟨U,hU,hp,continuousOn_prod_iff.mpr ?_⟩
  exact hR.comp_continuous (continuous_subtype_val.prodMap continuous_id)
    (fun z ↦ ⟨z.1.property,trivial⟩)

lemma LocalFamilyContinuous.continuousAt {R : P → A → X} {p : P}
    (h : LocalFamilyContinuous R p univ) (a : A) :
    ContinuousAt (Function.uncurry R) (p,a) := by
  obtain ⟨U,hU,hp,hR⟩ := h
  exact hR.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hp,trivial⟩)

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {P A B X C D : Type*} [TopologicalSpace P] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

lemma ProductChart.parameter_tile_local [T2Space X] [CompactSpace A] [CompactSpace B]
    [PathConnectedSpace A] [PathConnectedSpace B]
    {atlas : Set (OpenPartialHomeomorph X (C × D))}
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source) (e : ProductChart atlas)
    {R : P → A × B → X} (hR : ∀ p, IsBox atlas (R p)) (p₀ : P) (a₀ : A) (b₀ : B)
    (hbottom : LocalFamilyContinuous (fun p a ↦ R p (a,b₀)) p₀ univ)
    (hleft : LocalFamilyContinuous (fun p b ↦ R p (a₀,b)) p₀ univ)
    (he : ∀ w, R p₀ w ∈ e.chart.source) : LocalFamilyContinuous R p₀ univ := by
  obtain ⟨U,hU,hpU,hbU⟩ := hbottom
  obtain ⟨V,hV,hpV,hlV⟩ := hleft
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hpW : p₀ ∈ W := ⟨hpU,hpV⟩
  have hb : Continuous (fun z : W × A ↦ R z.1 (z.2,b₀)) :=
    hbU.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun z ↦ ⟨z.1.property.1,trivial⟩)
  have hl : Continuous (fun z : W × B ↦ R z.1 (a₀,z.2)) :=
    hlV.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun z ↦ ⟨z.1.property.2,trivial⟩)
  obtain ⟨T,hT,hpT,hRT⟩ := e.parameter_tile hcover (R := fun p : W ↦ R p)
    (fun p ↦ hR p) ⟨p₀,hpW⟩ a₀ b₀ hb hl he
  apply LocalFamilyContinuous.subtype_parameter hW hpW
  refine ⟨T,hT,hpT,continuousOn_prod_iff.mpr ?_⟩
  exact hRT.comp (continuous_id.prodMap continuous_subtype_val)

lemma LocalFamilyContinuous.prod_of_restrict {R : P → A × B → X} {p : P}
    {U : Set A} {V : Set B}
    (h : LocalFamilyContinuous (fun q (w : U × V) ↦ R q (w.1,w.2)) p univ) :
    LocalFamilyContinuous R p (U ×ˢ V) := by
  apply LocalFamilyContinuous.of_restrict
  exact h.precomp (Homeomorph.Set.prod U V).continuous (mapsTo_univ _ _)

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace ProductBoxTopology
variable {P X C D : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace C] [TopologicalSpace D]

theorem continuous_family [T2Space X]
    {atlas : Set (OpenPartialHomeomorph X (C × D))}
    (hcharts : ∀ x : X, ∃ e : ProductChart atlas, x ∈ e.chart.source)
    {R : P → I × I → X} (hR : ∀ p, IsBox atlas (R p))
    (hbottom : Continuous (fun z : P × I ↦ R z.1 (z.2,0)))
    (hleft : Continuous (fun z : P × I ↦ R z.1 (0,z.2))) :
    Continuous (Function.uncurry R) := by
  classical
  have hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source := by
    intro x
    obtain ⟨e,he⟩ := hcharts x
    exact ⟨e.chart,e.mem_atlas,he⟩
  have hbLocal (p : P) : LocalFamilyContinuous R p (univ ×ˢ {0}) := by
    refine ⟨univ,isOpen_univ,trivial,?_⟩
    have hc : Continuous (fun z : P × (I × I) ↦ R z.1 (z.2.1,0)) :=
      hbottom.comp (continuous_fst.prodMk continuous_snd.fst)
    apply hc.continuousOn.congr
    rintro ⟨q,a,b⟩ h
    have hb : b=0 := h.2.2
    subst b
    rfl
  have hlLocal (p : P) : LocalFamilyContinuous R p ({0} ×ˢ univ) := by
    refine ⟨univ,isOpen_univ,trivial,?_⟩
    have hc : Continuous (fun z : P × (I × I) ↦ R z.1 (0,z.2.2)) :=
      hleft.comp (continuous_fst.prodMk continuous_snd.snd)
    apply hc.continuousOn.congr
    rintro ⟨q,a,b⟩ h
    have ha : a=0 := h.2.1
    subst a
    rfl
  have hlocal (p₀ : P) : LocalFamilyContinuous R p₀ univ := by
    let c : ProductChart atlas → Set (I × I) := fun e ↦ R p₀ ⁻¹' e.chart.source
    have hc : ∀ e, IsOpen (c e) := fun e ↦ e.chart.open_source.preimage (hR p₀).1
    have hcU : univ ⊆ ⋃ e, c e := by
      intro w _
      obtain ⟨e,he⟩ := hcharts (R p₀ w)
      exact mem_iUnion.mpr ⟨e,he⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,ht⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc hcU
    have hprefix : ∀ i j, LocalFamilyContinuous R p₀ (Icc 0 (t i) ×ˢ Icc 0 (t j)) := by
      intro i
      induction i with
      | zero =>
        intro j
        apply (hlLocal p₀).mono
        intro w hw
        exact ⟨le_antisymm (ht0 ▸ hw.1.2) hw.1.1,trivial⟩
      | succ i hi =>
        intro j
        induction j with
        | zero =>
          apply (hbLocal p₀).mono
          intro w hw
          exact ⟨trivial,le_antisymm (ht0 ▸ hw.2.2) hw.2.1⟩
        | succ j hj =>
          have hti : t i ≤ t (i+1) := htmono (Nat.le_succ i)
          have htj : t j ≤ t (j+1) := htmono (Nat.le_succ j)
          let A := Icc (t i) (t (i+1))
          let B := Icc (t j) (t (j+1))
          let : PathConnectedSpace A := pathConnected_Icc_unit hti
          let : PathConnectedSpace B := pathConnected_Icc_unit htj
          let a₀ : A := ⟨t i,le_rfl,hti⟩
          let b₀ : B := ⟨t j,le_rfl,htj⟩
          obtain ⟨e,he⟩ := ht i j
          have htile : LocalFamilyContinuous R p₀ (A ×ˢ B) := by
            apply LocalFamilyContinuous.prod_of_restrict
            apply e.parameter_tile_local hcover
              (fun p ↦ (hR p).precomp continuous_subtype_val continuous_subtype_val) p₀ a₀ b₀
            · exact hj.precomp (continuous_subtype_val.prodMk continuous_const)
                (fun a _ ↦ ⟨⟨bot_le,a.property.2⟩,⟨bot_le,le_rfl⟩⟩)
            · exact (hi (j+1)).precomp (continuous_const.prodMk continuous_subtype_val)
                (fun b _ ↦ ⟨⟨bot_le,le_rfl⟩,⟨bot_le,b.property.2⟩⟩)
            · intro w
              exact he ⟨w.1.property,w.2.property⟩
          have hcl : IsClosed (Icc (0:I) (t i) ×ˢ Icc (0:I) (t (j+1))) := isClosed_Icc.prod isClosed_Icc
          have hcb : IsClosed (Icc (0:I) (t (i+1)) ×ˢ Icc (0:I) (t j)) := isClosed_Icc.prod isClosed_Icc
          have hct : IsClosed (A ×ˢ B) := isClosed_Icc.prod isClosed_Icc
          apply (((hi (j+1)).union hcl hcb hj).union (hcl.union hcb) hct htile).mono
          intro w hw
          by_cases hx : w.1 ≤ t i
          · exact Or.inl (Or.inl ⟨⟨hw.1.1,hx⟩,hw.2⟩)
          by_cases hy : w.2 ≤ t j
          · exact Or.inl (Or.inr ⟨hw.1,⟨hw.2.1,hy⟩⟩)
          exact Or.inr ⟨⟨(not_le.mp hx).le,hw.1.2⟩,⟨(not_le.mp hy).le,hw.2.2⟩⟩
    apply (hprefix N N).mono
    intro w _
    rw [hN N le_rfl]
    exact ⟨⟨bot_le,le_top⟩,⟨bot_le,le_top⟩⟩
  exact continuous_iff_continuousAt.mpr fun z ↦ (hlocal z.1).continuousAt z.2

end ProductBoxTopology
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PolydiskAxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric
namespace UnitPolydisk

def discShift (a z : ℂ) : ℂ := (a+z)/(1+star a*z)

lemma denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : 1+star a*z ≠ 0 := by
  intro he
  have hn : ‖star a*z‖ < 1 := by
    rw [norm_mul,norm_star]
    nlinarith [norm_nonneg a,norm_nonneg z]
  have hh : star a*z = -1 := by linear_combination he
  rw [hh,norm_neg,norm_one] at hn
  exact (lt_irrefl 1) hn

lemma normSq_difference (a z : ℂ) :
    Complex.normSq (1+star a*z) - Complex.normSq (a+z) =
      (1-Complex.normSq a)*(1-Complex.normSq z) := by
  simp only [Complex.star_def,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.one_re,Complex.one_im]
  ring

lemma discShift_mem {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖discShift a z‖ < 1 := by
  have hden := denominator_ne_zero ha hz
  have ha2 : Complex.normSq a < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz2 : Complex.normSq z < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hn : Complex.normSq (a+z) < Complex.normSq (1+star a*z) := by
    have hh := normSq_difference a z
    have hp := mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hz2)
    linarith
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hn
  rw [discShift,norm_div,div_lt_one (norm_pos_iff.mpr hden)]
  nlinarith [norm_nonneg (a+z),norm_nonneg (1+star a*z)]

lemma discShift_zero (a : ℂ) : discShift a 0=a := by simp [discShift]

lemma discShift_neg_self {a : ℂ}  : discShift (-a) a=0 := by
  simp [discShift]

lemma discShift_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    discShift (-a) (discShift a z)=z := by
  have hden := denominator_ne_zero ha hz
  have ha' : ‖-a‖ < 1 := by simpa using ha
  have hden' := denominator_ne_zero ha' (discShift_mem ha hz)
  change (-a+discShift a z)/(1+star (-a)*discShift a z)=z
  apply (div_eq_iff hden').mpr
  simp only [discShift,star_neg,div_eq_mul_inv]
  have hcancel : (1+star a*z)*(1+star a*z)⁻¹=1 := mul_inv_cancel₀ hden
  linear_combination (a+z)*hcancel

lemma differentiableOn_discShift {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (discShift a) (ball (0:ℂ) 1) := by
  exact ((differentiable_const a).add differentiable_id).differentiableOn.div
    ((differentiable_const 1).add ((differentiable_const (star a)).mul differentiable_id)).differentiableOn
    (fun z hz ↦ denominator_ne_zero ha (mem_ball_zero_iff.mp hz))

def shift {d : ℕ} (a z : Fin d → ℂ) : Fin d → ℂ := fun i ↦ discShift (a i) (z i)

lemma norm_coord_lt_one {d : ℕ} {a : Fin d → ℂ} (ha : a ∈ ball 0 1) (i : Fin d) : ‖a i‖ < 1 :=
  (norm_le_pi_norm a i).trans_lt (mem_ball_zero_iff.mp ha)

lemma shift_mem {d : ℕ} {a z : Fin d → ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    shift a z ∈ ball 0 1 := by
  rw [mem_ball_zero_iff,pi_norm_lt_iff (by norm_num : (0:ℝ)<1)]
  exact fun i ↦ discShift_mem (norm_coord_lt_one ha i) (norm_coord_lt_one hz i)

lemma shift_zero {d : ℕ} (a : Fin d → ℂ) : shift a 0=a := by ext i; exact discShift_zero (a i)

lemma shift_inverse {d : ℕ} {a z : Fin d → ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    shift (-a) (shift a z)=z := by
  ext i
  exact discShift_inverse (norm_coord_lt_one ha i) (norm_coord_lt_one hz i)

lemma differentiableOn_shift {d : ℕ} {a : Fin d → ℂ} (ha : a ∈ ball 0 1) :
    DifferentiableOn ℂ (shift a) (ball 0 1) := by
  apply differentiableOn_pi.mpr
  intro i
  exact (differentiableOn_discShift (norm_coord_lt_one ha i)).comp
    (differentiable_apply i).differentiableOn
    (fun z hz ↦ mem_ball_zero_iff.mpr (norm_coord_lt_one hz i))

end UnitPolydisk
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s d e : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def IsDiskHorizontal (S : HolomorphicSplitting X r s) (f : Polydisk d → X.Carrier) : Prop :=
  ∃ g : Model d → X.Carrier, IsHorizontalMap S (Polydisk d) g ∧ ∀ z : Polydisk d, g z=f z

def IsDiskVertical (S : HolomorphicSplitting X r s) (f : Polydisk e → X.Carrier) : Prop :=
  ∃ g : Model e → X.Carrier, IsVerticalMap S (Polydisk e) g ∧ ∀ z : Polydisk e, g z=f z

def IsDiskTile (S : HolomorphicSplitting X r s) (f : Polydisk d × Polydisk e → X.Carrier) : Prop :=
  ∃ g : Model d × Model e → X.Carrier, IsBlockBox S (Polydisk d ×ˢ Polydisk e) g ∧
    ∀ z : Polydisk d × Polydisk e, g (z.1,z.2)=f z

lemma IsDiskTile.horizontal {f : Polydisk d × Polydisk e → X.Carrier}
    (hf : IsDiskTile S f) (q : Polydisk e) : IsDiskHorizontal S (fun p ↦ f (p,q)) := by
  obtain ⟨g,hg,he⟩ := hf
  exact ⟨fun p ↦ g (p,q),hg.horizontal_slice isOpen_ball isOpen_ball q.property,
    fun p ↦ he (p,q)⟩

lemma IsDiskTile.vertical {f : Polydisk d × Polydisk e → X.Carrier}
    (hf : IsDiskTile S f) (p : Polydisk d) : IsDiskVertical S (fun q ↦ f (p,q)) := by
  obtain ⟨g,hg,he⟩ := hf
  exact ⟨fun q ↦ g (p,q),hg.vertical_slice isOpen_ball isOpen_ball p.property,
    fun q ↦ he (p,q)⟩

lemma IsDiskTile.plaqueBox {f : Polydisk d × Polydisk e → X.Carrier}
    (hf : IsDiskTile S f) : ProductBoxTopology.IsBox (splittingAtlas S) f := by
  obtain ⟨g,hg,he⟩ := hf
  have heq : f=(fun z : Polydisk d × Polydisk e ↦ g (z.1,z.2)) := funext fun z ↦ (he z).symm
  rw [heq]
  exact hg.plaqueBox isOpen_ball isOpen_ball

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PathBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

def IsHorizontal (atlas : Set (OpenPartialHomeomorph X (C × D))) (f : A → X) : Prop :=
  Continuous f ∧ ∀ e ∈ atlas,
    IsLocallyConstant (fun a : {a : A // f a ∈ e.source} ↦ (e (f a)).2)

def IsVertical (atlas : Set (OpenPartialHomeomorph X (C × D))) (f : A → X) : Prop :=
  Continuous f ∧ ∀ e ∈ atlas,
    IsLocallyConstant (fun a : {a : A // f a ∈ e.source} ↦ (e (f a)).1)

lemma IsBox.horizontal {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {f : A × B → X} (hf : IsBox atlas f) (b : B) :
    IsHorizontal atlas (fun a ↦ f (a,b)) :=
  ⟨hf.1.comp (continuous_id.prodMk continuous_const),fun e he ↦ (hf.2 e he).2 b⟩

lemma IsBox.vertical {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {f : A × B → X} (hf : IsBox atlas f) (a : A) :
    IsVertical atlas (fun b ↦ f (a,b)) :=
  ⟨hf.1.comp (continuous_const.prodMk continuous_id),fun e he ↦ (hf.2 e he).1 a⟩

end ProductBoxTopology

open Metric
open scoped Manifold
end
end

section

noncomputable section
open Set Filter Topology

namespace ClosedCoverGlue
variable {A X ι : Type*} [TopologicalSpace A] [TopologicalSpace X] [Finite ι]

theorem exists_glue (U : ι → Set A) (hU : ∀ i, IsClosed (U i))
    (cover : ∀ x, ∃ i, x ∈ U i) (f : ∀ i, U i → X) (hf : ∀ i, Continuous (f i))
    (compat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x,hi⟩=f j ⟨x,hj⟩) :
    ∃ F : A → X, Continuous F ∧ ∀ i (x : U i), F x=f i x := by
  classical
  let F : A → X := fun x ↦ f (cover x).choose ⟨x,(cover x).choose_spec⟩
  have herr (i : ι) (x : U i) : F x=f i x := compat _ _ _ _ _
  refine ⟨F,?_,herr⟩
  apply (locallyFinite_of_finite U).continuous (iUnion_eq_univ_iff.mpr cover) hU
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (U i).domRestrict F=f i := funext fun x ↦ herr i x
  rw [he]
  exact hf i

end ClosedCoverGlue
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace ProductBoxTopology
open IntervalChain
variable {X C D : Type*} [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

theorem grid_glue (atlas : Set (OpenPartialHomeomorph X (C × D)))
    (t u : ℕ → I) (ht0 : t 0=0) (hu0 : u 0=0) (ht : Monotone t) (hu : Monotone u)
    (N M : ℕ) (hN : t N=1) (hM : u M=1)
    (R : ∀ i j, cell t i × cell u j → X) (hR : ∀ i j, IsBox atlas (R i j))
    (seamA : ∀ i j (y : cell u j),
      R i j (⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩,y)=
      R (i+1) j (⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩,y))
    (seamB : ∀ i j (x : cell t i),
      R i j (x,⟨u (j+1),hu (Nat.le_succ j),le_rfl⟩)=
      R i (j+1) (x,⟨u (j+1),le_rfl,hu (Nat.le_succ (j+1))⟩)) :
    ∃ F : I × I → X, IsBox atlas F ∧
      ∀ i j (x : cell t i) (y : cell u j), F (x,y)=R i j (x,y) := by
  classical
  have compat (i j k l : ℕ) (p : I × I) (hi : p.1 ∈ cell t i) (hj : p.2 ∈ cell u j)
      (hk : p.1 ∈ cell t k) (hl : p.2 ∈ cell u l) :
      R i j (⟨p.1,hi⟩,⟨p.2,hj⟩)=R k l (⟨p.1,hk⟩,⟨p.2,hl⟩) := by
    have hA := overlap t ht (fun i x ↦ R i j (x,⟨p.2,hj⟩))
      (fun i ↦ seamA i j ⟨p.2,hj⟩) i k p.1 hi hk
    have hB := overlap u hu (fun j y ↦ R k j (⟨p.1,hk⟩,y))
      (fun j ↦ seamB k j ⟨p.1,hk⟩) j l p.2 hj hl
    exact hA.trans hB
  let K := Fin (N+1) × Fin (M+1)
  let U : K → Set I := fun k ↦ cell t k.1
  let V : K → Set I := fun k ↦ cell u k.2
  have cover (p : I × I) : ∃ k : K, p ∈ U k ×ˢ V k := by
    obtain ⟨i,hi,hpi⟩ := covers t ht0 ht N hN p.1
    obtain ⟨j,hj,hpj⟩ := covers u hu0 hu M hM p.2
    exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hpi,hpj⟩
  let f : ∀ k : K, (U k ×ˢ V k) → X := fun k p ↦
    R k.1 k.2 (⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩)
  have hf (k : K) : Continuous (f k) := (hR k.1 k.2).1.comp
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  obtain ⟨F,hF,hFr⟩ := ClosedCoverGlue.exists_glue (fun k ↦ U k ×ˢ V k)
    (fun _ ↦ isClosed_Icc.prod isClosed_Icc) cover f hf
    (fun a b p ha hb ↦ compat a.1 a.2 b.1 b.2 p ha.1 ha.2 hb.1 hb.2)
  have he (i j : ℕ) (x : cell t i) (y : cell u j) : F (x,y)=R i j (x,y) := by
    obtain ⟨k,hk⟩ := cover (x,y)
    exact (hFr k ⟨(x,y),hk⟩).trans (compat k.1 k.2 i j (x,y) hk.1 hk.2 x.property y.property)
  refine ⟨F,?_,he⟩
  apply IsBox.of_closed_rectangles hF U V (fun _ ↦ isClosed_Icc) (fun _ ↦ isClosed_Icc) cover
  intro k
  have hh : (fun p : U k × V k ↦ F (p.1,p.2))=R k.1 k.2 :=
    funext fun p ↦ he k.1 k.2 p.1 p.2
  rw [hh]
  exact hR k.1 k.2

end ProductBoxTopology
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
open IntervalChain
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {A : Type*} [TopologicalSpace A]

lemma continuous_local_parameter (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {γ : A → X.Carrier}
    (hγ : Continuous γ) (x : A) :
    ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∃ f : Polydisk r × Polydisk s → X.Carrier,
      IsDiskTile S f ∧ ∃ a : U → Polydisk r × Polydisk s, Continuous a ∧
        ∀ y, f (a y)=γ y := by
  obtain ⟨e,hxe,_⟩ := exists_splittingChart S h₁ h₂ (γ x)
  let U := γ ⁻¹' e.chart.source
  have heU (y : U) : γ y ∈ e.chart.source := y.property
  have hcoord (y : U) : e.chart (γ y) ∈ ball 0 e.radius ×ˢ ball 0 e.radius := by
    simpa only [←e.product_range] using e.chart.map_source (heU y)
  let a : U → Polydisk r × Polydisk s := fun y ↦
    (⟨(e.radius : ℂ)⁻¹ • (e.chart (γ y)).1,unscale_mem_ball e.radius_pos (hcoord y).1⟩,
     ⟨(e.radius : ℂ)⁻¹ • (e.chart (γ y)).2,unscale_mem_ball e.radius_pos (hcoord y).2⟩)
  have hc := e.chart.continuousOn.comp_continuous (hγ.comp continuous_subtype_val) heU
  have ha : Continuous a :=
    ((hc.fst.const_smul ((e.radius : ℂ)⁻¹)).subtype_mk _).prodMk
      ((hc.snd.const_smul ((e.radius : ℂ)⁻¹)).subtype_mk _)
  exact ⟨U,e.chart.open_source.preimage hγ,hxe,fun p ↦ e.unitMap (p.1,p.2),
    ⟨e.unitMap,e.unitMap_block,fun _ ↦ rfl⟩,a,ha,fun y ↦ e.unitMap_coordinates (heU y)⟩

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.EtaleGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace FunctionEtale
variable (X Y : Type*) [TopologicalSpace X]

def Total := (x : X) × Germ (𝓝 x) Y

variable {X Y}
def base (g : Total X Y) : X := g.1
def sectionOf (f : X → Y) (x : X) : Total X Y := ⟨x,(f : Germ (𝓝 x) Y)⟩

def basic (f : X → Y) (U : Set X) : Set (Total X Y) :=
  {g | base g ∈ U ∧ g=sectionOf f (base g)}

instance instTopologicalSpaceTotal : TopologicalSpace (Total X Y) :=
  TopologicalSpace.generateFrom {W | ∃ f U, IsOpen U ∧ W=basic f U}

lemma section_eq {f h : X → Y} {x : X} :
    sectionOf f x=sectionOf h x ↔ f =ᶠ[𝓝 x] h := by
  change (Sigma.mk (β := fun z : X ↦ Germ (𝓝 z) Y) x (f : Germ (𝓝 x) Y)=Sigma.mk x (h : Germ (𝓝 x) Y)) ↔ _
  simp only [Sigma.mk.inj_iff,heq_eq_eq,Germ.coe_eq,true_and]

lemma isOpen_basic (f : X → Y) {U : Set X} (hU : IsOpen U) : IsOpen (basic f U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨f,U,hU,rfl⟩

lemma continuous_section (f : X → Y) : Continuous (sectionOf f) := by
  apply continuous_generateFrom_iff.mpr
  rintro W ⟨h,U,hU,rfl⟩
  have he : sectionOf f ⁻¹' basic h U=U ∩ {x | f =ᶠ[𝓝 x] h} := by
    ext x; exact and_congr Iff.rfl section_eq
  rw [he]
  exact hU.inter isOpen_setOfPred_eventually_nhds

lemma exists_representative (g : Total X Y) : ∃ f : X → Y, g=sectionOf f (base g) := by
  rcases g with ⟨x,g⟩
  induction g using Germ.inductionOn with | h f => exact ⟨f,rfl⟩

lemma continuous_base : Continuous (base : Total X Y → X) := by
  apply continuous_def.mpr
  intro U hU
  have he : base ⁻¹' U=⋃ f : X → Y, basic f U := by
    ext g; constructor
    · intro h
      obtain ⟨f,hf⟩ := exists_representative g
      exact mem_iUnion.mpr ⟨f,h,hf⟩
    · intro h; obtain ⟨f,hf⟩ := mem_iUnion.mp h; exact hf.1
  rw [he]
  exact isOpen_iUnion (fun f ↦ isOpen_basic f hU)

def chart (f : X → Y) : OpenPartialHomeomorph (Total X Y) X where
  toFun := base
  invFun := sectionOf f
  source := basic f univ
  target := univ
  map_source' := fun _ _ ↦ trivial
  map_target' := fun _ _ ↦ ⟨trivial,rfl⟩
  left_inv' := fun _ h ↦ h.2.symm
  right_inv' := fun _ _ ↦ rfl
  open_source := isOpen_basic f isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := continuous_base.continuousOn
  continuousOn_invFun := (continuous_section f).continuousOn

lemma isLocalHomeomorph_base : IsLocalHomeomorph (base : Total X Y → X) := by
  intro g
  obtain ⟨f,hf⟩ := exists_representative g
  exact ⟨chart f,⟨trivial,hf⟩,rfl⟩

lemma isOpen_of_local {P : Set (Total X Y)}
    (hP : ∀ f : X → Y, IsOpen {x | sectionOf f x ∈ P}) : IsOpen P := by
  have he : P=⋃ f : X → Y, basic f {x | sectionOf f x ∈ P} := by
    ext g; constructor
    · intro h
      obtain ⟨f,hf⟩ := exists_representative g
      exact mem_iUnion.mpr ⟨f,show sectionOf f (base g) ∈ P from hf ▸ h,hf⟩
    · intro h
      obtain ⟨f,hf⟩ := mem_iUnion.mp h
      exact hf.2 ▸ hf.1
  rw [he]
  exact isOpen_iUnion (fun f ↦ isOpen_basic f (hP f))

lemma isLocalHomeomorph_restrict {P : Set (Total X Y)} (hP : IsOpen P) :
    IsLocalHomeomorph (fun g : P ↦ base g.val) :=
  isLocalHomeomorph_base.comp hP.isOpenEmbedding_subtypeVal.isLocalHomeomorph

lemma continuous_of_local {A : Type*} [TopologicalSpace A] {g : A → Total X Y}
    (hb : Continuous (base ∘ g))
    (hl : ∀ a, ∃ f : X → Y, ∀ᶠ b in 𝓝 a, g b=sectionOf f (base (g b))) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨f,hf⟩ := hl a
  exact ((continuous_section f).comp hb).continuousAt.congr (Filter.EventuallyEq.symm hf)

end FunctionEtale
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
namespace HolomorphicEtale
variable {m n : ℕ} (M : ComplexManifold m) (X : ComplexManifold n)

def IsHolomorphic (g : FunctionEtale.Total M.Carrier X.Carrier) : Prop :=
  ∃ U : Set M.Carrier, IsOpen U ∧ FunctionEtale.base g ∈ U ∧
    ∃ f : M.Carrier → X.Carrier,
      MDifferentiableOn (model m) (model n) f U ∧
      g=FunctionEtale.sectionOf f (FunctionEtale.base g)

abbrev Germs := {g : FunctionEtale.Total M.Carrier X.Carrier // IsHolomorphic M X g}
def base (g : Germs M X) : M.Carrier := FunctionEtale.base g.val

lemma isOpen_holomorphic : IsOpen {g | IsHolomorphic M X g} := by
  apply FunctionEtale.isOpen_of_local
  intro f
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U,hU,hxU,h,hh,he⟩ := hx
  have heq : f =ᶠ[𝓝 x] h := FunctionEtale.section_eq.mp he
  filter_upwards [hU.mem_nhds hxU,heq.eventually_nhds] with y hy he'
  exact ⟨U,hU,hy,h,hh,FunctionEtale.section_eq.mpr he'⟩

lemma localHomeomorph : IsLocalHomeomorph (base M X) :=
  FunctionEtale.isLocalHomeomorph_restrict (isOpen_holomorphic M X)

lemma separated : IsSeparatedMap (base M X) := by
  let : LocallyConnectedSpace M.Carrier := ChartedSpace.locallyConnectedSpace (Model m) M.Carrier
  intro a b hab hne
  obtain ⟨U,hU,haU,f,hf,ha⟩ := a.property
  obtain ⟨V,hV,hbV,g,hg,hb⟩ := b.property
  have hcommon : U ∩ V ∈ 𝓝 (base M X a) :=
    inter_mem (hU.mem_nhds haU) (hV.mem_nhds (hab ▸ hbV))
  obtain ⟨W,⟨hW,haW,hWc⟩,hsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (base M X a)).mem_iff.mp hcommon
  let A : Set (Germs M X) := Subtype.val ⁻¹' FunctionEtale.basic f W
  let B : Set (Germs M X) := Subtype.val ⁻¹' FunctionEtale.basic g W
  refine ⟨A,B,(FunctionEtale.isOpen_basic f hW).preimage continuous_subtype_val,
    (FunctionEtale.isOpen_basic g hW).preimage continuous_subtype_val,
    ⟨haW,ha⟩,⟨show base M X b ∈ W from hab ▸ haW,hb⟩,?_⟩
  apply disjoint_left.mpr
  intro c hcA hcB
  have hfg : f =ᶠ[𝓝 (base M X c)] g :=
    FunctionEtale.section_eq.mp (hcA.2.symm.trans hcB.2)
  have heq := holomorphic_manifolds_eqOn_of_preconnected_of_eventuallyEq hW hWc.2
    (hf.mono (fun _ h ↦ (hsub h).1)) (hg.mono (fun _ h ↦ (hsub h).2)) hcA.1 hfg
  apply hne
  apply Subtype.ext
  calc a.val=FunctionEtale.sectionOf f (base M X a) := ha
       _ = FunctionEtale.sectionOf g (base M X a) :=
         FunctionEtale.section_eq.mpr (Filter.mem_of_superset (hW.mem_nhds haW) heq)
       _ = b.val := by rw [hab]; exact hb.symm

end HolomorphicEtale
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma SplittingChart.transition_first (e d : SplittingChart S) {x : X.Carrier}
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    (fun y ↦ (e.chart y).1) =ᶠ[𝓝 x]
      (fun y ↦ (e.chart (d.chart.symm ((d.chart y).1,(d.chart x).2))).1) := by
  let z := d.chart x
  have hzt : z ∈ d.chart.target := d.chart.map_source hd
  have hN : d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source ∈ 𝓝 z := by
    refine inter_mem (d.chart.open_target.mem_nhds hzt) ((d.chart.symm.continuousAt hzt) ?_)
    simpa only [z,d.chart.left_inv hd] using e.chart.open_source.mem_nhds he
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp hN
  let U := ball z.1 ε
  let V := ball z.2 ε
  have hUV : U ×ˢ V ⊆ d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source := by
    simpa only [U,V,ball_prod_same,Prod.eta] using hεN
  have hc := e.block_coordinates (isOpen_ball.prod isOpen_ball)
    (d.inverse_isBlockBox.mono (fun _ h ↦ (hUV h).1)) (fun _ h ↦ (hUV h).2)
  let F : Model r × Model s → Model r := fun p ↦ (e.chart (d.chart.symm p)).1
  have hF : DifferentiableOn ℂ F (U ×ˢ V) := hc.1.fst
  have hzero : ∀ p ∈ U ×ˢ V, ∀ v : Model s, fderiv ℂ F p (0,v)=0 := by
    intro p hp v
    have H := ((hc.1.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hp)).hasFDerivAt.fst).fderiv
    change fderiv ℂ F p = _ at H
    rw [H]
    exact (hc.2 p hp).2 v
  have hloc : ∀ p ∈ U ×ˢ V, F p=F (p.1,z.2) := by
    intro p hp
    exact independent_second_of_fderiv_zero isOpen_ball isOpen_ball (convex_ball z.2 ε).isPreconnected
      hF hzero hp.1 hp.2 (mem_ball_self hε)
  have hdx := d.chart.continuousAt hd
  filter_upwards [d.chart.open_source.mem_nhds hd,
    hdx ((isOpen_ball.prod isOpen_ball).mem_nhds (show z ∈ U ×ˢ V from
      ⟨mem_ball_self hε,mem_ball_self hε⟩))] with y hy hdy
  simpa only [F,d.chart.left_inv hy] using hloc (d.chart y) hdy

namespace FirstGerm

def IsFirst (g : FunctionEtale.Total X.Carrier X.Carrier) : Prop :=
  ∀ e : SplittingChart S, FunctionEtale.base g ∈ e.chart.source →
    ∃ h : Model r → X.Carrier,
      g=FunctionEtale.sectionOf (fun y ↦ h (e.chart y).1) (FunctionEtale.base g)

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.GermTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def SplittingChart.firstProjection (e : SplittingChart S) (b : Model s) (x : X.Carrier) : X.Carrier :=
  e.chart.symm ((e.chart x).1,b)

lemma SplittingChart.firstProjection_target (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) {x : X.Carrier} (hx : x ∈ e.chart.source) :
    ((e.chart x).1,b) ∈ e.chart.target := by
  have h := e.chart.map_source hx
  rw [e.product_range] at h ⊢
  exact ⟨h.1,hb⟩

lemma SplittingChart.firstProjection_source (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) {x : X.Carrier} (hx : x ∈ e.chart.source) :
    e.firstProjection b x ∈ e.chart.source := e.chart.map_target (e.firstProjection_target hb hx)

lemma SplittingChart.firstProjection_coordinates (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) {x : X.Carrier} (hx : x ∈ e.chart.source) :
    e.chart (e.firstProjection b x)=((e.chart x).1,b) :=
  e.chart.right_inv (e.firstProjection_target hb hx)

lemma SplittingChart.firstProjection_holomorphic (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) :
    MDifferentiableOn (model n) (model n) (e.firstProjection b) e.chart.source := by
  have hfst : MDifferentiableOn (model n) (model r) (fun x ↦ (e.chart x).1) e.chart.source := by
    intro x hx
    exact (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp_mdifferentiableWithinAt x
      (e.holomorphic x hx)
  exact e.inverse_holomorphic.comp (hfst.prodMk_space mdifferentiableOn_const)
    (fun _ hx ↦ e.firstProjection_target hb hx)

lemma SplittingChart.firstProjection_self (e : SplittingChart S) {x : X.Carrier}
    (hx : x ∈ e.chart.source) : e.firstProjection (e.chart x).2 x=x := by
  exact e.chart.left_inv hx

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma independent_first_of_fderiv_zero
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPreconnected U) {f : E × F → H}
    (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (hzero : ∀ p ∈ U ×ˢ V, ∀ v : E, fderiv ℂ f p (v,0)=0)
    {a c : E} (ha : a ∈ U) (hc : c ∈ U) {b : F} (hb : b ∈ V) : f (a,b)=f (c,b) := by
  have hd (x : E) (hx : x ∈ U) :
      HasFDerivAt (fun t : E ↦ f (t,b)) (0 : E →L[ℂ] H) x := by
    have hp : HasFDerivAt (fun t : E ↦ (t,b)) (ContinuousLinearMap.inl ℂ E F) x := by
      convert (hasFDerivAt_id (𝕜 := ℂ) x).prodMk (hasFDerivAt_const (𝕜 := ℂ) b x) using 1 <;> rfl
    have hh := ((hf (x,b) ⟨hx,hb⟩).differentiableAt
      ((hU.prod hV).mem_nhds ⟨hx,hb⟩)).hasFDerivAt.comp x hp
    have he : fderiv ℂ f (x,b) ∘L ContinuousLinearMap.inl ℂ E F=0 := by
      ext v
      exact hzero (x,b) ⟨hx,hb⟩ v
    rw [he] at hh
    exact hh
  exact hU.is_const_of_fderiv_eq_zero hUc
    (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hd x hx).fderiv) ha hc

lemma SplittingChart.transition_second (e d : SplittingChart S) {x : X.Carrier}
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    (fun y ↦ (e.chart y).2) =ᶠ[𝓝 x]
      (fun y ↦ (e.chart (d.chart.symm ((d.chart x).1,(d.chart y).2))).2) := by
  let z := d.chart x
  have hzt : z ∈ d.chart.target := d.chart.map_source hd
  have hN : d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source ∈ 𝓝 z := by
    refine inter_mem (d.chart.open_target.mem_nhds hzt) ((d.chart.symm.continuousAt hzt) ?_)
    simpa only [z,d.chart.left_inv hd] using e.chart.open_source.mem_nhds he
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp hN
  let U := ball z.1 ε
  let V := ball z.2 ε
  have hUV : U ×ˢ V ⊆ d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source := by
    simpa only [U,V,ball_prod_same,Prod.eta] using hεN
  have hc := e.block_coordinates (isOpen_ball.prod isOpen_ball)
    (d.inverse_isBlockBox.mono (fun _ h ↦ (hUV h).1)) (fun _ h ↦ (hUV h).2)
  let F : Model r × Model s → Model s := fun p ↦ (e.chart (d.chart.symm p)).2
  have hF : DifferentiableOn ℂ F (U ×ˢ V) := hc.1.snd
  have hzero : ∀ p ∈ U ×ˢ V, ∀ v : Model r, fderiv ℂ F p (v,0)=0 := by
    intro p hp v
    have H := ((hc.1.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hp)).hasFDerivAt.snd).fderiv
    change fderiv ℂ F p = _ at H
    rw [H]
    exact (hc.2 p hp).1 v
  have hloc : ∀ p ∈ U ×ˢ V, F p=F (z.1,p.2) := by
    intro p hp
    exact independent_first_of_fderiv_zero isOpen_ball isOpen_ball (convex_ball z.1 ε).isPreconnected
      hF hzero hp.1 (mem_ball_self hε) hp.2
  have hdx := d.chart.continuousAt hd
  filter_upwards [d.chart.open_source.mem_nhds hd,
    hdx ((isOpen_ball.prod isOpen_ball).mem_nhds (show z ∈ U ×ˢ V from
      ⟨mem_ball_self hε,mem_ball_self hε⟩))] with y hy hdy
  simpa only [F,d.chart.left_inv hy] using hloc (d.chart y) hdy

lemma SplittingChart.firstProjection_germ_eq (e d : SplittingChart S) {x : X.Carrier}
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    e.firstProjection (e.chart x).2 =ᶠ[𝓝 x] d.firstProjection (d.chart x).2 := by
  have hb : (d.chart x).2 ∈ ball 0 d.radius := by
    have H := d.chart.map_source hd
    rw [d.product_range] at H
    exact H.2
  have hb' : (e.chart x).2 ∈ ball 0 e.radius := by
    have H := e.chart.map_source he
    rw [e.product_range] at H
    exact H.2
  let P := d.firstProjection (d.chart x).2
  have hPx : P x=x := d.firstProjection_self hd
  have hpc : Tendsto P (𝓝 x) (𝓝 x) := by
    have H := (d.firstProjection_holomorphic hb).continuousOn.continuousAt
      (d.chart.open_source.mem_nhds hd)
    change Tendsto P (𝓝 x) (𝓝 (P x)) at H
    simpa only [hPx] using H
  have hsecond := (e.transition_second d he hd).comp_tendsto hpc
  filter_upwards [e.chart.open_source.mem_nhds he,d.chart.open_source.mem_nhds hd,
    hpc (e.chart.open_source.mem_nhds he),e.transition_first d he hd,hsecond] with y hye hyd hpe hfirst hsec
  apply e.chart.injOn (e.firstProjection_source hb' hye) hpe
  rw [e.firstProjection_coordinates hb' hye]
  apply Prod.ext
  · exact hfirst
  · have H := congrArg (fun z : Model r × Model s ↦ z.2) (d.firstProjection_coordinates hb hyd)
    change (d.chart (P y)).2=(d.chart x).2 at H
    dsimp only [Function.comp_def] at hsec
    rw [H,d.chart.left_inv hd] at hsec
    exact hsec.symm

namespace FirstGerm

def projection (e : SplittingChart S) (x : X.Carrier) (hx : x ∈ e.chart.source) :
    HolomorphicEtale.Germs X X :=
  ⟨FunctionEtale.sectionOf (e.firstProjection (e.chart x).2) x,
    e.chart.source,e.chart.open_source,hx,e.firstProjection (e.chart x).2,
    e.firstProjection_holomorphic (by
      have H := e.chart.map_source hx
      rw [e.product_range] at H
      exact H.2),rfl⟩

lemma projection_eq (e d : SplittingChart S) (x : X.Carrier)
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    projection e x he=projection d x hd := by
  apply Subtype.ext
  exact FunctionEtale.section_eq.mpr (e.firstProjection_germ_eq d he hd)

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Monodromy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

noncomputable def initial (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (x : X.Carrier) :
    HolomorphicEtale.Germs X X :=
  projection (exists_splittingChart S h₁ h₂ x).choose x
    (exists_splittingChart S h₁ h₂ x).choose_spec.1

lemma initial_eq (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (e : SplittingChart S)
    (x : X.Carrier) (hx : x ∈ e.chart.source) :
    initial h₁ h₂ x=projection e x hx := projection_eq _ _ _ _ _

lemma continuous_horizontal {A : Type*} [TopologicalSpace A]
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α : A → X.Carrier} (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) α) :
    Continuous (fun a ↦ initial h₁ h₂ (α a)) := by
  apply continuous_induced_rng.mpr
  apply FunctionEtale.continuous_of_local (by change Continuous α; exact hα.1)
  intro a
  obtain ⟨e,hea,_⟩ := exists_splittingChart S h₁ h₂ (α a)
  let W := α ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hα.1
  have hlc := (hα.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨a,hea⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨a,hea⟩ _).mp hlc
  refine ⟨e.firstProjection (e.chart (α a)).2,?_⟩
  filter_upwards [hV,hW.mem_nhds hea] with b hbV hbW
  have hsec := hsub (show (⟨b,hbW⟩ : W) ∈ Subtype.val ⁻¹' V from hbV)
  change (e.chart (α b)).2=(e.chart (α a)).2 at hsec
  change (initial h₁ h₂ (α b)).val=
    FunctionEtale.sectionOf (e.firstProjection (e.chart (α a)).2) (α b)
  rw [initial_eq h₁ h₂ e (α b) hbW]
  change FunctionEtale.sectionOf (e.firstProjection (e.chart (α b)).2) (α b)=
    FunctionEtale.sectionOf (e.firstProjection (e.chart (α a)).2) (α b)
  rw [hsec]

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace FunctionEtale
variable {M X : Type*} [TopologicalSpace M]

def value (g : Total M X) : X :=
  Germ.liftOn g.2 (fun f ↦ f g.1) (fun _ _ h ↦ h.eq_of_nhds)

@[simp] lemma value_section (f : M → X) (x : M) : value (sectionOf f x)=f x := rfl
end FunctionEtale

namespace UniversalCoverSplitting
namespace HolomorphicEtale
variable {m n k : ℕ} {M : ComplexManifold m} {X : ComplexManifold n}
    {Z : ComplexManifold k}

def value (g : Germs M X) : X.Carrier := FunctionEtale.value g.val

lemma value_of_section {g : Germs M X} {f : M.Carrier → X.Carrier}
    (hg : g.val=FunctionEtale.sectionOf f (base M X g)) : value g=f (base M X g) := by
  exact congrArg FunctionEtale.value hg

lemma value_locally {A : Type*} [TopologicalSpace A]
    {F : A → Germs M X} (hF : Continuous F) {a : A}
    {f : M.Carrier → X.Carrier} (he : (F a).val=FunctionEtale.sectionOf f (base M X (F a))) :
    (fun b ↦ value (F b)) =ᶠ[𝓝 a] (fun b ↦ f (base M X (F b))) := by
  have hev := (continuous_subtype_val.comp hF).continuousAt.eventually
    ((FunctionEtale.isOpen_basic f isOpen_univ).mem_nhds ⟨mem_univ _,he⟩)
  exact hev.mono fun _ h ↦ value_of_section h.2

end HolomorphicEtale

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.GlobalProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}

structure GlobalProjection (π : OrdinaryUniversalCover X Z) (o : Z.Carrier)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) where
  germs : C(Z.Carrier,HolomorphicEtale.Germs X X)
  germs_base : HolomorphicEtale.base X X ∘ germs=π.projection
  germs_initial : germs o=initial h₁ h₂ (π.projection o)
  germs_first : ∀ z, IsFirst (S := S) (germs z).val
  toFun : Z.Carrier → Z.Carrier
  holomorphic : MDifferentiable (model n) (model n) toFun
  based : toFun o=o
  lift : π.projection ∘ toFun=HolomorphicEtale.value ∘ germs

variable {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma value_vertical {A : Type*} [TopologicalSpace A]
    {F : A → HolomorphicEtale.Germs X X} (hF : Continuous F)
    (hfirst : ∀ a, IsFirst (S := S) (F a).val)
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S) (HolomorphicEtale.base X X ∘ F))
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) :
    IsLocallyConstant (HolomorphicEtale.value ∘ F) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  obtain ⟨e,hea,_⟩ := exists_splittingChart S h₁ h₂ (HolomorphicEtale.base X X (F a))
  obtain ⟨f,hf⟩ := hfirst a e hea
  have hev := HolomorphicEtale.value_locally hF hf
  let W := (HolomorphicEtale.base X X ∘ F) ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hv.1
  have hlc := (hv.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨a,hea⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨a,hea⟩ _).mp hlc
  filter_upwards [hev,hV,hW.mem_nhds hea] with b hb hbV hbW
  have hh := hsub (show (⟨b,hbW⟩ : W) ∈ Subtype.val ⁻¹' V from hbV)
  change (e.chart (HolomorphicEtale.base X X (F b))).1=
    (e.chart (HolomorphicEtale.base X X (F a))).1 at hh
  change HolomorphicEtale.value (F b)=HolomorphicEtale.value (F a)
  rw [hb,HolomorphicEtale.value_of_section hf,hh]

lemma GlobalProjection.horizontal_germs (Q : GlobalProjection π o h₁ h₂)
    {α : I → Z.Carrier} (hα : Continuous α) (ha : α 0=o)
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α)) :
    ∀ t, Q.germs (α t)=initial h₁ h₂ (π.projection (α t)) := by
  have heq : (fun t ↦ Q.germs (α t))=(fun t ↦ initial h₁ h₂ (π.projection (α t))) := by
    refine (HolomorphicEtale.separated X X).eq_of_comp_eq
      (HolomorphicEtale.localHomeomorph X X).isLocallyInjective (Q.germs.continuous.comp hα)
      (continuous_horizontal h₁ h₂ hh) ?_ 0 ?_
    · ext t
      exact congrFun Q.germs_base (α t)
    · rw [ha,Q.germs_initial]
  exact congrFun heq

lemma GlobalProjection.horizontal_fixed (Q : GlobalProjection π o h₁ h₂)
    {α : I → Z.Carrier} (hα : Continuous α) (ha : α 0=o)
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α)) :
    ∀ t, Q.toFun (α t)=α t := by
  have hb : π.projection ∘ (Q.toFun ∘ α)=π.projection ∘ α := by
    ext t
    have H := congrFun Q.lift (α t)
    change π.projection (Q.toFun (α t))=HolomorphicEtale.value (Q.germs (α t)) at H
    rw [Q.horizontal_germs hα ha hh] at H
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (π.projection (α t))
    rw [initial_eq h₁ h₂ e _ he] at H
    exact H.trans (e.firstProjection_self he)
  have heq : Q.toFun ∘ α=α := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (Q.holomorphic.continuous.comp hα) hα hb 0 ?_
    change Q.toFun (α 0)=α 0
    rw [ha,Q.based]
  exact congrFun heq

lemma GlobalProjection.vertical_constant (Q : GlobalProjection π o h₁ h₂)
    {β : I → Z.Carrier} (hβ : Continuous β)
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β)) :
    ∀ t, Q.toFun (β t)=Q.toFun (β 0) := by
  have hc := value_vertical (Q.germs.continuous.comp hβ) (fun t ↦ Q.germs_first (β t))
    (show ProductBoxTopology.IsVertical (splittingAtlas S)
      (HolomorphicEtale.base X X ∘ (Q.germs ∘ β)) from by
        have he : HolomorphicEtale.base X X ∘ (Q.germs ∘ β)=π.projection ∘ β := by
          ext t; exact congrFun Q.germs_base (β t)
        rw [he]; exact hv) h₁ h₂
  have hb : π.projection ∘ (Q.toFun ∘ β)=π.projection ∘ (fun _ : I ↦ Q.toFun (β 0)) := by
    ext t
    exact (congrFun Q.lift (β t)).trans ((hc.apply_eq_of_preconnectedSpace t 0).trans
      (congrFun Q.lift (β 0)).symm)
  have heq : Q.toFun ∘ β=(fun _ : I ↦ Q.toFun (β 0)) :=
    π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (Q.holomorphic.continuous.comp hβ) continuous_const hb 0 rfl
  exact congrFun heq

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.RetractCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {Z : ComplexManifold n}

structure RetractChart (Z : ComplexManifold n) (Q : Z.Carrier → Z.Carrier) (r s : ℕ) where
  chart : OpenPartialHomeomorph Z.Carrier (Model r × Model s)
  radius : ℝ
  radius_pos : 0 < radius
  product_range : chart.target=ball 0 radius ×ˢ ball 0 radius
  holomorphic : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) chart chart.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) chart.symm chart.target
  maps : MapsTo Q chart.source chart.source
  projects : ∀ z ∈ chart.source, chart (Q z)=((chart z).1,0)

namespace RetractChart
variable {Q : Z.Carrier → Z.Carrier} (e : RetractChart Z Q r s)
abbrev Fixed (Q : Z.Carrier → Z.Carrier) := {z : Z.Carrier // Q z=z}

lemma fixed_iff {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Q z=z ↔ (e.chart z).2=0 := by
  constructor
  · intro h
    have hh := congrArg Prod.snd (e.projects z hz)
    simpa only [h] using hh
  · intro h
    apply e.chart.injOn (e.maps hz) hz
    rw [e.projects z hz,←h]

lemma fixed_inverse {a : Model r} (ha : a ∈ ball 0 e.radius) :
    Q (e.chart.symm (a,0))=e.chart.symm (a,0) := by
  have hat : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩
  apply (e.fixed_iff (e.chart.map_target hat)).mpr
  rw [e.chart.right_inv hat]

def fixedInv (a : Model r) : Fixed Q := by
  classical
  exact if h : a ∈ ball 0 e.radius then ⟨e.chart.symm (a,0),e.fixed_inverse h⟩
  else ⟨e.chart.symm (0,0),e.fixed_inverse (mem_ball_self e.radius_pos)⟩

lemma fixedInv_val {a : Model r} (ha : a ∈ ball 0 e.radius) :
    (e.fixedInv a).val=e.chart.symm (a,0) := by simp only [fixedInv,dite_eq_left ha]

lemma continuousOn_fixedInv : ContinuousOn e.fixedInv (ball 0 e.radius) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  apply (e.chart.symm.continuousOn.comp (show Continuous (fun a : Model r ↦ (a,(0 : Model s))) from by fun_prop).continuousOn
    (fun a ha ↦ by change (a,(0 : Model s)) ∈ e.chart.target; rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩)).congr
  exact fun a ha ↦ e.fixedInv_val ha

def fixedChart : OpenPartialHomeomorph (Fixed Q) (Model r) where
  toFun := fun z ↦ (e.chart z.val).1
  invFun := e.fixedInv
  source := Subtype.val ⁻¹' e.chart.source
  target := ball 0 e.radius
  map_source' := fun z hz ↦ (e.product_range ▸ e.chart.map_source hz).1
  map_target' := fun a ha ↦ by
    change (e.fixedInv a).val ∈ e.chart.source
    rw [e.fixedInv_val ha]
    apply e.chart.map_target
    rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩
  left_inv' := fun z hz ↦ by
    apply Subtype.ext
    rw [e.fixedInv_val ((e.product_range ▸ e.chart.map_source hz).1)]
    have hh := (e.fixed_iff hz).mp z.property
    rw [←hh,Prod.eta,e.chart.left_inv hz]
  right_inv' := fun a ha ↦ by
    rw [e.fixedInv_val ha,e.chart.right_inv (by
      rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩)]
  open_source := e.chart.open_source.preimage continuous_subtype_val
  open_target := isOpen_ball
  continuousOn_toFun := (e.chart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h ↦ h)).fst
  continuousOn_invFun := e.continuousOn_fixedInv

end RetractChart
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}

structure CoverProductChart (π : OrdinaryUniversalCover X Z) (S : HolomorphicSplitting X r s) where
  chart : OpenPartialHomeomorph Z.Carrier (Model r × Model s)
  radius : ℝ
  radius_pos : 0 < radius
  product_range : chart.target=ball 0 radius ×ˢ ball 0 radius
  holomorphic : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) chart chart.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) chart.symm chart.target
  downstairs : SplittingChart S
  maps : MapsTo π.projection chart.source downstairs.chart.source
  coordinates : ∀ z ∈ chart.source, chart z=downstairs.chart (π.projection z)

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.FixedManifolds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
namespace RetractChart
variable {n r s : ℕ} {Z : ComplexManifold n} {Q : Z.Carrier → Z.Carrier}

variable (c : Fixed Q → RetractChart Z Q r s)
    (hc : ∀ x, x.val ∈ (c x).chart.source)

@[instance_reducible] def fixedChartedSpace : ChartedSpace (Model r) (Fixed Q) where
  atlas := Set.range (fun x ↦ (c x).fixedChart)
  chartAt := fun x ↦ (c x).fixedChart
  mem_chart_source := hc
  chart_mem_atlas := fun x ↦ ⟨x,rfl⟩

end RetractChart
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.SwapSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

lemma HolomorphicSplitting.complement_range (S : HolomorphicSplitting X r s) (x : X.Carrier) :
    LinearMap.range (complementaryProjection S x).toLinearMap = LinearMap.ker (S.projection x).toLinearMap := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change S.projection x (w-S.projection x w)=0
    rw [map_sub,S.idempotent,sub_self]
  · intro hv
    refine ⟨v,?_⟩
    change v-S.projection x v=v
    change S.projection x v=0 at hv
    rw [hv,sub_zero]

lemma HolomorphicSplitting.complement_ker (S : HolomorphicSplitting X r s) (x : X.Carrier) :
    LinearMap.ker (complementaryProjection S x).toLinearMap = LinearMap.range (S.projection x).toLinearMap := by
  ext v
  constructor
  · intro hv
    change v-S.projection x v=0 at hv
    exact ⟨v,(sub_eq_zero.mp hv).symm⟩
  · rintro ⟨w,rfl⟩
    change S.projection x w-S.projection x (S.projection x w)=0
    rw [S.idempotent,sub_self]

def HolomorphicSplitting.swap (S : HolomorphicSplitting X r s) : HolomorphicSplitting X s r where
  projection := complementaryProjection S
  idempotent := by
    intro x v
    change v-S.projection x v-S.projection x (v-S.projection x v)=v-S.projection x v
    rw [map_sub,S.idempotent,sub_self,sub_zero]
  holomorphic := S.complement_holomorphic
  first_rank := fun x ↦ by
    rw [S.complement_range x]
    exact S.second_rank x
  second_rank := fun x ↦ by
    rw [S.complement_ker x]
    exact S.first_rank x

variable {S : HolomorphicSplitting X r s}

def SplittingChart.swapChart (e : SplittingChart S) :
    OpenPartialHomeomorph X.Carrier (Model s × Model r) where
  toFun := fun x ↦ (e.chart x).swap
  invFun := fun z ↦ e.chart.symm z.swap
  source := e.chart.source
  target := ball 0 e.radius ×ˢ ball 0 e.radius
  map_source' := by intro x hx; have h := e.chart.map_source hx; rw [e.product_range] at h; exact ⟨h.2,h.1⟩
  map_target' := by intro z hz; apply e.chart.map_target; rw [e.product_range]; exact ⟨hz.2,hz.1⟩
  left_inv' := by intro x hx; exact e.chart.left_inv hx
  right_inv' := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact congrArg Prod.swap (e.chart.right_inv ht)
  open_source := e.chart.open_source
  open_target := isOpen_ball.prod isOpen_ball
  continuousOn_toFun := continuous_swap.comp_continuousOn e.chart.continuousOn
  continuousOn_invFun := e.chart.continuousOn_symm.comp continuous_swap.continuousOn (by
    intro z hz; rw [e.product_range]; exact ⟨hz.2,hz.1⟩)

lemma SplittingChart.swapChart_holomorphic (e : SplittingChart S) :
    MDifferentiableOn (model n) 𝓘(ℂ,Model s × Model r) e.swapChart e.chart.source := by
  intro x hx
  exact (mdifferentiableAt_iff_differentiableAt.mpr
    (ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)).differentiableAt).comp_mdifferentiableWithinAt x
    (e.holomorphic x hx)

lemma SplittingChart.swapChart_derivative (e : SplittingChart S) {x : X.Carrier}
    (hx : x ∈ e.chart.source) (v : Tangent X x) :
    mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swapChart x v=
      (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart x v).swap := by
  let c := ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)
  have h := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := 𝓘(ℂ,Model s × Model r)) x
    (mdifferentiableAt_iff_differentiableAt.mpr c.differentiableAt)
    (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hx))
  change mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swapChart x = _ at h
  rw [mfderiv_eq_fderiv,c.hasFDerivAt.fderiv] at h
  exact congrArg (fun L : Model n →L[ℂ] (Model s × Model r) ↦ L v) h

def SplittingChart.swap (e : SplittingChart S) : SplittingChart S.swap where
  chart := e.swapChart
  radius := e.radius
  radius_pos := e.radius_pos
  product_range := rfl
  holomorphic := e.swapChart_holomorphic
  inverse_holomorphic := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds ht)).comp_mdifferentiableWithinAt z
      (mdifferentiableAt_iff_differentiableAt.mpr
        (ContinuousLinearEquiv.prodComm ℂ (Model s) (Model r)).differentiableAt).mdifferentiableWithinAt
  horizontal := by
    intro x hx v
    rw [e.swapChart_derivative hx]
    change v-S.projection x v=v ↔ _
    exact sub_eq_self.trans (e.vertical x hx v)
  vertical := by
    intro x hx v
    rw [e.swapChart_derivative hx]
    change v-S.projection x v=0 ↔ _
    exact sub_eq_zero.trans (eq_comm.trans (e.horizontal x hx v))

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

def CoverProductChart.swapChart (e : CoverProductChart π S) :
    OpenPartialHomeomorph Z.Carrier (Model s × Model r) where
  toFun := fun x ↦ (e.chart x).swap
  invFun := fun z ↦ e.chart.symm z.swap
  source := e.chart.source
  target := ball 0 e.radius ×ˢ ball 0 e.radius
  map_source' := by intro x hx; have h := e.chart.map_source hx; rw [e.product_range] at h; exact ⟨h.2,h.1⟩
  map_target' := by intro z hz; apply e.chart.map_target; rw [e.product_range]; exact ⟨hz.2,hz.1⟩
  left_inv' := by intro x hx; exact e.chart.left_inv hx
  right_inv' := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact congrArg Prod.swap (e.chart.right_inv ht)
  open_source := e.chart.open_source
  open_target := isOpen_ball.prod isOpen_ball
  continuousOn_toFun := continuous_swap.comp_continuousOn e.chart.continuousOn
  continuousOn_invFun := e.chart.continuousOn_symm.comp continuous_swap.continuousOn (by
    intro z hz; rw [e.product_range]; exact ⟨hz.2,hz.1⟩)

def CoverProductChart.swap (e : CoverProductChart π S) : CoverProductChart π S.swap where
  chart := e.swapChart
  radius := e.radius
  radius_pos := e.radius_pos
  product_range := rfl
  holomorphic := by
    intro x hx
    exact (mdifferentiableAt_iff_differentiableAt.mpr
      (ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)).differentiableAt).comp_mdifferentiableWithinAt x
      (e.holomorphic x hx)
  inverse_holomorphic := by
    intro z hz
    have ht : z.swap ∈ e.chart.target := by rw [e.product_range]; exact ⟨hz.2,hz.1⟩
    exact (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds ht)).comp_mdifferentiableWithinAt z
      (mdifferentiableAt_iff_differentiableAt.mpr
        (ContinuousLinearEquiv.prodComm ℂ (Model s) (Model r)).differentiableAt).mdifferentiableWithinAt
  downstairs := e.downstairs.swap
  maps := e.maps
  coordinates := fun z hz ↦ congrArg Prod.swap (e.coordinates z hz)

end UniversalCoverSplitting
end
end

end OAI
end



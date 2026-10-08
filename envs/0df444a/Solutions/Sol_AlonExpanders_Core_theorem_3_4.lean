-- Prove2me | solution 1 for AlonExpanders.Core.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T14:50:17.363708+00:00
-- url     : https://prove2.me/submissions/523944c6-030f-4d0b-ba25-9dd5ccd79e9f

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsIOBipartite
import Definitions.Def_AlonExpanders_Core_IsStrongExpander
import Theorems.Thm_AlonExpanders_Core_lemma_2_4
import Theorems.Thm_AlonExpanders_Core_lemma_3_1
import Theorems.Thm_AlonExpanders_Core_lemma_3_3


/-!
Auxiliary results for Lemma 2.4 of Alon, *Eigenvalues and expanders*: an elementary bound on
sums of squares, a fractional Hall theorem (the flow of the max-flow min-cut step), and the
Cauchy–Schwarz combination of (2.1), (2.2), (2.3).
-/

open Finset

namespace ALN

/-- If `0 ≤ xᵢ ≤ 1` and `∑ xᵢ ≤ 1 + c` with `c ≥ 0`, then `∑ xᵢ² ≤ 1 + c²`. -/
lemma sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) (hs : ∑ i ∈ s, x i ≤ 1 + c) :
    ∑ i ∈ s, x i ^ 2 ≤ 1 + c ^ 2 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp; positivity
  obtain ⟨m, hm, hmax⟩ := s.exists_max_image x hne
  set M := x m
  set R := ∑ i ∈ s.erase m, x i
  have hsplit : ∑ i ∈ s, x i = M + R := (Finset.add_sum_erase s x hm).symm
  have hsplit2 : ∑ i ∈ s, x i ^ 2 = M ^ 2 + ∑ i ∈ s.erase m, x i ^ 2 :=
    (Finset.add_sum_erase s (fun i => x i ^ 2) hm).symm
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i hi => h0 i (Finset.mem_of_mem_erase hi)
  have hM0 : 0 ≤ M := h0 m hm
  have hM1 : M ≤ 1 := h1 m hm
  have hTM : ∑ i ∈ s.erase m, x i ^ 2 ≤ M * R := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_of_mem_erase hi
    have := hmax i hi'
    nlinarith [h0 i hi']
  have hTR : ∑ i ∈ s.erase m, x i ^ 2 ≤ R * R := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_of_mem_erase hi
    have hle : x i ≤ R := Finset.single_le_sum (fun j hj => h0 j (Finset.mem_of_mem_erase hj)) hi
    nlinarith [h0 i hi']
  rw [hsplit] at hs
  rw [hsplit2]
  by_cases hR1 : R ≤ 1
  · by_cases ht : M + R ≤ 1
    · nlinarith
    · -- `M² + R² = 1 + (M + R - 1)² - 2(1 - M)(1 - R)`
      nlinarith [mul_nonneg (sub_nonneg.mpr hM1) (sub_nonneg.mpr hR1)]
  · have hMc : M ≤ c := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hMc hc]

/-- Monotonicity of `x ↦ x² / (4 + 2x²)` on `[0, ∞)`. -/
lemma bound_mono {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    c ^ 2 / (4 + 2 * c ^ 2) ≤ c' ^ 2 / (4 + 2 * c' ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hcc hcc hc (hc.trans hcc)]

section Flow

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Fractional Hall theorem** (the flow produced by the max-flow min-cut step of Alon's proof).
Each `u ∈ P` must send `(p + q)/q` units to vertices of its closed neighbourhood `Nb u`, every
vertex receiving at most `1`. This is possible as soon as `(p + q)|U| ≤ q |⋃_{u ∈ U} Nb u|` for
all `U ⊆ P`. -/
lemma exists_flow (P : Finset V) (Nb : V → Finset V) (p q : ℕ) (hq : 0 < q)
    (hHall : ∀ U ⊆ P, (p + q) * U.card ≤ q * (U.biUnion Nb).card) :
    ∃ F : V → V → ℝ, (∀ u v, 0 ≤ F u v) ∧ (∀ u v, F u v ≠ 0 → u ∈ P ∧ v ∈ Nb u) ∧
      (∀ u ∈ P, ∑ v, F u v = ((p + q : ℕ) : ℝ) / q) ∧ (∀ v, ∑ u, F u v ≤ 1) := by
  classical
  let ι := {x : V × Fin (p + q) // x.1 ∈ P}
  let t : ι → Finset (V × Fin q) := fun x => Nb x.1.1 ×ˢ (Finset.univ : Finset (Fin q))
  have hall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
    intro s
    set U := s.image (fun x : ι => x.1.1) with hU
    have hUP : U ⊆ P := by
      intro u hu
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu
      exact x.2
    have h1 : s.card ≤ (p + q) * U.card := by
      have : s.card ≤ (U ×ˢ (Finset.univ : Finset (Fin (p + q)))).card := by
        refine Finset.card_le_card_of_injOn (fun x : ι => x.1) ?_ ?_
        · intro x hx
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ,
            Set.mem_univ, and_true]
          exact Finset.mem_image_of_mem _ hx
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at this
      linarith
    have h2 : (U.biUnion Nb) ×ˢ (Finset.univ : Finset (Fin q)) ⊆ s.biUnion t := by
      intro y hy
      rw [Finset.mem_product] at hy
      obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp hy.1
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_product.mpr ⟨hyu, Finset.mem_univ _⟩⟩
    have h3 := Finset.card_le_card h2
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h3
    have := hHall U hUP
    nlinarith
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  let F : V → V → ℝ := fun u v =>
    ((Finset.univ.filter (fun x : ι => x.1.1 = u ∧ (f x).1 = v)).card : ℝ) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨F, fun u v => by positivity, ?_, ?_, ?_⟩
  · intro u v huv
    have hne : (Finset.univ.filter (fun x : ι => x.1.1 = u ∧ (f x).1 = v)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      apply huv
      simp only [F, h, Finset.card_empty, Nat.cast_zero, zero_div]
    obtain ⟨x, hx⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨x.2, (Finset.mem_product.mp (hft x)).1⟩
  · intro u hu
    simp only [F, ← Finset.sum_div]
    congr 1
    rw [← Nat.cast_sum]
    congr 1
    have h := Finset.card_eq_sum_card_fiberwise (f := fun x : ι => (f x).1)
      (s := Finset.univ.filter (fun x : ι => x.1.1 = u)) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    rw [← h]
    have hset : Finset.univ.filter (fun x : ι => x.1.1 = u) =
        Finset.univ.map ⟨fun i : Fin (p + q) => (⟨(u, i), hu⟩ : ι), fun i j hij => by
          simpa using congrArg (fun x : ι => x.1.2) hij⟩ := by
      ext ⟨⟨w, i⟩, hw⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · rintro rfl
        exact ⟨i, rfl⟩
      · rintro ⟨j, hj⟩
        have := congrArg (fun x : ι => x.1.1) hj
        exact this.symm
    rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro v
    simp only [F, ← Finset.sum_div]
    rw [div_le_one hqR, ← Nat.cast_sum]
    have hsum : ∑ u, (Finset.univ.filter (fun x : ι => x.1.1 = u ∧ (f x).1 = v)).card =
        (Finset.univ.filter (fun x : ι => (f x).1 = v)).card := by
      have h := Finset.card_eq_sum_card_fiberwise (f := fun x : ι => x.1.1)
        (s := Finset.univ.filter (fun x : ι => (f x).1 = v)) (t := Finset.univ)
        (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
      rw [h]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.filter_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [hsum]
    have : (Finset.univ.filter (fun x : ι => (f x).1 = v)).card ≤
        (Finset.univ.filter (fun y : V × Fin q => y.1 = v)).card := by
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro x hx
        simpa using hx
      · exact fun x _ y _ h => hfinj h
    have hc : (Finset.univ.filter (fun y : V × Fin q => y.1 = v)).card = q := by
      have hset : Finset.univ.filter (fun y : V × Fin q => y.1 = v) =
          Finset.univ.map ⟨fun i : Fin q => (v, i), fun i j hij => by
            simpa using congrArg Prod.snd hij⟩ := by
        ext ⟨w, i⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        constructor
        · rintro rfl
          exact ⟨i, rfl⟩
        · rintro ⟨j, hj⟩
          have := congrArg Prod.fst hj
          exact this.symm
      rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast this.trans hc.le

end Flow

end ALN

/-!
The analytic core of Lemma 2.4 (inequalities (2.2), (2.3) and the Cauchy–Schwarz step), and the
existence of a suitable eigenvector for `λ(G)`.
-/

open Finset Matrix WithLp
open scoped InnerProductSpace

namespace ALN

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Inequalities (2.2), (2.3) and the Cauchy–Schwarz step of Alon's proof. `g ≥ 0` is the positive
part of the eigenvector, `F u v` the flow sent from `u` to `v` (`u = v` or `uv ∈ E`); rows with
`g u ≠ 0` carry `1 + c`, every vertex receives at most `1`. Together with (2.1) this gives
`λ ≥ c² / (4 + 2c²)`. -/
lemma key (G : SimpleGraph V) [DecidableRel G.Adj] (g : V → ℝ) (F : V → V → ℝ) (c lam : ℝ)
    (hc : 0 ≤ c) (hF0 : ∀ u v, 0 ≤ F u v) (hFadj : ∀ u v, F u v ≠ 0 → u = v ∨ G.Adj u v)
    (hrow : ∀ u, g u ≠ 0 → ∑ v, F u v = 1 + c) (hrow' : ∀ u, ∑ v, F u v ≤ 1 + c)
    (hcol : ∀ v, ∑ u, F u v ≤ 1)
    (h21 : (1 / 2 : ℝ) * ∑ u, ∑ v, (if G.Adj u v then (g u - g v) ^ 2 else 0) ≤
      lam * ∑ v, g v ^ 2)
    (hpos : 0 < ∑ v, g v ^ 2) : c ^ 2 / (4 + 2 * c ^ 2) ≤ lam := by
  set Z := ∑ v, g v ^ 2 with hZ
  have hF1 : ∀ u v, F u v ≤ 1 := fun u v =>
    (Finset.single_le_sum (f := fun u' => F u' v) (fun u' _ => hF0 u' v)
      (Finset.mem_univ u)).trans (hcol v)
  set S := ∑ u, ∑ v, F u v * (g u ^ 2 - g v ^ 2) with hSdef
  -- (2.3): `S ≥ c Σ g²`
  have hS1 : S = ∑ u, g u ^ 2 * ∑ v, F u v - ∑ v, g v ^ 2 * ∑ u, F u v := by
    simp only [hSdef, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hScZ : c * Z ≤ S := by
    have e1 : ∑ u, g u ^ 2 * ∑ v, F u v = (1 + c) * Z := by
      rw [hZ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h : g u = 0
      · simp [h]
      · rw [hrow u h]; ring
    have e2 : ∑ v, g v ^ 2 * ∑ u, F u v ≤ Z :=
      Finset.sum_le_sum fun v _ => mul_le_of_le_one_right (sq_nonneg _) (hcol v)
    rw [hS1, e1]
    linarith
  -- antisymmetrize: `2S = Σ A B` with `A = [uv ∈ E](g u - g v)`, `B = h(u,v)(g u + g v)`
  let A : V → V → ℝ := fun u v => if G.Adj u v then g u - g v else 0
  let B : V → V → ℝ := fun u v => (F u v - F v u) * (g u + g v)
  have hAB : 2 * S = ∑ u, ∑ v, A u v * B u v := by
    have hswap : ∑ u, ∑ v, F v u * (g u ^ 2 - g v ^ 2) = -S := by
      rw [Finset.sum_comm, hSdef, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun u _ => by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
    have hterm : ∀ u v, A u v * B u v =
        F u v * (g u ^ 2 - g v ^ 2) - F v u * (g u ^ 2 - g v ^ 2) := by
      intro u v
      simp only [A, B]
      split_ifs with h
      · ring
      · by_cases huv : u = v
        · subst huv; ring
        · have h1 : F u v = 0 := by
            by_contra h'
            rcases hFadj u v h' with h'' | h''
            · exact huv h''
            · exact h h''
          have h2 : F v u = 0 := by
            by_contra h'
            rcases hFadj v u h' with h'' | h''
            · exact huv h''.symm
            · exact h h''.symm
          rw [h1, h2]; ring
    simp only [hterm, Finset.sum_sub_distrib, hswap]
    ring
  have hCS : (∑ u, ∑ v, A u v * B u v) ^ 2 ≤
      (∑ u, ∑ v, A u v ^ 2) * (∑ u, ∑ v, B u v ^ 2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (V × V))
      (fun x => A x.1 x.2) (fun x => B x.1 x.2)
    have e1 : ∑ u, ∑ v, A u v * B u v = ∑ x : V × V, A x.1 x.2 * B x.1 x.2 :=
      (Fintype.sum_prod_type' _).symm
    have e2 : ∑ u, ∑ v, A u v ^ 2 = ∑ x : V × V, A x.1 x.2 ^ 2 :=
      (Fintype.sum_prod_type' _).symm
    have e3 : ∑ u, ∑ v, B u v ^ 2 = ∑ x : V × V, B x.1 x.2 ^ 2 :=
      (Fintype.sum_prod_type' _).symm
    rw [e1, e2, e3]
    exact this
  -- (2.1)
  have hA : ∑ u, ∑ v, A u v ^ 2 ≤ 2 * lam * Z := by
    have : ∑ u, ∑ v, A u v ^ 2 = ∑ u, ∑ v, (if G.Adj u v then (g u - g v) ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      simp only [A]
      split_ifs <;> ring
    rw [this]
    linarith
  -- (2.2)
  have hrowsq : ∀ u, ∑ v, F u v ^ 2 ≤ 1 + c ^ 2 := fun u =>
    sum_sq_le _ _ c hc (fun v _ => hF0 u v) (fun v _ => hF1 u v) (hrow' u)
  have hcolsq : ∀ u, ∑ v, F v u ^ 2 ≤ 1 := fun u =>
    (Finset.sum_le_sum fun v _ => by nlinarith [hF0 v u, hF1 v u] :
      ∑ v, F v u ^ 2 ≤ ∑ v, F v u).trans (hcol u)
  have hH : ∀ u, ∑ v, (F u v - F v u) ^ 2 ≤ 2 + c ^ 2 := by
    intro u
    have : ∑ v, (F u v - F v u) ^ 2 ≤ ∑ v, (F u v ^ 2 + F v u ^ 2) :=
      Finset.sum_le_sum fun v _ => by nlinarith [mul_nonneg (hF0 u v) (hF0 v u)]
    rw [Finset.sum_add_distrib] at this
    linarith [hrowsq u, hcolsq u]
  have hB : ∑ u, ∑ v, B u v ^ 2 ≤ 4 * (2 + c ^ 2) * Z := by
    have h1 : ∀ u v, B u v ^ 2 ≤
        2 * (F u v - F v u) ^ 2 * g u ^ 2 + 2 * (F v u - F u v) ^ 2 * g v ^ 2 := by
      intro u v
      simp only [B]
      nlinarith [sq_nonneg ((F u v - F v u) * (g u - g v))]
    have hsw : ∑ u, ∑ v, 2 * (F v u - F u v) ^ 2 * g v ^ 2 =
        ∑ u, ∑ v, 2 * (F u v - F v u) ^ 2 * g u ^ 2 := Finset.sum_comm
    have h2 : ∀ u, ∑ v, 2 * (F u v - F v u) ^ 2 * g u ^ 2 ≤ 2 * (2 + c ^ 2) * g u ^ 2 := by
      intro u
      have : ∑ v, 2 * (F u v - F v u) ^ 2 * g u ^ 2 =
          2 * g u ^ 2 * ∑ v, (F u v - F v u) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [this]
      nlinarith [hH u, sq_nonneg (g u)]
    calc ∑ u, ∑ v, B u v ^ 2
        ≤ ∑ u, ∑ v, (2 * (F u v - F v u) ^ 2 * g u ^ 2 + 2 * (F v u - F u v) ^ 2 * g v ^ 2) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h1 u v
      _ = 2 * ∑ u, ∑ v, 2 * (F u v - F v u) ^ 2 * g u ^ 2 := by
          simp only [Finset.sum_add_distrib]
          rw [hsw]
          ring
      _ ≤ 2 * ∑ u, 2 * (2 + c ^ 2) * g u ^ 2 := by
          gcongr with u
          exact h2 u
      _ = 4 * (2 + c ^ 2) * Z := by
          rw [hZ, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring
  -- combine
  have hA0 : 0 ≤ 2 * lam * Z :=
    le_trans (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _) hA
  have hB0 : 0 ≤ ∑ u, ∑ v, B u v ^ 2 :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  have h4 : (2 * S) ^ 2 ≤ (2 * lam * Z) * (4 * (2 + c ^ 2) * Z) := by
    rw [hAB]
    exact hCS.trans (mul_le_mul hA hB hB0 hA0)
  have hcS : (c * Z) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (mul_nonneg hc hpos.le) hScZ 2
  have hZ2 : 0 < Z ^ 2 := by positivity
  have hfin : c ^ 2 * Z ^ 2 ≤ (2 * lam * (2 + c ^ 2)) * Z ^ 2 := by nlinarith
  have hfin' := le_of_mul_le_mul_right hfin hZ2
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### The eigenvector -/

noncomputable abbrev ev (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀
noncomputable abbrev basis (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis
    finrank_euclideanSpace

theorem ev_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin (Fintype.card V)) :
    0 ≤ ev G i := by
  have h := (G.posSemidef_lapMatrix ℝ).eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card V) ≃ V) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

theorem eigen (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin (Fintype.card V)) :
    G.lapMatrix ℝ *ᵥ ⇑(basis G i) = ev G i • ⇑(basis G i) := by
  have h := (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).apply_eigenvectorBasis
    finrank_euclideanSpace i
  exact congrArg (fun x : EuclideanSpace ℝ V => (x : V → ℝ)) h

theorem last_zero (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) :
    ev G ⟨Fintype.card V - 1, by omega⟩ = 0 := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hd := G.det_lapMatrix_eq_zero
  rw [(G.isHermitian_lapMatrix ℝ).det_eq_prod_eigenvalues] at hd
  obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hd
  apply le_antisymm _ (ev_nonneg G _)
  let i := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card V) ≃ V).symm v
  have hi : ev G i = 0 := hv
  rw [← hi]
  apply (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
  apply Fin.le_iff_val_le_val.mpr
  change i.val ≤ Fintype.card V - 1
  have := i.isLt
  omega

/-- The entries of `Q x` sum to zero (`Q` is symmetric and kills constants). -/
theorem sum_lap_mulVec (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    ∑ v, (G.lapMatrix ℝ *ᵥ x) v = 0 := by
  have hsym : ∀ u v, G.lapMatrix ℝ u v = G.lapMatrix ℝ v u := fun u v =>
    (congrFun (congrFun (G.isSymm_lapMatrix (R := ℝ)) v) u)
  have h1 : ∀ u, ∑ v, G.lapMatrix ℝ u v = 0 := fun u => by
    have := congrFun (G.lapMatrix_mulVec_const_eq_zero (R := ℝ)) u
    simpa [mulVec, dotProduct] using this
  simp only [mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun u _ => ?_
  simp_rw [hsym _ u]
  rw [← Finset.sum_mul, h1 u, zero_mul]

theorem inner_basis (G : SimpleGraph V) [DecidableRel G.Adj] (i j : Fin (Fintype.card V)) :
    ∑ v, basis G i v * basis G j v = if i = j then 1 else 0 := by
  have h := (basis G).inner_eq_ite i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [star_trivial, dotProduct] at h
  rw [← h]
  exact Finset.sum_congr rfl fun v _ => mul_comm _ _

/-- An eigenvector of `Q` for `λ(G)` orthogonal to the constants (as in Alon's proof, where `f` is
taken orthogonal to the eigenvector `(1, …, 1)` of the eigenvalue `0`). -/
theorem exists_eigvec (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) :
    ∃ f : V → ℝ, f ≠ 0 ∧ ∑ v, f v = 0 ∧
      G.lapMatrix ℝ *ᵥ f = AlonMilman.Diameter.lambda1 G • f := by
  set a : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  set b : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp only [a, b] at this
    omega
  have hlam : AlonMilman.Diameter.lambda1 G = ev G a := by
    rw [AlonMilman.Diameter.lambda1, dif_pos hn]
  set ea : V → ℝ := ⇑(basis G a)
  set eb : V → ℝ := ⇑(basis G b)
  have hea : ∑ v, ea v * ea v = 1 := by simpa using inner_basis G a a
  have heb : ∑ v, eb v * eb v = 1 := by simpa using inner_basis G b b
  have heab : ∑ v, ea v * eb v = 0 := by simpa [hab] using inner_basis G a b
  set sa := ∑ v, ea v
  set sb := ∑ v, eb v
  by_cases hsa : sa = 0
  · refine ⟨ea, ?_, hsa, ?_⟩
    · intro h
      rw [h] at hea
      simp at hea
    · rw [hlam]; exact eigen G a
  · -- then `λ(G) = 0`, and a combination of the two last eigenvectors works
    have hl0 : ev G a = 0 := by
      have h := sum_lap_mulVec G ea
      rw [eigen G a] at h
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
      exact (mul_eq_zero.mp h).resolve_right hsa
    have hb0 : ev G b = 0 := last_zero G hn
    refine ⟨sb • ea - sa • eb, ?_, ?_, ?_⟩
    · intro h
      have h' : ∑ v, (sb • ea - sa • eb) v * eb v = 0 := by rw [h]; simp
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        mul_assoc, ← Finset.mul_sum, heab, heb] at h'
      apply hsa
      linarith
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      change sb * sa - sa * sb = 0
      ring
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, eigen G a, eigen G b,
        hl0, hb0, hlam, hl0]
      simp

/-- Choose the sign of the eigenvector so that `0 < |V⁺| ≤ n/2`. -/
theorem exists_eigvec_pos (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) :
    ∃ f : V → ℝ, f ≠ 0 ∧ G.lapMatrix ℝ *ᵥ f = AlonMilman.Diameter.lambda1 G • f ∧
      (∃ v, 0 < f v) ∧ 2 * (Finset.univ.filter (fun v => 0 < f v)).card ≤ Fintype.card V := by
  obtain ⟨f, hf0, hfs, hf⟩ := exists_eigvec G hn
  have hpos : ∀ h : V → ℝ, h ≠ 0 → ∑ v, h v = 0 → ∃ v, 0 < h v := by
    intro h hh hs
    by_contra hc
    push_neg at hc
    apply hh
    funext v
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => hc v)).mp hs v (Finset.mem_univ v)
  have hcard : (Finset.univ.filter (fun v => 0 < f v)).card +
      (Finset.univ.filter (fun v => 0 < (-f) v)).card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_univ _
    · rw [Finset.disjoint_filter]
      intro v _ h1 h2
      simp only [Pi.neg_apply] at h2
      linarith
  by_cases h2 : 2 * (Finset.univ.filter (fun v => 0 < f v)).card ≤ Fintype.card V
  · exact ⟨f, hf0, hf, hpos f hf0 hfs, h2⟩
  · refine ⟨-f, neg_ne_zero.mpr hf0, ?_, hpos (-f) (neg_ne_zero.mpr hf0) ?_, by omega⟩
    · rw [Matrix.mulVec_neg, hf, smul_neg]
    · simp [Finset.sum_neg_distrib, hfs]

end ALN

/-! Spectral facts used in the proof of Theorem 3.4: the Rayleigh bound on the orthogonal
complement of the last eigenvector, `λ(G) ≤ d` for `d`-regular bipartite graphs with at least two
inputs, the value `λ(K₂) = 2`, and `λ(G) = 0` for edgeless graphs. -/

open Finset Matrix WithLp
open scoped InnerProductSpace

namespace ALN

variable {V : Type} [Fintype V] [DecidableEq V]

theorem parseval (G : SimpleGraph V) [DecidableRel G.Adj] (x y : EuclideanSpace ℝ V) :
    ∑ i, (basis G).repr x i * (basis G).repr y i = (x : V → ℝ) ⬝ᵥ (y : V → ℝ) := by
  have h := (basis G).repr.inner_map_map x y
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, mul_comm] using h

theorem repr_mul (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (i : Fin (Fintype.card V)) :
    (basis G).repr (toLp 2 (G.lapMatrix ℝ *ᵥ f)) i = ev G i * (basis G).repr (toLp 2 f) i :=
  (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace (toLp 2 f) i

/-- Rayleigh bound: if `z` is orthogonal to the eigenvector of the smallest eigenvalue, then
`λ(G) ‖z‖² ≤ ⟨z, Q z⟩`. -/
theorem rayleigh_orth (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V)
    (z : V → ℝ) (hz : ∑ v, basis G ⟨Fintype.card V - 1, by omega⟩ v * z v = 0) :
    AlonMilman.Diameter.lambda1 G * (z ⬝ᵥ z) ≤ z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z) := by
  let c := (basis G).repr (toLp 2 z)
  have hc : c ⟨Fintype.card V - 1, by omega⟩ = 0 := by
    change (basis G).repr (toLp 2 z) _ = 0
    rw [OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct]
    rw [← hz]
    exact Finset.sum_congr rfl fun v _ => by simp [mul_comm]
  have hnrm := parseval G (toLp 2 z) (toLp 2 z)
  have hq := parseval G (toLp 2 z) (toLp 2 (G.lapMatrix ℝ *ᵥ z))
  simp only [repr_mul] at hq
  change ∑ i, c i * c i = z ⬝ᵥ z at hnrm
  change ∑ i, c i * (ev G i * c i) = z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z) at hq
  rw [← hnrm, ← hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases he : i = ⟨Fintype.card V - 1, by omega⟩
  · subst i
    rw [hc]
    simp
  · have hle : i ≤ (⟨Fintype.card V - 2, by omega⟩ : Fin (Fintype.card V)) := by
      apply Fin.le_iff_val_le_val.mpr
      change i.val ≤ Fintype.card V - 2
      have hiLt := i.isLt
      have hv : i.val ≠ Fintype.card V - 1 := fun h => he (Fin.ext h)
      omega
    have hge := (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone hle
    rw [AlonMilman.Diameter.lambda1, dif_pos hn]
    nlinarith [sq_nonneg (c i), mul_nonneg (sub_nonneg.mpr hge) (sq_nonneg (c i))]

/-- An edgeless graph has `λ(G) = 0`. -/
theorem lambda1_eq_zero_of_noAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ u v, ¬ G.Adj u v) : AlonMilman.Diameter.lambda1 G = 0 := by
  by_cases hn : 2 ≤ Fintype.card V
  · obtain ⟨f, hf0, -, hf⟩ := exists_eigvec G hn
    have hQ : G.lapMatrix ℝ *ᵥ f = 0 := by
      funext v
      rw [SimpleGraph.lapMatrix_mulVec_apply]
      have hdeg : G.degree v = 0 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
        ext u
        simp [h v u]
      have hnb : G.neighborFinset v = ∅ := by
        ext u
        simp [h v u]
      simp [hdeg, hnb]
    rw [hQ] at hf
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hf0
    have := congrFun hf v
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hv
  · rw [AlonMilman.Diameter.lambda1, dif_neg hn]

end ALN

namespace ALN

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- For a `d`-regular bipartite graph with at least two inputs, `λ(G) ≤ d`: the Rayleigh quotient of
every vector supported on the inputs equals `d`, and the inputs carry a two-dimensional space of
such vectors, which meets the orthogonal complement of the last eigenvector. -/
theorem lambda1_le_deg (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (d : ℕ)
    (hbip : AlonExpanders.Core.IsIOBipartite G) (hreg : G.IsRegularOfDegree d)
    (hI : 2 ≤ Fintype.card I) : AlonMilman.Diameter.lambda1 G ≤ d := by
  have hn : 2 ≤ Fintype.card (I ⊕ O) := by rw [Fintype.card_sum]; omega
  haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i1, i2, h12⟩ := exists_pair_ne I
  set eb : I ⊕ O → ℝ := ⇑(basis G ⟨Fintype.card (I ⊕ O) - 1, by omega⟩) with heb
  -- a nonzero vector on the inputs orthogonal to `eb`
  obtain ⟨zI, hzI0, hzorth⟩ : ∃ zI : I → ℝ, zI ≠ 0 ∧ ∑ i, eb (Sum.inl i) * zI i = 0 := by
    by_cases hb : eb (Sum.inl i1) = 0
    · refine ⟨fun i => if i = i1 then 1 else 0, ?_, ?_⟩
      · intro h
        have := congrFun h i1
        simp at this
      · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hb]
    · refine ⟨fun i => (if i = i1 then eb (Sum.inl i2) else 0) -
          (if i = i2 then eb (Sum.inl i1) else 0), ?_, ?_⟩
      · intro h
        have := congrFun h i2
        simp only [h12.symm, if_false, if_true, zero_sub, Pi.zero_apply, neg_eq_zero] at this
        exact hb this
      · simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        ring
  let z : I ⊕ O → ℝ := Sum.elim zI (fun _ => 0)
  have hz : ∑ v, eb v * z v = 0 := by
    rw [Fintype.sum_sum_type]
    simp [z, hzorth]
  have hray := rayleigh_orth G hn z hz
  -- `⟨z, Q z⟩ = d ‖z‖²`
  have hQz : z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z) = (d : ℝ) * (z ⬝ᵥ z) := by
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [SimpleGraph.lapMatrix_mulVec_apply, hreg v]
    rcases v with i | o
    · have : ∑ u ∈ G.neighborFinset (Sum.inl i), z u = 0 := by
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [SimpleGraph.mem_neighborFinset] at hu
        rcases u with i' | o'
        · exact absurd hu (hbip.1 i i')
        · rfl
      rw [this]
      ring
    · simp [z]
  have hzz : 0 < z ⬝ᵥ z := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hzI0
    have h1 : 0 < z (Sum.inl i) * z (Sum.inl i) := by
      simp only [z, Sum.elim_inl]
      exact mul_self_pos.mpr hi
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun v => z v * z v)
      (fun v _ => mul_self_nonneg _) (Finset.mem_univ _))
  rw [hQz] at hray
  exact le_of_mul_le_mul_right hray hzz

/-- `λ(K₂) = 2`: the bipartite graph with one input, one output and the edge between them. -/
theorem lambda1_K2 (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj]
    (hI : Fintype.card I = 1) (hO : Fintype.card O = 1)
    (hbip : AlonExpanders.Core.IsIOBipartite G) (i : I) (o : O)
    (hadj : G.Adj (Sum.inl i) (Sum.inr o)) : AlonMilman.Diameter.lambda1 G = 2 := by
  have hn : 2 ≤ Fintype.card (I ⊕ O) := by rw [Fintype.card_sum]; omega
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.mp hI
  obtain ⟨o0, ho0⟩ := Fintype.card_eq_one_iff.mp hO
  have hiI : ∀ y : I, y = i := fun y => (hi0 y).trans (hi0 i).symm
  have hoO : ∀ y : O, y = o := fun y => (ho0 y).trans (ho0 o).symm
  obtain ⟨f, hf0, hfs, hf⟩ := exists_eigvec G hn
  set a : I ⊕ O := Sum.inl i
  set b : I ⊕ O := Sum.inr o
  have hsum : f a + f b = 0 := by
    rw [Fintype.sum_sum_type] at hfs
    rw [Fintype.sum_eq_single i (fun y hy => (hy (hiI y)).elim),
      Fintype.sum_eq_single o (fun y hy => (hy (hoO y)).elim)] at hfs
    exact hfs
  have hnb : G.neighborFinset a = {b} := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    rcases v with y | y
    · rw [hiI y]
      simp only [a, b, reduceCtorEq, iff_false]
      exact G.irrefl
    · rw [hoO y]
      simp only [a, b, iff_true]
      exact hadj
  have hdeg : G.degree a = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb, Finset.card_singleton]
  have hQa := congrFun hf a
  rw [SimpleGraph.lapMatrix_mulVec_apply, hdeg, hnb, Finset.sum_singleton] at hQa
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul] at hQa
  have hfa : f a ≠ 0 := by
    intro h
    apply hf0
    funext v
    rcases v with y | y
    · rw [hiI y]; exact h
    · rw [hoO y]; change f b = 0; linarith
  have : (AlonMilman.Diameter.lambda1 G - 2) * f a = 0 := by
    have hb : f b = - f a := by linarith
    rw [hb] at hQa
    linarith
  linarith [(mul_eq_zero.mp this).resolve_right hfa]

end ALN

/-! Theorem 3.4 of Alon, *Eigenvalues and expanders*. -/

open Finset

namespace ALN

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

open AlonExpanders.Core

/-- Strong expansion is monotone in the constant. -/
lemma strong_mono (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) {c c' : ℝ}
    (h : IsStrongExpander G n d c) (hcc : c' ≤ c) : IsStrongExpander G n d c' := by
  obtain ⟨hI, hO, hb, hd, hX⟩ := h
  refine ⟨hI, hO, hb, hd, fun X => le_trans ?_ (hX X)⟩
  have hXn : (X.card : ℝ) ≤ n := by rw [← hI]; exact_mod_cast X.card_le_univ
  have h1 : 0 ≤ 1 - (X.card : ℝ) / n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [sub_nonneg, div_le_one (by exact_mod_cast hn)]
      exact hXn
  exact mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hcc h1])
    (Nat.cast_nonneg _)

/-- With at most one input, a `d`-regular bipartite graph with `d ≥ 1` is a strong
`(n, d, c)`-expander for every `c`. -/
lemma strong_small (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ)
    (hd : 1 ≤ d) (hn : n ≤ 1) (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) : IsStrongExpander G n d c := by
  refine ⟨hI, hO, hbip, G.maxDegree_le_of_forall_degree_le d (fun v => (hreg v).le), ?_⟩
  intro X
  rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have hXc : X.card = n := by
      have h1 := X.card_le_univ
      have h2 := X.card_pos.mpr ⟨x, hx⟩
      rw [hI] at h1
      omega
    have hn1 : n = 1 := by
      have := X.card_pos.mpr ⟨x, hx⟩
      omega
    rw [hXc, hn1]
    simp only [Nat.cast_one, div_one, sub_self, mul_zero, add_zero, one_mul, Nat.one_le_cast]
    -- `inl x` has a neighbour
    have hdeg := hreg (Sum.inl x)
    have hne : (G.neighborFinset (Sum.inl x)).Nonempty := by
      rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree, hdeg]
      omega
    obtain ⟨v, hv⟩ := hne
    rw [SimpleGraph.mem_neighborFinset] at hv
    have hmem : v ∈ AKSSorting.Core.neighbours G (X.map Function.Embedding.inl) :=
      ⟨Sum.inl x, Finset.mem_map_of_mem _ hx, hv⟩
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, hmem⟩

theorem theorem34 (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    (∀ c : ℝ, 0 ≤ c → 1 ≤ n → IsStrongExpander G n d c →
        c ^ 2 / (1024 + 2 * c ^ 2) ≤ AlonMilman.Diameter.lambda1 G) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ AlonMilman.Diameter.lambda1 G →
        IsStrongExpander G n d ((2 * (d : ℝ) * ε - ε ^ 2) / (d : ℝ) ^ 2)) := by
  constructor
  · intro c hc hn1 hexp
    by_cases hn2 : 2 ≤ n
    · -- Lemma 3.1, then Lemma 2.4 with constant `c/16`
      have hm := lemma_3_1 G n d c hn2 hexp
      have h24 := lemma_2_4 G (2 * n) d (c / 16) (by omega) (by positivity) hm
      have heq : (c / 16) ^ 2 / (4 + 2 * (c / 16) ^ 2) = c ^ 2 / (1024 + 2 * c ^ 2) := by
        field_simp
        ring
      rwa [heq] at h24
    · -- `n = 1`: the graph is `K₂`, and `λ(K₂) = 2`
      have hn : n = 1 := by omega
      subst hn
      obtain ⟨-, -, -, -, hX⟩ := hexp
      obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hI
      have h1 := hX {i}
      simp only [Finset.card_singleton, Nat.cast_one, div_one, sub_self, mul_zero, add_zero,
        one_mul] at h1
      have hpos : 0 < (AKSSorting.Core.neighbours G
          (({i} : Finset I).map Function.Embedding.inl)).ncard := by
        exact_mod_cast (lt_of_lt_of_le one_pos h1)
      obtain ⟨v, x, hx, hxv⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
      simp only [Finset.map_singleton, Function.Embedding.inl_apply,
        Finset.mem_singleton] at hx
      subst hx
      rcases v with i' | o
      · exact absurd hxv (hbip.1 i i')
      · rw [lambda1_K2 G hI hO hbip i o hxv]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg c]
  · intro ε hε hel
    by_cases hd0 : d = 0
    · exfalso
      have h0 : AlonMilman.Diameter.lambda1 G = 0 := by
        apply lambda1_eq_zero_of_noAdj
        intro u v huv
        have := hreg u
        rw [hd0, ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero] at this
        have hv : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).mpr huv
        rw [this] at hv
        simp at hv
      linarith
    · by_cases hn2 : 2 ≤ n
      · -- `λ ≤ d`, so `ε ↦ 2dε − ε²` is monotone on `[ε, λ]`; then Lemma 3.3
        have hld : AlonMilman.Diameter.lambda1 G ≤ d :=
          lambda1_le_deg G d hbip hreg (by omega)
        have h33 := lemma_3_3 G n d (by omega) hI hO hbip hreg
        refine strong_mono G n d h33 ?_
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      · exact strong_small G n d _ (by omega) (by omega) hI hO hbip hreg

end ALN

open AlonExpanders.Core in
theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    (∀ c : ℝ, 0 ≤ c → 1 ≤ n → IsStrongExpander G n d c →
        c ^ 2 / (1024 + 2 * c ^ 2) ≤ AlonMilman.Diameter.lambda1 G) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ AlonMilman.Diameter.lambda1 G →
        IsStrongExpander G n d ((2 * (d : ℝ) * ε - ε ^ 2) / (d : ℝ) ^ 2)) :=
  ALN.theorem34 G n d hI hO hbip hreg

-- Prove2me | solution 1 for AlonExpanders.Core.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T14:50:15.500706+00:00
-- url     : https://prove2.me/submissions/a327641d-eafa-444b-b987-6cdce10da8e6

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsMagnifier
import Theorems.Thm_AlonExpanders_Core_eq_2_1


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

/-! Lemma 2.4 of Alon, *Eigenvalues and expanders*: every `(n, d, c)`-magnifier has
`λ(G) ≥ c² / (4 + 2c²)`. -/

open Finset

namespace ALN

variable {V : Type} [Fintype V] [DecidableEq V]

lemma ncard_nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    (AKSSorting.Core.neighbours G X \ (X : Set V)).ncard =
      ((Finset.univ.filter (fun v => ∃ x ∈ X, G.Adj x v)) \ X).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp [AKSSorting.Core.neighbours]

theorem lemma24 (G : SimpleGraph V) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ) (hn : 2 ≤ n)
    (hc : 0 ≤ c) (hG : AlonExpanders.Core.IsMagnifier G n d c) :
    c ^ 2 / (4 + 2 * c ^ 2) ≤ AlonMilman.Diameter.lambda1 G := by
  obtain ⟨hcard, -, hmag⟩ := hG
  have hn' : 2 ≤ Fintype.card V := hcard ▸ hn
  obtain ⟨f, hf0, hf, ⟨w, hw⟩, hhalf⟩ := exists_eigvec_pos G hn'
  set P := Finset.univ.filter (fun v => 0 < f v) with hP
  have hwP : w ∈ P := by simp [hP, hw]
  let Nf : Finset V → Finset V := fun X => (Finset.univ.filter (fun v => ∃ x ∈ X, G.Adj x v)) \ X
  -- the magnifying property for subsets of `V⁺`
  have hmagP : ∀ U ⊆ P, c * U.card ≤ (Nf U).card := by
    intro U hU
    have h2 : 2 * U.card ≤ n := by
      rw [← hcard]
      have := Finset.card_le_card hU
      omega
    have := hmag U h2
    rwa [ncard_nbhd] at this
  -- the best magnifying constant `c* = p/q ≥ c` on subsets of `V⁺` is rational
  have hne : (P.powerset.filter (fun U => U.Nonempty)).Nonempty := ⟨{w}, by simp [hwP]⟩
  obtain ⟨U0, hU0, hmin⟩ := (P.powerset.filter (fun U => U.Nonempty)).exists_min_image
    (fun U => ((Nf U).card : ℝ) / U.card) hne
  simp only [Finset.mem_filter, Finset.mem_powerset] at hU0
  set p := (Nf U0).card
  set q := U0.card
  have hq : 0 < q := hU0.2.card_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set cs : ℝ := (p : ℝ) / q with hcs
  have hccs : c ≤ cs := by
    rw [hcs, le_div_iff₀ hqR]
    exact hmagP U0 hU0.1
  have hcs0 : 0 ≤ cs := by positivity
  have hratio : ∀ U ⊆ P, p * U.card ≤ q * (Nf U).card := by
    intro U hU
    rcases U.eq_empty_or_nonempty with rfl | hUne
    · simp
    · have := hmin U (by simp [hU, hUne])
      rw [div_le_div_iff₀ hqR (by exact_mod_cast hUne.card_pos)] at this
      have h' : (p : ℝ) * U.card ≤ q * (Nf U).card := by linarith
      exact_mod_cast h'
  -- Hall's condition for the network of the max-flow min-cut step
  let Nb : V → Finset V := fun u => insert u (Finset.univ.filter (G.Adj u))
  have hHall : ∀ U ⊆ P, (p + q) * U.card ≤ q * (U.biUnion Nb).card := by
    intro U hU
    have hsub : U ∪ Nf U ⊆ U.biUnion Nb := by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · exact Finset.mem_biUnion.mpr ⟨v, h, Finset.mem_insert_self _ _⟩
      · simp only [Nf, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at h
        obtain ⟨⟨x, hx, hxv⟩, -⟩ := h
        exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_of_mem (by simp [hxv])⟩
    have hdisj : Disjoint U (Nf U) := Finset.disjoint_sdiff
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    have h2 := hratio U hU
    nlinarith
  obtain ⟨F, hF0, hFsupp, hFrow, hFcol⟩ := exists_flow P Nb p q hq hHall
  have hrowval : ((p + q : ℕ) : ℝ) / q = 1 + cs := by
    rw [hcs]
    push_cast
    field_simp
    ring
  have hFadj : ∀ u v, F u v ≠ 0 → u = v ∨ G.Adj u v := by
    intro u v h
    have hv := (hFsupp u v h).2
    simp only [Nb, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with rfl | hv
    · exact Or.inl rfl
    · exact Or.inr hv
  have hgP : ∀ u, max (f u) 0 ≠ 0 → u ∈ P := by
    intro u hu
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h
    push_neg at h
    exact hu (max_eq_right h)
  have hrow' : ∀ u, ∑ v, F u v ≤ 1 + cs := by
    intro u
    by_cases hu : u ∈ P
    · rw [hFrow u hu, hrowval]
    · have : ∑ v, F u v = 0 := Finset.sum_eq_zero fun v _ => by
        by_contra h
        exact hu (hFsupp u v h).1
      rw [this]
      linarith
  have h21 := AlonExpanders.Core.eq_2_1 G hn' f hf0 hf
  have hpos : 0 < ∑ v, (max (f v) 0) ^ 2 := by
    have hw' : 0 < (max (f w) 0) ^ 2 := by
      rw [max_eq_left hw.le]
      positivity
    exact lt_of_lt_of_le hw'
      (Finset.single_le_sum (f := fun v => (max (f v) 0) ^ 2) (fun v _ => sq_nonneg _)
        (Finset.mem_univ w))
  have hkey := key G (fun v => max (f v) 0) F cs _ hcs0 hF0 hFadj
    (fun u hu => by rw [hFrow u (hgP u hu), hrowval]) hrow' hFcol h21 hpos
  exact (bound_mono hc hccs).trans hkey

end ALN

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d : ℕ) (c : ℝ) (hn : 2 ≤ n) (hc : 0 ≤ c) (hG : AlonExpanders.Core.IsMagnifier G n d c) :
    c ^ 2 / (4 + 2 * c ^ 2) ≤ AlonMilman.Diameter.lambda1 G :=
  ALN.lemma24 G n d c hn hc hG

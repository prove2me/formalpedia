-- Prove2me | Definitions.Def_GirvingAKS_Graph_Walk
-- name    : GirvingAKS_Graph_Walk
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:13.740029+00:00
-- url     : https://prove2.me/theorems/e3593b04-6d7f-4902-92b3-2b2b3224eeab
-- title:
--   AKS sorting networks (Seiferas port) — General HalfEdgeGraph Walk Operator and Spectral Gap
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Graph/Walk.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** The normalized walk operator for general (irregular) graphs, defined via the self-adjoint operator `D^{-1/2} A D^{-1/2}` on `EuclideanSpace`.
--
--   For a `HalfEdgeGraph n` with half-edge representation:
--
--   - Walk operator: `(Nf)(v) = (1/√deg(v)) · ∑_{e: src(e)=v} f(target(e)) / √deg(target(e))`
--   - Mean projection: onto `u(v) = √deg(v) / √halfs`
--   - Spectral gap: `‖N - P‖`
--
--   Self-adjointness follows from the rotation bijection (same trick as `RegularGraph`). Division by zero is harmless: `Real.sqrt 0 = 0` and `a / 0 = 0` in Lean.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Graph/Walk.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Graph_Graph

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Graph/Walk.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # General HalfEdgeGraph Walk Operator and Spectral Gap

  The normalized walk operator for general (irregular) graphs, defined via
  the self-adjoint operator `D^{-1/2} A D^{-1/2}` on `EuclideanSpace`.

  For a `HalfEdgeGraph n` with half-edge representation:
  - Walk operator: `(Nf)(v) = (1/√deg(v)) · ∑_{e: src(e)=v} f(target(e)) / √deg(target(e))`
  - Mean projection: onto `u(v) = √deg(v) / √halfs`
  - Spectral gap: `‖N - P‖`

  Self-adjointness follows from the rotation bijection (same trick as `RegularGraph`).
  Division by zero is harmless: `Real.sqrt 0 = 0` and `a / 0 = 0` in Lean.
-/


section


open Finset BigOperators

noncomputable section


/-! **Walk Operator** -/

/-- The normalized walk function on plain vectors:
    `(Nf)(v) = (1/√deg(v)) · ∑_{e: src(e)=v} f(target(e)) / √deg(target(e))`. -/
def HalfEdgeGraph.normalizedWalkFun {n : ℕ} (G : HalfEdgeGraph n) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun v ↦ (1 / Real.sqrt (G.deg v)) *
    ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt (G.deg (G.target e))

/-- The normalized walk operator as a linear map on `EuclideanSpace`. -/
def HalfEdgeGraph.normalizedWalkLM {n : ℕ} (G : HalfEdgeGraph n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (G.normalizedWalkFun (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    show G.normalizedWalkFun (WithLp.ofLp f + WithLp.ofLp g) v =
      G.normalizedWalkFun (WithLp.ofLp f) v + G.normalizedWalkFun (WithLp.ofLp g) v
    simp only [HalfEdgeGraph.normalizedWalkFun, Pi.add_apply, add_div,
      Finset.sum_add_distrib, mul_add]
  map_smul' r f := by
    apply PiLp.ext; intro v
    show G.normalizedWalkFun (r • WithLp.ofLp f) v =
      r • G.normalizedWalkFun (WithLp.ofLp f) v
    simp only [HalfEdgeGraph.normalizedWalkFun, Pi.smul_apply, smul_eq_mul]
    have : ∀ e, r * (WithLp.ofLp f) (G.target e) / Real.sqrt ↑(G.deg (G.target e)) =
        r * ((WithLp.ofLp f) (G.target e) / Real.sqrt ↑(G.deg (G.target e))) :=
      fun e ↦ mul_div_assoc _ _ _
    simp_rw [this, ← Finset.mul_sum]; ring

/-- The normalized walk operator as a continuous linear map on `EuclideanSpace`. -/
def HalfEdgeGraph.normalizedWalkCLM {n : ℕ} (G : HalfEdgeGraph n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  G.normalizedWalkLM.toContinuousLinearMap

@[simp]
theorem HalfEdgeGraph.normalizedWalkCLM_apply {n : ℕ} (G : HalfEdgeGraph n)
    (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    G.normalizedWalkCLM f v = (1 / Real.sqrt (G.deg v)) *
      ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt (G.deg (G.target e)) :=
  rfl


/-! **Mean Projection** -/

/-- The degree-weighted mean function: projects onto the `√deg` direction.
    `(Pf)(v) = √deg(v) · (∑_w f(w) · √deg(w)) / halfs`. -/
def HalfEdgeGraph.degreeMeanFun {n : ℕ} (G : HalfEdgeGraph n) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun v ↦ Real.sqrt (G.deg v) * (∑ w, f w * Real.sqrt (G.deg w)) / G.halfs

/-- The degree-weighted mean projection as a linear map on `EuclideanSpace`. -/
def HalfEdgeGraph.degreeMeanLM {n : ℕ} (G : HalfEdgeGraph n) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (G.degreeMeanFun (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    show G.degreeMeanFun (WithLp.ofLp f + WithLp.ofLp g) v =
      G.degreeMeanFun (WithLp.ofLp f) v + G.degreeMeanFun (WithLp.ofLp g) v
    simp only [HalfEdgeGraph.degreeMeanFun, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    apply PiLp.ext; intro v
    show G.degreeMeanFun (r • WithLp.ofLp f) v =
      r • G.degreeMeanFun (WithLp.ofLp f) v
    simp only [HalfEdgeGraph.degreeMeanFun, Pi.smul_apply, smul_eq_mul]
    have : ∀ w, r * (WithLp.ofLp f) w * Real.sqrt ↑(G.deg w) =
        r * ((WithLp.ofLp f) w * Real.sqrt ↑(G.deg w)) := fun w ↦ by ring
    simp_rw [this, ← Finset.mul_sum]; ring

/-- The degree-weighted mean projection as a continuous linear map on `EuclideanSpace`. -/
def HalfEdgeGraph.degreeMeanCLM {n : ℕ} (G : HalfEdgeGraph n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  G.degreeMeanLM.toContinuousLinearMap

@[simp]
theorem HalfEdgeGraph.degreeMeanCLM_apply {n : ℕ} (G : HalfEdgeGraph n)
    (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    G.degreeMeanCLM f v =
      Real.sqrt (G.deg v) * (∑ w, f w * Real.sqrt (G.deg w)) / G.halfs :=
  rfl


/-! **Spectral Gap** -/

/-- The spectral gap of a general graph: `‖N - P‖` where `N` is the normalized
    walk operator and `P` is the projection onto the `√deg` direction.
    Generalizes `spectralGap` for `RegularGraph`. -/
def HalfEdgeGraph.spectralGap {n : ℕ} (G : HalfEdgeGraph n) : ℝ :=
  ‖G.normalizedWalkCLM - G.degreeMeanCLM‖


/-! **Self-Adjointness** -/

/-- The inner product `⟨Nf, g⟩` equals a symmetric sum over half-edges.
    Stated with `g * walk` order to match `simp` output of `PiLp.inner_apply`. -/
private theorem HalfEdgeGraph.inner_normalizedWalk_eq {n : ℕ} (G : HalfEdgeGraph n)
    (f g : Fin n → ℝ) :
    ∑ v, g v *
      (1 / Real.sqrt ↑(G.deg v) *
        ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) =
    ∑ e : Fin G.halfs,
      f (G.target e) * g (G.src e) /
      (Real.sqrt ↑(G.deg (G.src e)) * Real.sqrt ↑(G.deg (G.target e))) := by
  -- Distribute g(v)/√deg(v) into the filtered sum
  have factor : ∀ v : Fin n,
      g v * (1 / Real.sqrt ↑(G.deg v) *
        ∑ e ∈ univ.filter (G.src · = v), f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) =
      ∑ e ∈ univ.filter (G.src · = v),
        f (G.target e) * g v / (Real.sqrt ↑(G.deg v) * Real.sqrt ↑(G.deg (G.target e))) := by
    intro v
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e _; ring
  simp_rw [factor]
  -- Collapse: ∑_v ∑_{e:src=v} h(e) = ∑_e h(e) via fiberwise
  rw [← Finset.sum_fiberwise_of_maps_to (g := G.src) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  -- In the fiber where src(e) = v, replace g(v) with g(src e) and √deg(v) with √deg(src e)
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi]

/-- The normalized walk operator is self-adjoint, via the rotation bijection. -/
theorem HalfEdgeGraph.normalizedWalkCLM_isSelfAdjoint {n : ℕ} (G : HalfEdgeGraph n) :
    IsSelfAdjoint G.normalizedWalkCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (G.normalizedWalkCLM f) g = @inner ℝ _ _ f (G.normalizedWalkCLM g)
  simp only [PiLp.inner_apply, normalizedWalkCLM_apply]
  simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => by
    show RCLike.re (b * starRingEnd ℝ a) = b * a
    simp only [RCLike.conj_to_real, RCLike.re_to_real]]
  -- Both sides: ∑_v (something) = half-edge sum via inner_normalizedWalk_eq
  -- LHS has g * (walk applied to f), RHS has f * (walk applied to g)
  -- Commute RHS terms: f(v) * (Ng)(v) → (Ng)(v) * f(v) so inner_normalizedWalk_eq matches
  conv_rhs => arg 2; ext v; rw [mul_comm]
  rw [G.inner_normalizedWalk_eq (WithLp.ofLp f) (WithLp.ofLp g),
      G.inner_normalizedWalk_eq (WithLp.ofLp g) (WithLp.ofLp f)]
  -- LHS: ∑_e f(target e) · g(src e) / (√deg(src) · √deg(target))
  -- RHS: ∑_e g(target e) · f(src e) / (√deg(src) · √deg(target))
  -- Apply rotation bijection: reindex e ↦ rot(e)
  rw [← G.rotEquiv.sum_comp (fun e ↦
    (WithLp.ofLp g) (G.target e) * (WithLp.ofLp f) (G.src e) /
    (Real.sqrt ↑(G.deg (G.src e)) * Real.sqrt ↑(G.deg (G.target e))))]
  -- After reindexing: src(rot e) = target e, rot(rot e) = e
  apply Finset.sum_congr rfl; intro e _
  simp only [HalfEdgeGraph.target]
  dsimp [HalfEdgeGraph.rotEquiv]
  rw [G.rot_involution]; ring

/-- The degree-weighted mean projection is self-adjoint. -/
theorem HalfEdgeGraph.degreeMeanCLM_isSelfAdjoint {n : ℕ} (G : HalfEdgeGraph n) :
    IsSelfAdjoint G.degreeMeanCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (G.degreeMeanCLM f) g = @inner ℝ _ _ f (G.degreeMeanCLM g)
  simp only [PiLp.inner_apply, degreeMeanCLM_apply]
  simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => by
    show RCLike.re (b * starRingEnd ℝ a) = b * a
    simp only [RCLike.conj_to_real, RCLike.re_to_real]]
  -- Both sides equal S_g · S_f / halfs where S_x = ∑_v x(v) · √deg(v)
  set sf := ∑ w, (WithLp.ofLp f) w * Real.sqrt ↑(G.deg w)
  set sg := ∑ w, (WithLp.ofLp g) w * Real.sqrt ↑(G.deg w)
  have lhs : ∀ v, (WithLp.ofLp g) v *
      (Real.sqrt ↑(G.deg v) * sf / ↑G.halfs) =
      (WithLp.ofLp g) v * Real.sqrt ↑(G.deg v) * (sf / ↑G.halfs) :=
    fun v ↦ by ring
  have rhs : ∀ v, Real.sqrt ↑(G.deg v) * sg / ↑G.halfs *
      (WithLp.ofLp f) v =
      (WithLp.ofLp f) v * Real.sqrt ↑(G.deg v) * (sg / ↑G.halfs) :=
    fun v ↦ by ring
  simp_rw [lhs, rhs, ← Finset.sum_mul]; ring


/-! **Idempotency and Eigenvector** -/

/-- The sum of `√deg(v) * √deg(v)` equals `halfs` (since `√x * √x = x`). -/
theorem HalfEdgeGraph.sum_sqrt_deg_sq {n : ℕ} (G : HalfEdgeGraph n) :
    ∑ w : Fin n, Real.sqrt ↑(G.deg w) * Real.sqrt ↑(G.deg w) = ↑G.halfs := by
  have h : ∀ w : Fin n, Real.sqrt ↑(G.deg w) * Real.sqrt ↑(G.deg w) = ↑(G.deg w) :=
    fun w ↦ Real.mul_self_sqrt (Nat.cast_nonneg _)
  simp_rw [h, ← Nat.cast_sum]
  exact_mod_cast G.sum_deg

/-- The degree-weighted mean projection is idempotent: `P² = P`. -/
theorem HalfEdgeGraph.degreeMeanCLM_idempotent {n : ℕ} (G : HalfEdgeGraph n) :
    G.degreeMeanCLM * G.degreeMeanCLM = G.degreeMeanCLM := by
  ext f : 1; apply PiLp.ext; intro v
  show G.degreeMeanCLM (G.degreeMeanCLM f) v = G.degreeMeanCLM f v
  simp only [degreeMeanCLM_apply]
  -- Inner sum: ∑_w (√deg(w) · S / halfs) · √deg(w) = S · (∑ deg) / halfs = S
  set S := ∑ w, f w * Real.sqrt ↑(G.deg w)
  -- Factor: (√deg(w) · S / halfs) · √deg(w) = √deg(w) · √deg(w) · (S / halfs)
  have factor : ∀ w : Fin n, Real.sqrt ↑(G.deg w) * S / ↑G.halfs *
      Real.sqrt ↑(G.deg w) = Real.sqrt ↑(G.deg w) * Real.sqrt ↑(G.deg w) *
      (S / ↑G.halfs) := fun w ↦ by ring
  simp_rw [factor, ← Finset.sum_mul, G.sum_sqrt_deg_sq]
  rcases Nat.eq_zero_or_pos G.halfs with hh | hh
  · simp [hh]
  · have hne : (G.halfs : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_div_cancel₀ S hne]

/-- Any half-edge `e` witnesses that `deg(src e) > 0`. -/
theorem HalfEdgeGraph.deg_src_pos {n : ℕ} (G : HalfEdgeGraph n) (e : Fin G.halfs) :
    0 < G.deg (G.src e) :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- The walk operator preserves the mean projection: `N(Pf) = Pf`. -/
theorem HalfEdgeGraph.normalizedWalkCLM_comp_degreeMean {n : ℕ} (G : HalfEdgeGraph n) :
    ∀ f : EuclideanSpace ℝ (Fin n),
      G.normalizedWalkCLM (G.degreeMeanCLM f) = G.degreeMeanCLM f := by
  intro f; ext v
  simp only [normalizedWalkCLM_apply, degreeMeanCLM_apply]
  set S := ∑ w, f w * Real.sqrt ↑(G.deg w)
  -- Each summand: (√deg(t) · S / halfs) / √deg(t) = S / halfs
  -- since deg(target e) > 0 for any half-edge e (rot(e) witnesses this)
  have cancel : ∀ e ∈ univ.filter (G.src · = v),
      Real.sqrt ↑(G.deg (G.target e)) * S / ↑G.halfs /
        Real.sqrt ↑(G.deg (G.target e)) = S / ↑G.halfs := by
    intro e _
    have h : Real.sqrt ↑(G.deg (G.target e)) ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      exact Nat.cast_pos.mpr (G.deg_src_pos (G.rot e))
    rw [mul_div_assoc, mul_div_cancel_left₀ _ h]
  rw [Finset.sum_congr rfl cancel, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  -- Goal: (1/√deg(v) * ↑card) * (S/halfs) = √deg(v) * S / halfs
  -- card = G.deg v (defeq), so key identity: 1/√d * d = √d
  conv_rhs => rw [mul_div_assoc]
  congr 1
  show 1 / Real.sqrt ↑(G.deg v) * ↑(G.deg v) = Real.sqrt ↑(G.deg v)
  rcases Nat.eq_zero_or_pos (G.deg v) with h | h
  · simp [h]
  · rw [one_div, inv_mul_eq_div, div_eq_iff (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr h))]
    exact (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm


/-! **Norm Bounds** -/

/-- The normalized walk operator is a contraction: `‖N‖ ≤ 1`.
    Proof: Cauchy-Schwarz per vertex + rotation bijection. -/
theorem HalfEdgeGraph.normalizedWalkCLM_norm_le_one {n : ℕ} (G : HalfEdgeGraph n) :
    ‖G.normalizedWalkCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  rw [← Real.sqrt_sq (norm_nonneg (G.normalizedWalkCLM f)),
      ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, normalizedWalkCLM_apply]
  -- ∑_v (Nf(v))² ≤ ∑_v (f v)²
  -- Step 1: Cauchy-Schwarz per vertex: (1/√d · ∑ g)² ≤ ∑ g²
  have per_v : ∀ v : Fin n,
      (1 / Real.sqrt ↑(G.deg v) *
        ∑ e ∈ univ.filter (G.src · = v),
          f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 ≤
      ∑ e ∈ univ.filter (G.src · = v),
        (f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 := by
    intro v
    rcases Nat.eq_zero_or_pos (G.deg v) with h | h
    · have : univ.filter (G.src · = v) = ∅ :=
        Finset.card_eq_zero.mp (show _ = 0 from h ▸ rfl)
      simp [this]
    · have hd : (0 : ℝ) < ↑(G.deg v) := Nat.cast_pos.mpr h
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _),
          one_div, inv_mul_eq_div, div_le_iff₀ hd]
      have cs := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _
        (univ.filter (G.src · = v))
        (fun e ↦ f (G.target e) / Real.sqrt ↑(G.deg (G.target e)))
      rw [show (univ.filter (G.src · = v)).card = G.deg v from rfl] at cs
      linarith
  -- Step 2: Chain: CS per vertex → fiberwise collapse → rotation → fiberwise cancel
  calc ∑ v, _ ≤ ∑ v, ∑ e ∈ univ.filter (G.src · = v),
          (f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 :=
        Finset.sum_le_sum (fun v _ ↦ per_v v)
    _ = ∑ e : Fin G.halfs,
          (f (G.target e) / Real.sqrt ↑(G.deg (G.target e))) ^ 2 := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := G.src) (fun _ _ ↦ mem_univ _)]
    _ = ∑ e : Fin G.halfs,
          (f (G.src e) / Real.sqrt ↑(G.deg (G.src e))) ^ 2 :=
        G.sum_target_eq_sum_src (fun v ↦ (f v / Real.sqrt ↑(G.deg v)) ^ 2)
    _ ≤ ∑ v, f v ^ 2 := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := G.src) (fun _ _ ↦ mem_univ _)]
        apply Finset.sum_le_sum; intro v _
        rw [Finset.sum_congr rfl (fun e he ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he; rw [he])]
        rw [Finset.sum_const, nsmul_eq_mul,
            show (univ.filter (G.src · = v)).card = G.deg v from rfl,
            div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        rcases Nat.eq_zero_or_pos (G.deg v) with h | h
        · simp [h]; exact sq_nonneg _
        · exact le_of_eq (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega)))

/-- The spectral gap is nonnegative. -/
theorem HalfEdgeGraph.spectralGap_nonneg {n : ℕ} (G : HalfEdgeGraph n) :
    0 ≤ G.spectralGap :=
  norm_nonneg _

/-- Subtracting the degree-weighted mean doesn't increase the norm: `‖f - Pf‖ ≤ ‖f‖`. -/
private theorem HalfEdgeGraph.norm_sub_degreeMeanCLM_le {n : ℕ} (G : HalfEdgeGraph n)
    (f : EuclideanSpace ℝ (Fin n)) :
    ‖f - G.degreeMeanCLM f‖ ≤ ‖f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  have hfv : ∀ v : Fin n, (f - G.degreeMeanCLM f) v =
      f v - Real.sqrt ↑(G.deg v) * (∑ w, f w * Real.sqrt ↑(G.deg w)) / ↑G.halfs := by
    intro v; simp [degreeMeanCLM_apply]
  simp_rw [hfv]
  set S := ∑ w : Fin n, f w * Real.sqrt ↑(G.deg w)
  have expand : ∀ v : Fin n,
      (f v - Real.sqrt ↑(G.deg v) * S / ↑G.halfs) ^ 2 =
      f v ^ 2 - 2 * (S / ↑G.halfs) * (f v * Real.sqrt ↑(G.deg v)) +
      (S / ↑G.halfs) ^ 2 * (Real.sqrt ↑(G.deg v) * Real.sqrt ↑(G.deg v)) :=
    fun v ↦ by ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, G.sum_sqrt_deg_sq]
  have key : 2 * (S / ↑G.halfs) * S - (S / ↑G.halfs) ^ 2 * ↑G.halfs ≥ 0 := by
    rcases Nat.eq_zero_or_pos G.halfs with hh | hh
    · simp [hh]
    · have : 2 * (S / ↑G.halfs) * S - (S / ↑G.halfs) ^ 2 * ↑G.halfs =
          S ^ 2 / ↑G.halfs := by
        field_simp; ring
      linarith [div_nonneg (sq_nonneg S) (Nat.cast_nonneg G.halfs)]
  linarith

/-- The spectral gap is at most 1: `‖N - P‖ ≤ 1`.
    Proof: factor `(N-P)f = N(f-Pf)`, then `‖N‖ ≤ 1` and `‖f-Pf‖ ≤ ‖f‖`. -/
theorem HalfEdgeGraph.spectralGap_le_one {n : ℕ} (G : HalfEdgeGraph n) :
    G.spectralGap ≤ 1 := by
  unfold HalfEdgeGraph.spectralGap
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  have hNP := G.normalizedWalkCLM_comp_degreeMean f
  calc ‖(G.normalizedWalkCLM - G.degreeMeanCLM) f‖
      = ‖G.normalizedWalkCLM f - G.degreeMeanCLM f‖ := by
        simp [ContinuousLinearMap.sub_apply]
    _ = ‖G.normalizedWalkCLM f - G.normalizedWalkCLM (G.degreeMeanCLM f)‖ := by rw [hNP]
    _ = ‖G.normalizedWalkCLM (f - G.degreeMeanCLM f)‖ := by rw [map_sub]
    _ ≤ ‖G.normalizedWalkCLM‖ * ‖f - G.degreeMeanCLM f‖ := G.normalizedWalkCLM.le_opNorm _
    _ ≤ 1 * ‖f - G.degreeMeanCLM f‖ := by
        apply mul_le_mul_of_nonneg_right G.normalizedWalkCLM_norm_le_one (norm_nonneg _)
    _ = ‖f - G.degreeMeanCLM f‖ := one_mul _
    _ ≤ ‖f‖ := G.norm_sub_degreeMeanCLM_le f


/-! **Contraction Bound** -/

/-- The lifted function for the contraction bound:
    `g(v) = f(s(v)) · √(deg_G(v)) / √(deg_{G.contract s}(s(v)))`.
    Designed so that `‖g‖ = ‖f‖` (isometry) and the factorization
    `(N'-P')f(u) = (1/√d'_u) · ∑_{v:s(v)=u} √d_v · ((N-P)g)(v)` holds. -/
private def contractLift {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m)
    (f : Fin m → ℝ) : Fin n → ℝ :=
  fun v ↦ f (s v) * Real.sqrt (G.deg v) / Real.sqrt ((G.contract s).deg (s v))

/-- The lifted function satisfies `‖g‖² ≤ ‖f‖²` (with equality when all
    contracted vertices have positive degree). -/
private theorem contractLift_norm_sq_le {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ}
    (s : Fin n → Fin m) (f : EuclideanSpace ℝ (Fin m)) :
    ∑ v, (contractLift G s f v) ^ 2 ≤ ∑ u, (f u) ^ 2 := by
  simp only [contractLift]
  -- Group by fiber: ∑_v ... = ∑_u ∑_{v:s(v)=u} ...
  rw [← Finset.sum_fiberwise_of_maps_to (g := s) (fun _ _ ↦ Finset.mem_univ _)]
  apply Finset.sum_le_sum; intro u _
  -- ∑_{v:s(v)=u} (f(u) * √d_v / √d'_u)² ≤ f(u)²
  rw [Finset.sum_congr rfl (fun v hv ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv; rw [hv])]
  rcases Nat.eq_zero_or_pos ((G.contract s).deg u) with hd | hd
  · -- d'_u = 0: all summands are 0 (√0 = 0), so sum ≤ f(u)²
    have fiber_zero : ∀ v ∈ Finset.univ.filter (s · = u),
        Real.sqrt ↑(G.deg v) = 0 := by
      intro v hv
      have hdv : G.deg v = 0 := Nat.eq_zero_of_le_zero (by
        calc G.deg v
            ≤ ∑ x ∈ Finset.univ.filter (s · = u), G.deg x :=
              Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hv
          _ = 0 := by rw [← G.contract_deg_eq_sum_fiber s u, hd])
      rw [hdv, Nat.cast_zero]; exact Real.sqrt_zero
    rw [Finset.sum_eq_zero (fun v hv ↦ by rw [fiber_zero v hv]; ring)]
    exact sq_nonneg _
  · -- d'_u > 0: factor out f(u)² / d'_u and use ∑ d_v = d'_u
    have hne : (↑((G.contract s).deg u) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
    have factor : ∀ v ∈ Finset.univ.filter (s · = u),
        (f u * Real.sqrt ↑(G.deg v) / Real.sqrt ↑((G.contract s).deg u)) ^ 2 =
        f u ^ 2 * (↑(G.deg v) / ↑((G.contract s).deg u)) := by
      intro v _; rw [mul_div_assoc, mul_pow, div_pow,
        Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [Finset.sum_congr rfl factor, ← Finset.mul_sum, ← Finset.sum_div]
    rw [show ∑ v ∈ Finset.univ.filter (s · = u), (G.deg v : ℝ) =
      ↑((G.contract s).deg u) from by
      rw [G.contract_deg_eq_sum_fiber s u]; push_cast; rfl]
    rw [div_self hne, mul_one]

/-- Per-summand: `g(w)/√d_w = f(s(w))/√d'_{s(w)}` when `d_w > 0`. -/
private theorem contractLift_div_sqrt {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m)
    (f : Fin m → ℝ) (w : Fin n) (hdw : 0 < G.deg w) :
    contractLift G s f w / Real.sqrt ↑(G.deg w) =
    f (s w) / Real.sqrt ↑((G.contract s).deg (s w)) := by
  simp only [contractLift, div_div]
  exact mul_div_mul_right _ _ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hdw))

/-- Mean sum identity: `∑_w g(w) * √d_w = ∑_u f(u) * √d'_u`. -/
private theorem contractLift_mean_sum {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ} (s : Fin n → Fin m)
    (f : Fin m → ℝ) :
    ∑ w, contractLift G s f w * Real.sqrt ↑(G.deg w) =
    ∑ u, f u * Real.sqrt ↑((G.contract s).deg u) := by
  simp only [contractLift]
  -- LHS: ∑_w (f(s w) * √d_w / √d'_{s w}) * √d_w = ∑_w f(s w) * d_w / √d'_{s w}
  have simpl : ∀ w : Fin n,
      f (s w) * Real.sqrt ↑(G.deg w) / Real.sqrt ↑((G.contract s).deg (s w)) *
        Real.sqrt ↑(G.deg w) =
      f (s w) * ↑(G.deg w) / Real.sqrt ↑((G.contract s).deg (s w)) := by
    intro w
    have h := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (G.deg w))
    rw [div_mul_eq_mul_div, mul_assoc, h]
  simp_rw [simpl]
  -- Group by fiber
  rw [← Finset.sum_fiberwise_of_maps_to (g := s) (fun _ _ ↦ Finset.mem_univ _)]
  apply Finset.sum_congr rfl; intro u _
  -- ∑_{v:s(v)=u} f(u) * d_v / √d'_u = f(u) * √d'_u
  rw [Finset.sum_congr rfl (fun v hv ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv; rw [hv])]
  -- Factor out f(u) and 1/√d'_u
  have : ∀ v ∈ Finset.univ.filter (s · = u),
      f u * ↑(G.deg v) / Real.sqrt ↑((G.contract s).deg u) =
      f u * (↑(G.deg v) / Real.sqrt ↑((G.contract s).deg u)) := fun v _ ↦ mul_div_assoc _ _ _
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Finset.sum_div]
  rw [show ∑ v ∈ Finset.univ.filter (s · = u), (G.deg v : ℝ) =
    ↑((G.contract s).deg u) from by
    rw [G.contract_deg_eq_sum_fiber s u]; push_cast; rfl]
  -- f(u) * (d'_u / √d'_u) = f(u) * √d'_u
  rcases Nat.eq_zero_or_pos ((G.contract s).deg u) with hd | hd
  · simp [hd]
  · congr 1
    rw [div_eq_iff (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd))]
    exact (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm

/-- The key factorization: `(N'-P')f(u) = (1/√d'_u) · ∑_{v:s(v)=u} √d_v · ((N-P)g)(v)`.
    This decomposes the contracted operator into a weighted sum over fibers. -/
private theorem contract_factorization {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ}
    (s : Fin n → Fin m) (f : EuclideanSpace ℝ (Fin m)) (u : Fin m) :
    (G.contract s).normalizedWalkCLM f u - (G.contract s).degreeMeanCLM f u =
    (1 / Real.sqrt ((G.contract s).deg u)) *
      ∑ v ∈ Finset.univ.filter (s · = u),
        Real.sqrt (G.deg v) *
        (G.normalizedWalkCLM (WithLp.toLp 2 (contractLift G s f)) v -
         G.degreeMeanCLM (WithLp.toLp 2 (contractLift G s f)) v) := by
  set S := Finset.univ.filter (fun v : Fin n ↦ s v = u)
  set fiber := fun v ↦ Finset.univ.filter (fun e : Fin G.halfs ↦ G.src e = v)
  -- Fiber partition (same as in contract_deg_eq_sum_fiber)
  have partition : Finset.univ.filter (fun e : Fin G.halfs ↦ s (G.src e) = u) =
      S.biUnion fiber := by
    ext e; simp only [S, fiber, mem_filter, mem_univ, true_and, mem_biUnion]
    exact ⟨fun h ↦ ⟨G.src e, h, rfl⟩, fun ⟨_, hv, he⟩ ↦ he ▸ hv⟩
  have hdisj : (S : Set (Fin n)).PairwiseDisjoint fiber := by
    intro v₁ _ v₂ _ hne
    simp only [fiber, Finset.disjoint_filter]
    intro e _ h₁ h₂; exact hne (h₁.symm.trans h₂)
  -- Prove walk and mean parts separately, then combine
  have walk : (G.contract s).normalizedWalkCLM f u =
      (1 / Real.sqrt ↑((G.contract s).deg u)) *
        ∑ v ∈ S, Real.sqrt ↑(G.deg v) *
          G.normalizedWalkCLM (WithLp.toLp 2 (contractLift G s f)) v := by
    -- Work at the ℝ level
    show (G.contract s).normalizedWalkFun (WithLp.ofLp f) u =
      (1 / Real.sqrt ↑((G.contract s).deg u)) *
        ∑ v ∈ S, Real.sqrt ↑(G.deg v) *
          G.normalizedWalkFun (contractLift G s (WithLp.ofLp f)) v
    simp only [HalfEdgeGraph.normalizedWalkFun, HalfEdgeGraph.contract_src, HalfEdgeGraph.contract_target]
    congr 1
    -- Cancel √d_v * (1/√d_v * inner_sum) = inner_sum, then fiberwise collapse
    have cancel : ∀ v ∈ S,
        Real.sqrt ↑(G.deg v) * (1 / Real.sqrt ↑(G.deg v) *
          ∑ e ∈ fiber v,
            contractLift G s (WithLp.ofLp f) (G.target e) /
            Real.sqrt ↑(G.deg (G.target e))) =
        ∑ e ∈ fiber v,
          contractLift G s (WithLp.ofLp f) (G.target e) /
          Real.sqrt ↑(G.deg (G.target e)) := by
      intro v _
      rcases Nat.eq_zero_or_pos (G.deg v) with hd | hd
      · have : fiber v = ∅ := Finset.card_eq_zero.mp (show _ = 0 from hd ▸ rfl)
        simp [this, hd]
      · rw [one_div, ← mul_assoc,
            mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)), one_mul]
    rw [Finset.sum_congr rfl cancel, ← Finset.sum_biUnion hdisj, ← partition]
    -- Summands: g(target)/√d_{target} = f(s(target))/√d'_{s(target)}
    apply Finset.sum_congr rfl; intro e _
    exact (contractLift_div_sqrt G s _ (G.target e) (G.deg_src_pos (G.rot e))).symm
  have mean : (G.contract s).degreeMeanCLM f u =
      (1 / Real.sqrt ↑((G.contract s).deg u)) *
        ∑ v ∈ S, Real.sqrt ↑(G.deg v) *
          G.degreeMeanCLM (WithLp.toLp 2 (contractLift G s f)) v := by
    -- Work at the ℝ level
    show (G.contract s).degreeMeanFun (WithLp.ofLp f) u =
      (1 / Real.sqrt ↑((G.contract s).deg u)) *
        ∑ v ∈ S, Real.sqrt ↑(G.deg v) *
          G.degreeMeanFun (contractLift G s (WithLp.ofLp f)) v
    simp only [HalfEdgeGraph.degreeMeanFun]
    -- Factor: √d_v * (√d_v * S_g / halfs) = d_v * (S_g / halfs)
    set Sg := ∑ w, contractLift G s (WithLp.ofLp f) w * Real.sqrt ↑(G.deg w)
    have factor : ∀ v ∈ S,
        Real.sqrt ↑(G.deg v) * (Real.sqrt ↑(G.deg v) * Sg / ↑G.halfs) =
        ↑(G.deg v) * (Sg / ↑G.halfs) := by
      intro v _
      rw [← mul_div_assoc, ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _), mul_div_assoc]
    rw [Finset.sum_congr rfl factor, ← Finset.sum_mul]
    -- ∑_{v∈S} d_v = d'_u
    rw [show ∑ v ∈ S, (G.deg v : ℝ) = ↑((G.contract s).deg u) from by
      rw [G.contract_deg_eq_sum_fiber s u]; push_cast; rfl]
    -- halfs' = halfs (definitional)
    rw [show (G.contract s).halfs = G.halfs from rfl]
    -- S_g = S' (mean sum identity)
    rw [show Sg = ∑ w, (WithLp.ofLp f) w * Real.sqrt ↑((G.contract s).deg w) from
      contractLift_mean_sum G s (WithLp.ofLp f)]
    -- Goal: √d' * S' / halfs = (1/√d') * (d' * (S' / halfs))
    rcases Nat.eq_zero_or_pos ((G.contract s).deg u) with hd | hd
    · simp [hd]
    · have hne := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)
      have key : (Real.sqrt ↑((G.contract s).deg u))⁻¹ * ↑((G.contract s).deg u) =
          Real.sqrt ↑((G.contract s).deg u) := by
        rw [inv_mul_eq_div, div_eq_iff hne]
        exact (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
      rw [one_div, ← mul_assoc, key, mul_div_assoc]
  rw [walk, mean, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun v _ ↦ (mul_sub _ _ _).symm)

/-- Per-vertex Cauchy-Schwarz: `((N'-P')f(u))² ≤ ∑_{v:s(v)=u} ((N-P)g(v))²`.
    Uses the factorization `(N'-P')f(u) = (1/√d'_u) · ∑ √d_v · h_v`
    and weighted CS: `(∑ √w · h)² ≤ (∑ w)(∑ h²)`. -/
private theorem contract_per_vertex_bound {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ}
    (s : Fin n → Fin m) (f : EuclideanSpace ℝ (Fin m)) (u : Fin m) :
    ((G.contract s).normalizedWalkCLM f u - (G.contract s).degreeMeanCLM f u) ^ 2 ≤
    ∑ v ∈ Finset.univ.filter (s · = u),
      (G.normalizedWalkCLM (WithLp.toLp 2 (contractLift G s f)) v -
       G.degreeMeanCLM (WithLp.toLp 2 (contractLift G s f)) v) ^ 2 := by
  -- Rewrite LHS using the factorization (BEFORE setting abbreviations)
  rw [contract_factorization G s f u]
  -- Goal LHS: ((1/√d') * ∑ √d_v * (N-P)g(v))^2
  -- Goal RHS: ∑ ((N-P)g(v))^2
  rcases Nat.eq_zero_or_pos ((G.contract s).deg u) with hd | hd
  · -- d'_u = 0: LHS = 0 since 1/√0 = 0
    have : Real.sqrt ↑((G.contract s).deg u) = 0 := by
      rw [show ((G.contract s).deg u : ℝ) = 0 from by exact_mod_cast hd]; exact Real.sqrt_zero
    rw [this, div_zero, zero_mul, zero_pow (by omega : 2 ≠ 0)]
    exact Finset.sum_nonneg (fun v _ ↦ sq_nonneg _)
  · -- d'_u > 0: weighted Cauchy-Schwarz
    rw [mul_pow, div_pow, one_pow,
        Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) ((G.contract s).deg u))]
    -- Goal: 1/↑d' * (∑ ...)^2 ≤ ∑ (...)^2
    rw [div_mul_eq_mul_div, one_mul]
    -- Goal: (∑ ...)^2 / ↑d' ≤ ∑ (...)^2
    have hd_ne : (↑((G.contract s).deg u) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
    rw [div_le_iff₀ (Nat.cast_pos.mpr hd)]
    -- Goal: (∑ ...)^2 ≤ ↑d' * ∑ (...)^2
    -- Apply CS: (∑ a*b)^2 ≤ (∑ a^2)(∑ b^2) where a_v = √d_v
    -- CS: (∑ a*b)^2 ≤ (∑ a^2)(∑ b^2)
    refine le_trans (sum_mul_sq_le_sq_mul_sq _ _ _) ?_
    -- Goal: (∑ (√d_v)^2) * (∑ h^2) ≤ (∑ h^2) * d'_u
    -- Since ∑ (√d_v)^2 = ∑ d_v = d'_u
    have sqrt_sq : ∑ v ∈ Finset.univ.filter (s · = u),
        Real.sqrt ↑(G.deg v) ^ 2 = ↑((G.contract s).deg u) := by
      simp_rw [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) _)]
      rw [G.contract_deg_eq_sum_fiber s u]; push_cast; rfl
    rw [sqrt_sq, mul_comm]

/-- The spectral gap can only decrease under contraction. -/
theorem HalfEdgeGraph.spectralGap_contract {n : ℕ} (G : HalfEdgeGraph n) {m : ℕ}
    (s : Fin n → Fin m) :
    (G.contract s).spectralGap ≤ G.spectralGap := by
  set G' := G.contract s
  apply ContinuousLinearMap.opNorm_le_bound _ G.spectralGap_nonneg
  intro f
  -- Define the lifted function g
  set g : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (contractLift G s f)
  -- Step 1: ‖(N'-P')f‖ ≤ ‖(N-P)g‖ via per-vertex Cauchy-Schwarz
  have step1 : ‖(G'.normalizedWalkCLM - G'.degreeMeanCLM) f‖ ≤
      ‖(G.normalizedWalkCLM - G.degreeMeanCLM) g‖ := by
    suffices hsq : ‖(G'.normalizedWalkCLM - G'.degreeMeanCLM) f‖ ^ 2 ≤
        ‖(G.normalizedWalkCLM - G.degreeMeanCLM) g‖ ^ 2 by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp_rw [Real.norm_eq_abs, sq_abs, ContinuousLinearMap.sub_apply]
    calc ∑ u, (G'.normalizedWalkCLM f u - G'.degreeMeanCLM f u) ^ 2
        ≤ ∑ u, ∑ v ∈ Finset.univ.filter (s · = u),
            (G.normalizedWalkCLM g v - G.degreeMeanCLM g v) ^ 2 :=
          Finset.sum_le_sum (fun u _ ↦ contract_per_vertex_bound G s f u)
      _ = ∑ v, (G.normalizedWalkCLM g v - G.degreeMeanCLM g v) ^ 2 := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := s) (fun _ _ ↦ Finset.mem_univ _)]
  -- Step 2: ‖(N-P)g‖ ≤ spectralGap * ‖g‖ (operator norm bound)
  -- Step 3: ‖g‖ = ‖f‖ (isometry)
  have step3 : ‖g‖ ≤ ‖f‖ := by
    rw [← Real.sqrt_sq (norm_nonneg g), ← Real.sqrt_sq (norm_nonneg f)]
    apply Real.sqrt_le_sqrt
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp_rw [Real.norm_eq_abs, sq_abs]
    exact contractLift_norm_sq_le G s f
  calc ‖(G'.normalizedWalkCLM - G'.degreeMeanCLM) f‖
      ≤ ‖(G.normalizedWalkCLM - G.degreeMeanCLM) g‖ := step1
    _ ≤ ‖G.normalizedWalkCLM - G.degreeMeanCLM‖ * ‖g‖ :=
        (G.normalizedWalkCLM - G.degreeMeanCLM).le_opNorm g
    _ ≤ G.spectralGap * ‖f‖ := by
        unfold HalfEdgeGraph.spectralGap
        exact mul_le_mul_of_nonneg_left step3 (norm_nonneg _)


/-! **Regular HalfEdgeGraph Compatibility** -/

/-- For a regular graph, `HalfEdgeGraph.spectralGap` agrees with `spectralGap` (when `d > 0`).
    When `d = 0`, isolated vertices have degree-weighted mean 0 but uniform mean is nonzero. -/
theorem spectralGap_toGraph {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    G.toGraph.spectralGap = spectralGap G := by
  have hdeg : ∀ w : Fin n, G.toGraph.deg w = d := fun w ↦ G.toGraph_deg hd w
  -- Walk operator: normalizedWalkCLM = walkCLM
  have hw : G.toGraph.normalizedWalkCLM = G.walkCLM := by
    refine ContinuousLinearMap.ext (fun f ↦ ?_); apply PiLp.ext; intro v
    show G.toGraph.normalizedWalkCLM f v = G.walkCLM f v
    simp only [HalfEdgeGraph.normalizedWalkCLM_apply, RegularGraph.walkCLM_apply, hdeg]
    -- (1/√d) * ∑_{e:src=v} f(target e) / √d = (∑_i f(nbr v i)) / d
    -- Factor 1/√d out of each summand
    have rw_div : ∀ e ∈ Finset.univ.filter (G.toGraph.src · = v),
        f (G.toGraph.target e) / Real.sqrt ↑d =
        f (G.toGraph.target e) * (1 / Real.sqrt ↑d) := fun e _ ↦ by ring
    rw [Finset.sum_congr rfl rw_div, ← Finset.sum_mul,
      G.toGraph_sum_target hd v (fun w ↦ f w)]
    -- (√d)⁻¹ * (S * (√d)⁻¹) = S / d
    have hsd : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)
    field_simp; rw [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]; ring
  -- Mean projection: degreeMeanCLM = meanCLM n
  have hm : G.toGraph.degreeMeanCLM = meanCLM n := by
    refine ContinuousLinearMap.ext (fun f ↦ ?_); apply PiLp.ext; intro v
    show G.toGraph.degreeMeanCLM f v = meanCLM n f v
    simp only [HalfEdgeGraph.degreeMeanCLM_apply, meanCLM_apply, hdeg, RegularGraph.toGraph_halfs]
    -- √d * (∑_w f(w) * √d) / (n*d) = (∑ f) / n
    rw [← Finset.sum_mul, mul_comm (∑ w, f w) (Real.sqrt ↑d), ← mul_assoc,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rw [mul_comm (↑n : ℝ) ↑d, mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (by omega) : (d : ℝ) ≠ 0)]
  unfold HalfEdgeGraph.spectralGap spectralGap; rw [hw, hm]

end

end



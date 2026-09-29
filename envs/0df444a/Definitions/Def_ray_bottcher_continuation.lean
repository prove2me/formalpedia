-- Prove2me | Definitions.Def_ray_bottcher_continuation
-- name    : ray_bottcher_continuation
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:09:18.109389+00:00
-- url     : https://prove2.me/theorems/c6ee74d2-70e9-493d-9c2f-3e59a4ecc95e
-- title:
--   ray (9/12): analytic continuation of the Böttcher map
-- statement:
--   **Analytic continuation of Böttcher coordinates up to the critical value.** External rays are grown from $a$ by analytic continuation until they reach the critical potential. They give an analytic inverse of the Böttcher map, and hence $b_c(z)$ extends analytically to the whole postcritical region $P = \{(c,z) : \phi_c(z) < \phi_c^\ast\}$. There it is an analytic homeomorphism from each fibre onto the open disk of radius $\phi_c^\ast$. The file also proves that a bijective analytic map between 1D manifolds has an analytic global inverse.
--
--   This file is part 9 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_potential

/-!
# ray (9/12): analytic continuation of the Böttcher map

Part 9 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Dynamics.Grow`
* `Ray.Dynamics.Ray`
* `Ray.Dynamics.Multiple`
* `Ray.Manifold.GlobalInverse`
* `Ray.Dynamics.Bottcher`
-/

-- ===== Ray.Dynamics.Grow =====
section Ray_Ray_Dynamics_Grow
/-!
## Analytic continuation of external rays for all postcritical values

After `BottcherNearM.lean` and `Potential.lean`, we have Böttcher coordinates
`s.bottcherNear : ℂ → S → ℂ` defined near `a`, and `s.potential : ℂ → S → ℝ` continuous everywhere
if `OnePreimage s`.  `s.bottcherNear` is invertible at any `(c,a)`, so near `a` we have an external
ray map `ray : ℂ → ℂ → S`.

We now grow these rays out to the critical potential `s.p c`, which will give a ray map analytic
throughout `s.post`.  We fix `c`, require `ray` to be analytic on a neighborhood of
`{c} ×ˢ closedBall 0 p`, and apply continuous induction to increase `p` from a small value up to
(right below) `s.p c`.  The resulting map is unique near any `c`, so we can stitch the continuations
for all `c` together into a single map (`Super.has_ray`).

A lot of the detail here is related to working with analytic functions in neighborhoods of points
and sets without using the heavier machinery of germs, stalks, and sheaves.  But I don't know that
machinery well, so I'm sticking to the low tech approach for now.

The defining equation of external rays `r`, with `c` suppressed, is
  `bottcher (r x) = x`
However, we know `bottcher` only locally near `a`, specifically on `s.near`.  If we have `n` s.t.
`f^[n] z ∈ s.near`, we can map the above equation forward `n` times to get
  `bottcher (f^[n] (r x)) = bottcher (r x) ^ d ^ n = x ^ d ^ n`
-/

open Classical
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball mem_closedBall mem_ball_self)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {p : ℝ}
variable {s : Super f d a}
variable {r : ℂ → ℂ → S}

/-- `Eqn s n r (c,z)` means `r` looks locally like external rays near `z`, mapping forwards
    by `f c^[n]` to hit `s.near`. -/
structure Eqn (s : Super f d a) (n : ℕ) (r : ℂ → ℂ → S) (x : ℂ × ℂ) : Prop where
  holo : ContMDiffAt II I ω (uncurry r) x
  near : (x.1, (f x.1)^[n] (r x.1 x.2)) ∈ s.near
  eqn : s.bottcherNear x.1 ((f x.1)^[n] (r x.1 x.2)) = x.2 ^ d ^ n

/-- `r` is an external ray map in a neighborhood of `{c} ×ˢ closedBall 0 p` -/
structure Grow (s : Super f d a) (c : ℂ) (p : ℝ) (n : ℕ) (r : ℂ → ℂ → S) : Prop where
  nonneg : 0 ≤ p
  zero : r c 0 = a
  start : ∀ᶠ x : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear x.1 (r x.1 x.2) = x.2
  eqn : ∀ᶠ x : ℂ × ℂ in 𝓝ˢ ({c} ×ˢ closedBall 0 p), Eqn s n r x

/-- Construct `Eqn` using fewer `∀ᶠ` -/
theorem eqn_near {s : Super f d a} {n : ℕ} {r : ℂ → ℂ → S} {c x : ℂ}
    (holo : ContMDiffAt II I ω (uncurry r) (c, x)) (mem : (c, (f c)^[n] (r c x)) ∈ s.near)
    (loc : ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), s.bottcherNear y.1 ((f y.1)^[n] (r y.1 y.2)) = y.2 ^ d ^ n) :
    ∀ᶠ y in 𝓝 (c, x), Eqn s n r y := by
  have m : ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), (y.1, (f y.1)^[n] (r y.1 y.2)) ∈ s.near := by
    refine ContinuousAt.eventually_mem ?_ (s.isOpen_near.mem_nhds mem)
    exact continuousAt_fst.prodMk (s.continuousAt_iter continuousAt_fst holo.continuousAt)
  apply holo.eventually.mp; apply loc.mp; apply m.mp
  exact .of_forall fun _ m l h ↦ ⟨h, m, l⟩

/-- `Eqn` is local -/
theorem Eqn.congr {x : ℂ × ℂ} {r0 r1 : ℂ → ℂ → S} (e : Eqn s n r0 x)
    (loc : uncurry r0 =ᶠ[𝓝 x] uncurry r1) : Eqn s n r1 x := by
  have s := loc.self_of_nhds; simp only [uncurry] at s
  exact
    { holo := e.holo.congr_of_eventuallyEq loc.symm
      near := by simp only [← s, e.near]
      eqn := by simp only [← s, e.eqn] }

/-- We can increase `n` in `Eqn` -/
theorem Eqn.mono {x : ℂ × ℂ} (e : Eqn s n r x) {m : ℕ} (nm : n ≤ m) : Eqn s m r x :=
  { holo := e.holo
    near := s.iter_stays_near' e.near nm
    eqn := by
      refine Nat.le_induction e.eqn ?_ m nm; intro k nk h
      simp only [h, Function.iterate_succ_apply',
        s.bottcherNear_eqn (s.iter_stays_near' e.near nk), pow_succ, pow_mul] }

/-- We can increase `n` in `Grow` -/
theorem Grow.mono (g : Grow s c p n r) {m : ℕ} (nm : n ≤ m) : Grow s c p m r :=
  { nonneg := g.nonneg
    zero := g.zero
    start := g.start
    eqn := g.eqn.mp (.of_forall fun _ e ↦ e.mono nm) }

/-- Centers `(c,0)` are in the domain -/
theorem mem_domain (c : ℂ) {p : ℝ} (p0 : 0 ≤ p) :
    (c, (0 : ℂ)) ∈ ({c} ×ˢ closedBall 0 p : Set (ℂ × ℂ)) :=
  mk_mem_prod rfl (Metric.mem_closedBall_self p0)

/-- The boundary is in the domain -/
theorem mem_domain_self {c x : ℂ} :
    (c, x) ∈ ({c} ×ˢ closedBall 0 ‖x‖ : Set (ℂ × ℂ)) := by
  simp only [mem_prod_eq, mem_singleton_iff, mem_closedBall, Complex.dist_eq, sub_zero, true_and,
    le_refl]

/-- Our domain is preconnected -/
theorem domain_preconnected (c : ℂ) (p : ℝ) :
    IsPreconnected ({c} ×ˢ closedBall 0 p : Set (ℂ × ℂ)) :=
  isPreconnected_singleton.prod (convex_closedBall _ _).isPreconnected

/-- Our domain is monotonic in `p` -/
theorem domain_mono (c : ℂ) {p0 p1 : ℝ} (le : p0 ≤ p1) :
    ({c} ×ˢ closedBall 0 p0 : Set (ℂ × ℂ)) ⊆ {c} ×ˢ closedBall 0 p1 :=
  prod_mono_right (Metric.closedBall_subset_closedBall le)

/-- If `closedBall 0 p ⊆ t`, we can increase `p` bit without leaving `t` -/
theorem domain_open' {p : ℝ} {t : Set ℂ} (sub : closedBall (0 : ℂ) p ⊆ t) (ot : IsOpen t) :
    ∃ q, p < q ∧ closedBall 0 q ⊆ t := by
  set u := norm '' (closedBall 0 (p + 1) \ t)
  by_cases ne : u = ∅
  · refine ⟨p + 1, by bound, ?_⟩; rw [image_eq_empty, sdiff_eq_empty] at ne; exact ne
  replace ne := nonempty_iff_ne_empty.mpr ne
  have uc : IsClosed u :=
    (((isCompact_closedBall _ _).diff ot).image continuous_norm).isClosed
  have up : ∀ x : ℝ, x ∈ u → p < x := by
    intro x m; rcases m with ⟨z, ⟨_, mt⟩, e⟩; rw [← e]; contrapose mt
    simp only [not_lt] at mt ⊢
    apply sub; simp only [mem_closedBall, Complex.dist_eq, sub_zero, mt]
  have ub : BddBelow u := ⟨p, fun _ m ↦ (up _ m).le⟩
  have iu : sInf u ∈ u := IsClosed.csInf_mem uc ne ub
  rcases exists_between (up _ iu) with ⟨q, pq, qi⟩
  use min q (p + 1), lt_min pq (by linarith)
  intro z m; simp only [mem_closedBall, Complex.dist_eq, sub_zero, le_min_iff] at m
  rcases m with ⟨zq, zp⟩; have zi := lt_of_le_of_lt zq qi
  contrapose zi; simp only [not_lt]; refine csInf_le ub (mem_image_of_mem _ ?_)
  simp only [mem_sdiff, mem_closedBall, Complex.dist_eq, sub_zero]; use zp, zi

/-- If `{c} ×ˢ closedBall 0 p ⊆ t`, we can increase `p` bit without leaving `t` -/
theorem domain_open {p : ℝ} {t : Set (ℂ × ℂ)} (sub : {c} ×ˢ closedBall 0 p ⊆ t) (o : IsOpen t) :
    ∃ q, p < q ∧ {c} ×ˢ closedBall 0 q ⊆ t := by
  have sub : closedBall 0 p ⊆ {b | (c, b) ∈ t} := by
    intro z m; simp only [mem_ofPred]; apply sub; exact ⟨mem_singleton _, m⟩
  rcases domain_open' sub (o.snd_preimage c) with ⟨q, pq, sub⟩
  use q, pq; intro ⟨e, z⟩ ⟨ec, m⟩; simp only [mem_singleton_iff] at ec
  replace m := sub m; simp only [← ec, mem_ofPred] at m; exact m

/-- `Grow` is local -/
theorem Grow.congr {r0 r1 : ℂ → ℂ → S} (g : Grow s c p n r0)
    (e : uncurry r0 =ᶠ[𝓝ˢ ({c} ×ˢ closedBall 0 p)] uncurry r1) : Grow s c p n r1 :=
  { nonneg := g.nonneg
    zero := by
      have e := e.self_of_nhdsSet (mem_domain c g.nonneg)
      simp only [uncurry] at e; rw [← e]; exact g.zero
    start := by
      refine g.start.mp ((e.filter_mono (nhds_le_nhdsSet (mem_domain c g.nonneg))).mp ?_)
      refine .of_forall fun x e s ↦ ?_
      simp only [uncurry] at e; rw [← e]; exact s
    eqn := by
      have eqn := g.eqn; simp only [Filter.EventuallyEq, eventually_nhdsSet_iff_forall] at eqn e ⊢
      intro x m
      refine (eqn x m).mp ((e x m).eventually_nhds.mp (.of_forall fun y e eqn ↦ ?_))
      exact eqn.congr e }

/-- `s.potential (r x) = abs x`, if `Eqn s n r x` -/
theorem Eqn.potential {x : ℂ × ℂ} (e : Eqn s n r x) :
    s.potential x.1 (r x.1 x.2) = ‖x.2‖ := by
  simp only [s.potential_eq e.near, e.eqn, norm_pow, ← Nat.cast_pow,
    Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ s.d0)]

/-- `Eqn` implies that `s.bottcherNearIter` is noncritical -/
theorem eqn_noncritical {x : ℂ × ℂ} (e : ∀ᶠ y in 𝓝 x, Eqn s n r y) (x0 : x.2 ≠ 0) :
    mfderiv I I (s.bottcherNearIter n x.1) (r x.1 x.2) ≠ 0 := by
  rcases x with ⟨c, x⟩; contrapose x0
  replace x0 : mfderiv I I (fun y ↦ s.bottcherNearIter n c (r c y)) x = 0 := by
    rw [←Function.comp_def,
      mfderiv_comp x
        ((s.bottcherNearIter_mAnalytic e.self_of_nhds.near).along_snd.mdifferentiableAt (by decide))
        (e.self_of_nhds.holo.along_snd.mdifferentiableAt (by decide)),
      x0, ContinuousLinearMap.zero_comp]
  have loc : (fun y ↦ s.bottcherNearIter n c (r c y)) =ᶠ[𝓝 x] fun y ↦ y ^ d ^ n :=
    ((continuousAt_const.prodMk continuousAt_id).eventually e).mp
      (.of_forall fun _ e ↦ e.eqn)
  rw [mfderiv_eq_fderiv, loc.fderiv_eq] at x0
  have d := (differentiableAt_pow (𝕜 := ℂ) (x := x) (d ^ n)).hasFDerivAt.hasDerivAt.deriv
  replace x0 := ContinuousLinearMap.ext_iff.mp x0 1
  rw [x0] at d
  have z1 : (0 : ℂ →L[ℂ] ℂ) 1 = (0 : ℂ) := rfl
  replace d := d.trans z1
  simp only [differentiableAt_fun_id, deriv_fun_pow, Nat.cast_pow, deriv_id'', mul_one, mul_eq_zero,
    pow_eq_zero_iff', Nat.cast_eq_zero, s.d0, ne_eq, false_and, false_or] at d
  exact d.1

/-- `p < 1` for any `p` in `Grow` -/
theorem Grow.p1 (g : Grow s c p n r) : p < 1 := by
  by_contra p1; simp only [not_lt] at p1
  have e := (g.eqn.filter_mono (nhds_le_nhdsSet (x := (c, 1)) ?_)).self_of_nhds
  · have lt := s.potential_lt_one (s.basin_iff_near.mpr ⟨_, e.near⟩)
    rw [e.potential, norm_one, lt_self_iff_false] at lt
    exact lt
  · simp only [p1, singleton_prod, mem_image, mem_closedBall_zero_iff, norm_one, Prod.mk_inj,
      true_and, exists_eq_right]

/-- `r` is analytic throughout the domain -/
theorem Grow.holo (g : Grow s c p n r) : ContMDiffOnNhd II I (uncurry r) ({c} ×ˢ closedBall 0 p) :=
  fun _ m ↦ (g.eqn.filter_mono (nhds_le_nhdsSet m)).self_of_nhds.holo

/-- `Grow` exists for small `p`, since small `p` is near `a` -/
theorem Super.grow_start (s : Super f d a) (c : ℂ) : ∃ p r, 0 < p ∧ Grow s c p 0 r := by
  have ba := s.bottcherNear_mAnalytic' (s.mem_near c)
  have nc := s.bottcherNear_mfderiv_ne_zero c
  rcases complex_inverse_fun ba nc with ⟨r, ra, rb, br⟩
  rw [s.bottcherNear_a] at ra br
  have rm : ∀ᶠ x : ℂ × ℂ in 𝓝 (c, 0), (x.1, r x.1 x.2) ∈ s.near := by
    refine (continuousAt_fst.prodMk ra.continuousAt).eventually_mem (s.isOpen_near.mem_nhds ?_)
    have r0 := rb.self_of_nhds; simp only [s.bottcherNear_a] at r0
    simp only [uncurry, r0]; exact s.mem_near c
  rcases eventually_nhds_iff.mp (ra.eventually.and (br.and rm)) with ⟨t, h, o, m⟩
  rcases Metric.isOpen_iff.mp o _ m with ⟨p, pp, sub⟩
  replace h := fun (x : ℂ × ℂ) m ↦ h x (sub m)
  have nb : ball (c, (0 : ℂ)) p ∈ 𝓝ˢ ({c} ×ˢ closedBall (0 : ℂ) (p / 2)) := by
    rw [isOpen_ball.mem_nhdsSet, ← ball_prod_same]; apply prod_mono
    rw [singleton_subset_iff]; exact mem_ball_self pp
    apply Metric.closedBall_subset_ball; exact half_lt_self pp
  use p / 2, r, half_pos pp
  exact
    { nonneg := (half_pos pp).le
      zero := by convert rb.self_of_nhds; simp only [s.bottcherNear_a]
      start := Filter.eventually_iff_exists_mem.mpr ⟨_, ball_mem_nhds _ pp, fun _ m ↦ (h _ m).2.1⟩
      eqn :=
        Filter.eventually_iff_exists_mem.mpr
          ⟨_, nb, fun _ m ↦
            { holo := (h _ m).1
              near := (h _ m).2.2
              eqn := by simp only [Function.iterate_zero_apply, pow_zero, pow_one, (h _ m).2.1] }⟩ }

/-- We can grow `p` and vary `c` a bit in `Grow` -/
theorem Grow.open (g : Grow s c p n r) : ∃ p', p < p' ∧ ∀ᶠ c' in 𝓝 c, Grow s c' p' n r := by
  have e := g.eqn; simp only [isCompact_singleton.nhdsSet_prod_eq (isCompact_closedBall _ _)] at e
  rcases Filter.mem_prod_iff.mp e with ⟨a', an, b', bn, sub⟩
  simp only [subset_ofPred] at sub
  rcases eventually_nhds_iff.mp (nhdsSet_singleton.subst an) with ⟨a, aa, ao, am⟩
  rcases eventually_nhdsSet_iff_exists.mp bn with ⟨b, bo, bp, bb⟩
  rcases domain_open' bp bo with ⟨q, pq, qb⟩
  use q, pq
  have m : ∀ᶠ c' in 𝓝 c, (c', r c' 0) ∈ s.near := by
    refine (continuousAt_id.prodMk ?_).eventually_mem (s.isOpen_near.mem_nhds ?_)
    · exact (g.eqn.filter_mono (nhds_le_nhdsSet (mem_domain c
        g.nonneg))).self_of_nhds.holo.along_fst.continuousAt
    · simp only [id, g.zero, s.mem_near c]
  apply m.mp
  apply ((continuousAt_id.prodMk continuousAt_const).eventually g.start.eventually_nhds).mp
  refine eventually_nhds_iff.mpr ⟨a, ?_, ao, am⟩
  intro c' am' start m
  exact
    { nonneg := _root_.trans g.nonneg pq.le
      zero := by have e := start.self_of_nhds; simp only [id, s.bottcherNear_eq_zero m] at e; exact e
      start
      eqn := by
        refine eventually_nhdsSet_iff_exists.mpr ⟨a ×ˢ b, ao.prod bo, ?_, ?_⟩
        · exact prod_mono (singleton_subset_iff.mpr am') qb
        · intro x ⟨cm, xm⟩; exact sub x ⟨aa _ cm, bb _ xm⟩ }

/-- We can decrease `p` in `Grow` -/
theorem Grow.anti (g : Grow s c p n r) {q : ℝ} (nonneg : 0 ≤ q) (le : q ≤ p) : Grow s c q n r :=
  { nonneg
    zero := g.zero
    start := g.start
    eqn :=
      g.eqn.filter_mono (nhdsSet_mono (prod_mono_right (Metric.closedBall_subset_closedBall le))) }

/-- `Eqn` determines `r` locally, given equality at a point -/
theorem eqn_unique {r0 r1 : ℂ → ℂ → S} {x : ℂ × ℂ} (e0 : ∀ᶠ y in 𝓝 x, Eqn s n r0 y)
    (e1 : ∀ᶠ y in 𝓝 x, Eqn s n r1 y) (r01 : r0 x.1 x.2 = r1 x.1 x.2) (x0 : x.2 ≠ 0) :
    uncurry r0 =ᶠ[𝓝 x] uncurry r1 := by
  have ba := s.bottcherNearIter_mAnalytic e0.self_of_nhds.near
  have inj := ba.local_inj' (eqn_noncritical e0 x0); nth_rw 2 [r01] at inj
  have t : Tendsto (fun x : ℂ × ℂ ↦ (x.1, r0 x.1 x.2, r1 x.1 x.2)) (𝓝 x)
      (𝓝 (x.1, r0 x.1 x.2, r1 x.1 x.2)) :=
    continuousAt_fst.prodMk
      (e0.self_of_nhds.holo.continuousAt.prodMk e1.self_of_nhds.holo.continuousAt)
  apply (t.eventually inj).mp
  refine e0.mp (e1.mp (.of_forall fun x e1 e0 inj ↦ ?_))
  specialize inj _
  simp only [Super.bottcherNearIter, e0.eqn, e1.eqn]
  exact inj

/-- The property that we will use to define valid germs in analytic continuation.
    This is normally just `Eqn`, but requiring `=ᶠ[𝓝 (c,0)]` if we're at the origin
    since there `Eqn` uniqueness breaks down. -/
structure Eqns (s : Super f d a) (n : ℕ) (r0 r : ℂ → ℂ → S) (x : ℂ × ℂ) : Prop where
  eqn : ∀ᶠ y in 𝓝 x, Eqn s n r y
  start : x.2 = 0 → uncurry r =ᶠ[𝓝 x] uncurry r0

/-- `Eqns` implies `r` is analytic -/
theorem Eqns.holo {r0 r : ℂ → ℂ → S} {x : ℂ × ℂ} (e : Eqns s n r0 r x) :
    ContMDiffAt II I ω (uncurry r) x :=
  e.eqn.self_of_nhds.holo

/-- `Eqns` is local -/
theorem Eqns.congr {x : ℂ × ℂ} {r0 r1 r2 : ℂ → ℂ → S} (e1 : Eqns s n r0 r1 x)
    (loc : uncurry r1 =ᶠ[𝓝 x] uncurry r2) : Eqns s n r0 r2 x :=
  { eqn := e1.eqn.mp (loc.eventually_nhds.mp (.of_forall fun _ loc e ↦ e.congr loc))
    start := fun x0 ↦ loc.symm.trans (e1.start x0) }

variable [T2Space S]

/-- The equivalent of `Grow` on `{c} ×ˢ ball 0 p`, where the ball is open rather than closed.
    However, we use an `n` that covers the boundary at potential `p` as well, so that analytic
    continuation will work without changing `n`. -/
structure GrowOpen (s : Super f d a) (c : ℂ) (p : ℝ) (r : ℂ → ℂ → S) : Prop where
  pos : 0 < p
  post : p < s.p c
  zero : r c 0 = a
  start : ∀ᶠ x : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear x.1 (r x.1 x.2) = x.2
  eqn : ∀ᶠ x : ℂ × ℂ in 𝓝ˢ ({c} ×ˢ ball 0 p), Eqn s (s.np c p) r x

/-- We can analytically continue `r` to any point in the closure -/
theorem GrowOpen.point (g : GrowOpen s c p r) [OnePreimage s] {x : ℂ} (ax : ‖x‖ ≤ p) :
    ∃ r' : ℂ → ℂ → S,
      (∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), Eqn s (s.np c p) r' y) ∧
        ∃ᶠ y in 𝓝 x, y ∈ ball (0 : ℂ) p ∧ r' c y = r c y := by
  -- If z = a, we can use r
  by_cases za : ‖x‖ = 0
  · use r
    simp only [norm_eq_zero] at za
    simp only [za, and_true]
    constructor
    · refine g.eqn.filter_mono (nhds_le_nhdsSet ?_)
      exact mk_mem_prod rfl (mem_ball_self g.pos)
    · exact (isOpen_ball.eventually_mem (mem_ball_self g.pos)).frequently
  replace za := (Ne.symm za).lt_of_le (norm_nonneg _)
  -- Choose a value z = r' c x as a cluster point of r c at 𝓝[t] x
  set t := ball (0 : ℂ) p
  have xt : x ∈ closure t := by
    simp only [t, closure_ball _ g.pos.ne', mem_closedBall, Complex.dist_eq, sub_zero, ax]
  have ez : ∃ z : S, MapClusterPt z (𝓝[t] x) (r c) :=
    @exists_clusterPt_of_compactSpace _ _ _ _
      (Filter.map_neBot (hf := mem_closure_iff_nhdsWithin_neBot.mp xt))
  rcases ez with ⟨z, cp⟩
  have pz : s.potential c z = ‖x‖ := by
    refine eq_of_nhds_neBot (cp.map (Continuous.potential s).along_snd.continuousAt
      (Filter.tendsto_map' ?_))
    have e : ∀ y, y ∈ t → (s.potential c ∘ r c) y = ‖y‖ := by
      intro y m; simp only [Function.comp]; exact (g.eqn.self_of_nhdsSet (c, y) ⟨rfl, m⟩).potential
    exact tendsto_nhdsWithin_congr (fun t m ↦ (e t m).symm)
      continuous_norm.continuousWithinAt
  have nice := s.nice_np c (lt_of_lt_of_le g.post s.p_le_one)
  have ba := nice.contMDiffAt_bottcherNearIter (le_trans (le_of_eq pz) ax)
  have nc := nice.mfderiv_ne_zero (le_trans (le_of_eq pz) ax) (le_refl _)
  generalize hn : s.np c p = n
  rw [hn] at ba nc
  generalize hb : s.bottcherNearIter n = b
  have bz : b c z = x ^ d ^ n := by
    refine eq_of_nhds_neBot (cp.map ?_ (Filter.tendsto_map' ?_))
    · rw [← hb]
      exact ba.along_snd.continuousAt
    · have e : ∀ y, y ∈ t → (b c ∘ r c) y = y ^ d ^ n := by
        intro y m
        simp only [Function.comp, ← hb, ← hn]
        exact (g.eqn.self_of_nhdsSet (c, y) ⟨rfl, m⟩).eqn
      exact tendsto_nhdsWithin_congr (fun t m ↦ (e t m).symm) (continuous_pow _).continuousWithinAt
  have post : Postcritical s c z := lt_of_le_of_lt (_root_.trans (le_of_eq pz) ax) g.post
  rw [← pz] at za
  -- Invert s.bottcherNearIter at z
  replace nc := s.bottcherNearIter_mfderiv_ne_zero nc (post.not_precritical za.ne')
  rcases complex_inverse_fun ba nc with ⟨i, ia, ib, bi⟩
  simp only [hb, bz] at ia bi ib
  have pt : Tendsto (fun p : ℂ × ℂ ↦ (p.1, p.2 ^ d ^ n)) (𝓝 (c, x)) (𝓝 (c, x ^ d ^ n)) :=
    continuousAt_fst.prodMk (continuousAt_snd.pow _)
  have ian : ContMDiffAt II I ω (uncurry fun e y : ℂ ↦ i e (y ^ d ^ n)) (c, x) :=
    ia.comp₂_of_eq contMDiffAt_fst ((contMDiff_pow _).contMDiffAt.comp _ contMDiffAt_snd) rfl
  use fun e y ↦ i e (y ^ d ^ n); constructor
  · -- We satisfy eqn near x
    apply eqn_near ian
    · simp only [← bz]
      rw [ib.self_of_nhds, ← hn]
      exact nice.near (le_trans (le_of_eq pz) ax)
    · refine (pt.eventually bi).mp (.of_forall ?_)
      intro _ bi; simp only [← hb] at bi; exact bi
  · -- We frequently match r, by local injectivity of b
    have ne : MapClusterPt (z, z) (𝓝[t] x) fun y ↦ (r c y, i c (y ^ d ^ n)) := by
      apply cp.prod; refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have ic := ian.along_snd.continuousAt
      simp only [ContinuousAt, ←bz] at ic; rw [ib.self_of_nhds] at ic
      exact ic
    have inj := (@Filter.Eventually.frequently _ _ ne _
            (Filter.Eventually.filter_mono inf_le_left (ba.along_snd.local_inj nc))).filter_mono
        inf_le_right
    simp only [Filter.frequently_map, frequently_nhdsWithin_iff] at inj
    apply inj.mp
    apply ((continuousAt_const.prodMk (continuousAt_pow _ _)).eventually bi).mp
    refine .of_forall ?_; simp only [← hb, ← hn]; intro x bi ⟨inj, m⟩
    refine ⟨m, (inj ?_).symm⟩; simp only [bi]
    exact (g.eqn.self_of_nhdsSet ⟨c, x⟩ (mk_mem_prod rfl m)).eqn

/-- `Eqns` determines `r` once one point is fixed -/
theorem eqns_unique {r0 r1 r2 : ℂ → ℂ → S} {t : Set (ℂ × ℂ)}
    (pre : IsPreconnected t) (e1 : ∀ x, x ∈ t → Eqns s n r0 r1 x)
    (e2 : ∀ x, x ∈ t → Eqns s n r0 r2 x) (ne : ∃ x, x ∈ t ∧ uncurry r1 x = uncurry r2 x) :
    EqOn (uncurry r1) (uncurry r2) t := by
  -- The set on which r0 = r1 is both relatively open and closed, so it's everything
  set u := {x | uncurry r1 x = uncurry r2 x}
  replace ne : (t ∩ u).Nonempty := ne
  have op : t ∩ u ⊆ interior u := by
    intro ⟨c, x⟩ ⟨mt, mu⟩; rw [mem_interior_iff_mem_nhds]
    by_cases x0 : x = 0; exact ((e1 _ mt).start x0).trans ((e2 _ mt).start x0).symm
    exact eqn_unique (e1 _ mt).eqn (e2 _ mt).eqn mu x0
  have cl : t ∩ closure u ⊆ u := by
    intro x ⟨mt, mu⟩; simp only [mem_closure_iff_frequently] at mu ⊢
    exact tendsto_nhds_unique_of_frequently_eq (e1 _ mt).holo.continuousAt
      (e2 _ mt).holo.continuousAt mu
  exact _root_.trans (pre.relative_clopen ne op cl) interior_subset

/-- `r` is unique in `Grow` -/
theorem Grow.unique {r0 r1 : ℂ → ℂ → S} {p0 p1 : ℝ} {n0 n1 : ℕ} (g0 : Grow s c p0 n0 r0)
    (g1 : Grow s c p1 n1 r1) (p01 : p0 ≤ p1) :
    uncurry r0 =ᶠ[𝓝ˢ ({c} ×ˢ closedBall 0 p0)] uncurry r1 := by
  -- Reduce to equality near (c,0)
  by_cases pos : p0 < 0
  · simp only [Metric.closedBall_eq_empty.mpr pos, singleton_prod, image_empty, nhdsSet_empty,
      Filter.EventuallyEq, Filter.eventually_bot]
  have m : (c, (0 : ℂ)) ∈ {c} ×ˢ closedBall (0 : ℂ) p0 := mem_domain c (not_lt.mp pos)
  refine ContMDiffOnNhd.eq_of_locally_eq g0.holo (g1.holo.mono (domain_mono _ p01))
      (domain_preconnected _ _) ⟨(c, 0), m, ?_⟩
  -- Injectivity of s.bottcherNear gives us the rest
  have t : ContinuousAt (fun x : ℂ × ℂ ↦ (x.1, r0 x.1 x.2, r1 x.1 x.2)) (c, 0) :=
    continuousAt_fst.prodMk
      ((g0.eqn.filter_mono (nhds_le_nhdsSet m)).self_of_nhds.holo.continuousAt.prodMk
        (g1.eqn.filter_mono (nhds_le_nhdsSet (domain_mono c p01 m))).self_of_nhds.holo.continuousAt)
  simp only [ContinuousAt, g0.zero, g1.zero] at t
  have inj := (s.bottcherNear_mAnalytic' (s.mem_near c)).local_inj'
    (s.bottcherNear_mfderiv_ne_zero c)
  refine ((t.eventually inj).and (g0.start.and g1.start)).mp (.of_forall ?_)
  intro ⟨e, y⟩ ⟨inj, s0, s1⟩; exact inj (s0.trans s1.symm)

/-- Given `GrowOpen _ _ p`, we can analytically continue to the boundary to get `Grow _ _ p` -/
theorem GrowOpen.grow (g : GrowOpen s c p r) [OnePreimage s] : ∃ r', Grow s c p (s.np c p) r' := by
  set n := s.np c p
  have b : Base (fun f x ↦ Eqns s n r (curry f) x) ({c} ×ˢ ball (0 : ℂ) p) (uncurry r) :=
    { convex := (convex_singleton c).prod (convex_ball 0 p)
      compact := by
        simp only [closure_prod_eq, closure_ball _ g.pos.ne', closure_singleton]
        exact isCompact_singleton.prod (isCompact_closedBall _ _)
      congr := by intro r0 r1 x e0 r01; exact e0.congr (by simp only [Function.uncurry_curry, r01])
      start := by
        simp only [Filter.eventually_iff]; rw [mem_nhdsSet_iff_forall]; intro x m
        exact (g.eqn.filter_mono (nhds_le_nhdsSet m)).eventually_nhds.mp
          (.of_forall fun y e ↦
          { eqn := e
            start := by
              simp only [Function.curry_uncurry, Filter.EventuallyEq.refl, imp_true_iff] })
      point := by
        intro ⟨c', x⟩ m
        simp only [closure_prod_eq, closure_ball _ g.pos.ne', closure_singleton, mem_prod_eq,
          mem_singleton_iff, mem_closedBall, Complex.dist_eq, sub_zero] at m
        have ct : Tendsto (fun x ↦ (c, x)) (𝓝 x) (𝓝 (c, x)) :=
          continuousAt_const.prodMk continuousAt_id
        by_cases x0 : x ≠ 0
        · rw [m.1]; rcases g.point m.2 with ⟨r', e, rr⟩
          use uncurry r'; constructor
          · have t : ContinuousAt (fun y : ℂ × ℂ ↦ y.2) (c, x) := continuousAt_snd
            refine e.eventually_nhds.mp ((t.eventually_ne x0).mp (.of_forall ?_))
            intro y y0 e
            exact
              { eqn := e
                start := fun h ↦ (y0 h).elim }
          · refine ct.frequently (rr.mp (.of_forall ?_)); intro x ⟨m, e⟩
            simp only [mem_prod_eq, mem_singleton_iff, true_and]; use m, e
        · use uncurry r; simp only [not_not] at x0
          simp only [m.1, x0, and_true] at ct ⊢; constructor
          · refine
              (g.eqn.filter_mono (nhds_le_nhdsSet ?_)).eventually_nhds.mp
                (.of_forall fun y e ↦ ?_)
            use rfl, mem_ball_self g.pos; simp only [Function.curry_uncurry]
            exact
              { eqn := e
                start := by
                  simp only [Filter.EventuallyEq.refl, imp_true_iff] }
          · refine ct.frequently (Filter.Eventually.frequently ?_)
            simp only [mem_prod_eq, mem_singleton_iff, true_and]
            exact isOpen_ball.eventually_mem (mem_ball_self g.pos)
      unique := by
        intro r0 r1 t _ pre e0 e1 r01
        have u := eqns_unique pre e0 e1 ?_
        simp only [Function.uncurry_curry] at u; exact u
        simp only [Function.uncurry_curry]; exact r01 }
  have m0 : (c, (0 : ℂ)) ∈ ({c} ×ˢ ball 0 p : Set (ℂ × ℂ)) := by
    simp only [mem_prod_eq, mem_singleton_iff, true_and, mem_ball_self g.pos]
  use curry b.u
  exact
    { nonneg := g.pos.le
      zero := by rw [curry, b.uf.self_of_nhdsSet m0, uncurry, g.zero]
      start := by
        refine g.start.mp ((b.uf.filter_mono (nhds_le_nhdsSet m0)).mp (.of_forall ?_))
        intro x e b; simp only [curry, uncurry, Prod.mk.eta] at e ⊢; rw [e]; exact b
      eqn := by
        have fp := b.up
        simp only [closure_prod_eq, closure_singleton, closure_ball _ g.pos.ne'] at fp
        exact fp.mp (.of_forall fun x e ↦ e.eqn.self_of_nhds) }

/-- Given a increasing sequence of `p`s with corresponding `r`s and `Grow`s, we can piece together
    a single, globally consistent `r`. -/
theorem join_r (s : Super f d a) {p : ℕ → ℝ} {n : ℕ → ℕ} {ps : ℝ} {r : ℕ → ℂ → ℂ → S}
    (g : ∀ k, Grow s c (p k) (n k) (r k)) (mono : Monotone p)
    (tend : Tendsto p atTop (𝓝 ps)) :
    ∃ rs : ℂ → ℂ → S, ∀ (k) (x : ℂ), ‖x‖ < p k → uncurry rs =ᶠ[𝓝 (c, x)] uncurry (r k) := by
  have above : ∀ k, p k ≤ ps := fun k ↦ mono.ge_of_tendsto tend k
  generalize hrs : (fun e x : ℂ ↦
    if h : ‖x‖ < ps then r (Nat.find (tend.exists_lt h)) e x else a) = rs
  use rs
  -- rs is locally each r, via induction
  have loc : ∀ k, ∀ᶠ e in 𝓝 c, ∀ x : ℂ, ‖x‖ < p k → rs e x = r k e x := by
    intro k; induction' k with k h
    · refine .of_forall fun e x x0 ↦ ?_
      have xe : ∃ k, ‖x‖ < p k := ⟨0, x0⟩
      simp only [← hrs, lt_of_lt_of_le x0 (above _), dif_pos, (Nat.find_eq_zero xe).mpr x0]
    · have eq := (g k).unique (g (k + 1)) (mono (Nat.lt_succ_self _).le)
      simp only [isCompact_singleton.nhdsSet_prod_eq (isCompact_closedBall _ _)] at eq
      apply h.mp
      rcases Filter.mem_prod_iff.mp eq with ⟨u0, n0, u1, n1, eq⟩
      simp only [nhdsSet_singleton] at n0
      refine Filter.eventually_of_mem n0 fun e eu h x xk1 ↦ ?_
      by_cases xk0 : ‖x‖ < p k
      · have m : (e, x) ∈ u0 ×ˢ u1 := by
          refine mk_mem_prod eu (subset_of_mem_nhdsSet n1 ?_)
          simp only [mem_closedBall, Complex.dist_eq, sub_zero, xk0.le]
        specialize eq m; simp only [mem_ofPred, uncurry] at eq
        rw [h _ xk0, eq]
      · have xe : ∃ k, ‖x‖ < p k := ⟨k + 1, xk1⟩
        have n := (Nat.find_eq_iff xe).mpr ⟨xk1, ?_⟩
        simp only [← hrs, lt_of_lt_of_le xk1 (above _), dif_pos, n]
        intro j jk; simp only [not_lt, Nat.lt_succ_iff] at jk xk0 ⊢
        exact _root_.trans (mono jk) xk0
  -- rs is locally each r, final form
  intro k x xk
  rcases eventually_nhds_iff.mp (loc k) with ⟨u, eq, uo, uc⟩
  have m : u ×ˢ ball (0 : ℂ) (p k) ∈ 𝓝 (c, x) := by
    refine prod_mem_nhds (uo.mem_nhds uc) (isOpen_ball.mem_nhds ?_)
    simp only [mem_ball, Complex.dist_eq, sub_zero, xk]
  apply Filter.eventually_of_mem m; intro ⟨e, y⟩ ⟨m0, m1⟩
  simp only [mem_ball, Complex.dist_eq, sub_zero] at m1
  exact eq _ m0 _ m1

/-- If we can `Grow` up to any `q < p`, we get a `GrowOpen` up to `p` -/
theorem joined_growOpen (s : Super f d a) {p : ℕ → ℝ} {ps : ℝ} {r : ℕ → ℂ → ℂ → S} {rs : ℂ → ℂ → S}
    (g : ∀ k, Grow s c (p k) (s.np c ps) (r k)) (tend : Tendsto p atTop (𝓝 ps))
    (post : ps < s.p c) (pos : 0 < ps)
    (loc : ∀ (k) (x : ℂ), ‖x‖ < p k → uncurry rs =ᶠ[𝓝 (c, x)] uncurry (r k)) :
    GrowOpen s c ps rs :=
  { pos
    post
    zero := by
      rcases tend.exists_lt pos with ⟨k, pos⟩
      have e := (loc k 0 (by simp only [norm_zero, pos])).self_of_nhds
      simp only [uncurry] at e; simp only [e, (g k).zero]
    start := by
      rcases tend.exists_lt pos with ⟨k, pos⟩
      apply (g k).start.mp
      apply (loc k 0 (by simp only [norm_zero, pos])).mp
      refine .of_forall fun ⟨e, x⟩ loc start ↦ ?_
      simp only [uncurry] at loc start ⊢; simp only [start, loc]
    eqn := by
      apply mem_nhdsSet_iff_forall.mpr; intro ⟨c', x⟩ lt
      simp only [mem_prod_eq, mem_singleton_iff, mem_ball, Complex.dist_eq, sub_zero] at lt
      simp only [lt.1, true_and, ← Filter.eventually_iff] at lt ⊢; clear c'
      rcases tend.exists_lt lt with ⟨k, ltp⟩
      have m : (c, x) ∈ {c} ×ˢ closedBall (0 : ℂ) (p k) := by
        simp only [mem_prod_eq, mem_singleton_iff, Metric.mem_closedBall, true_and, Complex.dist_eq,
          sub_zero, ltp.le]
      have lt' : ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), ‖y.2‖ < ps :=
        (continuous_norm.continuousAt.comp continuousAt_snd).eventually_lt
          continuousAt_const lt
      apply ((g k).eqn.filter_mono (nhds_le_nhdsSet m)).mp
      apply (loc _ _ ltp).eventually_nhds.mp
      apply lt'.mp
      refine .of_forall fun ⟨e, y⟩ _ loc eq ↦ ?_
      exact eq.congr (Filter.EventuallyEq.symm loc) }

/-- We can grow up to the postcritical value `s.p c` -/
theorem Super.grow (s : Super f d a) [OnePreimage s] :
    ∀ p, 0 ≤ p → p < s.p c → ∃ r, Grow s c p (s.np c p) r := by
  set t : Set ℝ := {p | 0 ≤ p ∧ ∀ q, 0 ≤ q → q ≤ p → ∃ r, Grow s c q (s.np c q) r}
  have self : ∀ {p}, p ∈ t → ∃ r, Grow s c p (s.np c p) r := fun {p} m ↦ m.2 _ m.1 (le_refl _)
  have t1 : ∀ p : ℝ, p ∈ t → p < 1 := by intro p m; rcases self m with ⟨r, g⟩; exact g.p1
  have above : BddAbove t := bddAbove_def.mpr ⟨1, fun p m ↦ (t1 p m).le⟩
  rcases s.grow_start c with ⟨p0, r0, pos0, g0⟩
  have start : p0 ∈ t := by
    use g0.nonneg; intro q q0 qp; use r0; exact (g0.anti q0 qp).mono (Nat.zero_le _)
  have ne : t.Nonempty := ⟨p0, start⟩
  have pos : 0 < sSup t := lt_csSup_of_lt above start pos0
  by_cases missing : sSup t ∈ t
  · -- Contradict by growing a bit beyond Sup t
    rcases self missing with ⟨r, g⟩; rcases g.open with ⟨p, sp, g'⟩
    suffices m : p ∈ t by linarith [le_csSup above m]
    use g'.self_of_nhds.nonneg
    intro q q0 qp; by_cases le : q ≤ sSup t; exact missing.2 _ q0 le
    use r; simp only [not_le] at le
    exact (g'.self_of_nhds.anti q0 qp).mono (s.np_mono c le.le (lt_of_le_of_lt qp g'.self_of_nhds.p1))
  by_cases post : sSup t < s.p c
  · exfalso; apply missing; use pos.le; intro q q0 le
    -- q < Sup t is trivial
    by_cases lt : q < sSup t
    · rcases exists_lt_of_lt_csSup ne lt with ⟨q', ⟨_, m⟩, qq⟩
      exact m _ q0 qq.le
    have eq := le_antisymm le (not_lt.mp lt); rw [eq]; clear eq lt le q0 q
    -- Piece together a single r that works < Sup t, then close to Sup t
    rcases exists_seq_tendsto_sSup ne above with ⟨p, mono, tend, sub⟩
    simp only [mem_ofPred, t] at sub
    set pr := fun k ↦ choose (self (sub k))
    have pg : ∀ k, Grow s c (p k) (s.np c (sSup t)) (pr k) := fun k ↦
      (choose_spec (self (sub k))).mono
        (s.np_mono c (le_csSup above (sub k)) (lt_of_lt_of_le post s.p_le_one))
    rcases join_r s pg mono tend with ⟨r, loc⟩
    exact (joined_growOpen s pg tend post pos loc).grow
  -- Finish!
  simp only [not_lt] at post
  intro p p0 lt
  rcases exists_lt_of_lt_csSup ne (lt_of_lt_of_le lt post) with ⟨q, m, pq⟩
  exact m.2 _ p0 pq.le

/-- There is a single `r` that achieves all `Grow`s for all `c` and `p < s.p c`.

    That is, there exists a map on `𝓝ˢ ({c} ×ˢ ball 0 (s.p c))` which everywhere looks
    like an inverse to Böttcher coordinates, and thus defines external rays up to the
    critical potential `s.p c`. -/
theorem Super.has_ray (s : Super f d a) [OnePreimage s] :
    ∃ r : ℂ → ℂ → S, ∀ c p, 0 ≤ p → p < s.p c → Grow s c p (s.np c p) r := by
  generalize hr : (fun {c p} (h : 0 ≤ p ∧ p < s.p c) ↦ choose (s.grow _ h.1 h.2)) = r
  have g : ∀ {c p} (h : 0 ≤ p ∧ p < s.p c), Grow s c p (s.np c p) (r h) := by
    intro c p h; rw [← hr]; exact choose_spec _
  clear hr
  generalize hray : (fun c x : ℂ ↦
    if h : ‖x‖ < s.p c then r ⟨norm_nonneg _, h⟩ c x else a) = ray
  have loc : ∀ {c p} (h : 0 ≤ p ∧ p < s.p c),
      uncurry ray =ᶠ[𝓝ˢ ({c} ×ˢ closedBall 0 p)] uncurry (r h) := by
    intro c p h
    rcases(g h).open with ⟨q', pq', gh⟩
    rcases exists_between (lt_min pq' h.2) with ⟨q, pq, qlo⟩
    rcases lt_min_iff.mp qlo with ⟨qq', qs⟩
    have q0 : 0 ≤ q := _root_.trans h.1 pq.le
    replace gh := gh.mp (.of_forall fun c' g ↦ g.anti q0 qq'.le)
    clear qlo qq' pq' q'
    rcases eventually_nhds_iff.mp gh with ⟨t0, gh, ot0, ct0⟩
    rcases eventually_nhds_iff.mp (s.lowerSemicontinuous_p _ _ qs) with ⟨t1, lo, ot1, ct1⟩
    refine eventually_nhdsSet_iff_exists.mpr
        ⟨(t0 ∩ t1) ×ˢ ball 0 q, (ot0.inter ot1).prod isOpen_ball, ?_, ?_⟩
    · exact prod_mono (singleton_subset_iff.mpr ⟨ct0, ct1⟩) (Metric.closedBall_subset_ball pq)
    · intro ⟨e, x⟩ ⟨⟨et0, et1⟩, xq⟩; simp only [uncurry] at et0 et1 xq ⊢
      simp only [mem_ball, Complex.dist_eq, sub_zero] at xq
      have hx : 0 ≤ ‖x‖ ∧ ‖x‖ < s.p e := ⟨norm_nonneg _, _root_.trans xq (lo _ et1)⟩
      simp only [← hray, dif_pos hx.2]
      refine ((g hx).unique (gh _ et0) xq.le).self_of_nhdsSet (x := ⟨e, x⟩) ⟨rfl, ?_⟩
      simp only [mem_closedBall, Complex.dist_eq, sub_zero, le_refl]
  use ray; intro c p p0 h
  exact (g ⟨p0, h⟩).congr (loc ⟨p0, h⟩).symm

end
end Ray_Ray_Dynamics_Grow

-- ===== Ray.Dynamics.Ray =====
section Ray_Ray_Dynamics_Ray
/-
## The external ray map

We define the external ray map `s.ray` on all postcritical points `(c,z)` (points where
`s.potential c z < s.potential c w` for all non-`a` critical points `w` of `f c`).

The existence of `s.ray` was proven in `Grow.lean` as `Super.has_ray`.  Here we define the
map, write down its basic properties, and prove that `(c,y) ↦ (c, s.ray c y)` is a
bijection from `s.ext` to `s.post`, where `s.ext = {(c,y) | abs y < s.p c}`.

Note that while our `s.ray` map is defined for all `c`, we are working in dynamical space:
the key varying coordinate is `z`.  In particular, our bijection result is equivalent to
`s.ray c` being a bijection from `ball 0 (s.p c)` to `{z | s.potential c z < s.p c}` for all `c`.

We still haven't defined Böttcher coordinates except near `a`, but their existence is immediate
from bijectivity of `s.ray`; see `Bottcher.lean`.
-/

open Classical
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball mem_closedBall mem_ball_self)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c x : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {s : Super f d a}
variable {y : ℂ × ℂ}

/-- The `c`-slice of `s.ext` is `ball 0 (s.p c)` -/
theorem Super.ext_slice (s : Super f d a) (c : ℂ) :
    {x | (c, x) ∈ s.ext} = ball (0 : ℂ) (s.p c) := by
  apply Set.ext; intro x; simp only [Super.ext, mem_ball, mem_ofPred, Complex.dist_eq, sub_zero]

variable [T2Space S]

/-- The external ray map: `s.ray c y` is moving in external ray space from the superattractor `a`
    out by `y`.  `s.ray` is well behaved for all postcritical values `(c,y) ∈ s.ext` (see below). -/
def Super.ray (s : Super f d a) [OnePreimage s] : ℂ → ℂ → S :=
  choose s.has_ray

/-- `s.ext` is open -/
theorem Super.isOpen_ext (s : Super f d a) [OnePreimage s] : IsOpen s.ext := by
  set f := fun y : ℂ × ℂ ↦ s.p y.1 - ‖y.2‖
  have fc : LowerSemicontinuous f :=
    (s.lowerSemicontinuous_p.comp continuous_fst).add
      (continuous_norm.comp continuous_snd).neg.lowerSemicontinuous
  have e : s.ext = f ⁻¹' Ioi 0 :=
    Set.ext fun _ ↦ by simp only [Super.ext, mem_ofPred, mem_preimage, mem_Ioi, sub_pos, f]
  rw [e]; exact fc.isOpen_preimage _

/-- `(c,0) ∈ s.ext` -/
@[simp] theorem Super.mem_ext (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (c, (0 : ℂ)) ∈ s.ext := by
  simp only [Super.ext, mem_ofPred, norm_zero, s.p_pos c]

/-- `c`-slices of `s.ext` are connected -/
theorem Super.ext_slice_connected (s : Super f d a) [OnePreimage s] (c : ℂ) :
    IsConnected {x | (c, x) ∈ s.ext} := by
  rw [s.ext_slice c]
  exact ⟨⟨(0 : ℂ), mem_ball_self (s.p_pos c)⟩, (convex_ball (0 : ℂ) (s.p c)).isPreconnected⟩

/-- `s.ext` is connected (since `c`-slices and `univ ×ˢ {0}` are connected) -/
theorem Super.ext_connected (s : Super f d a) [OnePreimage s] : IsConnected s.ext := by
  refine ⟨⟨(0, 0), s.mem_ext 0⟩, isPreconnected_of_forall (0, 0) ?_⟩; intro ⟨c, x⟩ m
  use(fun x ↦ (c, x)) '' {x | (c, x) ∈ s.ext} ∪ univ ×ˢ {0}
  simp only [mem_image, mem_union, union_subset_iff, mem_ofPred, mem_prod_eq, mem_univ, true_and,
    mem_singleton_iff, or_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro y n; simp only [mem_image, mem_ofPred] at n; rcases n with ⟨x, m, e⟩; rw [e] at m; exact m
  · intro ⟨c, x⟩ m; simp only [mem_prod_eq, mem_singleton_iff] at m; rw [m.2]; exact s.mem_ext c
  · left; exact ⟨x, m, rfl⟩
  · refine IsPreconnected.union (c, 0) ?_ ?_ ?_ ?_
    · use 0, s.mem_ext c
    · exact mk_mem_prod (mem_univ _) rfl
    · exact IsPreconnected.image (s.ext_slice_connected c).isPreconnected _
        (Continuous.prodMk_right _).continuousOn
    · exact isPreconnected_univ.prod isPreconnected_singleton

/-- `s.ray` satisfies `Grow` (it looks like a local inverse to Böttcher coordinates) -/
lemma Super.ray_spec (s : Super f d a) [OnePreimage s] :
    ∀ {c p}, 0 ≤ p → p < s.p c → Grow s c p (s.np c p) s.ray :=
  fun {c p} ↦ choose_spec s.has_ray c p

/-- `s.ray` satisfies `Eqn` -/
lemma Super.ray_eqn_self (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    Eqn s (s.np c ‖x‖) s.ray (c, x) :=
  (s.ray_spec (norm_nonneg _) post).eqn.self_of_nhdsSet _ mem_domain_self

/-- `s.ray` is analytic on `s.ext` (up to the critical potential for each `c`) -/
theorem Super.ray_mAnalytic (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    ContMDiffAt II I ω (uncurry s.ray) (c, x) :=
  (s.ray_eqn_self post).holo

/-- `s.ray c` is analytic up to the critical potential (that is, on `ball 0 (s.p c)`) -/
theorem Super.ray_mAnalytic_slice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ContMDiffOnNhd I I (s.ray c) {x | (c, x) ∈ s.ext} := fun _ m ↦ (s.ray_mAnalytic m).along_snd

/-- `s.ray` is analytic on `s.ext` (up to the critical potential for each `c`) -/
theorem Super.ray_mAnalyticOn (s : Super f d a) [OnePreimage s] :
    ContMDiffOnNhd II I (uncurry s.ray) s.ext := by intro ⟨c, x⟩ m; exact s.ray_mAnalytic m

/-- Rays start at `a`: `s.ray c 0 = a` -/
@[simp] theorem Super.ray_zero (s : Super f d a) [OnePreimage s] (c : ℂ) : s.ray c 0 = a :=
  (s.ray_spec (le_refl _) (s.p_pos c)).zero

/-- `s.ray` maps `s.ext` into `s.basin` -/
theorem Super.ray_basin (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, s.ray c x) ∈ s.basin :=
  s.basin_iff_near.mpr ⟨_, (s.ray_eqn_self post).near⟩

/-- `s.ray` maps into `s.near` with if we iterate `s.np c ‖x‖` times -/
theorem Super.ray_near (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, (f c)^[s.np c ‖x‖] (s.ray c x)) ∈ s.near :=
  (s.ray_eqn_self post).near

/-- `s.ray` inverts `s.bottcherNear` near 0 -/
theorem Super.ray_eqn_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ∀ᶠ y : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear y.1 (s.ray y.1 y.2) = y.2 :=
  (s.ray_spec (le_refl _) (s.p_pos c)).start

/-- `s.ray` inverts `s.bottcherNear` after iteration -/
theorem Super.ray_eqn_iter' (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x),
      s.bottcherNearIter (s.np c ‖x‖) y.1 (s.ray y.1 y.2) = y.2 ^ d ^ s.np c ‖x‖ :=
  ((s.ray_spec (norm_nonneg _) post).eqn.filter_mono (nhds_le_nhdsSet mem_domain_self)).mp
    (.of_forall fun _ e ↦ e.eqn)

/-- `s.ray` sends absolute value to potential -/
theorem Super.ray_potential (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    s.potential c (s.ray c x) = ‖x‖ :=
  (s.ray_eqn_self post).potential

/-- `s.ray` maps `s.ext` into `s.post` -/
theorem Super.ray_post (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, s.ray c x) ∈ s.post := by
  simp only [Super.post, Postcritical, mem_ofPred, s.ray_potential post]; exact post

/-- `s.ray` is noncritical at 0 -/
theorem Super.ray_noncritical_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    mfderiv I I (s.ray c) 0 ≠ 0 := by
  have h : mfderiv I I (s.bottcherNear c ∘ s.ray c) 0 ≠ 0 := by
    have e : s.bottcherNear c ∘ s.ray c =ᶠ[𝓝 0] id :=
      (continuousAt_const.prodMk continuousAt_id).eventually (s.ray_eqn_zero c)
    rw [e.mfderiv_eq]; exact id_mderiv_ne_zero
  contrapose h
  have hb : MDifferentiableAt I I (s.bottcherNear c) (s.ray c 0) := by
    rw [s.ray_zero]
    exact (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd.mdifferentiableAt (by decide)
  have hr : MDifferentiableAt I I (s.ray c) 0 :=
    (s.ray_mAnalytic (s.mem_ext c)).along_snd.mdifferentiableAt (by decide)
  rw [mfderiv_comp 0 hb hr, h, ContinuousLinearMap.comp_zero]

-- `s.ray` is noncritical everywhere in `s.ext`
theorem Super.ray_noncritical (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    mfderiv I I (s.ray c) x ≠ 0 := by
  by_cases x0 : x = 0; rw [x0]; exact s.ray_noncritical_zero c
  set n := s.np c ‖x‖
  have h : mfderiv I I (s.bottcherNearIter n c ∘ s.ray c) x ≠ 0 := by
    have e : s.bottcherNearIter n c ∘ s.ray c =ᶠ[𝓝 x] fun x ↦ x ^ d ^ n :=
      (continuousAt_const.prodMk continuousAt_id).eventually (s.ray_eqn_iter' post)
    rw [e.mfderiv_eq]; contrapose x0
    rw [mfderiv_eq_fderiv] at x0
    have d := (differentiableAt_pow (x := x) (d ^ n)).hasFDerivAt.hasDerivAt.deriv
    replace x0 := ContinuousLinearMap.ext_iff.mp x0 1
    rw [x0] at d
    have z1 : (0 : ℂ →L[ℂ] ℂ) 1 = (0 : ℂ) := rfl
    replace d := d.trans z1
    simp only [differentiableAt_fun_id, deriv_fun_pow, Nat.cast_pow, deriv_id'', mul_one,
      mul_eq_zero, pow_eq_zero_iff', Nat.cast_eq_zero, s.d0, ne_eq, false_and, false_or] at d
    exact d.1
  have d := mfderiv_comp x
      ((s.bottcherNearIter_mAnalytic (s.ray_near post)).along_snd.mdifferentiableAt (by decide))
      ((s.ray_mAnalytic post).along_snd.mdifferentiableAt (by decide))
  simp only [Function.comp_def, n] at d h
  simp only [d, Ne, mderiv_comp_eq_zero_iff, not_or] at h
  exact h.2

/-- `s.ray` is nontrivial, since it is noncritical at 0 and `s.ext` is connected -/
theorem Super.ray_nontrivial (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    NontrivialMAnalyticAt (s.ray c) x :=
  (nontrivialMAnalyticAt_of_mfderiv_ne_zero (s.ray_mAnalytic (s.mem_ext c)).along_snd
        (s.ray_noncritical_zero c)).on_preconnected
    (s.ray_mAnalytic_slice c).contMDiffOn (s.mem_ext c) (s.isOpen_ext.snd_preimage c)
    (s.ext_slice_connected c).isPreconnected _ post

/-- `s.ray c` is injective, or alternately `(c,x) ↦ (c, s.ray c x)` is injective on `s.ext`.

    We prove this by continuous induction on potential:
    1. `s.ray c` is injective for small potentials, since it is noncritical at (c,0)`
    2. If `s.ray c x0 = s.ray c x1`, we can use the fact that `s.ray` is a local inverse
       to `s.bottcherNear` to find a slightly smaller `t < 1` where
       `s.ray c (t*x0) = s.ray c (t*x1)`
    3. (1) + (2) is a contradiction, since we can walk all the down to `t ≈ 0`. -/
theorem Super.ray_inj (s : Super f d a) [OnePreimage s] {x0 x1 : ℂ} :
    (c, x0) ∈ s.ext → (c, x1) ∈ s.ext → s.ray c x0 = s.ray c x1 → x0 = x1 := by
  -- Preliminaries
  intro p0 p1 e
  have ax : ‖x0‖ = ‖x1‖ := by simp only [← s.ray_potential p0, ← s.ray_potential p1, e]
  by_cases x00 : x0 = 0
  · simp only [x00, norm_zero] at ax ⊢; exact (norm_eq_zero.mp ax.symm).symm
  have tc : ∀ (x : ℂ) (t), ContinuousAt (fun t : ℝ ↦ ↑t * x) t := fun x t ↦
    Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  have pt : ∀ {x : ℂ} {t : ℝ}, (c, x) ∈ s.ext → t ∈ Ioc (0 : ℝ) 1 → (c, ↑t * x) ∈ s.ext := by
    intro x t p m
    simp only [Super.ext, mem_ofPred, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos m.1] at p ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) m.2) p
  -- It suffices to show that the set of t's where the x0 and x1 rays match
  -- is relatively clopen in Ioc 0 1
  set u : Set ℝ := {t : ℝ | s.ray c (t * x0) = s.ray c (t * x1)}
  suffices h : Ioc (0 : ℝ) 1 ⊆ interior u by
    replace h := _root_.trans h interior_subset
    replace tc := (tc x0 0).prodMk (tc x1 0)
    simp only [ContinuousAt, Complex.ofReal_zero, MulZeroClass.zero_mul] at tc
    have inj := tc.eventually ((s.ray_mAnalytic (s.mem_ext c)).along_snd.local_inj
      (s.ray_noncritical_zero c))
    rcases Metric.eventually_nhds_iff.mp inj with ⟨r, rp, inj⟩
    simp only [Real.dist_eq, sub_zero] at inj
    set t := min 1 (r / 2)
    have t0 : 0 < t := lt_min zero_lt_one (half_pos rp)
    have t01 : t ∈ Ioc (0 : ℝ) 1 := mem_Ioc.mpr ⟨t0, min_le_left _ _⟩
    specialize @inj t (by simp only [t, abs_of_pos t0, min_lt_of_right_lt (half_lt_self rp)])
      (h t01)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr t0.ne') inj
  refine isPreconnected_Ioc.relative_clopen ?_ ?_ ?_
  · use 1, right_mem_Ioc.mpr zero_lt_one
    simp only [mem_ofPred, Complex.ofReal_one, one_mul, e, u]
  · intro t ⟨m, e⟩
    simp only [mem_interior_iff_mem_nhds] at e ⊢
    generalize hn : s.np c ‖↑t * x0‖ = n
    have t0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr m.1.ne'
    have pe : ‖↑t * x0‖ = ‖↑t * x1‖ := by
      simp only [mem_ofPred_eq, u] at e
      simp only [← s.ray_potential (pt p0 m), e, ← s.ray_potential (pt p1 m)]
    have e0 := (s.ray_spec (norm_nonneg _) (pt p0 m)).eqn.filter_mono
      (nhds_le_nhdsSet mem_domain_self)
    have e1 := (s.ray_spec (norm_nonneg _) (pt p1 m)).eqn.filter_mono
      (nhds_le_nhdsSet mem_domain_self)
    simp only [← pe, hn] at e0 e1
    have de : (↑t * x0) ^ d ^ n = (↑t * x1) ^ d ^ n := by
      have e0 := e0.self_of_nhds.eqn
      have e1 := e1.self_of_nhds.eqn
      simp only [mem_ofPred_eq, u] at e
      simp only [← e] at e0 e1
      exact e0.symm.trans e1
    simp only [mul_pow] at de
    replace de := mul_left_cancel₀ (pow_ne_zero _ t0) de
    generalize hr : (fun e x ↦ s.ray e (x1 / x0 * x)) = r
    have xe : x1 / x0 * (↑t * x0) = ↑t * x1 := by
      rw [← mul_assoc, mul_comm _ (t:ℂ), mul_assoc, div_mul_cancel₀ _ x00]
    have er : ∀ᶠ y in 𝓝 (c, ↑t * x0), Eqn s n r y := by
      rw [← hr]; apply eqn_near
      exact (s.ray_mAnalytic (pt p1 m)).comp₂_of_eq contMDiffAt_fst
          (contMDiffAt_const.mul contMDiffAt_snd) (by simp [xe])
      rw [xe]; exact e1.self_of_nhds.near
      have xc : ContinuousAt (fun y : ℂ × ℂ ↦ (y.1, x1 / x0 * y.2)) (c, ↑t * x0) :=
        continuousAt_fst.prodMk (continuousAt_const.mul continuousAt_snd)
      simp only [ContinuousAt] at xc
      rw [← mul_assoc, mul_comm _ (t:ℂ), mul_assoc, div_mul_cancel₀ _ x00] at xc
      refine (xc.eventually e1).mp (.of_forall ?_); intro ⟨e, x⟩ e1
      exact _root_.trans e1.eqn (by
        simp only [mul_pow, div_pow, ← de, div_self (pow_ne_zero _ x00), one_mul])
    refine ((continuousAt_const.prodMk (Complex.continuous_ofReal.continuousAt.mul
        continuousAt_const)).eventually
        (eqn_unique e0 er ?_ (mul_ne_zero t0 x00))).mp (.of_forall fun u e ↦ ?_)
    · simp only [← hr]; simp only [Pi.mul_apply]; rw [xe]; exact e
    · rw [← hr] at e; simp only [uncurry] at e
      simp only [Pi.mul_apply] at e ⊢
      rw [← mul_assoc, mul_comm _ (u:ℂ), mul_assoc, div_mul_cancel₀ _ x00] at e
      exact e
  · intro t ⟨m, e⟩; simp only [mem_closure_iff_frequently] at e ⊢
    have rc : ∀ {x : ℂ}, (c, x) ∈ s.ext → ContinuousAt (fun t : ℝ ↦ s.ray c (↑t * x)) t :=
      fun {x} p ↦
      (s.ray_mAnalytic (pt p m)).along_snd.continuousAt.comp_of_eq
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const) rfl
    exact tendsto_nhds_unique_of_frequently_eq (rc p0) (rc p1) e

/-- Special case of injectivity: `s.ray c x = a` iff `x = 0` -/
@[simp] lemma Super.ray_eq_a_iff (s : Super f d a) [OnePreimage s] {x : ℂ}
    (m : (c, x) ∈ s.ext) : s.ray c x = a ↔ x = 0 := by
  constructor
  · intro e
    nth_rw 2 [← s.ray_zero (c := c)] at e
    exact s.ray_inj m (s.mem_ext c) e
  · intro e
    simp only [e, s.ray_zero]

/-- `s.ray` surjects from `s.ext` to `s.post`

    We prove this by continuous induction on potential, but phrased in terms of explicit sets.
    Fixing `c`, we have
    1. The image of `s.ray c` is open (by the Open Mapping Theorem)
    2. The image of `s.ray c` restricted to `s.potential c z ≤ p` is closed.
    3. By picking `p` greater than any particular postcritical potential, we cover `s.post`. -/
theorem Super.ray_surj (s : Super f d a) [OnePreimage s] :
    ∀ {z}, (c, z) ∈ s.post → ∃ x, (c, x) ∈ s.ext ∧ s.ray c x = z := by
  intro z0 m0
  by_contra i0; simp only [not_exists, not_and] at i0
  set p0 := s.potential c z0
  simp only [Super.post, mem_ofPred, Postcritical] at m0
  rcases exists_between m0 with ⟨p1, p01, post⟩
  set i := s.ray c '' {x | (c, x) ∈ s.ext}
  set j := {z | s.potential c z ≤ p1} ∩ i
  set u := {z | s.potential c z ≤ p1} \ i
  have pc : Continuous (s.potential c) := (Continuous.potential s).along_snd
  have io : IsOpen i := by
    rw [isOpen_iff_eventually]; intro z ⟨x, m, xz⟩
    have eq := (s.ray_nontrivial m).nhds_eq_map_nhds; rw [xz] at eq
    rw [eq, Filter.eventually_map]
    exact ((s.isOpen_ext.snd_preimage c).eventually_mem m).mp
      (.of_forall fun x m ↦ ⟨x, m, rfl⟩)
  have jc : IsClosed j := by
    have e : j = s.ray c '' closedBall 0 p1 := by
      refine Set.ext fun z ↦ ?_
      simp only [mem_inter_iff, mem_ofPred, mem_image, mem_closedBall, Complex.dist_eq, sub_zero, j]
      constructor
      · intro ⟨zp1, x, xp, xz⟩; rw [← xz, s.ray_potential xp] at zp1; use x, zp1, xz
      · intro ⟨x, xp, xz⟩; have zp1 := lt_of_le_of_lt xp post; rw [← xz, s.ray_potential zp1]
        use xp, x, zp1
    rw [e]; refine (IsCompact.image_of_continuousOn (isCompact_closedBall _ _) ?_).isClosed
    intro x m; simp only [mem_closedBall, Complex.dist_eq, sub_zero] at m
    exact (s.ray_mAnalytic (lt_of_le_of_lt m post)).along_snd.continuousAt.continuousWithinAt
  have uc : IsCompact u := ((isClosed_le pc continuous_const).sdiff io).isCompact
  have z0u : z0 ∈ u := by
    simp only [mem_sdiff, mem_ofPred, u]; use p01.le; contrapose i0
    simp only [not_not, not_forall, exists_prop] at i0 ⊢; exact i0
  have ne : u.Nonempty := ⟨z0, z0u⟩
  rcases uc.exists_isMinOn ne pc.continuousOn with ⟨z, zu, zm⟩
  simp only [mem_sdiff, mem_ofPred, u] at zu
  replace zm : ∀ᶠ w in 𝓝 z, s.potential c z ≤ s.potential c w := by
    have m : z ∈ jᶜ := by rw [compl_inter]; right; exact zu.2
    have lt : s.potential c z < p1 := lt_of_le_of_lt (zm z0u) p01
    apply (jc.isOpen_compl.eventually_mem m).mp
    apply ((Continuous.potential s).along_snd.continuousAt.eventually_lt continuousAt_const lt).mp
    refine .of_forall fun w lt m ↦ ?_
    rw [compl_inter] at m; cases' m with m m
    · simp only [compl_ofPred, mem_ofPred, not_le] at m; linarith
    · apply zm; simp only [mem_sdiff, mem_ofPred, u]; use lt.le, m
  simp only [mem_ofPred, mem_image, not_exists, not_and, i] at zu
  have za := s.potential_minima_only_a (lt_of_le_of_lt zu.1 post) zm
  have h := zu.2 0 (s.mem_ext c); simp only [s.ray_zero] at h; exact h za.symm

/-- `s.ray` is bijective from `s.ext` to `s.post`, accounting for `c` -/
theorem Super.ray_bij (s : Super f d a) [OnePreimage s] :
    BijOn (fun y : ℂ × ℂ ↦ (y.1, s.ray y.1 y.2)) s.ext s.post := by
  refine ⟨fun _ m ↦ s.ray_post m, ?_, ?_⟩
  · intro ⟨c0, x0⟩ m0 ⟨c1, x1⟩ m1 e; simp only [Prod.ext_iff] at e ⊢; rcases e with ⟨ec, ex⟩
    rw [ec] at m0 ex; use ec, s.ray_inj m0 m1 ex
  · intro ⟨c, x⟩ m; simp only [mem_image, Prod.ext_iff]
    rcases s.ray_surj m with ⟨x, m, e⟩; use⟨c, x⟩, m, rfl, e

end
end Ray_Ray_Dynamics_Ray

-- ===== Ray.Dynamics.Multiple =====
section Ray_Ray_Dynamics_Multiple
/-!
## Non-injectivity near multiple roots

Let `f : S → T` be an analytic function between 1D complex manifolds.  We show that if
`f` has zero derivative at a point, it is not locally injective near that point.  Indeed,
we show that there is a nontrivial local nonlinear rotation `g : S → S` around the point
that locally commutes with `f`: `f (g z) = f z` and `g z ≠ z` except at the point.

This is a bit of a sledgehammer, as (1) the rotation `g` is defined using Böttcher coordinates
and so far we use only (2) the fact that injectivity implies nonzero derivative.  There are
surely simpler proofs of (2), but it's nice to have the rotation fact, and we already have
Böttcher coordinates.

The proof proceeds in w.l.o.g. stages, reducing first from manifolds to `ℂ → ℂ`, then moving
the point to `0` and standardizing the leading coefficient to be 1.
-/

open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped ContDiff NNReal Topology Real
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold I ω T]

/-- There are nontrivial `d`th roots of unity if `2 ≤ d` -/
theorem exist_root_of_unity {d : ℕ} (d2 : 2 ≤ d) : ∃ a : ℂ, a ≠ 1 ∧ a ^ d = 1 := by
  set n : ℕ+ := ⟨d, lt_of_lt_of_le (by norm_num) d2⟩
  have two : Nontrivial (rootsOfUnity n ℂ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, Complex.card_rootsOfUnity]
    simp only [PNat.mk_coe, n]; exact lt_of_lt_of_le (by norm_num) d2
  rcases two with ⟨⟨a, am⟩, ⟨b, bm⟩, ab⟩
  simp only [Ne, Subtype.mk_eq_mk, mem_rootsOfUnity] at am bm ab
  by_cases a1 : a = 1
  · use b; rw [a1] at ab; constructor
    · simp only [ne_eq, Units.val_eq_one, Ne.symm ab, not_false_eq_true]
    · simp only [PNat.mk_coe, n] at bm; rw [← Units.val_pow_eq_pow_val, bm, Units.val_one]
  · use a; constructor
    · simp only [ne_eq, Units.val_eq_one, a1, not_false_eq_true]
    · simp only [PNat.mk_coe, n] at am; rw [← Units.val_pow_eq_pow_val, am, Units.val_one]

/-- Case `c = 0, f 0 = 0`, when `f` has a monic, superattracting fixpoint at 0.  Every
    nearby point is achieved at least twice.  We operationalize this statement via a
    nontrivial function `g : ℂ → ℂ` s.t. `f (g z) = f z`. -/
theorem SuperAt.not_local_inj {f : ℂ → ℂ} {d : ℕ} (s : SuperAt f d) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ ∀ᶠ z in 𝓝[{0}ᶜ] 0, g z ≠ z ∧ f (g z) = f z := by
  rcases s.superNear with ⟨t, s⟩
  have ba : AnalyticAt ℂ (bottcherNear f d) 0 := bottcherNear_analytic_z s _ s.t0
  have nc : mfderiv I I (bottcherNear f d) 0 ≠ 0 := by
    rw [mfderiv_eq_fderiv, ← toSpanSingleton_deriv, (bottcherNear_monic s).deriv]
    exact ContinuousLinearMap.smulRight_ne_zero ContinuousLinearMap.one_ne_zero (by norm_num)
  rcases complex_inverse_fun' (ba.mAnalyticAt I I) nc with ⟨i, ia, ib, bi⟩
  rw [bottcherNear_zero] at bi ia
  have i0 : i 0 = 0 := by nth_rw 1 [← bottcherNear_zero]; rw [ib.self_of_nhds]
  have inj : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), i p.1 = i p.2 → p.1 = p.2 := by
    refine ia.local_inj ?_
    have d0 : mfderiv I I (fun z : ℂ ↦ z) 0 ≠ 0 := id_mderiv_ne_zero
    rw [(Filter.EventuallyEq.symm ib).mfderiv_eq] at d0
    rw [←Function.comp_def, mfderiv_comp 0 _ ba.differentiableAt.mdifferentiableAt] at d0
    rw [bottcherNear_zero] at d0
    exact fun h ↦ d0 (ContinuousLinearMap.ext fun v ↦ by rw [h]; rfl)
    rw [bottcherNear_zero]; exact ia.mdifferentiableAt (by decide)
  rcases exist_root_of_unity s.d2 with ⟨a, a1, ad⟩
  refine ⟨fun z ↦ i (a * bottcherNear f d z), ?_, ?_, ?_⟩
  · apply ContMDiffAt.analyticAt I I
    refine ia.comp_of_eq (contMDiffAt_const.mul (ba.mAnalyticAt I I)) ?_
    simp only [bottcherNear_zero, MulZeroClass.mul_zero]
  · simp only [bottcherNear_zero, MulZeroClass.mul_zero, i0]
  · simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff]
    have t0 : ContinuousAt (fun z ↦ a * bottcherNear f d z) 0 :=
      continuousAt_const.mul ba.continuousAt
    have t1 : ContinuousAt (fun z ↦ f (i (a * bottcherNear f d z))) 0 := by
      refine s.fa0.continuousAt.comp_of_eq (ia.continuousAt.comp_of_eq t0 ?_) ?_
      repeat' simp only [bottcherNear_zero, MulZeroClass.mul_zero, i0]
    have t2 : ContinuousAt f 0 := s.fa0.continuousAt
    have m0 : ∀ᶠ z in 𝓝 0, i (a * bottcherNear f d z) ∈ t := by
      refine (ia.continuousAt.comp_of_eq t0 ?_).eventually_mem (s.o.mem_nhds ?_)
      repeat' simp only [bottcherNear_zero, MulZeroClass.mul_zero, i0, s.t0, Function.comp_def]
    have m1 : ∀ᶠ z in 𝓝 0, z ∈ t := s.o.eventually_mem s.t0
    simp only [ContinuousAt, bottcherNear_zero, MulZeroClass.mul_zero, i0, s.f0] at t0 t1 t2
    have tp := t0.prodMk ba.continuousAt
    simp only [← nhds_prod_eq, bottcherNear_zero] at tp
    apply (tp.eventually inj).mp
    refine ib.mp (bi.mp ((t1.eventually ib).mp
      ((t0.eventually bi).mp ((t2.eventually ib).mp (m0.mp (m1.mp ?_))))))
    refine .of_forall fun z m1 m0 t2 t0 t1 _ ib tp z0 ↦ ⟨?_, ?_⟩
    · contrapose tp; simp only [Classical.not_imp] at tp ⊢
      rw [ib]; use tp
      contrapose a1
      have b0 := bottcherNear_ne_zero s m1 z0
      calc a
        _ = a * bottcherNear f d z / bottcherNear f d z := by field_simp [b0]
        _ = bottcherNear f d z / bottcherNear f d z := by rw [a1]
        _ = 1 := div_self b0
    · rw [← t1, bottcherNear_eqn s m0, t0, mul_pow, ad, one_mul, ← bottcherNear_eqn s m1, t2]

/-- Case `c = 0, f 0 = 0, f' 0 = 0`.  Every nearby point is achieved at least twice.  We
    operationalize this statement via a nontrivial function `g : ℂ → ℂ` s.t. `f (g z) = f z`. -/
theorem not_local_inj_of_deriv_zero' {f : ℂ → ℂ} (fa : AnalyticAt ℂ f 0) (df : HasDerivAt f 0 0)
    (f0 : f 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ ∀ᶠ z in 𝓝[{0}ᶜ] 0, g z ≠ z ∧ f (g z) = f z := by
  by_cases o0 : orderAt f 0 = 0
  · simp only [orderAt_eq_zero_iff fa, f0, Ne, not_true, or_false] at o0
    use fun z ↦ -z, analyticAt_id.neg, neg_zero; rw [eventually_nhdsWithin_iff]
    have e0 : ∀ᶠ z in 𝓝 0, f (-z) = 0 := by
      nth_rw 1 [← neg_zero] at o0; exact continuousAt_neg.eventually o0
    refine o0.mp (e0.mp (.of_forall fun z f0' f0 z0 ↦ ?_))
    simp only [mem_compl_singleton_iff] at z0; rw [Pi.zero_apply] at f0
    rwa [f0, f0', eq_self_iff_true, and_true, neg_ne_self]
  have o1 : orderAt f 0 ≠ 1 := by
    have d := df.deriv; contrapose d
    exact deriv_ne_zero_of_orderAt_eq_one d
  have d2 : 2 ≤ orderAt f 0 := by rw [Nat.two_le_iff]; use o0, o1
  clear o1 df f0
  set a := leadingCoeff f 0
  have a0 : a ≠ 0 := leadingCoeff_ne_zero fa o0
  set g := fun z ↦ a⁻¹ • f z
  have s : SuperAt g (orderAt f 0) :=
    { d2
      fa0 := analyticAt_const.mul fa
      fd := by rw [orderAt_const_smul (inv_ne_zero a0)]
      fc := by rw [leadingCoeff_const_smul]; simp only [smul_eq_mul, inv_mul_cancel₀ a0, a] }
  rcases s.not_local_inj with ⟨h, ha, h0, e⟩
  use h, ha, h0; refine e.mp (.of_forall ?_)
  intro z ⟨h0, hz⟩; use h0
  exact (IsUnit.smul_left_cancel (Ne.isUnit (inv_ne_zero a0))).mp hz

/-- If `f' z = 0`, then every value near `f z` is achieved at least twice (`ℂ → ℂ` version).
    We operationalize this statement via a nontrivial function `g : ℂ → ℂ` s.t. `f (g w) = f w`
    near `z`. -/
theorem not_local_inj_of_deriv_zero {f : ℂ → ℂ} {c : ℂ} (fa : AnalyticAt ℂ f c)
    (df : HasDerivAt f 0 c) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧ g c = c ∧ ∀ᶠ z in 𝓝[{c}ᶜ] c, g z ≠ z ∧ f (g z) = f z := by
  set f' := fun z ↦ f (z + c) - f c
  have fa' : AnalyticAt ℂ f' 0 :=
    AnalyticAt.sub
      (AnalyticAt.comp (by simp only [zero_add, fa]) (analyticAt_id.add analyticAt_const))
      analyticAt_const
  have df' : HasDerivAt f' (0 * 1) 0 := by
    refine HasDerivAt.sub_const _ ?_
    have e : (fun z ↦ f (z + c)) = f ∘ fun z ↦ z + c := rfl
    rw [e]; apply HasDerivAt.comp; simp only [zero_add, df]
    exact HasDerivAt.add_const _ (hasDerivAt_id _)
  simp only [MulZeroClass.zero_mul] at df'
  have f0' : (fun z ↦ f (z + c) - f c) 0 = 0 := by simp only [zero_add, sub_self]
  rcases not_local_inj_of_deriv_zero' fa' df' f0' with ⟨g, ga, e, h⟩; clear fa df fa' df'
  refine ⟨fun z ↦ g (z - c) + c, ?_, ?_, ?_⟩
  · exact AnalyticAt.add (AnalyticAt.comp (by simp only [sub_self, ga])
      (analyticAt_id.sub analyticAt_const)) analyticAt_const
  · simp only [sub_self, e, zero_add]
  · simp only [eventually_nhdsWithin_iff] at h ⊢
    have sc : Tendsto (fun z ↦ z - c) (𝓝 c) (𝓝 0) := by
      rw [← sub_self c]; exact continuousAt_id.sub continuousAt_const
    refine (sc.eventually h).mp (.of_forall ?_)
    simp only [mem_compl_singleton_iff, sub_ne_zero]
    intro z h zc; rcases h zc with ⟨gz, ff⟩; constructor
    contrapose gz; nth_rw 2 [← gz]; ring
    simp only [sub_left_inj, sub_add_cancel, f'] at ff; exact ff

/-- If `f' z = 0`, then every value near `f z` is achieved at least twice (manifold version).
    We operationalize this statement via a nontrivial function `g : S → T` s.t. `f (g w) = f w`
    near `z`. -/
theorem not_local_inj_of_mfderiv_zero {f : S → T} {c : S} (fa : ContMDiffAt I I ω f c)
    (df : mfderiv I I f c = 0) :
    ∃ g : S → S, ContMDiffAt I I ω g c ∧ g c = c ∧ ∀ᶠ z in 𝓝[{c}ᶜ] c, g z ≠ z ∧ f (g z) = f z := by
  generalize hg : (fun z ↦ extChartAt I (f c) (f ((extChartAt I c).symm z))) = g
  have dg : mfderiv I I g (extChartAt I c c) = 0 := by
    have fd : MDifferentiableAt I I f ((extChartAt I c).symm (extChartAt I c c)) := by
      rw [PartialEquiv.left_inv]
      exact fa.mdifferentiableAt (by decide)
      apply mem_extChartAt_source
    rw [← hg, ←Function.comp_def, ← Function.comp_def,
      mfderiv_comp _ ((contMDiffAt_extChartAt' _).mdifferentiableAt one_ne_zero) _,
      mfderiv_comp _ fd (((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' _)).mdifferentiableAt one_ne_zero),
      PartialEquiv.left_inv, df]
    · apply ContinuousLinearMap.ext
      intro v
      exact ContinuousLinearMap.map_zero _
    · apply mem_extChartAt_source
    · apply mem_extChartAt_target
    · simp
    · exact MDifferentiableAt.comp _ fd
        (((contMDiffOn_extChartAt_symm _).contMDiffAt
        (extChartAt_target_mem_nhds' (mem_extChartAt_target c))).mdifferentiableAt one_ne_zero)
  simp only [mAnalyticAt_iff_of_boundaryless, Function.comp_def, hg] at fa
  have dg' : HasFDerivAt g (0 : ℂ →L[ℂ] ℂ) (extChartAt I c c) := by
    have h := fa.2.differentiableAt.mdifferentiableAt.hasMFDerivAt
    rw [dg] at h
    exact hasMFDerivAt_iff_hasFDerivAt.mp h
  replace dg : HasDerivAt g 0 (extChartAt I c c) := dg'.hasDerivAt
  rcases not_local_inj_of_deriv_zero fa.2 dg with ⟨h, ha, h0, e⟩
  refine ⟨fun z ↦ (extChartAt I c).symm (h (extChartAt I c z)), ?_, ?_, ?_⟩
  · apply ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target c))).comp_of_eq
    apply (ha.mAnalyticAt I I).comp_of_eq
      (contMDiffAt_extChartAt' (mem_chart_source _ c)) rfl
    exact h0
  · simp only [h0, PartialEquiv.left_inv _ (mem_extChartAt_source c)]
  · rw [eventually_nhdsWithin_iff] at e ⊢
    apply ((continuousAt_extChartAt c).eventually e).mp
    apply ((isOpen_extChartAt_source c).eventually_mem (mem_extChartAt_source (I := I) c)).mp
    have m1 : ∀ᶠ z in 𝓝 c, h (extChartAt I c z) ∈ (extChartAt I c).target := by
      refine ContinuousAt.eventually_mem ?_ (extChartAt_target_mem_nhds' ?_)
      · exact ha.continuousAt.comp_of_eq (continuousAt_extChartAt c) rfl
      · rw [h0]; exact mem_extChartAt_target c
    have m2 : ∀ᶠ z in 𝓝 c, f z ∈ (extChartAt I (f c)).source :=
      fa.1.eventually_mem (extChartAt_source_mem_nhds _)
    have m3 : ∀ᶠ z in 𝓝 c,
        f ((extChartAt I c).symm (h (extChartAt I c z))) ∈ (extChartAt I (f c)).source := by
      refine ContinuousAt.eventually_mem ?_ (extChartAt_source_mem_nhds' ?_)
      · apply fa.1.comp_of_eq; apply (continuousAt_extChartAt_symm _).comp_of_eq
        apply ha.continuousAt.comp_of_eq; exact continuousAt_extChartAt _
        rfl; exact h0; rw [h0, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
      · rw [h0, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
        apply mem_extChartAt_source
    refine m1.mp (m2.mp (m3.mp (.of_forall ?_)))
    simp only [mem_compl_singleton_iff]
    intro z m3 m2 m1 m0 even zc
    rcases even ((PartialEquiv.injOn _).ne m0 (mem_extChartAt_source c) zc) with ⟨hz, gh⟩
    constructor
    · nth_rw 2 [← PartialEquiv.left_inv _ m0]
      rw [(PartialEquiv.injOn _).ne_iff]; exact hz
      rw [PartialEquiv.symm_source]; exact m1
      rw [PartialEquiv.symm_source]; exact PartialEquiv.map_source _ m0
    · simp only [← hg] at gh
      rw [PartialEquiv.left_inv _ m0] at gh
      rw [(PartialEquiv.injOn _).eq_iff m3 m2] at gh; exact gh

/-- Injectivity on an open set implies nonzero derivative (flat version) -/
theorem Set.InjOn.deriv_ne_zero {f : ℂ → ℂ} {s : Set ℂ} (inj : InjOn f s) (so : IsOpen s)
    {c : ℂ} (m : c ∈ s) (fa : AnalyticAt ℂ f c) : deriv f c ≠ 0 := by
  contrapose inj
  simp only [InjOn, not_forall] at inj ⊢
  have d := inj ▸ fa.differentiableAt.hasDerivAt
  rcases not_local_inj_of_deriv_zero fa d with ⟨g, ga, gc, fg⟩
  have gm : ∀ᶠ z in 𝓝 c, g z ∈ s :=
    ga.continuousAt.eventually_mem (so.mem_nhds (by simp only [gc, m]))
  replace fg := fg.and (((so.eventually_mem m).and gm).filter_mono nhdsWithin_le_nhds)
  rcases @Filter.Eventually.exists _ _ _ (AnalyticManifold.punctured_nhds_neBot I c) fg
    with ⟨z, ⟨gz, fg⟩, zs, gs⟩
  use g z, gs, z, zs, fg, gz

/-- Injectivity on an open set implies nonzero derivative (manifold version) -/
theorem Set.InjOn.mfderiv_ne_zero {f : S → T} {s : Set S} (inj : InjOn f s) (so : IsOpen s)
    {c : S} (m : c ∈ s) (fa : ContMDiffAt I I ω f c) : mfderiv I I f c ≠ 0 := by
  contrapose inj
  simp only [InjOn, not_forall] at inj ⊢
  rcases not_local_inj_of_mfderiv_zero fa inj with ⟨g, ga, gc, fg⟩
  have gm : ∀ᶠ z in 𝓝 c, g z ∈ s :=
    ga.continuousAt.eventually_mem (so.mem_nhds (by simp only [gc, m]))
  replace fg := fg.and (((so.eventually_mem m).and gm).filter_mono nhdsWithin_le_nhds)
  rcases @Filter.Eventually.exists _ _ _ (AnalyticManifold.punctured_nhds_neBot I c) fg
    with ⟨z, ⟨gz, fg⟩, zs, gs⟩
  use g z, gs, z, zs, fg, gz

end
end Ray_Ray_Dynamics_Multiple

-- ===== Ray.Manifold.GlobalInverse =====
section Ray_Ray_Manifold_GlobalInverse
/-!
## Global inverse functions theorems on 1D complex manifolds

Given a parameterized analytic function `f : ℂ → S → T` where `(c,z) ↦ (c, f c z)` is
injective, there exists a global inverse `g : ℂ → T → S` to `f` with `g c (f c z) = z`.

We prove several versions of this result, with different hypotheses:
1. `global_complex_inverse_fun_open`: `f : ℂ → S → T` is nonsingular and injective on an open set
2. `global_complex_inverse_fun_compact`: `f : S → T` is nonsingular and injective on a compact set
3. `global_complex_inverse_fun_open': `f` is injective on an open set

These results follow straightforwardly by stitching together local inverses, except that
(3) needs the result from `AnalyticManifold.Multiple` that injectivity implies nonzero derivative.
-/

open Classical
open Filter (Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [cms : IsManifold I ω S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [cmt : IsManifold I ω T]

/-- The global 1D inverse function theorem (parameterized, open case): if `f : ℂ → S → T`
    is nonsingular and injective on an open set `s`, it has a global analytic inverse. -/
theorem global_complex_inverse_fun_open {f : ℂ → S → T} [Nonempty S] {s : Set (ℂ × S)}
    (fa : ContMDiffOn II I ω (uncurry f) s) (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) s) (so : IsOpen s) :
    ∃ g : ℂ → T → S,
      ContMDiffOnNhd II I (uncurry g) ((fun p : ℂ × S ↦ (p.1, f p.1 p.2)) '' s) ∧
        ∀ p : ℂ × S, p ∈ s → g p.1 (f p.1 p.2) = p.2 := by
  --obtain blah := complex_inverse_fun
  have i : ∀ p : ℂ × S, p ∈ s → ComplexInverseFun.Cinv f p.1 p.2 := by
    intro ⟨c, z⟩ m; exact
      { fa := fa.contMDiffAt (so.mem_nhds m)
        nc := nc _ m }
  generalize hg : (fun c w ↦
    if h : ∃ z, (c, z) ∈ s ∧ f c z = w then choose h else Classical.arbitrary S) = g
  have left : ∀ c z, (c, z) ∈ s → g c (f c z) = z := by
    intro c z m
    have h : ∃ x, (c, x) ∈ s ∧ f c x = f c z := ⟨z, m, rfl⟩
    simp only [← hg, dif_pos h]
    rcases choose_spec h with ⟨m0, w0⟩
    have left := (i _ m).left_inv.self_of_nhds
    simp only at left
    have e : (c, choose h) = (c, (i _ m).g c (f c z)) := by
      refine (inj.eq_iff m0 ?_).mp ?_
      · simp only [left, m]
      · simp only [left, w0]
    rw [left] at e; exact (Prod.ext_iff.mp e).2
  have ge : ∀ (p : ℂ × S) (m : p ∈ s), ∀ᶠ q : ℂ × T in 𝓝 (p.1, f p.1 p.2),
      g q.1 q.2 = (i p m).g q.1 q.2 := by
    intro ⟨c, z⟩ m
    have n := nontrivialMAnalyticAt_of_mfderiv_ne_zero
      (fa.contMDiffAt (so.mem_nhds m)).along_snd (nc _ m)
    simp only [n.nhds_eq_map_nhds_param (fa.contMDiffAt (so.mem_nhds m)), Filter.eventually_map]
    apply (i _ m).left_inv.mp; apply (so.eventually_mem m).mp
    refine .of_forall fun ⟨e, w⟩ wm gf ↦ ?_
    simp only at gf
    simp only [left _ _ wm, gf]
  use g; constructor
  · intro ⟨c, w⟩ wm
    rcases(mem_image _ _ _).mp wm with ⟨⟨c', z⟩, zm, e⟩
    simp only [Prod.ext_iff] at e; simp only [e.1] at e zm; simp only [← e.2]
    exact ((i _ zm).ga.congr_of_eventuallyEq (ge _ zm)).contMDiffWithinAt
  · intro ⟨c, z⟩ m; exact left _ _ m

/-- The global 1D inverse function theorem (compact case): if `f : S → T` is nonsingular and
    injective on a compact set `s`, it has a global analytic inverse. -/
theorem global_complex_inverse_fun_compact {f : ℂ → S → T} [Nonempty S] [T2Space T]
    {s : Set (ℂ × S)} (fa : ContMDiffOnNhd II I (uncurry f) s)
    (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) s) (sc : IsCompact s) :
    ∃ g : ℂ → T → S,
      ContMDiffOnNhd II I (uncurry g) ((fun p : ℂ × S ↦ (p.1, f p.1 p.2)) '' s) ∧
        ∀ᶠ p : ℂ × S in 𝓝ˢ s, g p.1 (f p.1 p.2) = p.2 := by
  -- Enlarge s while preserving injectivity
  have t : ∃ t, IsOpen t ∧ s ⊆ t ∧ InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) t := by
    apply inj.exists_isOpen_superset sc (fun _ m ↦ continuousAt_fst.prodMk (fa _ m).continuousAt)
    intro ⟨c, z⟩ m; rcases complex_inverse_fun (fa _ m) (nc _ m) with ⟨g, _, gf, _⟩
    rcases eventually_nhds_iff.mp gf with ⟨t, gf, o, m⟩
    use t, o.mem_nhds m; intro ⟨c0, z0⟩ m0 ⟨c1, z1⟩ m1 e
    simp only [Prod.ext_iff] at e ⊢; use e.1
    have e0 := gf _ m0; have e1 := gf _ m1; simp only at e0 e1
    rw [← e0, ← e1, e.2, ← e.1]
  rcases t with ⟨t, ot, st, ti⟩
  -- Shrink t to recover openness and deriv ≠ 0
  set u := t ∩ {p | ContMDiffAt II I ω (uncurry f) p ∧ mfderiv I I (f p.1) p.2 ≠ 0}
  have tu : u ⊆ t := inter_subset_left
  have su : s ⊆ u := subset_inter st (subset_inter fa nc)
  have uo : IsOpen u := by
    apply ot.inter; rw [isOpen_iff_eventually]; intro ⟨c, z⟩ ⟨fa, nc⟩
    refine fa.eventually.mp ((mfderiv_ne_zero_eventually' fa nc).mp (.of_forall ?_))
    intro ⟨c, z⟩ nc fa; use fa, nc
  -- Find our inverse on u
  have fa' : ∀ x ∈ u, ContMDiffAt II I ω (uncurry f) x := fun _ m ↦ (inter_subset_right m).1
  have d0 : ∀ (p : ℂ × S), p ∈ u → mfderiv I I (f p.fst) p.snd ≠ 0 :=
    fun _ m ↦ (inter_subset_right m).2
  rcases global_complex_inverse_fun_open
    (fun x m ↦ (fa' x m).contMDiffWithinAt) d0 (ti.mono tu) uo with ⟨g, ga, gf⟩
  exact ⟨g, ga.mono (image_mono su), Filter.eventually_of_mem (uo.mem_nhdsSet.mpr su) gf⟩

/-- The global 1D inverse function theorem (weak, open case): if `f : S → T` is nonsingular
    and injective on an open set `s`, it has a global analytic inverse (we remove the need
    for nonsingularity below, by deriving it from injectivity). -/
theorem weak_global_complex_inverse_fun_open {f : S → T} [Nonempty S] {s : Set S}
    (fa : ContMDiffOn I I ω f s) (nc : ∀ z, z ∈ s → mfderiv I I f z ≠ 0) (inj : InjOn f s)
    (so : IsOpen s) : ∃ g : T → S, ContMDiffOnNhd I I g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z := by
  set f' := fun (_ : ℂ) (z : S) ↦ f z
  have nc' : ∀ p : ℂ × S, p ∈ (univ : Set ℂ) ×ˢ s → mfderiv I I (f' p.1) p.2 ≠ 0 := by
    intro ⟨c, z⟩ ⟨_, zs⟩; exact nc _ zs
  have inj' : InjOn (fun p : ℂ × S ↦ (p.1, f' p.1 p.2)) (univ ×ˢ s) := by
    intro ⟨c0, z0⟩ ⟨_, zs0⟩ ⟨c1, z1⟩ ⟨_, zs1⟩ h; simp only [Prod.ext_iff] at h zs0 zs1
    rw [h.1, inj zs0 zs1]; exact h.2
  have fa' : ∀ x ∈ univ ×ˢ s, ContMDiffAt II I ω (uncurry f') x := by
    intro ⟨c, z⟩ ⟨_, zs⟩
    exact (fa.contMDiffAt (so.mem_nhds zs)).comp_of_eq contMDiffAt_snd rfl
  rcases global_complex_inverse_fun_open (fun x m ↦ (fa' x m).contMDiffWithinAt)
    nc' inj' (isOpen_univ.prod so) with ⟨g, ga, gf⟩
  use g 0
  constructor
  · intro z ⟨w, m⟩
    exact (ga ⟨0, z⟩ (by aesop)).along_snd
  · intro z m; exact gf ⟨0, z⟩ ⟨mem_univ _, m⟩

/-- The global 1D inverse function theorem (open case): if `f : S → T` is injective on an
    open set `s`, it has a global analytic inverse. -/
theorem global_complex_inverse_fun_open' {f : S → T} [Nonempty S] {s : Set S}
    (fa : ContMDiffOn I I ω f s) (inj : InjOn f s) (so : IsOpen s) :
    ∃ g : T → S, ContMDiffOnNhd I I g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z :=
  weak_global_complex_inverse_fun_open fa
    (fun _ m ↦ inj.mfderiv_ne_zero so m (fa.contMDiffAt (so.mem_nhds m))) inj so

/-- The global 1D inverse function theorem (open, complex case): if `f : ℂ → ℂ` is injective on an
    open set `s`, it has a global analytic inverse. -/
theorem global_complex_inverse_fun_open'' {f : ℂ → ℂ} {s : Set ℂ}
    (fa : AnalyticOnNhd ℂ f s) (inj : InjOn f s) (so : IsOpen s) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z := by
  have ⟨g,ga,gf⟩ := global_complex_inverse_fun_open' (f := f) ?_ inj so
  · refine ⟨g, ?_, gf⟩
    intro z m
    exact (ga z m).analyticAt
  · intro z m
    specialize fa z m
    rw [analyticAt_iff_mAnalyticAt (I := I) (J := I)] at fa
    exact fa.contMDiffWithinAt

end
end Ray_Ray_Manifold_GlobalInverse

-- ===== Ray.Dynamics.Bottcher =====
section Ray_Ray_Dynamics_Bottcher
/-!
## The Böttcher map for all postcritical points

We define analytic Böttcher coordinates everywhere in `s.post` (the set of all postcritical points),
as the global inverse of the external ray map `s.ray`.  Since `Ray.lean` has already shown that
`s.ray` is bijective, it immediately has a global inverse, and the Böttcher equation follows easily:

  `s.bottcher c (f c z) = s.bottcher c z ^ d`

Combining `s.ray` and `s.bottcher`, we have an analytic bijection `s.homeomorphSlice` between
postcritical points `{z | s.potential c z < s.p c}` and the disk `ball 0 (s.p c)` (or equivalently
an all-`c` bijection `s.homeomorph` between `s.post` and `s.ext`).

To make `s.bottcher` easier to work with later, define it nonanalytically everywhere on `ℂ × S`
such that the defining equation always holds.  In particular, this means that
`s.potential c z = abs (s.bottcher c z)` unconditionally.  It is analytic only on `s.post`,
since for higher potentials we choose roots arbitrarily.
-/

open Classical
open Complex
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball mem_closedBall mem_ball_self)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [T3Space S] [ChartedSpace ℂ S]
  [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c x : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {s : Super f d a}
variable {y : ℂ × ℂ}

/-- `s.ray` has a global inverse -/
theorem Super.ray_inv (s : Super f d a) [OnePreimage s] : ∃ b : ℂ → S → ℂ,
    ContMDiffOnNhd II I (uncurry b) s.post ∧
      ∀ y : ℂ × ℂ, y ∈ s.ext → b y.1 (s.ray y.1 y.2) = y.2 := by
  rw [← s.ray_bij.image_eq]
  exact global_complex_inverse_fun_open s.ray_mAnalyticOn.contMDiffOn
      (fun _ m ↦ s.ray_noncritical m) s.ray_bij.injOn s.isOpen_ext

/-- The bottcher map throughout `s.post` -/
def Super.bottcherPost (s : Super f d a) [OnePreimage s] : ℂ → S → ℂ :=
  choose s.ray_inv

/-- The bottcher map tweaked so the defining equation holds even where it isn't continuous.

    On `s.post`, `s.bottcher` is analytic.  Otherwise, we iterate until we reach `s.post` and
    pull back the value using an arbitrary `d^n`th root (or use 1 outside `s.basin`). -/
def Super.bottcher (s : Super f d a) [OnePreimage s] : ℂ → S → ℂ := fun c z ↦
  if h : ∃ n, (c, (f c)^[n] z) ∈ s.post then
    let n := Nat.find h
    (fun w ↦ w ^ (d : ℂ)⁻¹)^[n] (s.bottcherPost c ((f c)^[n] z))
  else
    1

/-- `bottcher = bottcherPost` on `s.post` -/
theorem Super.bottcher_eq_bottcherPost (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    s.bottcher c z = s.bottcherPost c z := by
  have h : ∃ n, (c, (f c)^[n] z) ∈ s.post := ⟨0, by simpa only [Function.iterate_zero_apply]⟩
  have h0 := (Nat.find_eq_zero h).mpr m
  simp only [Super.bottcher, h, dif_pos, h0, Function.iterate_zero_apply]

/-- `bottcher = bottcherPost` on `s.post` -/
theorem Super.eqOn_bottcher_bottcherPost (s : Super f d a) [OnePreimage s] :
    EqOn (uncurry s.bottcher) (uncurry s.bottcherPost) s.post := fun _ m ↦
  s.bottcher_eq_bottcherPost m

/-- `s.bottcher` is analytic on `s.post` -/
theorem Super.bottcher_mAnalyticOn (s : Super f d a) [OnePreimage s] :
    ContMDiffOnNhd II I (uncurry s.bottcher) s.post := by
  intro ⟨c, z⟩ m; apply ((choose_spec s.ray_inv).1 _ m).congr_of_eventuallyEq
  exact (s.eqOn_bottcher_bottcherPost.symm.eventuallyEq_of_mem (s.isOpen_post.mem_nhds m)).symm

/-- `s.bottcher` is the left inverse of `s.ray` -/
theorem Super.bottcher_ray (s : Super f d a) [OnePreimage s] (m : (c, x) ∈ s.ext) :
    s.bottcher c (s.ray c x) = x := by
  rw [s.bottcher_eq_bottcherPost (s.ray_post m)]; exact (choose_spec s.ray_inv).2 _ m

/-- `s.bottcher` is the right inverse of `s.ray` -/
theorem Super.ray_bottcher (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    s.ray c (s.bottcher c z) = z := by
  rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m]

/-- `s.bottcher` maps `s.post` to `s.ext` -/
theorem Super.bottcher_ext (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    (c, s.bottcher c z) ∈ s.ext := by
  rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m]; exact m

/-- `s.bottcher` is `s.bottcherNear` near `a` -/
theorem Super.bottcher_eq_bottcherNear (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ∀ᶠ z in 𝓝 a, s.bottcher c z = s.bottcherNear c z := by
  have eq := (s.ray_nontrivial (s.mem_ext c)).nhds_eq_map_nhds; simp only [s.ray_zero] at eq
  simp only [eq, Filter.eventually_map]
  apply ((continuousAt_const.prodMk continuousAt_id).eventually (s.ray_eqn_zero c)).mp
  refine ((s.isOpen_ext.snd_preimage c).eventually_mem (s.mem_ext c)).mp
    (.of_forall fun z m e ↦ ?_)
  simp only [s.bottcher_ray m]; exact e.symm

/-- `s.ext` and `s.post` are (analytically) bijective -/
def Super.equiv (s : Super f d a) [OnePreimage s] : PartialEquiv (ℂ × ℂ) (ℂ × S) where
  toFun := fun y : ℂ × ℂ ↦ (y.1, s.ray y.1 y.2)
  invFun := fun y : ℂ × S ↦ (y.1, s.bottcher y.1 y.2)
  source := s.ext
  target := s.post
  map_source' := by intro ⟨c, x⟩ m; exact s.ray_post m
  map_target' := by intro ⟨c, z⟩ m; exact s.bottcher_ext m
  left_inv' := by intro ⟨c, x⟩ m; simp only [s.bottcher_ray m]
  right_inv' := by intro ⟨c, z⟩ m; simp only [s.ray_bottcher m]

/-- `s.ext` and `s.post` are (analytically) homeomorphic -/
def Super.homeomorph (s : Super f d a) [OnePreimage s] : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × S) where
  toPartialEquiv := s.equiv
  open_source := s.isOpen_ext
  open_target := s.isOpen_post
  continuousOn_toFun := continuousOn_fst.prodMk s.ray_mAnalyticOn.continuousOn
  continuousOn_invFun := continuousOn_fst.prodMk s.bottcher_mAnalyticOn.continuousOn

/-- `c`-slices of `s.ext` and `s.post` are (analytically) bijective -/
def Super.equivSlice (s : Super f d a) [OnePreimage s] (c : ℂ) : PartialEquiv ℂ S where
  toFun := s.ray c
  invFun := s.bottcher c
  source := {x | (c, x) ∈ s.ext}
  target := {z | (c, z) ∈ s.post}
  map_source' _ m := s.ray_post m
  map_target' _ m := s.bottcher_ext m
  left_inv' _ m := by simp only [s.bottcher_ray m]
  right_inv' _ m := by simp only [s.ray_bottcher m]

/-- `c`-slices of `s.ext` and `s.post` are (analytically) homeomorphic -/
def Super.homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    OpenPartialHomeomorph ℂ S where
  toPartialEquiv := s.equivSlice c
  open_source := s.isOpen_ext.snd_preimage c
  open_target := s.isOpen_post.snd_preimage c
  continuousOn_toFun _ m := (s.ray_mAnalytic m).along_snd.continuousAt.continuousWithinAt
  continuousOn_invFun _ m := (s.bottcher_mAnalyticOn _ m).along_snd.continuousAt.continuousWithinAt

@[simp] lemma Super.toFun_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.homeomorphSlice c = s.ray c := by rfl
@[simp] lemma Super.invFun_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (s.homeomorphSlice c).symm = s.bottcher c := by rfl
@[simp] lemma Super.source_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (s.homeomorphSlice c).source = {x | (c, x) ∈ s.ext} := by rfl
@[simp] lemma Super.target_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (s.homeomorphSlice c).target = {z | (c, z) ∈ s.post} := by rfl

/-- `s.post` is connected -/
theorem Super.post_connected (s : Super f d a) [OnePreimage s] : IsConnected s.post := by
  have e : s.post = s.homeomorph '' s.ext := s.homeomorph.image_source_eq_target.symm
  rw [e]; exact s.ext_connected.image _ s.homeomorph.continuousOn

/-- `c`-slices of `s.post` are connected -/
theorem Super.post_slice_connected (s : Super f d a) [OnePreimage s] (c : ℂ) :
    IsConnected {z | (c, z) ∈ s.post} := by
  have e : {z | (c, z) ∈ s.post} = s.homeomorphSlice c '' {x | (c, x) ∈ s.ext} :=
    (s.homeomorphSlice c).image_source_eq_target.symm
  rw [e]; exact (s.ext_slice_connected c).image _ (s.homeomorphSlice c).continuousOn

/-- Outside of the basin, `bottcher = 1` for simplicity -/
theorem Super.bottcher_not_basin (s : Super f d a) [OnePreimage s] (m : (c, z) ∉ s.basin) :
    s.bottcher c z = 1 := by
  have p : ¬∃ n, (c, (f c)^[n] z) ∈ s.post := by
    contrapose m; rcases m with ⟨n, m⟩
    rcases s.basin_iff_near.mp (s.post_basin m) with ⟨k, m⟩
    simp only [← Function.iterate_add_apply] at m
    exact s.basin_iff_near.mpr ⟨k + n, m⟩
  simp only [Super.bottcher, p]; rw [dif_neg]; exact not_false

/-- `s.bottcher` satifies the Böttcher equation everywhere

    1. It satisfies it near `a`, since it matches `s.bottcherNear` there
    2. It satisfies it throughout `s.post` since `s.post` is connected
    3. It satisfies it everywhere since we've defined it that way -/
theorem Super.bottcher_eqn (s : Super f d a) [OnePreimage s] :
    s.bottcher c (f c z) = s.bottcher c z ^ d := by
  have h0 : ∀ {c z}, (c, z) ∈ s.post → s.bottcher c (f c z) = s.bottcher c z ^ d := by
    intro c z m
    suffices e : ∀ᶠ w in 𝓝 a, s.bottcher c (f c w) = s.bottcher c w ^ d by
      refine (ContMDiffOnNhd.eq_of_locally_eq ?_ (fun z m ↦
        ((contMDiff_pow _).contMDiffAt.comp _ (s.bottcher_mAnalyticOn (c, z) m).along_snd))
        (s.post_slice_connected c).isPreconnected ⟨a, s.post_a c, e⟩).self_of_nhdsSet m
      intro z m
      exact (s.bottcher_mAnalyticOn _ (s.stays_post m)).along_snd.comp _ (s.fa _).along_snd
    have e := s.bottcher_eq_bottcherNear c
    have fc := (s.fa (c, a)).along_snd.continuousAt; simp only [ContinuousAt, s.f0] at fc
    apply e.mp; apply (fc.eventually e).mp
    apply ((s.isOpen_near.snd_preimage c).eventually_mem (s.mem_near c)).mp
    refine .of_forall fun w m e0 e1 ↦ ?_
    simp only [e0, e1]; exact s.bottcherNear_eqn m
  by_cases p : (c, z) ∈ s.post; simp only [h0 p]
  by_cases m : (c, z) ∈ s.basin
  · have e0 : ∃ n, (c, (f c)^[n] z) ∈ s.post := s.basin_post m
    have e1 : ∃ n, (c, (f c)^[n] (f c z)) ∈ s.post := by
      rcases e0 with ⟨n, e0⟩; use n
      simp only [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact s.stays_post e0
    simp only [Super.bottcher, e0, e1, dif_pos]
    generalize hk0 : Nat.find e0 = k0
    generalize hk1 : Nat.find e1 = k1
    have kk : k0 = k1 + 1 := by
      rw [← hk0, ← hk1]; apply le_antisymm
      · apply Nat.find_le; simp only [Function.iterate_succ_apply]
        exact Nat.find_spec e1
      · rw [Nat.succ_le_iff, Nat.lt_find_iff]; intro n n1
        contrapose n1; simp only [not_le] at n1 ⊢
        have n0 : n ≠ 0 := by
          contrapose p
          simp only [p, Function.iterate_zero_apply] at n1; exact n1
        rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← Nat.sub_add_cancel (Nat.pos_of_ne_zero n0)]
        apply Nat.succ_le_succ; apply Nat.find_le
        simp only [← Function.iterate_succ_apply, Nat.succ_eq_add_one,
          Nat.sub_add_cancel (Nat.pos_of_ne_zero n0), n1, zero_add]
    simp only [kk, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [Complex.cpow_nat_inv_pow _ s.d0]
  have m1 : (c, f c z) ∉ s.basin := by
    contrapose m
    obtain ⟨n, m⟩ := s.basin_iff_near.mp m
    refine s.basin_iff_near.mpr ⟨n + 1, ?_⟩
    rwa [Function.iterate_succ_apply]
  simp only [s.bottcher_not_basin m, s.bottcher_not_basin m1, one_pow]

/-- `s.bottcher` satisfies the iterated Böttcher equation -/
theorem Super.bottcher_eqn_iter (s : Super f d a) [OnePreimage s] (n : ℕ) :
    s.bottcher c ((f c)^[n] z) = s.bottcher c z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  simp only [Function.iterate_succ_apply', s.bottcher_eqn, h, ← pow_mul, pow_succ]

/-- `abs (s.bottcher c z) = s.potential c z` -/
theorem Super.norm_bottcher (s : Super f d a) [OnePreimage s] :
    ‖s.bottcher c z‖ = s.potential c z := by
  have base : ∀ {c z}, (c, z) ∈ s.post → ‖s.bottcher c z‖ = s.potential c z := by
    intro c z m; rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m, s.ray_potential m]
  by_cases m : (c, z) ∈ s.basin
  · rcases s.basin_post m with ⟨n, p⟩
    rw [← Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero n s.d0), ←
      norm_pow, ← s.bottcher_eqn_iter n, base p, s.potential_eqn_iter,
      Real.pow_rpow_inv_natCast s.potential_nonneg (pow_ne_zero n s.d0)]
  · simp only [s.bottcher_not_basin m, norm_one, s.potential_eq_one m]

/-- `abs (s.bottcher c z) < 1` on `s.post` -/
theorem Super.bottcher_lt_one (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    ‖s.bottcher c z‖ < 1 := by
  replace m := s.bottcher_ext m
  simp only [Super.ext, mem_ofPred] at m
  exact lt_of_lt_of_le m s.p_le_one

/-- Functional equation for `s.ray` -/
lemma Super.ray_eqn (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    f c (s.ray c x) = s.ray c (x ^ d) := by
  generalize hz : s.ray c x = z
  rw [← s.bottcher_ray post, ← s.bottcher_eqn, s.ray_bottcher, hz]
  exact s.stays_post (s.ray_post post)

omit [T3Space S] in
/-- Raising to powers stays in `s.ext` -/
lemma Super.pow_ext (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) (n : ℕ) :
    (c, x ^ d ^ n) ∈ s.ext := by
  simp only [ext, mem_ofPred_eq, norm_pow] at post ⊢
  refine lt_of_le_of_lt (pow_le_of_le_one (by bound) ?_ (by simp [s.d0])) post
  exact le_trans post.le s.p_le_one

/-- Functional equation for `s.ray`, iterated -/
lemma Super.ray_eqn_iter (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) (n : ℕ) :
    (f c)^[n] (s.ray c x) = s.ray c (x ^ d ^ n) := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  · rw [Function.iterate_succ_apply', h, pow_succ, pow_mul, s.ray_eqn (s.pow_ext post n)]

/-- `s.bottcher c` is injective (pulling it out of `s.homeomorphSlice c`) -/
lemma Super.bottcher_inj (s : Super f d a) [OnePreimage s] (c : ℂ) :
    InjOn (s.bottcher c) {z | (c, z) ∈ s.post} :=
  (s.homeomorphSlice c).symm.injOn

/-- `s.bottcher c` sends the fixpoint to 0 -/
@[simp] lemma Super.bottcher_a (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.bottcher c a = 0 := by
  rw [← norm_eq_zero]
  have lt : ‖s.bottcher c a‖ < 1 := s.bottcher_lt_one (s.post_a c)
  have e := s.f0 _ ▸ s.bottcher_eqn (c := c) (z := a)
  replace e : ‖s.bottcher c a‖ ^ d = ‖s.bottcher c a‖ := by rw [← norm_pow, ← e]
  contrapose e
  simp only [norm_eq_zero, ne_eq, ← norm_pos_iff] at e
  exact (pow_lt_self_of_lt_one₀ e lt s.d1).ne

end
end Ray_Ray_Dynamics_Bottcher



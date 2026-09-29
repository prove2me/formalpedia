-- Prove2me | Definitions.Def_ray_potential
-- name    : ray_potential
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:06:46.179842+00:00
-- url     : https://prove2.me/theorems/d1cee5e0-68a7-4a76-94b2-74b8c65cab9f
-- title:
--   ray (8/12): the dynamical potential, open mapping, nonseparating sets
-- statement:
--   For a holomorphic family $f_c : S \to S$ on a compact 1D manifold with a superattracting fixed point $a$, this file defines the continuous potential $\phi_c : S \to [0,1]$, where $\phi_c(z) = |b_c(z)|$ near $a$ and $\phi_c(f_c(z)) = \phi_c(z)^d$, and proves its continuity. It defines the postcritical region $\{\phi_c(z) < \phi_c^\ast\}$, where $\phi_c^\ast$ is the minimal potential of a critical point other than $a$. The file also contains the open mapping theorem for analytic maps between 1D manifolds, local injectivity, the fact that points and totally disconnected sets do not separate open connected sets, and a general analytic-continuation principle.
--
--   This file is part 8 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_manifold_nontrivial

/-!
# ray (8/12): the dynamical potential, open mapping, nonseparating sets

Part 8 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Dynamics.Potential`
* `Ray.Dynamics.Nice`
* `Ray.Manifold.OpenMapping`
* `Ray.Dynamics.Postcritical`
* `Ray.Manifold.LocalInj`
* `Ray.Manifold.Nonseparating`
* `Ray.Misc.Continuation`
-/

-- ===== Ray.Dynamics.Potential =====
section Ray_Ray_Dynamics_Potential
/-!
## The potential map for a superattracting fixpoint

Let `s : Super f d a`, so that `a` is a superattracting fixpoint of `f c` of order d.
`Bottcher.lean` defines local Böttcher coordinates `s.bottcherNear` near `a`.

Throughout the basin of attraction of `f` to `a`, we define a `[0,1)`-valued `s.potential`
function that measures how fast `f`-iteration converges to `a`.  We define `s.potential c z = 1`
if `z` doesn't attract to `a`, to give a `[0,1]`-valued map defined everywhere in the manifold.
`s.potential` is `ℝ`-valued rather than `ℂ`-valued since it is defined via iterated `d`th roots,
which may not have globally continuously definable argument.

If `a` has no preimages under `f c` besides itself (`OnePreimage s`), then `s.potential` is
continuous everywhere.  This is true for the Mandelbrot and Multibrot sets, but is not true
for the Newton fractal of `z ↦ z^3 - 1` for example: `s.potential c z = 0` if `z` is an exact
iterated preimage of `a`, but such points cluster near `z = 0` with `s.potential c 0 = 1`.

## Removing the one preimage constraint

The `OnePreimage s` can be replaced by restricting to the basin of attraction.  This is mostly
straightforward, but requires working over noncompact manifolds, using compactness of levelsets
of `s.potential`.
-/

open Classical
open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped ContDiff NNReal Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z : S}
variable {d n : ℕ}

/-- If we're in the basin, we have a stable potential value -/
lemma Super.exists_potential (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∃ p : ℝ, 0 ≤ p ∧ ∀ᶠ n in atTop, ‖s.bottcherNear c ((f c)^[n] z)‖ = p ^ d ^ n := by
  obtain ⟨n,a⟩ := s.basin_iff_near.mp m
  generalize hb : ‖s.bottcherNear c ((f c)^[n] z)‖ = b
  have b0 : 0 ≤ b := by bound
  refine ⟨b ^ ((d : ℝ) ^ n)⁻¹, by bound, Filter.eventually_atTop.mpr ⟨n, fun k nk ↦ ?_⟩⟩
  rw [← Nat.sub_add_cancel nk, Function.iterate_add_apply]
  simp only [s.bottcherNear_eqn_iter a, hb, norm_pow, ← Real.rpow_natCast, Nat.cast_pow,
    ← Real.rpow_mul b0, ← div_eq_inv_mul, ← Real.rpow_sub (Nat.cast_pos.mpr s.dp),
    Nat.cast_add, add_sub_cancel_right]

/-- `potential` in terms of any `s.near` iterate -/
theorem Super.potential_eq (s : Super f d a) (m : (c, (f c)^[n] z) ∈ s.near) :
    s.potential c z = ‖s.bottcherNear c ((f c)^[n] z)‖ ^ (d ^ n : ℝ)⁻¹ := by
  have mb : (c, z) ∈ s.basin := s.basin_iff_near.mpr ⟨_, m⟩
  have ep := s.exists_potential mb
  simp only [Super.potential, mb, ep, true_and, dif_pos]
  obtain ⟨p0, ph⟩ := choose_spec ep
  generalize hp : choose ep = p at ph p0
  clear hp ep
  obtain ⟨k, ph⟩ := Filter.eventually_atTop.mp ph
  have e : ‖s.bottcherNear c ((f c)^[n] z)‖ ^ d ^ k = p ^ d ^ (k + n) := by
    refine Eq.trans ?_ (ph _ (by omega))
    rw [Function.iterate_add_apply, s.bottcherNear_eqn_iter m, norm_pow]
  generalize hb : ‖s.bottcherNear c ((f c)^[n] z)‖ = b at e
  have b0 : 0 ≤ b := by bound
  trans (p ^ d ^ (k + n)) ^ (d ^ (k + n) : ℝ)⁻¹
  · simp only [← Real.rpow_natCast (x := p), ← Real.rpow_mul p0, Nat.cast_pow]
    rw [mul_inv_cancel₀ (by simp [s.d0]), Real.rpow_one]
  · have d0 : (d ^ k : ℝ) ≠ 0 := by simp [s.d0]
    rw [← e, ← Real.rpow_natCast (x := b), ← Real.rpow_mul b0, Nat.cast_pow, pow_add]
    field_simp [d0]

/-- `‖bottcherNear‖` in terms of `potential` -/
theorem Super.norm_bottcherNear (s : Super f d a) {n : ℕ} (r : (c, (f c)^[n] z) ∈ s.near) :
    ‖s.bottcherNear c ((f c)^[n] z)‖ = s.potential c z ^ d ^ n := by
  rw [s.potential_eq r, ← Real.rpow_natCast, ← Real.rpow_mul (by bound), Nat.cast_pow,
    inv_mul_cancel₀ (by simp [s.d0]), Real.rpow_one]

/-- `potential a = 0` -/
theorem Super.potential_a (s : Super f d a) : s.potential c a = 0 := by
  have r : (c, (f c)^[0] a) ∈ s.near := by simp only [Function.iterate_zero, s.mem_near, id]
  simp only [s.potential_eq r, Function.iterate_zero, id, s.bottcherNear_a,
    norm_zero, pow_zero, inv_one, Real.rpow_one]

/-- If `z` isn't in the basin, `potential = 1` -/
theorem Super.potential_eq_one (s : Super f d a) (a : (c, z) ∉ s.basin) :
    s.potential c z = 1 := by
  simp [Super.potential, a]

/-- If `z` is in the basin, `potential < 1` -/
theorem Super.potential_lt_one (s : Super f d a) (a : (c, z) ∈ s.basin) :
    s.potential c z < 1 := by
  obtain ⟨n, r⟩ := s.basin_iff_near.mp a
  simp only [s.potential_eq r]
  exact Real.rpow_lt_one (norm_nonneg _) (s.bottcherNear_lt_one r) (by bound)

/-- `z` is in the basin iff `potential < 1` -/
theorem Super.potential_lt_one_iff (s : Super f d a) :
    s.potential c z < 1 ↔ (c, z) ∈ s.basin := by
  refine ⟨fun h ↦ ?_, s.potential_lt_one⟩
  contrapose h
  simp only [s.potential_eq_one h, lt_self_iff_false, not_false_iff]

/-- `potential ≤ 1` -/
@[bound] theorem Super.potential_le_one (s : Super f d a) : s.potential c z ≤ 1 := by
  by_cases a : (c, z) ∈ s.basin
  exact (s.potential_lt_one a).le
  exact le_of_eq (s.potential_eq_one a)

/-- `0 ≤ potential` -/
@[bound] theorem Super.potential_nonneg (s : Super f d a) : 0 ≤ s.potential c z := by
  by_cases r : (c, z) ∈ s.basin
  · rcases s.basin_iff_near.mp r with ⟨n, r⟩
    simp only [s.potential_eq r]; bound
  · simp only [s.potential_eq_one r, zero_le_one]

/-- The defining equation of `s.potential` -/
theorem Super.potential_eqn (s : Super f d a) :
    s.potential c (f c z) = s.potential c z ^ d := by
  by_cases a : (c, z) ∈ s.basin
  · rcases s.basin_iff_near.mp a with ⟨n, a⟩
    have a' : (c, (f c)^[n] (f c z)) ∈ s.near := by
      simp only [← Function.iterate_succ_apply, Function.iterate_succ', s.stays_near a,
        Function.comp]
    simp only [s.potential_eq a, s.potential_eq a', ← Function.iterate_succ_apply,
      Function.iterate_succ', s.bottcherNear_eqn a, norm_pow, ← Real.rpow_natCast, ←
      Real.rpow_mul (norm_nonneg _), mul_comm, Function.comp]
  · have a' : (c, f c z) ∉ s.basin := by
      contrapose a
      simp only [s.basin_iff_near, ← Function.iterate_succ_apply] at a ⊢
      rcases a with ⟨n, a⟩; exact ⟨n + 1, a⟩
    simp only [s.potential_eq_one a, s.potential_eq_one a', one_pow]

/-- The potential equation, iterated -/
theorem Super.potential_eqn_iter (s : Super f d a) (n : ℕ) :
    s.potential c ((f c)^[n] z) = s.potential c z ^ d ^ n := by
  induction' n with n h
  · simp only [Function.iterate_zero, id, pow_zero, pow_one]
  · simp only [Function.iterate_succ', Super.potential_eqn, h, ← pow_mul, ← pow_succ,
      Function.comp]

/-- Our standard iteration is analytic -/
theorem Super.iter_mAnalytic' (s : Super f d a) (n : ℕ) :
    ContMDiff II I ω fun p : ℂ × S ↦ (f p.1)^[n] p.2 := by
  intro p; induction' n with n h; simp [Function.iterate_zero, contMDiffAt_snd]
  simp only [Function.iterate_succ', Function.comp_def]
  exact (s.fa _).comp₂ contMDiffAt_fst h

theorem Super.iter_mAnalytic (s : Super f d a) (n : ℕ) :
    ContMDiff II II ω fun p : ℂ × S ↦ (p.1, (f p.1)^[n] p.2) := by
  intro p; apply contMDiffAt_fst.prodMk; apply s.iter_mAnalytic'

/-- `s.potential` is continuous where we attract -/
theorem ContinuousAt.potential_of_reaches (s : Super f d a) (a : (c, z) ∈ s.basin) :
    ContinuousAt (uncurry s.potential) (c, z) := by
  obtain ⟨n,a⟩ := s.basin_iff_near.mp a
  have e : uncurry s.potential =ᶠ[𝓝 (c, z)]
      fun p : ℂ × S ↦ ‖s.bottcherNear p.1 ((f p.1)^[n] p.2)‖ ^ (d ^ n : ℝ)⁻¹ := by
    have a' : ∀ᶠ p : ℂ × S in 𝓝 (c, z), (p.1, (f p.1)^[n] p.2) ∈ s.near :=
      (s.iter_mAnalytic n _).continuousAt.eventually_mem (s.isOpen_near.mem_nhds a)
    refine a'.mp (.of_forall fun p h ↦ ?_)
    simp only [uncurry, s.potential_eq h]
  simp only [continuousAt_congr e]
  refine ContinuousAt.rpow ?_ continuousAt_const ?_
  · apply continuous_norm.continuousAt.comp
    refine ((s.bottcherNear_mAnalytic' ?_).comp _ (s.iter_mAnalytic n (c, z))).continuousAt
    exact a
  · bound

/-- `s.potential = 0` exactly on iterated preimages of `a` -/
theorem Super.potential_eq_zero (s : Super f d a) : s.potential c z = 0 ↔ ∃ n, (f c)^[n] z = a := by
  constructor
  · intro h
    by_cases r : (c, z) ∈ s.basin
    · rcases s.basin_iff_near.mp r with ⟨n, r⟩
      simp only [s.potential_eq r, Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _), norm_eq_zero,
        s.bottcherNear_eq_zero r] at h
      use n, h.1
    · simp only [s.potential_eq_one r, one_ne_zero] at h
  · intro p; rcases p with ⟨n, p⟩
    have nz : d^n > 0 := pow_pos s.dp _
    rw [← pow_eq_zero_iff nz.ne', ← s.potential_eqn_iter n, p, s.potential_a]

/-- `s.potential` is upper semicontinuous unconditionally -/
theorem UpperSemicontinuous.potential (s : Super f d a) :
    UpperSemicontinuous (uncurry s.potential) := by
  intro ⟨c, z⟩
  by_cases r : (c, z) ∈ s.basin
  · exact (ContinuousAt.potential_of_reaches s r).upperSemicontinuousAt
  · simp only [uncurry, SemicontinuousAt, s.potential_eq_one r]
    exact fun y y1 ↦ .of_forall fun p ↦ lt_of_le_of_lt s.potential_le_one y1

theorem Super.preimage_eq' (s : Super f d a) [o : OnePreimage s] : f c z = a ↔ z = a := by
  have e := o.eq_a c z; refine ⟨e, ?_⟩; intro e; simp only [e, s.f0]

theorem Super.preimage_eq (s : Super f d a) [o : OnePreimage s] {n : ℕ} :
    (f c)^[n] z = a ↔ z = a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply', s.preimage_eq', h]

theorem Super.potential_eq_zero_of_onePreimage (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.potential c z = 0 ↔ z = a := by
  constructor
  · intro h; rw [s.potential_eq_zero] at h; rcases h with ⟨n, h⟩; rw [s.preimage_eq] at h; exact h
  · intro h; simp only [h, s.potential_a]

theorem Super.potential_ne_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.potential c z ≠ 0 ↔ z ≠ a := by simp only [Ne, s.potential_eq_zero_of_onePreimage]

theorem Super.potential_pos (s : Super f d a) [OnePreimage s] (c : ℂ) :
    0 < s.potential c z ↔ z ≠ a := by
  rw [← s.potential_ne_zero c]
  use ne_of_gt, fun ne ↦ ne.symm.lt_of_le s.potential_nonneg

/-- `f` can't get from far from `(c,a)` to arbitrarily close to `(c,a)` in one step -/
theorem Super.no_jump (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ) (n : Set (ℂ × S))
    (no : IsOpen n) (na : (c, a) ∈ n) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), ∀ q, p = s.fp q → q ∈ n := by
  have h : ∀ q : ℂ × S, f q.1 q.2 = a → q.2 = a := fun _ ↦ by simp only [s.preimage_eq', imp_self]
  contrapose h
  simp only [Filter.not_eventually, not_forall, exists_prop] at h
  set t := s.fp '' (closedBall c 1 ×ˢ univ ∩ nᶜ)
  have tc : IsClosed t := by
    refine (IsCompact.image ?_ s.fpa.continuous).isClosed
    exact ((isCompact_closedBall _ _).prod isCompact_univ).inter_right no.isClosed_compl
  have th : ∃ᶠ p in 𝓝 (c, a), p ∈ t := by
    have mb : ∀ᶠ p : ℂ × S in 𝓝 (c, a), p.1 ∈ closedBall c 1 :=
      continuousAt_fst.eventually_mem_nhd (Metric.closedBall_mem_nhds _ zero_lt_one)
    refine (h.and_eventually mb).mp (.of_forall fun p i ↦ ?_)
    rcases i with ⟨⟨q, qp, m⟩, b⟩
    simp only [Prod.ext_iff] at qp; simp only [qp.1] at b
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_prod_eq, Set.mem_univ,
      and_true, Prod.ext_iff, t]
    use q, ⟨b, m⟩, qp.1.symm, qp.2.symm
  have m := th.mem_of_closed tc
  rcases(Set.mem_image _ _ _).mp m with ⟨p, m, pa⟩
  simp only [Super.fp, Prod.mk_inj] at pa
  simp only [not_forall]; use p, pa.2
  contrapose m
  rw [← @Prod.mk.eta _ _ p, pa.1, m]
  simp only [Set.mem_inter_iff, Set.prodMk_mem_set_prod_eq, Metric.mem_closedBall, dist_self,
    zero_le_one, Set.mem_univ, Set.mem_compl_iff, true_and, not_not, na]

/-- A barrier is a compact, annular region around `a` (but not containing it) such that
    outside points must pass through it to reach `a`. -/
structure Barrier (s : Super f d a) (c : ℂ) (n t : Set (ℂ × S)) : Prop where
  compact : IsCompact t
  tn : t ⊆ n
  near : t ⊆ s.near
  hole : ∀ e, (e, a) ∉ t
  barrier : ∀ᶠ e in 𝓝 c, ∀ z, (e, z) ∉ n → Attracts (f e) z a → ∃ n, (e, (f e)^[n] z) ∈ t

/-- `f` can't get from far from `(c,a)` to close to `(c,a)` without passing through a barrier -/
theorem Super.barrier (s : Super f d a) [OnePreimage s] [T2Space S] (n : Set (ℂ × S))
    (no : IsOpen n) (na : (c, a) ∈ n) : ∃ t : Set (ℂ × S), Barrier s c n t := by
  set n' := n ∩ s.near
  have nn' : n' ∈ 𝓝 (c, a) :=
    Filter.inter_mem (no.mem_nhds na) (s.isOpen_near.mem_nhds (s.mem_near c))
  rcases (Filter.hasBasis_iff.mp (compact_basis_nhds (c, a)) n').mp nn' with ⟨u, ⟨un, uc⟩, us⟩
  simp only [Set.subset_inter_iff, n'] at us
  rcases eventually_nhds_iff.mp
      (s.no_jump c (interior u) isOpen_interior (mem_interior_iff_mem_nhds.mpr un)) with
    ⟨i, ih, io, ia⟩
  rcases mem_nhds_prod_iff'.mp (Filter.inter_mem un (io.mem_nhds ia)) with
    ⟨i0, i1, i0o, i0m, i1o, i1m, ii⟩
  simp only [Set.subset_inter_iff] at ii
  set t := u \ univ ×ˢ i1
  have ta : ∀ e, (e, a) ∉ t := fun e ↦
    Set.notMem_sdiff_of_mem (Set.mk_mem_prod (Set.mem_univ _) i1m)
  use t
  refine ⟨uc.diff (isOpen_univ.prod i1o), subset_trans sdiff_subset us.1,
      subset_trans sdiff_subset us.2, ta, ?_⟩
  rw [eventually_nhds_iff]; use i0; refine ⟨?_, i0o, i0m⟩
  intro e em z zm za
  rcases tendsto_atTop_nhds.mp za i1 i1m i1o with ⟨m, mh⟩
  have en : ∃ n, (f e)^[n] z ∈ i1 := ⟨m, mh m (le_refl _)⟩
  set n := Nat.find en
  use n - 1
  have ni1 : (f e)^[n] z ∈ i1 := Nat.find_spec en
  have n0 : n ≠ 0 := by
    contrapose zm
    simp only [zm, Function.iterate_zero, id_eq] at ni1
    exact us.1 (ii.1 (Set.mk_mem_prod em ni1))
  have nt : (f e)^[n-1] z ∉ i1 := Nat.find_min en (Nat.pred_lt n0)
  apply Set.mem_sdiff_of_mem
  · apply interior_subset; apply ih (e, (f e)^[n] z) (ii.2 (Set.mk_mem_prod em ni1))
    simp only [Super.fp]; rw [← Function.iterate_succ_apply' (f e) (n - 1)]
    simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero n0))]
  · contrapose nt
    simp only [Set.prodMk_mem_set_prod_eq] at nt ⊢
    exact nt.2

/-- `s.potential` is large on barriers (because they are compact) -/
theorem Barrier.potential_large {s : Super f d a} [OnePreimage s] {n t : Set (ℂ × S)}
    (b : Barrier s c n t) : ∃ r : ℝ, r > 0 ∧ ∀ e z, (e, z) ∈ t → r ≤ s.potential e z := by
  by_cases t0 : t = ∅
  · use 1, zero_lt_one
    simp only [t0, Set.mem_empty_iff_false, IsEmpty.forall_iff, forall_const, imp_true_iff]
  simp only [← ne_eq, ← Set.nonempty_iff_ne_empty] at t0
  have pc : ContinuousOn (uncurry s.potential) t := by
    refine ContinuousOn.mono ?_ b.near
    intro ⟨c, z⟩ m; apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.potential_of_reaches s
    simp only [s.basin_iff_near]
    use 0
    simpa only [Function.iterate_zero_apply]
  rcases b.compact.exists_isMinOn t0 pc with ⟨⟨e, z⟩, ps, pm⟩
  use s.potential e z; constructor
  · have h := b.hole e; contrapose h; simp only [not_lt] at h
    have h' := le_antisymm h s.potential_nonneg
    simp only [s.potential_eq_zero, s.preimage_eq, exists_const] at h'
    simp only [← h', ps]
  · intro e z m; simp only [isMinOn_iff, uncurry] at pm ⊢; exact pm _ m

/-- The first `n` preimages of a barrier -/
@[nolint unusedArguments]
def Barrier.fast {s : Super f d a} {n t : Set (ℂ × S)} (_ : Barrier s c n t) (m : ℕ) :
    Set (ℂ × S) :=
  ⋃ k : Fin m, (fun p : ℂ × S ↦ (p.1, (f p.1)^[k] p.2)) ⁻¹' t

theorem Barrier.closed_fast {s : Super f d a} [T2Space S] {n t : Set (ℂ × S)} (b : Barrier s c n t)
    (m : ℕ) : IsClosed (b.fast m) := by
  apply isClosed_iUnion_of_finite; intro k; refine IsClosed.preimage ?_ b.compact.isClosed
  apply continuous_fst.prodMk; generalize hn : (k : ℕ) = n; clear k hn; induction' n with n h
  simp only [Function.iterate_zero_apply]; exact continuous_snd
  simp only [Function.iterate_succ_apply']; exact s.fa.continuous.comp (continuous_fst.prodMk h)

theorem Barrier.mem_fast {s : Super f d a} {n t : Set (ℂ × S)} (b : Barrier s c n t) {m : ℕ} {e : ℂ}
    {z : S} : (e, z) ∈ b.fast m ↔ ∃ n, n < m ∧ (e, (f e)^[n] z) ∈ t := by
  simp only [Barrier.fast, Set.mem_iUnion, Set.mem_preimage]; constructor
  intro h; rcases h with ⟨n, h⟩; use n, Fin.is_lt _, h
  intro h; rcases h with ⟨n, nm, h⟩; use⟨n, nm⟩, h

theorem Barrier.fast_reaches {s : Super f d a} {n t : Set (ℂ × S)} (b : Barrier s c n t) {m : ℕ}
    {e : ℂ} {z : S} (q : (e, z) ∈ b.fast m) : ∃ n, (e, (f e)^[n] z) ∈ s.near := by
  rw [b.mem_fast] at q; rcases q with ⟨n, _, q⟩; exact ⟨n, b.near q⟩

/-- `s.potential` is everywhere lower semicontinuous (and thus continuous) if `OnePreimage s` -/
theorem Continuous.potential (s : Super f d a) [OnePreimage s] [T2Space S] :
    Continuous (uncurry s.potential) := by
  -- Reduce to showing that nearby bounded potential means reaches
  refine continuous_iff_lower_upperSemicontinuous.mpr ⟨?_, UpperSemicontinuous.potential s⟩
  intro ⟨c, z⟩
  by_cases re : (c, z) ∈ s.basin
  · exact (ContinuousAt.potential_of_reaches s re).lowerSemicontinuousAt
  intro y y1
  simp only [uncurry, s.potential_eq_one re] at y1 ⊢
  contrapose re
  simp only [Filter.not_eventually, not_lt] at re
  -- Construct a barrier separating (c,z) from (c,a)
  by_cases za : z = a
  · simp only [s.basin_iff_near]
    use 0
    simp only [za, Function.iterate_zero_apply, s.mem_near c]
  have sn : {(c, a)}ᶜ ∈ 𝓝 (c, z) :=
    compl_singleton_mem_nhds (by simp only [za, Ne, Prod.mk_inj, and_false, not_false_iff])
  rcases (Filter.hasBasis_iff.mp (compact_basis_nhds (c, z)) ({(c, a)}ᶜ)).mp sn with
    ⟨u, ⟨un, uc⟩, ua⟩
  simp only [Set.subset_compl_singleton_iff] at ua
  rcases s.barrier (uᶜ) uc.isClosed.isOpen_compl (Set.mem_compl ua) with ⟨t, b⟩
  rcases b.potential_large with ⟨r, rp, rt⟩
  -- `potential ≤ y →` reaches the barrier quickly
  have en : ∃ n, ∀ᶠ e in 𝓝 c, ∀ z, (e, z) ∈ u → s.potential e z ≤ y → (e, z) ∈ b.fast n := by
    -- Find n s.t. y ^ (d^n) < r
    rcases exists_pow_lt_of_lt_one rp y1 with ⟨k, ky⟩
    rcases Filter.exists_le_of_tendsto_atTop (tendsto_pow_atTop_atTop_of_one_lt s.d1) 0 k
      with ⟨n, _, nk⟩
    use n
    -- Our upper bound on `potential e z`, plus on our lower bound on `t`,
    -- implies that `z` reaches near quickly
    refine b.barrier.mp (.of_forall fun e h z m py ↦ ?_)
    have za : Attracts (f e) z a := by
      by_cases r : (e, z) ∈ s.basin
      · rcases s.basin_iff_near.mp r with ⟨n, r⟩; exact s.attracts r
      · rw [s.potential_eq_one r] at py; linarith
    rcases h z (notMem_compl_iff.mpr m) za with ⟨o, oh⟩
    by_cases no : n ≤ o
    · have pyo : s.potential e z ^ d ^ o ≤ y ^ d ^ o := by bound
      rw [← s.potential_eqn_iter o] at pyo
      have ryo : r ≤ y ^ d ^ o := _root_.trans (rt _ _ oh) pyo
      have kdo : k ≤ d ^ o := _root_.trans nk (Nat.pow_le_pow_right s.dp no)
      have ryk : r ≤ y ^ k :=
        _root_.trans ryo (pow_le_pow_of_le_one (_root_.trans s.potential_nonneg py) y1.le kdo)
      linarith
    · simp only [not_le] at no; rw [b.mem_fast]; use o, no, oh
  -- Now that we've bounded n, (c,z) must reach near
  rcases en with ⟨n, h⟩
  rcases eventually_nhds_iff.mp h with ⟨v, vh, vo, vc⟩
  have ev : ∀ᶠ p : ℂ × S in 𝓝 (c, z), p ∈ u ∩ v ×ˢ univ := by
    simp only [Filter.eventually_iff, Set.ofPred_mem_eq]
    exact Filter.inter_mem un ((vo.prod isOpen_univ).mem_nhds (Set.mk_mem_prod vc (Set.mem_univ _)))
  have ef : ∃ᶠ p in 𝓝 (c, z), p ∈ b.fast n := by
    refine (re.and_eventually ev).mp (.of_forall ?_)
    intro ⟨e, z⟩ ⟨zy, m⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true] at m
    exact vh e m.2 z m.1 zy
  rcases b.mem_fast.mp (ef.mem_of_closed (b.closed_fast _)) with ⟨n, _, r⟩
  exact s.basin_iff_near.mpr ⟨n, b.near r⟩

/-- potential levelsets form a neighborhood basis at `a` (open version) -/
theorem Super.potential_basis' (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ) {t : Set S}
    (n : t ∈ 𝓝 a) (o : IsOpen t) :
    ∃ p, 0 < p ∧ {z | s.potential c z < p} ⊆ t := by
  by_cases ne : tᶜ = ∅
  · use 1, zero_lt_one; simp only [compl_empty_iff] at ne; rw [ne]; exact subset_univ _
  replace ne := Set.Nonempty.image (s.potential c) (nonempty_iff_ne_empty.mpr ne)
  have pos : ∀ p : ℝ, p ∈ s.potential c '' tᶜ → 0 ≤ p := by
    intro p m; simp only [mem_image] at m; rcases m with ⟨z, _, e⟩; rw [← e]
    exact s.potential_nonneg
  have below : BddBelow (s.potential c '' tᶜ) := bddBelow_def.mpr ⟨0, pos⟩
  generalize hq : sInf (s.potential c '' tᶜ) = q
  have qt : ∀ z, s.potential c z < q → z ∈ t := by
    intro z i; contrapose i; simp only [not_lt, ← hq]; apply csInf_le below
    simp only [mem_image]; use z, i
  have qp : 0 < q := by
    simp only [← hq]
    have mc := csInf_mem_closure ne below
    rw [IsClosed.closure_eq] at mc
    · simp only [mem_image] at mc; rcases mc with ⟨z, m, e⟩
      rw [← e]; contrapose m
      replace m := le_antisymm (not_lt.mp m) s.potential_nonneg
      rw [s.potential_eq_zero_of_onePreimage] at m; simp only [m, notMem_compl_iff]
      exact mem_of_mem_nhds n
    · exact (o.isClosed_compl.isCompact.image (Continuous.potential s).along_snd).isClosed
  use q, qp, qt

/-- potential levelsets form a neighborhood basis at `a` (general version) -/
theorem Super.potential_basis (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ)
    {t : Set S} (n : t ∈ 𝓝 a) : ∃ p, 0 < p ∧ {z | s.potential c z < p} ⊆ t := by
  rcases mem_nhds_iff.mp n with ⟨t', tt, o, m⟩
  rcases s.potential_basis' c (o.mem_nhds m) o with ⟨p, pp, sub⟩
  use p, pp, _root_.trans sub tt

end
end Ray_Ray_Dynamics_Potential

-- ===== Ray.Dynamics.Nice =====
section Ray_Ray_Dynamics_Nice
/-!
## An `n` which maps whole potential levelsets to `s.near`
-/

open Classical
open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped ContDiff NNReal Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c : ℂ} {p : ℝ}
variable {a z : S}
variable {d n n0 n1 k : ℕ}
variable {s : Super f d a}

/-- Fix `c`, and let `p < 1`.  Then `u = s.potential c ⁻¹' Icc 0 p` is closed, and thus compact,
    and thus there is a fixed `n` s.t. `f c^[n] '' u ⊆ s.near`.  This lets us work with fixed `n`
    more of the time. -/
def Super.IsNiceN (s : Super f d a) (c : ℂ) (p : ℝ) (n : ℕ) :=
  ∀ z, s.potential c z ≤ p →
    (c, (f c)^[n] z) ∈ s.near ∧ ∀ k, n ≤ k → mfderiv I I (s.bottcherNear c) ((f c)^[k] z) ≠ 0

lemma Super.IsNiceN.near (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p) :
    (c, (f c)^[n] z) ∈ s.near :=
  (nice z le).1

theorem Super.isNice_zero (s : Super f d a) (c : ℂ) [OnePreimage s] : s.IsNiceN c 0 0 := by
  intro z zp
  have za := le_antisymm zp s.potential_nonneg
  simp only [s.potential_eq_zero_of_onePreimage] at za
  rw [za, Function.iterate_zero_apply]; use s.mem_near c
  intro k _; rw [s.iter_a]; exact s.bottcherNear_mfderiv_ne_zero c

theorem Super.isNiceN_mono (s : Super f d a) (nice : s.IsNiceN c p n0) (n01 : n0 ≤ n1) :
    s.IsNiceN c p n1 := by
  intro z zp; rcases nice z zp with ⟨m, nc⟩
  use s.iter_stays_near' m n01, fun k n1k ↦ nc k (_root_.trans n01 n1k)

variable [T2Space S]

theorem Super.has_nice_n (s : Super f d a) (c : ℂ) (p1 : p < 1) [op : OnePreimage s] :
    ∃ n, s.IsNiceN c p n := by
  have et : ∀ᶠ z in 𝓝 a, (c, z) ∈ s.near ∧ mfderiv I I (s.bottcherNear c) z ≠ 0 := by
    apply
      (mfderiv_ne_zero_eventually (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd
          (s.bottcherNear_mfderiv_ne_zero c)).mp
    apply ((s.isOpen_near.snd_preimage c).eventually_mem (s.mem_near c)).mp
    refine .of_forall fun z m nc ↦ ?_; use m, nc
  rcases et.exists_mem with ⟨t, m, h⟩
  rcases s.potential_basis c m with ⟨q, qp, qt⟩; clear et m
  rcases exists_pow_lt_of_lt_one qp p1 with ⟨n, pq⟩
  use n; intro z m
  replace m : ∀ k, n ≤ k → s.potential c ((f c)^[k] z) < q := by
    intro k nk; refine lt_of_le_of_lt ?_ pq; simp only [s.potential_eqn_iter]
    have dn := (Nat.lt_pow_self s.d1 (n := k)).le
    apply _root_.trans (pow_le_pow_of_le_one s.potential_nonneg s.potential_le_one dn)
    refine _root_.trans (pow_le_pow_left₀ s.potential_nonneg m _) ?_
    exact pow_le_pow_of_le_one (_root_.trans s.potential_nonneg m) p1.le nk
  use(h _ (qt (m n (le_refl _)))).1, fun k nk ↦ (h _ (qt (m k nk))).2

/-- An `n` such that `(f c)^[n]` sends everything with potential < `p` to `s.near` -/
def Super.np (s : Super f d a) (c : ℂ) (p : ℝ) : ℕ :=
  if q : p < 1 ∧ OnePreimage s then Nat.find (s.has_nice_n c q.1 (op := q.2)) else 0

theorem Super.nice_np (s : Super f d a) (c : ℂ) (p1 : p < 1) [op : OnePreimage s] :
    s.IsNiceN c p (s.np c p) := by
  have q : p < 1 ∧ OnePreimage s := ⟨p1, op⟩
  simp only [Super.np, q, true_and, dif_pos]
  exact Nat.find_spec (s.has_nice_n c p1)

theorem Super.np_zero (s : Super f d a) (c : ℂ) [op : OnePreimage s] : s.np c 0 = 0 := by
  simp only [Super.np, zero_lt_one, op, true_and, dif_pos, Nat.find_eq_zero, Super.isNice_zero]

theorem Super.np_mono (s : Super f d a) (c : ℂ) {p0 p1 : ℝ} (le : p0 ≤ p1) (p11 : p1 < 1)
    [op : OnePreimage s] : s.np c p0 ≤ s.np c p1 := by
  have p01 : p0 < 1 := lt_of_le_of_lt le p11
  have e : s.np c p0 = Nat.find (s.has_nice_n c p01) := by
    simp only [Super.np, p01, op, true_and, dif_pos]
  rw [e]; apply Nat.find_min'; exact fun z zp ↦ s.nice_np c p11 _ (_root_.trans zp le)

/-- An `n` such that `(f c)^[n]` sends everything with potential < `s.potential c z` to `s.near` -/
def Super.nz (s : Super f d a) (c : ℂ) (z : S) : ℕ :=
  s.np c (s.potential c z)

lemma Super.nice_nz (s : Super f d a) (m : (c, z) ∈ s.basin) [OnePreimage s] :
    s.IsNiceN c (s.potential c z) (s.nz c z) :=
  s.nice_np c (s.potential_lt_one m)

/-!
## Nice properties that don't depend on `s.near`, since that isn't in `Defs.lean`
-/

namespace Super.IsNiceN
omit [T2Space S]

lemma contMDiffAt_bottcherNearIter (nice : s.IsNiceN c p n)
    (le : s.potential c z ≤ p) : ContMDiffAt II I ω (uncurry (s.bottcherNearIter n)) (c, z) :=
  s.bottcherNearIter_mAnalytic (nice z le).1

lemma bottcherNear_eq_zero (nice : s.IsNiceN c p n)
    (le : s.potential c z ≤ p) : s.bottcherNearIter n c z = 0 ↔ (f c)^[n] z = a :=
  s.bottcherNear_eq_zero (nice z le).1

lemma mfderiv_ne_zero (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p)
    (nk : n ≤ k) : mfderiv I I (s.bottcherNear c) ((f c)^[k] z) ≠ 0 :=
  (nice z le).2 _ nk

lemma norm_bottcherNear' (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p) :
    ∀ᶠ w in 𝓝 z, ‖s.bottcherNear c ((f c)^[n] w)‖ = s.potential c w ^ d ^ n := by
  filter_upwards [((s.isOpen_preimage _).snd_preimage c).eventually_mem (nice z le).1] with w m
  exact s.norm_bottcherNear m

lemma norm_bottcherNear (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p) :
    ‖s.bottcherNear c ((f c)^[n] z)‖ = s.potential c z ^ d ^ n :=
  (nice.norm_bottcherNear' le).self_of_nhds

end Super.IsNiceN
end
end Ray_Ray_Dynamics_Nice

-- ===== Ray.Manifold.OpenMapping =====
section Ray_Ray_Manifold_OpenMapping
/-!
## The open mapping theorem on 1D complex manifolds

`AnalyticAt.eventually_constant_or_nhds_le_map_nhds` shows that `ℂ → ℂ` analytic
functions are either locally constant or locally open (mapping open neighborhoods to
open neighborhoods).  We slightly generalize this result, to

1. Parameterized analytic maps `f : ℂ → ℂ → ℂ`, where the analogue of openness for `f`
   is openness of `(c,z) ↦ (c, f c z)`.
2. MAnalytic maps `S → T` where `S, T` are 1D analytic manifolds
3. (1) and (2) together: parameterized analytic maps `f : ℂ → S → T`, where
   `S, T` are 1D analytic manifolds.

The parameterized versions follow straightforwardly from effective versions of the
unparameterized version, and specificaly our underlying workhorse is
`DiffContOnCl.ball_subset_image_closedBall`.  The manifold versions are straightforward
extentions of the flat versions lifted to charts.
-/

open Classical
open Complex
open Filter (Tendsto)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball mem_ball mem_closedBall mem_ball_self
  mem_closedBall_self mem_sphere sphere)
open OneDimension
open Set
open scoped ContDiff Real Topology Manifold
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
variable {U : Type} [TopologicalSpace U] [ChartedSpace ℂ U]

/-- Nontriviality at a point from nontriviality on a sphere -/
theorem nontrivial_local_of_global {f : ℂ → ℂ} {z : ℂ} {e r : ℝ}
    (fa : AnalyticOnNhd ℂ f (closedBall z r))
    (rp : 0 < r) (ep : 0 < e) (ef : ∀ w, w ∈ sphere z r → e ≤ ‖f w - f z‖) :
    NontrivialMAnalyticAt f z := by
  replace fa : ∃ t, r < t ∧ AnalyticOnNhd ℂ f (ball z t) :=
    exists_ball_superset fa (isOpen_analyticAt ℂ f)
  obtain ⟨t, rt, fa⟩ := fa
  have fh : ∀ x ∈ ball z t, ContMDiffAt I I ω f x := fun _ m ↦ (fa _ m).mAnalyticAt I I
  have zs : z ∈ ball z t := mem_ball_self (by linarith)
  use fh _ zs
  contrapose ef
  simp only [Filter.not_frequently, not_not] at ef
  simp only [not_forall, not_le]
  have zrs : z + r ∈ sphere z r := by
    simp only [mem_sphere, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, abs_of_pos rp,
      Real.norm_eq_abs]
  use z + r, zrs
  have lc := ContMDiffOn.const_of_locally_const (fun _ m ↦ (fh _ m).contMDiffWithinAt) zs
      isOpen_ball (convex_ball z t).isPreconnected ef (z + r) (Metric.sphere_subset_ball rt zrs)
  simp only [lc, sub_self, norm_zero, ep]

/-- The effective parameterized open mapping theorem for analytic `f : ℂ → ℂ → ℂ`.
    We lose more effectiveness than is optimal, since our goal is ineffective versions. -/
theorem AnalyticOnNhd.ball_subset_image_closedBall_param {f : ℂ → ℂ → ℂ} {c z : ℂ} {e r : ℝ}
    {u : Set ℂ} (fa : AnalyticOnNhd ℂ (uncurry f) (u ×ˢ closedBall z r)) (rp : 0 < r) (ep : 0 < e)
    (un : u ∈ 𝓝 c) (ef : ∀ d, d ∈ u → ∀ w, w ∈ sphere z r → e ≤ ‖f d w - f d z‖) :
    (fun p : ℂ × ℂ ↦ (p.1, f p.1 p.2)) '' u ×ˢ closedBall z r ∈ 𝓝 (c, f c z) := by
  have fn : ∀ d, d ∈ u → ∃ᶠ w in 𝓝 z, f d w ≠ f d z := by
    refine fun d m ↦ (nontrivial_local_of_global (fa.along_snd.mono ?_) rp ep (ef d m)).nonconst
    simp only [mem_prod_eq, ofPred_mem_eq, (iff_true _).mpr m, true_and, subset_refl]
  have op : ∀ d, d ∈ u → ball (f d z) (e / 2) ⊆ f d '' closedBall z r := by
    intro d du; refine DiffContOnCl.ball_subset_image_closedBall ?_ rp (ef d du) (fn d du)
    have e : f d = uncurry f ∘ fun w ↦ (d, w) := rfl
    rw [e]; apply DifferentiableOn.diffContOnCl; apply AnalyticOnNhd.differentiableOn
    refine fa.comp (analyticOnNhd_const.prod analyticOnNhd_id) ?_
    intro w wr; simp only [closure_ball _ rp.ne'] at wr
    simp only [mem_prod_eq, wr, true_and, du]
  rcases Metric.continuousAt_iff.mp
      (fa (c, z) (mk_mem_prod (mem_of_mem_nhds un) (mem_closedBall_self rp.le))).continuousAt
      (e / 4) (by linarith) with
    ⟨s, sp, sh⟩
  rw [mem_nhds_prod_iff]
  refine ⟨u ∩ ball c s, Filter.inter_mem un (Metric.ball_mem_nhds c (by linarith)), ?_⟩
  use ball (f c z) (e / 4), Metric.ball_mem_nhds _ (by linarith)
  intro ⟨d, w⟩ m
  simp only [mem_inter_iff, mem_prod_eq, mem_image, @mem_ball _ _ c] at m op ⊢
  have wm : w ∈ ball (f d z) (e / 2) := by
    simp only [mem_ball] at m ⊢
    specialize @sh ⟨d, z⟩; simp only [Prod.dist_eq, dist_self, Function.uncurry] at sh
    specialize sh (max_lt m.1.2 sp); rw [dist_comm] at sh
    calc dist w (f d z)
      _ ≤ dist w (f c z) + dist (f c z) (f d z) := by bound
      _ < e / 4 + dist (f c z) (f d z) := by linarith [m.2]
      _ ≤ e / 4 + e / 4 := by linarith [sh]
      _ = e / 2 := by ring
  specialize op d m.1.1 wm
  rcases (mem_image _ _ _).mp op with ⟨y, yr, yw⟩
  use⟨d, y⟩
  simp only [yw, and_true, yr, m.1.1]

/-- A trivial lemma used repeatedly below -/
theorem norm_sub_self_lt {z : ℂ} {r : ℝ} (rp : 0 < r) : ‖z - z‖ < r := by
  simp [sub_self, norm_zero, rp]

/-- The parameterized open mapping theorem for analytic `f : ℂ → ℂ → ℂ`:
    `(c,z) ↦ (c, f c z)` sends neighborhoods to neighborhoods if `f` is nontrivial. -/
theorem NontrivialMAnalyticAt.nhds_le_map_nhds_param' {f : ℂ → ℂ → ℂ} {c z : ℂ}
    (n : NontrivialMAnalyticAt (f c) z) (fa : AnalyticAt ℂ (uncurry f) (c, z)) :
    𝓝 (c, f c z) ≤ Filter.map (fun p : ℂ × ℂ ↦ (p.1, f p.1 p.2)) (𝓝 (c, z)) := by
  -- Reduce to a neighborhood of (c,z) on which f is analytic
  rw [Filter.le_map_iff]
  intro s' sn
  generalize hs : s' ∩ {p | AnalyticAt ℂ (uncurry f) p} = s
  have ss : s ⊆ s' := by rw [← hs]; apply inter_subset_left
  replace sn : s ∈ 𝓝 (c, z) := by rw [← hs]; exact Filter.inter_mem sn fa.eventually_analyticAt
  replace fa : AnalyticOnNhd ℂ (uncurry f) s := by rw [← hs]; apply inter_subset_right
  refine Filter.mem_of_superset ?_ (image_mono ss)
  clear ss hs s'
  rcases Metric.mem_nhds_iff.mp sn with ⟨e, ep, es⟩
  -- Find a radius within s where f c is nontrivial
  have er : ∃ r, 0 < r ∧ closedBall (c, z) r ⊆ s ∧ f c z ∉ f c '' sphere z r := by
    have h := n.eventually_ne; contrapose h
    simp only [not_exists, not_not, not_and, not_exists] at h
    simp only [Classical.not_imp, not_not, Filter.eventually_iff, Metric.mem_nhds_iff, not_exists,
      not_subset, mem_ofPred, not_and]
    intro r rp; specialize h (min (e/2) (r/2)) ?_ ?_
    · bound
    · exact _root_.trans (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _)
        (half_lt_self ep))) es
    · rcases (mem_image _ _ _).mp h with ⟨w, ws, wz⟩
      use w; refine ⟨?_, ?_, wz⟩
      · exact Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self rp))
          (Metric.sphere_subset_closedBall ws)
      · contrapose ws
        simp only [ws, Metric.mem_sphere, dist_self]
        exact ne_of_lt (by bound)
  rcases er with ⟨r, rp, rs, fr⟩
  -- Get a lower bound of f c '' sphere z r, then extend to a neighborhood of c
  have fc : ContinuousOn (fun w ↦ ‖f c w - f c z‖) (sphere z r) := by
    apply ContinuousOn.norm; refine ContinuousOn.sub ?_ continuousOn_const
    apply fa.along_snd.continuousOn.mono; intro x xs; apply rs
    simp only [← closedBall_prod_same, mem_prod_eq]
    use Metric.mem_closedBall_self rp.le, Metric.sphere_subset_closedBall xs
  rcases (isCompact_sphere _ _).exists_isMinOn (NormedSpace.sphere_nonempty.mpr rp.le) fc with
    ⟨x, xs, xm⟩
  generalize he : ‖f c x - f c z‖ = e
  have ep : 0 < e := by
    contrapose fr
    simp only [norm_pos_iff, sub_ne_zero, not_not, mem_image, ← he] at fr ⊢
    use x, xs, fr
  rcases Metric.uniformContinuousOn_iff.mp
      ((isCompact_closedBall _ _).uniformContinuousOn_of_continuous (fa.continuousOn.mono rs))
      (e / 4) (by linarith) with
    ⟨t, tp, ft⟩
  have ef : ∀ d, d ∈ ball c (min t r) → ∀ w, w ∈ sphere z r → e / 2 ≤ ‖f d w - f d z‖ := by
    intro d dt w wr
    simp only [Complex.dist_eq, Prod.forall, mem_closedBall, Prod.dist_eq, max_le_iff, max_lt_iff,
      Function.uncurry, and_imp] at ft
    simp only [mem_ball, Complex.dist_eq, lt_min_iff] at dt
    have a1 : ‖f d w - f c w‖ ≤ e / 4 :=
      (ft d w dt.2.le (le_of_eq (mem_sphere_iff_norm.mp wr)) c w (norm_sub_self_lt rp).le (le_of_eq (mem_sphere_iff_norm.mp wr)) dt.1
        (norm_sub_self_lt tp)).le
    have a2 : ‖f c z - f d z‖ ≤ e / 4 := by
      refine (ft c z (norm_sub_self_lt rp).le (norm_sub_self_lt rp).le d z
          dt.2.le (norm_sub_self_lt rp).le ?_ (norm_sub_self_lt tp)).le
      rw [← neg_sub, norm_neg]; exact dt.1
    calc ‖f d w - f d z‖
      _ = ‖f c w - f c z + (f d w - f c w) + (f c z - f d z)‖ := by ring_nf
      _ ≥ ‖f c w - f c z + (f d w - f c w)‖ - ‖f c z - f d z‖ := by bound
      _ ≥ ‖f c w - f c z‖ - ‖f d w - f c w‖ - ‖f c z - f d z‖ := by bound
      _ ≥ e - e / 4 - e / 4 := by rw [← he] at a1 a2 ⊢; exact sub_le_sub (sub_le_sub (xm wr) a1) a2
      _ = e / 2 := by ring
  -- Apply the partially effective parameterized open mapping theorem
  have ss : ball c (min t r) ×ˢ closedBall z r ⊆ s := by
    refine _root_.trans ?_ rs; rw [← closedBall_prod_same]; apply prod_mono_left
    exact _root_.trans (Metric.ball_subset_ball (min_le_right _ _)) Metric.ball_subset_closedBall
  exact Filter.mem_of_superset ((fa.mono ss).ball_subset_image_closedBall_param rp (half_pos ep)
    (Metric.ball_mem_nhds _ (by bound)) ef) (image_mono ss)

/-- If `f : S → T` is nontrivial, it is nontrivial when written in charts -/
theorem NontrivialMAnalyticAt.inCharts {f : S → T} {z : S} (n : NontrivialMAnalyticAt f z) :
    NontrivialMAnalyticAt (fun w ↦ extChartAt I (f z) (f ((extChartAt I z).symm w)))
      (extChartAt I z z) := by
  use (mAnalyticAt_iff_of_boundaryless.mp n.mAnalyticAt).2.mAnalyticAt I I
  have c := n.nonconst; contrapose c
  simp only [Filter.not_frequently, not_not, ← map_extChartAt_nhds_of_boundaryless z,
    Filter.eventually_map] at c ⊢
  apply c.mp
  apply ((isOpen_extChartAt_source z).eventually_mem (mem_extChartAt_source (I := I) z)).mp
  apply (n.mAnalyticAt.continuousAt.eventually_mem (extChartAt_source_mem_nhds (I := I) (f z))).mp
  refine .of_forall fun w fm m fn ↦ ?_
  rw [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ (mem_extChartAt_source z)] at fn
  exact ((PartialEquiv.injOn _).eq_iff fm (mem_extChartAt_source _)).mp fn

/-- The local open mapping theorem, manifold version: if `f : S → T` is nontrivial,
    `f` sends neighborhoods to neighborhoods.  This is a manifold version of
    `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`. -/
theorem NontrivialMAnalyticAt.nhds_eq_map_nhds [IsManifold I ω T] {f : S → T} {z : S}
    (n : NontrivialMAnalyticAt f z) : 𝓝 (f z) = Filter.map f (𝓝 z) := by
  refine le_antisymm ?_ n.mAnalyticAt.continuousAt
  generalize hg : (fun x ↦ extChartAt I (f z) (f ((extChartAt I z).symm x))) = g
  have ga : AnalyticAt ℂ g (extChartAt I z z) := by
    rw [← hg]; exact (mAnalyticAt_iff_of_boundaryless.mp n.mAnalyticAt).2
  cases' ga.eventually_constant_or_nhds_le_map_nhds with h h
  · contrapose h; clear h; simp only [Filter.not_eventually]
    apply n.inCharts.nonconst.mp; simp only [← hg, Ne, imp_self, Filter.eventually_true]
  · -- The open mapping theorem for g = c ∘ f ∘ c⁻¹ (with charts c) is
    --   𝓝 (g (c z)) ≤ map g (𝓝 (c z))
    -- We have
    --   map c⁻¹ (𝓝 (g (c z))) ≤ map c⁻¹ (map g (𝓝 (c z))  -- Monotonicity of map
    --   𝓝 (c⁻¹ (g (c z))) ≤ map (c' ∘ g ∘ c) (𝓝 z)        -- Charts map 𝓝 to 𝓝
    --   𝓝 (f z) ≤ map f (𝓝 z)                             -- Congruence
    simp only [← map_extChartAt_nhds_of_boundaryless z, Filter.map_map] at h
    replace h := @Filter.map_mono _ _ (extChartAt I (f z)).symm _ _ h
    simp only [← hg] at h; rw [PartialEquiv.left_inv _ (mem_extChartAt_source z)] at h
    simp only [extChartAt_symm_map_nhds' I (f z), Filter.map_map, Function.comp_def] at h
    have e : (fun w ↦ (extChartAt I (f z)).symm
        (extChartAt I (f z) (f ((extChartAt I z).symm (extChartAt I z w))))) =ᶠ[𝓝 z] f := by
      apply ((isOpen_extChartAt_source z).eventually_mem (mem_extChartAt_source (I := I) z)).mp
      apply (n.mAnalyticAt.continuousAt.eventually_mem
        (extChartAt_source_mem_nhds (I := I) (f z))).mp
      refine .of_forall fun w fm m ↦ ?_
      simp only [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ fm]
    rw [Filter.map_congr e] at h; exact h

/-- Special case of `Filter.prod_map_map_eq` where the first map is `id` -/
theorem Filter.prod_map_id_map_eq {A B C : Type} {f : Filter A} {g : Filter B} {m : B → C} :
    f ×ˢ (Filter.map m g) = Filter.map (fun p : A × B ↦ (p.1, m p.2)) (f ×ˢ g) :=
  Filter.prod_map_map_eq (f₁ := f) (f₂ := g) (m₁ := id) (m₂ := m)

/-- The local open mapping theorem, parameterized manifold version: if `f : ℂ → S → T` is
    nontrivial, then `(c,z) ↦ (c, f c z)` sends neighborhoods to neighborhoods. -/
theorem NontrivialMAnalyticAt.nhds_eq_map_nhds_param [IsManifold I ω T] {f : ℂ → S → T}
    {c : ℂ} {z : S} (n : NontrivialMAnalyticAt (f c) z)
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) :
    𝓝 (c, f c z) = Filter.map (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) (𝓝 (c, z)) := by
  refine le_antisymm ?_ (continuousAt_fst.prodMk fa.continuousAt)
  generalize hg : (fun e x ↦ extChartAt I (f c z) (f e ((extChartAt I z).symm x))) = g
  have ga : AnalyticAt ℂ (uncurry g) (c, extChartAt I z z) := by
    rw [← hg]; exact (mAnalyticAt_iff_of_boundaryless.mp fa).2
  have gn : NontrivialMAnalyticAt (g c) (extChartAt I z z) := by rw [← hg]; exact n.inCharts
  have h := gn.nhds_le_map_nhds_param' ga
  -- We follow the 𝓝 ≤ 𝓝 argument of nontrivial_mAnalytic_at.nhds_le_map_nhds
  -- above, but a bit more complicated due to the parameterization.
  simp only [nhds_prod_eq, ← map_extChartAt_nhds_of_boundaryless z, Filter.map_map,
    Filter.prod_map_id_map_eq] at h
  replace h := @Filter.map_mono _ _ (fun p : ℂ × ℂ ↦ (p.1, (extChartAt I (f c z)).symm p.2)) _ _ h
  simp only [← hg] at h; rw [PartialEquiv.left_inv _ (mem_extChartAt_source z)] at h
  have pe := Filter.prod_map_id_map_eq (f := 𝓝 c) (g := 𝓝 (extChartAt I (f c z) (f c z)))
    (m := fun x ↦ (extChartAt I (f c z)).symm x)
  rw [extChartAt_symm_map_nhds', ←nhds_prod_eq] at pe
  refine _root_.trans (le_of_eq pe) (_root_.trans h (le_of_eq ?_)); clear h pe
  rw [←nhds_prod_eq, Filter.map_map]; apply Filter.map_congr
  apply ((isOpen_extChartAt_source (c, z)).eventually_mem
    (mem_extChartAt_source (I := II) (c, z))).mp
  apply (fa.continuousAt.eventually_mem (extChartAt_source_mem_nhds (I := I) (f c z))).mp
  refine .of_forall fun ⟨e, w⟩ fm m ↦ ?_
  simp only [uncurry, extChartAt_prod, PartialEquiv.prod_source, mem_prod_eq] at fm m
  simp only [Function.comp, PartialEquiv.left_inv _ m.2, PartialEquiv.left_inv _ fm]

end
end Ray_Ray_Manifold_OpenMapping

-- ===== Ray.Dynamics.Postcritical =====
section Ray_Ray_Dynamics_Postcritical
/-!
## Postcritical points

A postcritical point w.r.t. a superattracting fixpoint `a` of `f : ℂ → S → S` is a point `z`
with potential smaller than any critical point of `f` other than `a` (in this file we assume
`OnePotential s`, so `a` is the only preimage of `a` under `f`).  Postcritical points are
special because the Böttcher can be analytically continued through all of them, which we
show in `Grow.lean`.  Roughly, this is true because

1. Postcritical points stay postcritical under iteration, since iteration decreases `s.potential`
2. Thus, postcritical points are never precritical
3. Postcritical points form a simply connected set (indeed, a disk), so analytic continuation works

This file has definitions and continuity results only, which are then used by `Grow.lean`,
`Ray.lean`, and `Bottcher.lean` to construct the analytic continuations.
-/

open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z z0 z1 : S}
variable {d n : ℕ}
variable {s : Super f d a}

/-- `s.ps c` is nonempty (since it contains 1) -/
theorem Super.nonempty_ps (s : Super f d a) : (s.ps c).Nonempty :=
  ⟨1, by simp only [Super.ps, mem_ofPred, true_or]⟩

/-- `s.ps c` is compact -/
theorem Super.compact_ps (s : Super f d a) [OnePreimage s] [T2Space S] :
    IsCompact (s.ps c) := by
  have pc : Continuous (s.potential c) := (Continuous.potential s).along_snd
  have c1 : IsCompact {(1 : ℝ)} := isCompact_singleton
  convert c1.union ((s.isClosed_critical_not_a.snd_preimage c).isCompact.image pc)
  apply Set.ext; intro p
  simp only [mem_ofPred, Super.ps, mem_singleton_iff, mem_union, mem_image, Ne, ←
    s.potential_eq_zero_of_onePreimage c]
  apply or_congr_right; constructor
  intro ⟨p0, z, e, c⟩; rw [← e] at p0; exact ⟨z, ⟨c, p0⟩, e⟩
  intro ⟨z, ⟨c, p0⟩, e⟩; rw [e] at p0; exact ⟨p0, z, e, c⟩

/-- `s.ps c` has positive members only, since we exclude the critical point at `a` -/
theorem Super.ps_pos (s : Super f d a) (c : ℂ) {p : ℝ} (m : p ∈ s.ps c) : 0 < p := by
  cases' m with m m; simp only [m, zero_lt_one]; rcases m with ⟨p0, z, e, c⟩; rw [← e] at p0 ⊢
  exact p0.symm.lt_of_le s.potential_nonneg

/-- `s.ps c` is bounded below -/
theorem Super.bddBelow_ps (s : Super f d a) : BddBelow (s.ps c) :=
  bddBelow_def.mpr ⟨0, fun _ m ↦ (s.ps_pos c m).le⟩

/-- `s.ps c` attains its infimum -/
theorem Super.mem_ps (s : Super f d a) (c : ℂ) [OnePreimage s] [T2Space S] : s.p c ∈ s.ps c := by
  rw [← s.compact_ps.isClosed.closure_eq]; exact csInf_mem_closure s.nonempty_ps s.bddBelow_ps

/-- `s.p c` is positive, since it is the infimum of a compact set of positive numbers -/
theorem Super.p_pos (s : Super f d a) (c : ℂ) [OnePreimage s] [T2Space S] : 0 < s.p c :=
  s.ps_pos c (s.mem_ps c)

/-- `s.p c ≤ 1` -/
@[bound] theorem Super.p_le_one (s : Super f d a) : s.p c ≤ 1 :=
  csInf_le s.bddBelow_ps (Or.inl rfl)

/-- `s.p` doesn't jump down locally as a function of `c`.

    Intuitively, this is because if `c` varies a little bit, critical points might suddenly
    disappear (if we're at the furthest `c` extent of a critical surface) but they can't suddenly
    appear as the set of critical points is closed. -/
theorem Super.lowerSemicontinuous_p (s : Super f d a) [OnePreimage s] [T2Space S] :
    LowerSemicontinuous s.p := by
  intro c p h; contrapose h
  simp only [not_lt, Filter.not_eventually] at h ⊢
  -- Add a bit of slack
  apply le_of_forall_gt
  intro q' pq'
  rcases exists_between pq' with ⟨q, pq, qq⟩; refine lt_of_le_of_lt ?_ qq; clear qq pq' q'
  by_cases q1 : 1 ≤ q; exact _root_.trans s.p_le_one q1
  simp only [not_le] at q1
  -- Use closedness of the set of non-a critical points
  set t : Set (ℂ × S) := {x | s.potential x.1 x.2 ≤ q ∧ Critical (f x.1) x.2 ∧ x.2 ≠ a}
  have ct : IsClosed t :=
    (isClosed_le (Continuous.potential s) continuous_const).inter s.isClosed_critical_not_a
  set u := Prod.fst '' t
  have cu : IsClosed u := isClosedMap_fst_of_compactSpace _ ct
  suffices m : c ∈ u by
    rcases(mem_image _ _ _).mp m with ⟨⟨c', z⟩, ⟨zp, zc, za⟩, cc⟩
    simp only at cc za zc zp; simp only [cc] at za zc zp; clear cc c'
    simp only [Ne, ← s.potential_eq_zero_of_onePreimage c] at za
    refine _root_.trans (csInf_le s.bddBelow_ps ?_) zp; right; use za, z, rfl, zc
  refine Filter.Frequently.mem_of_closed ?_ cu
  refine h.mp (.of_forall fun e h ↦ ?_)
  rcases exists_lt_of_csInf_lt s.nonempty_ps (lt_of_le_of_lt h pq) with ⟨r, m, rq⟩
  cases' m with m m; linarith; rcases m with ⟨r0, z, zr, zc⟩
  rw [← zr, Ne, s.potential_eq_zero_of_onePreimage] at r0; rw [mem_image]
  refine ⟨(e, z), ⟨?_, zc, r0⟩, rfl⟩; simp only [zr]; exact rq.le

/-- Postcritical points are in the basin, since they have `s.potential c z < s.p c ≤ 1` -/
theorem Postcritical.basin (p : Postcritical s c z) : (c, z) ∈ s.basin :=
  s.potential_lt_one_iff.mp (lt_of_lt_of_le p s.p_le_one)

/-- If `s.potential c z0 ≤ s.potential c z1` and `z1` is postcritical, then `z0` is postcritical -/
theorem Postscritical.mono (p : Postcritical s c z1) (z01 : s.potential c z0 ≤ s.potential c z1) :
    Postcritical s c z0 :=
  lt_of_le_of_lt z01 p

/-- Postcritical points are not precritical, since iteration decreases potential (except for `a`) -/
theorem Postcritical.not_precritical (p : Postcritical s c z) (p0 : s.potential c z ≠ 0) :
    ¬Precritical (f c) z := by
  contrapose p; simp only [Postcritical, not_lt] at p ⊢
  rcases p with ⟨n, p⟩; trans s.potential c ((f c)^[n] z)
  · refine csInf_le s.bddBelow_ps (Or.inr ⟨?_, (f c)^[n] z, rfl, p⟩)
    simp only [s.potential_eqn_iter]; exact pow_ne_zero _ p0
  · simp only [s.potential_eqn_iter]
    exact pow_le_of_le_one s.potential_nonneg s.potential_le_one (pow_ne_zero _ s.d0)

/-- Postcritical points are not precritical, since iteration decreases potential (except for `a`) -/
theorem Postcritical.not_precritical' (p : Postcritical s c z) (za : z ≠ a) [OnePreimage s] :
    ¬Precritical (f c) z := by
  apply p.not_precritical; simp only [Ne, s.potential_eq_zero_of_onePreimage]; exact za

/-- `s.post` is open -/
theorem Super.isOpen_post (s : Super f d a) [OnePreimage s] [T2Space S] : IsOpen s.post := by
  set f := fun x : ℂ × S ↦ s.p x.1 - s.potential x.1 x.2
  have fc : LowerSemicontinuous f :=
    (s.lowerSemicontinuous_p.comp continuous_fst).add
      (Continuous.potential s).neg.lowerSemicontinuous
  have e : s.post = f ⁻¹' Ioi 0 :=
    Set.ext fun _ ↦ by
      simp only [Super.post, mem_ofPred, Postcritical, mem_preimage, mem_Ioi, sub_pos, f]
  rw [e]; exact fc.isOpen_preimage _

/-- Postcritical holds locally -/
theorem Postcritical.eventually (p : Postcritical s c z) [OnePreimage s] [T2Space S] :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z), Postcritical s p.1 p.2 := by
  refine (s.isOpen_post.eventually_mem ?_).mp (.of_forall fun _ m ↦ m); exact p

/-- Postcritical points are in the basin -/
theorem Super.post_basin (s : Super f d a) : s.post ⊆ s.basin := fun _ m ↦
  Postcritical.basin m

/-- `p ∈ s.post` means `p` is postcritical -/
theorem Super.postPostcritical (s : Super f d a) {p : ℂ × S} (m : p ∈ s.post) :
    Postcritical s p.1 p.2 := m

/-- `a` is postcritical -/
@[simp] lemma Super.post_a (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ) :
    (c, a) ∈ s.post := by
  simp only [Super.post, Postcritical, s.potential_a, mem_ofPred]; exact s.p_pos c

/-- `f` maps `s.post` into itself -/
theorem Super.stays_post (s : Super f d a) {p : ℂ × S} (m : p ∈ s.post) :
    (p.1, f p.1 p.2) ∈ s.post := by
  rcases p with ⟨c, z⟩; simp only [Super.post, mem_ofPred, Postcritical, s.potential_eqn]
  exact lt_of_le_of_lt (pow_le_of_le_one s.potential_nonneg s.potential_le_one s.d0) m

/-- Iterating `f` maps `s.post` into itself -/
theorem Super.iter_stays_post (s : Super f d a) {p : ℂ × S} (m : p ∈ s.post) (n : ℕ) :
    (p.1, (f p.1)^[n] p.2) ∈ s.post := by
  induction' n with n h; simp only [Function.iterate_zero_apply]; exact m
  simp only [Function.iterate_succ_apply']; exact s.stays_post h

/-- We can get from `s.basin` to `s.post` with enough iterations -/
theorem Super.basin_post (s : Super f d a) [OnePreimage s] [T2Space S]
    (m : (c, z) ∈ s.basin) : ∃ n, (c, (f c)^[n] z) ∈ s.post := by
  rcases tendsto_atTop_nhds.mp (s.basin_attracts m) {z | (c, z) ∈ s.post} (s.post_a c)
      (s.isOpen_post.snd_preimage c) with ⟨n, h⟩
  specialize h n (le_refl n); simp only [mem_ofPred] at h; use n, h

/-- `s.potential` has postcritical minima only at `z = a` -/
theorem Super.potential_minima_only_a (s : Super f d a) [OnePreimage s] [T2Space S]
    (p : Postcritical s c z) (m : ∀ᶠ w in 𝓝 z, s.potential c z ≤ s.potential c w) : z = a := by
  contrapose m; simp only [Filter.not_eventually, not_le]
  have nice := s.nice_nz p.basin
  set f : S → ℂ := s.bottcherNearIter (s.nz c z) c
  have o : 𝓝 (f z) = Filter.map f (𝓝 z) := (nontrivialMAnalyticAt_of_mfderiv_ne_zero
      (nice.contMDiffAt_bottcherNearIter (le_refl _)).along_snd
      (s.bottcherNearIter_mfderiv_ne_zero (nice.mfderiv_ne_zero (le_refl _) (le_refl _))
        (p.not_precritical ((s.potential_ne_zero _).mpr m)))).nhds_eq_map_nhds
  have e : ∃ᶠ x : ℂ in 𝓝 (f z), ‖x‖ < ‖f z‖ := by
    apply frequently_smaller
    contrapose m
    rwa [nice.bottcherNear_eq_zero (le_refl _), s.preimage_eq] at m
  rw [o, Filter.frequently_map] at e
  apply e.mp
  filter_upwards [nice.norm_bottcherNear' (le_refl _)] with w wp lt
  simp only [f, Super.bottcherNearIter, nice.norm_bottcherNear (le_refl _), wp] at lt
  rwa [pow_lt_pow_iff_left₀ (by bound) (by bound) (by simp [s.d0])] at lt

end
end Ray_Ray_Dynamics_Postcritical

-- ===== Ray.Manifold.LocalInj =====
section Ray_Ray_Manifold_LocalInj
/-!
## Nonzero derivative analytic functions are locally injective

This is a straightforward consequence of the inverse function theorem.  We also prove
parameterized versions, where `f : ℂ → S → T`.
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

/-- Nonzero derivative analytic functions are locally injective -/
theorem ContMDiffAt.local_inj {f : S → T} {z : S}
    (fa : ContMDiffAt I I ω f z) (nc : mfderiv I I f z ≠ 0) :
    ∀ᶠ p : S × S in 𝓝 (z, z), f p.1 = f p.2 → p.1 = p.2 := by
  rcases complex_inverse_fun' fa nc with ⟨g, ga, gf, fg⟩
  have n : NontrivialMAnalyticAt g (f z) := by
    rw [← gf.self_of_nhds] at fa
    refine (NontrivialMAnalyticAt.anti ?_ fa ga).2
    exact (nontrivialMAnalyticAt_id _).congr (Filter.EventuallyEq.symm fg)
  have o := n.nhds_eq_map_nhds; rw [gf.self_of_nhds] at o
  simp only [nhds_prod_eq, o, Filter.prod_map_map_eq, Filter.eventually_map]
  refine (fg.prod_mk fg).mp (.of_forall ?_); intro ⟨x, y⟩ ⟨ex, ey⟩ h
  simp only at ex ey; simp only [ex, ey] at h; simp only [h]

/-- Nonzero derivative analytic functions are locally injective, parameterized version.
    Specifically, we show local injectivity of `(c,z) ↦ (c, f c z)`. -/
theorem ContMDiffAt.local_inj'' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (nc : mfderiv I I (f c) z ≠ 0) :
    ∀ᶠ p : (ℂ × S) × ℂ × S in 𝓝 ((c, z), (c, z)),
      p.1.1 = p.2.1 → f p.1.1 p.1.2 = f p.2.1 p.2.2 → p.1 = p.2 := by
  rcases complex_inverse_fun fa nc with ⟨g, ga, gf, fg⟩
  have n : NontrivialMAnalyticAt (g c) (f c z) := by
    have e : (c, z) = (c, g c (f c z)) := by rw [gf.self_of_nhds]
    rw [e] at fa
    refine (NontrivialMAnalyticAt.anti ?_ fa.along_snd ga.along_snd).2
    refine (nontrivialMAnalyticAt_id _).congr ?_
    refine ((continuousAt_const.prodMk continuousAt_id).eventually fg).mp (.of_forall ?_)
    exact fun _ e ↦ e.symm
  have o := n.nhds_eq_map_nhds_param ga; rw [gf.self_of_nhds] at o; simp only at o
  rw [nhds_prod_eq, o]; simp only [Filter.prod_map_map_eq, Filter.eventually_map]
  refine (fg.prod_mk fg).mp (.of_forall ?_); intro ⟨x, y⟩ ⟨ex, ey⟩ h1 h2
  simp only at h1; simp only [h1] at ex ey h2 ⊢; simp only [ex, ey] at h2; simp only [h2]

/-- Nonzero derivative analytic functions are locally injective, parameterized version.
    Specifically, we show local injectivity of `(c,z) ↦ (c, f c z)`. -/
theorem ContMDiffAt.local_inj' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (nc : mfderiv I I (f c) z ≠ 0) :
    ∀ᶠ p : ℂ × S × S in 𝓝 (c, z, z), f p.1 p.2.1 = f p.1 p.2.2 → p.2.1 = p.2.2 := by
  set g : ℂ × S × S → (ℂ × S) × ℂ × S := fun p ↦ ((p.1, p.2.1), (p.1, p.2.2))
  have t : Tendsto g (𝓝 (c, z, z)) (𝓝 ((c, z), (c, z))) := by
    apply Continuous.continuousAt; apply Continuous.prodMk
    · exact continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    · exact continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  refine (t.eventually (fa.local_inj'' nc)).mp (.of_forall ?_)
  intro ⟨e, x, y⟩ inj fe; exact (Prod.ext_iff.mp (inj rfl fe)).2

end
end Ray_Ray_Manifold_LocalInj

-- ===== Ray.Manifold.Nonseparating =====
section Ray_Ray_Manifold_Nonseparating
/-!
## Sets that don't separate open sets when they are removed

Given `t : Set X`, `Nonseparating t` means that removing `t` from any connected open set
does not disconnect the set.  The simplest case is a single point in more than one real
dimension (or in at least one complex dimension), but we also need `line ×ˢ point` in two
complex dimensions.
-/

open Complex
open Metric (ball mem_ball)
open OneDimension
open Set
open scoped Real Topology
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {Y : Type} [TopologicalSpace Y]
variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- A sufficient condition on `t` such that removing it from a connected open set does not
    disconnect the set -/
structure Nonseparating (t : Set X) : Prop where
  dense : Dense (tᶜ)
  loc : ∀ x u, x ∈ t → u ∈ 𝓝 x → ∃ c, c ⊆ u \ t ∧ c ∈ 𝓝[tᶜ] x ∧ IsPreconnected c

/-- `univ ×ˢ t` is nonseparating if `t` is -/
theorem Nonseparating.univ_prod [LocallyConnectedSpace X] {t : Set Y} (n : Nonseparating t) :
    Nonseparating ((univ : Set X) ×ˢ t) := by
  have e : ((univ : Set X) ×ˢ t)ᶜ = univ ×ˢ tᶜ := by
    apply Set.ext; intro ⟨a, x⟩; rw [mem_compl_iff]
    simp only [prodMk_mem_set_prod_eq, mem_univ, mem_compl_iff, true_and]
  constructor; · rw [e]; exact dense_univ.prod n.dense
  · intro ⟨a, x⟩ u m un; simp only [mem_prod_eq, mem_univ, true_and] at m
    rcases mem_nhds_prod_iff.mp un with ⟨u0, n0, u1, n1, uu⟩
    rcases n.loc x u1 m n1 with ⟨c1, cs1, cn1, cp1⟩
    rcases locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp (by infer_instance) a u0 n0 with
      ⟨c0, cs0, co0, cm0, cc0⟩
    use c0 ×ˢ c1; refine ⟨?_, ?_, ?_⟩
    · intro ⟨b, y⟩ m'; simp only [mem_prod_eq, mem_sdiff, mem_univ, true_and] at m' ⊢
      refine ⟨?_, (cs1 m'.2).2⟩; apply uu; use cs0 m'.1, (cs1 m'.2).1
    · rw [e, nhdsWithin_prod_eq, nhdsWithin_univ]; exact Filter.prod_mem_prod (co0.mem_nhds cm0) cn1
    · exact cc0.isPreconnected.prod cp1

/-- Nonseparation in a manifold is the same as nonseparation in each chart -/
theorem Nonseparating.complexManifold {t : Set S}
    (h : ∀ z, Nonseparating ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' t)) :
    Nonseparating t :=
  { dense := by
      rw [dense_iff_inter_open]; intro u uo ⟨z, m⟩
      by_cases zt : z ∉ t; use z, m, zt
      simp only [not_not] at zt
      generalize hv : (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' u = v
      have vo : IsOpen v := by
        rw [← hv]
        exact (continuousOn_extChartAt_symm z).isOpen_inter_preimage (isOpen_extChartAt_target z) uo
      have vn : v.Nonempty := by
        use extChartAt I z z
        simp only [mem_inter_iff, mem_extChartAt_target, true_and, mem_preimage,
          PartialEquiv.left_inv _ (mem_extChartAt_source z), m, ← hv]
      rcases dense_iff_inter_open.mp (h z).dense v vo vn with ⟨y, m⟩
      use(extChartAt I z).symm y
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, not_and, ← hv] at m
      rcases m with ⟨⟨ym, yu⟩, yt⟩
      simp only [mem_inter_iff, yu, true_and, mem_compl_iff]; exact yt ym
    loc := by
      intro z u zt un
      have m : extChartAt I z z ∈ (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' t := by
        simp only [mem_inter_iff, mem_extChartAt_target z, true_and, mem_preimage,
          PartialEquiv.left_inv _ (mem_extChartAt_source z), zt]
      have n : (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' u ∈ 𝓝 (extChartAt I z z) := by
        apply Filter.inter_mem
        exact (isOpen_extChartAt_target z).mem_nhds (mem_extChartAt_target z)
        exact extChartAt_preimage_mem_nhds un
      rcases (h z).loc _ _ m n with ⟨c, cs, cn, cp⟩
      have e : (extChartAt I z).source ∩ extChartAt I z ⁻¹' c = (extChartAt I z).symm '' c := by
        apply Set.ext; intro x; simp only [mem_inter_iff, mem_preimage, mem_image]; constructor
        · intro ⟨xz, xc⟩; refine ⟨_, xc, ?_⟩; simp only [PartialEquiv.left_inv _ xz]
        · intro ⟨y, yc, yx⟩; rw [← yx]
          have xc := cs yc; simp only [mem_sdiff, mem_inter_iff, mem_preimage] at xc
          have yz := xc.1.1; use PartialEquiv.map_target _ yz
          simp only [PartialEquiv.right_inv _ yz, yc]
      use(extChartAt I z).source ∩ extChartAt I z ⁻¹' c; refine ⟨?_, ?_, ?_⟩
      · intro x xm; simp only [mem_inter_iff, mem_preimage] at xm; rcases xm with ⟨xz, xc⟩
        replace xc := cs xc
        simp only [mem_sdiff, mem_inter_iff, mem_preimage, PartialEquiv.map_source _ xz, true_and,
          PartialEquiv.left_inv _ xz] at xc
        exact xc
      · rw [e]; convert Filter.image_mem_map cn
        have ee : ⇑(extChartAt I z).symm = (extChartAt' I z).symm := rfl
        rw [ee, (extChartAt' I z).symm.map_nhdsWithin_eq (mem_extChartAt_target z), ← ee]
        simp only [extChartAt', OpenPartialHomeomorph.symm_source,
          PartialEquiv.left_inv _ (mem_extChartAt_source z), compl_inter, inter_union_distrib_left,
          inter_compl_self, empty_union]
        apply nhdsWithin_eq_nhdsWithin (mem_extChartAt_source z)
          (isOpen_extChartAt_source (I := I) z)
        apply Set.ext; intro x
        simp only [mem_inter_iff, mem_compl_iff, mem_image, mem_preimage]; constructor
        · intro ⟨xt, xz⟩; refine ⟨⟨extChartAt I z x, ?_⟩, xz⟩
          simp only [PartialEquiv.left_inv _ xz, xt, PartialEquiv.map_source _ xz, not_false_iff,
            and_self_iff]
        · intro ⟨⟨y, ⟨⟨yz, yt⟩, yx⟩⟩, _⟩
          simp only [← yx, yt, PartialEquiv.map_target _ yz, not_false_iff, true_and]
      · rw [e]; apply cp.image; apply (continuousOn_extChartAt_symm z).mono
        exact _root_.trans cs (_root_.trans sdiff_subset inter_subset_left) }

/-- A sufficient condition on `t` for `s \ t` to be preconnected, for `s` open and preconnected.
    Roughly, `t` has empty interior and there are arbitrarily small connected rings around each
    `x ∈ t`. -/
theorem IsPreconnected.open_diff {s t : Set X} (sc : IsPreconnected s) (so : IsOpen s)
    (ts : Nonseparating t) : IsPreconnected (s \ t) := by
  rw [isPreconnected_iff_subset_of_disjoint] at sc ⊢
  intro u v uo vo suv duv
  generalize hf : (fun u : Set X ↦ u ∪ {x | x ∈ s ∧ x ∈ t ∧ ∀ᶠ y in 𝓝[tᶜ] x, y ∈ u}) = f
  have mono : ∀ u, u ⊆ f u := by rw [← hf]; exact fun _ ↦ subset_union_left
  have fopen : ∀ {u}, IsOpen u → IsOpen (f u) := by
    intro u o; rw [isOpen_iff_eventually]; intro x m
    by_cases xu : x ∈ u
    · rw [← hf]
      exact (o.eventually_mem xu).mp (.of_forall fun q m ↦ subset_union_left m)
    by_cases xt : x ∉ t
    · contrapose xu; clear xu
      simp only [mem_union, mem_ofPred, xt, false_and, and_false, or_false, ← hf] at m
      exact m
    simp only [not_not] at xt
    have n := m
    simp only [mem_union, xt, xu, false_or, true_and, mem_ofPred,
      eventually_nhdsWithin_iff, ← hf] at n
    refine (so.eventually_mem n.1).mp (n.2.eventually_nhds.mp (.of_forall fun y n m ↦ ?_))
    by_cases yt : y ∈ t
    simp only [mem_union, mem_ofPred, eventually_nhdsWithin_iff, ← hf]; right; use m, yt, n
    exact mono _ (n.self_of_nhds yt)
  have mem : ∀ {x u c}, x ∈ s → x ∈ t → c ∈ 𝓝[tᶜ] x → c ⊆ u → x ∈ f u := by
    intro x u c m xt cn cu; rw [← hf]; right; use m, xt
    simp only [Filter.eventually_iff, ofPred_mem_eq]; exact Filter.mem_of_superset cn cu
  have cover : s ⊆ f u ∪ f v := by
    intro x m
    by_cases xt : x ∉ t; exact union_subset_union (mono _) (mono _) (suv (mem_sdiff_of_mem m xt))
    simp only [not_not] at xt
    rcases ts.loc x s xt (so.mem_nhds m) with ⟨c, cst, cn, cp⟩
    have d := inter_subset_inter_left (u ∩ v) cst; rw [duv, subset_empty_iff] at d
    cases' isPreconnected_iff_subset_of_disjoint.mp cp u v uo vo (_root_.trans cst suv) d with cu cv
    exact subset_union_left (mem m xt cn cu)
    exact subset_union_right (mem m xt cn cv)
  have fdiff : ∀ {u}, f u \ t ⊆ u := by
    intro u x m; simp only [mem_sdiff, mem_union, mem_ofPred, ← hf] at m
    simp only [m.2, false_and, and_false, or_false, not_false_iff, and_true] at m
    exact m
  have fnon : ∀ {x u}, IsOpen u → x ∈ f u → ∀ᶠ y in 𝓝[tᶜ] x, y ∈ u := by
    intro x u o m; simp only [mem_union, mem_ofPred, ← hf] at m
    cases' m with xu m; exact (o.eventually_mem xu).filter_mono nhdsWithin_le_nhds; exact m.2.2
  have disj : s ∩ (f u ∩ f v) = ∅ := by
    contrapose duv; simp only [← ne_eq, ← nonempty_iff_ne_empty] at duv ⊢
    rcases duv with ⟨x, m⟩; simp only [mem_inter_iff] at m
    have b := ((so.eventually_mem m.1).filter_mono nhdsWithin_le_nhds).and
      ((fnon uo m.2.1).and (fnon vo m.2.2))
    simp only [eventually_nhdsWithin_iff] at b
    rcases eventually_nhds_iff.mp b with ⟨n, h, no, xn⟩
    rcases ts.dense.exists_mem_open no ⟨_, xn⟩ with ⟨y, yt, yn⟩
    use y; simp only [mem_inter_iff, mem_sdiff, ← mem_compl_iff]; specialize h y yn yt
    exact ⟨⟨h.1,yt⟩,h.2.1,h.2.2⟩
  cases' sc (f u) (f v) (fopen uo) (fopen vo) cover disj with su sv
  left; exact _root_.trans (sdiff_subset_sdiff_left su) fdiff
  right; exact _root_.trans (sdiff_subset_sdiff_left sv) fdiff

/-- ∅ is nonseparating -/
theorem Nonseparating.empty : Nonseparating (∅ : Set X) :=
  { dense := by simp only [compl_empty, dense_univ]
    loc := by simp only [mem_empty_iff_false, IsEmpty.forall_iff, forall_const, imp_true_iff] }

/-- Punctured complex balls are preconnected -/
theorem IsPreconnected.ball_diff_center {a : ℂ} {r : ℝ} : IsPreconnected (ball a r \ {a}) := by
  by_cases rp : r ≤ 0; simp only [Metric.ball_eq_empty.mpr rp, empty_sdiff]
  exact isPreconnected_empty
  simp only [not_le] at rp
  have e : ball a r \ {a} =
      (fun p : ℝ × ℝ ↦ a + p.1 * Complex.exp (p.2 * Complex.I)) '' Ioo 0 r ×ˢ univ := by
    apply Set.ext; intro z
    simp only [mem_sdiff, mem_ball, Complex.dist_eq, mem_singleton_iff, mem_image, Prod.exists,
      mem_prod_eq, mem_Ioo, mem_univ, and_true]
    constructor
    · intro ⟨zr, za⟩
      use ‖z - a‖, Complex.arg (z - a)
      simp only [norm_pos_iff, Ne, Complex.norm_mul_exp_arg_mul_I, add_sub_cancel, sub_eq_zero, za,
        zr, not_false_iff, and_true]
    · intro ⟨s, t, ⟨s0, sr⟩, e⟩
      simp only [← e, add_sub_cancel_left, norm_mul, Complex.norm_real, abs_of_pos s0,
        Complex.norm_exp_ofReal_mul_I, mul_one, sr, true_and, add_eq_left, mul_eq_zero,
        Complex.exp_ne_zero, or_false, Complex.ofReal_eq_zero, Real.norm_eq_abs]
      exact s0.ne'
  rw [e]; apply IsPreconnected.image; exact isPreconnected_Ioo.prod isPreconnected_univ
  apply Continuous.continuousOn; continuity

/-- `{z}ᶜ` is nonseparating in `ℂ` -/
theorem Complex.nonseparating_singleton (a : ℂ) : Nonseparating ({a} : Set ℂ) :=
  { dense := by
      rw [dense_iff_inter_open]; intro u uo ⟨z, m⟩
      by_cases za : z ≠ a
      · use z; use m; exact za
      simp only [not_not] at za; rw [za] at m; clear za z
      rcases Metric.isOpen_iff.mp uo a m with ⟨r, rp, rs⟩
      use a + r / 2
      simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, add_eq_left, div_eq_zero_iff,
        Complex.ofReal_eq_zero, or_false, rp.ne', not_false_iff, and_true, two_ne_zero]
      apply rs
      simp only [mem_ball, dist_self_add_left, norm_div, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_two, abs_of_pos rp, half_lt_self rp]
    loc := by
      intro z u m n; simp only [mem_singleton_iff] at m; simp only [m] at n ⊢; clear m z
      rcases Metric.mem_nhds_iff.mp n with ⟨r, rp, rs⟩
      use ball a r \ {a}; refine ⟨sdiff_subset_sdiff_left rs, ?_, IsPreconnected.ball_diff_center⟩
      exact sdiff_mem_nhdsWithin_compl (Metric.ball_mem_nhds _ rp) _ }

/-- `{z}ᶜ` is nonseparating in 1D complex manifolds -/
theorem AnalyticManifold.nonseparating_singleton (a : S) : Nonseparating ({a} : Set S) := by
  apply Nonseparating.complexManifold; intro z
  by_cases az : a ∈ (extChartAt I z).source
  · convert Complex.nonseparating_singleton (extChartAt I z a)
    simp only [eq_singleton_iff_unique_mem, mem_inter_iff, PartialEquiv.map_source _ az, true_and,
      mem_preimage, mem_singleton_iff, PartialEquiv.left_inv _ az]
    intro x ⟨m, e⟩; simp only [← e, PartialEquiv.right_inv _ m]
  · convert Nonseparating.empty
    simp only [eq_empty_iff_forall_notMem, mem_inter_iff, mem_preimage, mem_singleton_iff, not_and]
    intro x m; contrapose az; rw [← az]
    exact PartialEquiv.map_target _ m

/-- Removing a point in a complex manifold `S` leaves it locally connected -/
theorem IsPreconnected.open_diff_singleton {s : Set S} (sc : IsPreconnected s) (so : IsOpen s)
    (a : S) : IsPreconnected (s \ {a}) :=
  IsPreconnected.open_diff sc so (AnalyticManifold.nonseparating_singleton a)

/-- Removing a line in `ℂ × S` leaves it locally connected -/
theorem IsPreconnected.open_diff_line {s : Set (ℂ × S)} (sc : IsPreconnected s) (so : IsOpen s)
    (a : S) : IsPreconnected (s \ {p | p.2 = a}) := by
  apply IsPreconnected.open_diff sc so
  have e : {p : ℂ × S | p.2 = a} = univ ×ˢ {a} := by
    apply Set.ext; intro ⟨c, z⟩
    simp only [mem_prod_eq, mem_ofPred, mem_univ, true_and, mem_singleton_iff]
  rw [e]; exact Nonseparating.univ_prod (AnalyticManifold.nonseparating_singleton _)

end
end Ray_Ray_Manifold_Nonseparating

-- ===== Ray.Misc.Continuation =====
section Ray_Ray_Misc_Continuation
/-!
## Continuation of a function from a convex set to its closure

We give an abstract version of "analytic continuation" from a convex set to its compact closure,
assuming that local continuation is possible at each boundary point.  We do not refer to analytic
functions directly at all: instead we speak of functions which everywhere satisfy a predicate
`p : (E → α) → E → Prop` where `E` is a normed space and `α : Type`.

Convexity is used only to guarantee a "good open cover" in the sense of
https://ncatlab.org/nlab/show/good+open+cover: a family of neighborhoods such that intersections
of neighborhoods are contractable.  Since our base set `s` is convex, we can use balls as good
neighborhoods, and all intersections are convex and thus contractable.

It would be better to define good neighborhoods directly and show that nice spaces have them,
but this may require a lot of machinery to cover manifolds in particular: the nLab page uses
the existence of Riemannian metrics.
-/

open Classical
open Filter (Tendsto atTop)
open Metric (ball closedBall isOpen_ball mem_ball mem_ball_self closedBall_zero)
open Set
open scoped Real Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : Type} {p : (E → α) → E → Prop} {s : Set E} {f : E → α} {z : E}

-- Continuation of a functional equation from an open convex set to its closure
section Continuation

/-- Information we need to continue a function from a convex set `s` to `closure s`, while
    preserving local properties of the function.  Such properties are represented by an abstract
    `p : (E → α) → E → Prop`, where `p f x` means `f` is a valid germ at `x`. -/
structure Base (p : (E → α) → E → Prop) (s : Set E) (f : E → α) : Prop where
  /-- The base set is convex -/
  convex : Convex ℝ s
  /-- Its closure is compact, so that we can stitch together finitely many local continuations -/
  compact : IsCompact (closure s)
  /-- `p f x` is a local property of `f` near `x` -/
  congr : ∀ {f g x}, p f x → f =ᶠ[𝓝 x] g → p g x
  /-- `f` is valid near each `x ∈ s` -/
  start : ∀ᶠ x in 𝓝ˢ s, p f x
  /-- Given `x ∈ closure s`, we can continue `f` to a neighorhood of `x` -/
  point : ∀ {x}, x ∈ closure s → ∃ g, (∀ᶠ z in 𝓝 x, p g z) ∧ ∃ᶠ z in 𝓝 x, z ∈ s ∧ g z = f z
  /-- If `f0, f1` are valid on an open preconnected set, and match somewhere,
      they match everywhere -/
  unique : ∀ {f0 f1 : E → α} {t : Set E}, IsOpen t → IsPreconnected t →
    (∀ x, x ∈ t → p f0 x) → (∀ x, x ∈ t → p f1 x) → (∃ x, x ∈ t ∧ f0 x = f1 x) → EqOn f0 f1 t

/-- There is a ball around each `x ∈ closure s` with an associated defined `g` -/
lemma Base.ball (b : Base p s f) (x : closure s) :
    ∃ g r, 0 < r ∧ (∀ z, z ∈ ball (x : E) r → p g z) ∧ g =ᶠ[𝓝ˢ (s ∩ ball (x : E) r)] f := by
  rcases x with ⟨x, m⟩; simp only
  rcases b.point m with ⟨g, pg, e⟩
  rcases Metric.eventually_nhds_iff_ball.mp pg with ⟨r, rp, pg⟩
  rcases Filter.frequently_iff.mp e (Metric.ball_mem_nhds _ rp) with ⟨y, yb, ys, e⟩
  use g, r, rp, fun z zr ↦ pg z zr
  simp only [Filter.EventuallyEq, Filter.eventually_iff, mem_nhdsSet_iff_forall]
  intro z ⟨zs, zr⟩; simp only [← Filter.eventually_iff]
  have n : {z | p g z ∧ p f z} ∈ 𝓝ˢ (s ∩ Metric.ball x r) := by
    refine Filter.inter_mem ?_ ?_
    · exact nhdsSet_mono inter_subset_right (Filter.mem_of_superset isOpen_ball.mem_nhdsSet_self pg)
    · exact nhdsSet_mono inter_subset_left b.start
  rcases local_preconnected_nhdsSet (b.convex.inter (convex_ball _ _)).isPreconnected n with
    ⟨u, uo, iu, up, uc⟩
  have eq := b.unique uo uc (fun _ m ↦ (up m).1) (fun _ m ↦ (up m).2) ⟨y, iu ⟨ys, yb⟩, e⟩
  exact eq.eventuallyEq_of_mem (uo.mem_nhds (iu ⟨zs, zr⟩))

/-- A particular `g` that continues `f` near `x` -/
def Base.g (b : Base p s f) (x : closure s) : E → α :=
  choose (b.ball x)

/-- The radius on which `g` is valid around `x` -/
def Base.r (b : Base p s f) (x : closure s) : ℝ :=
  choose (choose_spec (b.ball x))

/-- The radius is positive -/
lemma Base.rp (b : Base p s f) (x : closure s) : 0 < b.r x :=
  (choose_spec (choose_spec (b.ball x))).1

/-- `g` is valid on `ball x r`-/
lemma Base.gp (b : Base p s f) (x : closure s) (m : z ∈ Metric.ball (x : E) (b.r x)) :
    p (b.g x) z :=
  (choose_spec (choose_spec (b.ball x))).2.1 _ m

/-- `g` matches `f` where they are both defined -/
lemma Base.gf (b : Base p s f) (x : closure s) :
    b.g x =ᶠ[𝓝ˢ (s ∩ Metric.ball (x : E) (b.r x))] f :=
  (choose_spec (choose_spec (b.ball x))).2.2

/-- There exists a finite subcover of the `g` balls -/
lemma Base.exists_cover (b : Base p s f) :
    ∃ c : Finset (closure s), closure s ⊆ ⋃ (x) (_ : x ∈ c), Metric.ball (x : E) (b.r x) := by
  refine b.compact.elim_finite_subcover (fun x : closure s ↦ Metric.ball (x : E) (b.r x))
    (fun _ ↦ isOpen_ball) ?_
  intro x m; exact mem_iUnion_of_mem ⟨x, m⟩ (mem_ball_self (b.rp ⟨x, m⟩))

/-- Choose a finite subcover of the `g` balls -/
def Base.c (b : Base p s f) : Finset (closure s) :=
  choose b.exists_cover

/-- The union of our chosen finite set of `g` balls -/
def Base.t (b : Base p s f) : Set E :=
  ⋃ (x) (_ : x ∈ b.c), Metric.ball (x : E) (b.r x)

/-- Map a point in the union of our ball cover to one ball that contains it -/
def Base.y (b : Base p s f) (m : z ∈ b.t) : closure s :=
  choose (mem_iUnion.mp m)

lemma Base.yt (b : Base p s f) (m : z ∈ b.t) : z ∈ Metric.ball (b.y m : E) (b.r (b.y m)) := by
  simp only [Base.t, Base.y, mem_iUnion] at m ⊢; exact choose_spec (choose_spec m)

lemma Base.ot (b : Base p s f) : IsOpen b.t :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_ball

theorem Base.cover (b : Base p s f) : closure s ⊆ b.t :=
  choose_spec b.exists_cover

/-- Given two intersecting balls centered in `closure s`, their intersection touches `s` -/
theorem Convex.inter_ball (c : Convex ℝ s) (x0 x1 : closure s) {r0 r1 : ℝ} (r0p : 0 < r0)
    (r1p : 0 < r1) (ne : ∃ z, z ∈ ball (x0 : E) r0 ∩ ball (x1 : E) r1) :
    ∃ w, w ∈ s ∩ ball (x0 : E) r0 ∩ ball (x1 : E) r1 := by
  rcases x0 with ⟨x0, m0⟩; rcases x1 with ⟨x1, m1⟩; simp only
  have x01 : ‖x1 - x0‖ < r0 + r1 := by
    rcases ne with ⟨z, m0, m1⟩; simp only [mem_ball, dist_eq_norm] at m0 m1
    calc ‖x1 - x0‖
      _ = ‖z - x0 - (z - x1)‖ := by abel_nf
      _ ≤ ‖z - x0‖ + ‖z - x1‖ := (norm_sub_le _ _)
      _ < r0 + r1 := add_lt_add m0 m1
  have sub : ∀ (x : E) {a b : ℝ}, 0 < a → 0 < b → (a / (a + b)) • x - x = -((b / (a + b)) • x) := by
    intro x a b ap bp; have rnz := (add_pos ap bp).ne'
    calc (a / (a + b)) • x - x
      _ = (a / (a + b) - (a + b) / (a + b)) • x := by simp only [one_smul, sub_smul, div_self rnz]
      _ = -((b / (a + b)) • x) := by rw [← sub_div, sub_add_cancel_left, neg_div, neg_smul]
  have le : ∀ {a : ℝ}, 0 < a → a / (r0 + r1) * ‖x1 - x0‖ < a := by
    intro a ap; apply lt_of_lt_of_le (mul_lt_mul_of_pos_left x01 (div_pos ap (add_pos r0p r1p)))
    rw [div_mul_cancel₀ _ (add_pos r0p r1p).ne']
  have e : ∀ᶠ p : E × E in 𝓝 (x0, x1),
      (r1 / (r0 + r1)) • p.1 + (r0 / (r0 + r1)) • p.2 ∈ ball x0 r0 ∩ ball x1 r1 := by
    refine ContinuousAt.eventually_mem ?_ ((isOpen_ball.inter isOpen_ball).mem_nhds ?_)
    · exact ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)).continuousAt
    · simp only [mem_inter_iff, mem_ball, dist_eq_norm, ← sub_add_eq_add_sub _ x0 _,
        add_sub_assoc _ _ x1]
      nth_rw 1 [add_comm r0 r1]; simp only [sub _ r0p r1p, sub _ r1p r0p]
      simp only [add_comm r1 r0, neg_add_eq_sub, ← sub_eq_add_neg, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_div, abs_of_pos r0p, abs_of_pos r1p, abs_of_pos (add_pos r0p r1p),
        norm_sub_rev (x0 : E) x1]
      use le r0p, le r1p
  have f : ∃ᶠ p : E × E in 𝓝 (x0, x1), p.1 ∈ s ∧ p.2 ∈ s := by
    simp only [nhds_prod_eq]; rw [Prod.frequently (p := fun x ↦ x ∈ s) (q := fun x ↦ x ∈ s)]
    use mem_closure_iff_frequently.mp m0, mem_closure_iff_frequently.mp m1
  rcases(f.and_eventually e).exists with ⟨⟨z0, z1⟩, ⟨m0, m1⟩, m⟩
  refine ⟨_, ⟨?_, m.1⟩, m.2⟩
  apply c m0 m1; bound; bound
  simp only [← add_div, add_comm r1 r0, div_self (add_pos r0p r1p).ne']

/-- Our full continuation `u` throughout `closure s` -/
def Base.u (b : Base p s f) : E → α := fun z ↦
  if m : z ∈ b.t then b.g (b.y m) z else f z

/-- The continuation `u` is equal to each `g` -/
theorem Base.ug (b : Base p s f) (x : closure s) :
    EqOn b.u (b.g x) (b.t ∩ Metric.ball (x : E) (b.r x)) := by
  intro z ⟨zt, m⟩; simp only [Base.u, zt, dif_pos]
  refine b.unique (isOpen_ball.inter isOpen_ball)
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    (fun _ m ↦ b.gp _ (inter_subset_left m)) (fun _ m ↦ b.gp _ (inter_subset_right m))
    ?_ ⟨b.yt zt, m⟩
  rcases b.convex.inter_ball (b.y zt) x (b.rp _) (b.rp _) ⟨_, ⟨b.yt zt, m⟩⟩ with ⟨w, m⟩
  exact ⟨w, ⟨m.1.2, m.2⟩, _root_.trans ((b.gf _).self_of_nhdsSet ⟨m.1.1, m.1.2⟩)
    ((b.gf x).self_of_nhdsSet ⟨m.1.1, m.2⟩).symm⟩

/-- `u` is equal to our original `f` -/
theorem Base.uf (b : Base p s f) : b.u =ᶠ[𝓝ˢ s] f := by
  simp only [Filter.EventuallyEq, Filter.eventually_iff, mem_nhdsSet_iff_forall]
  intro z m; simp only [← Filter.eventually_iff]
  set x : closure s := ⟨z, subset_closure m⟩
  have zs : z ∈ Metric.ball (x : E) (b.r x) := mem_ball_self (b.rp x)
  have ug := (b.ug x).eventuallyEq_of_mem ((b.ot.inter isOpen_ball).mem_nhds
    ⟨b.cover (subset_closure m), zs⟩)
  exact ug.trans ((b.gf x).filter_mono (nhds_le_nhdsSet ⟨m, zs⟩))

/-- `u` is valid in `𝓝ˢ (closure s)` -/
theorem Base.up (b : Base p s f) : ∀ᶠ z in 𝓝ˢ (closure s), p b.u z := by
  apply Filter.eventually_of_mem (b.ot.mem_nhdsSet.mpr b.cover)
  intro x m; refine b.congr (b.gp (b.y m) (b.yt m)) ?_
  exact ((b.ug _).eventuallyEq_of_mem ((b.ot.inter isOpen_ball).mem_nhds ⟨m, b.yt m⟩)).symm

/-!
### Continuation throughout a ball, starting from a point
-/

variable [ProperSpace E]
variable {c : E} {s' : Set E} {r t : ℝ}

/-- Information we need to continue a function throughout an open ball. -/
structure Continuation [NormedSpace ℝ E] [ProperSpace E] (p : (E → α) → E → Prop)
    (c : E) (r : ℝ) (fs : E → α) : Prop where
  /-- The radius is positive -/
  pos : 0 < r
  /-- `p f x` is a local property of `f` near `x` -/
  congr : ∀ {f g x}, p f x → f =ᶠ[𝓝 x] g → p g x
  /-- The seed `fs` is valid near `x` -/
  start : ∀ᶠ y in 𝓝 c, p fs y
  /-- Given `f` valid on convex `s`, we can continue `f` to a neighorhood of any `x ∈ closure s` -/
  point : ∀ {f t x}, 0 < t → t < r → (∀ᶠ x in 𝓝ˢ (ball c t), p f x) → x ∈ closedBall c t →
    ∃ g, (∀ᶠ z in 𝓝 x, p g z) ∧ ∃ᶠ z in 𝓝 x, z ∈ ball c t ∧ g z = f z
  /-- If `f0, f1` are valid on an open preconnected set, and match somewhere,
      they match everywhere -/
  unique : ∀ {f0 f1 : E → α} {t : Set E}, IsOpen t → IsPreconnected t →
    (∀ x, x ∈ t → p f0 x) → (∀ x, x ∈ t → p f1 x) → (∃ x, x ∈ t ∧ f0 x = f1 x) → EqOn f0 f1 t

namespace Continuation

variable {fs : E → α}
variable {i : Continuation p c r fs}
attribute [bound_forward] Continuation.pos

/-- We can grow out through a set `t` -/
def Grow (_ : Continuation p c r fs) (s : Set E) : Prop :=
  ∃ f, f c = fs c ∧ ∀ᶠ x in 𝓝ˢ s, p f x

/-- Grow is monotonic -/
lemma Grow.mono (g : i.Grow s) (sub : s' ⊆ s) : i.Grow s' := by
  obtain ⟨f, e, h⟩ := g
  exact ⟨f, e, h.filter_mono (nhdsSet_mono sub)⟩

/-- We can grow through a small open ball -/
lemma grow_small (i : Continuation p c r fs) : ∃ t > 0, t ≤ r ∧ i.Grow (ball c t) := by
  obtain ⟨t,t0,g⟩ := Metric.eventually_nhds_iff_ball.mp i.start
  refine ⟨min t r, by bound, by bound, fs, ?_⟩
  simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal]
  aesop

/-- If we can grow up to `ball c r`, we can grow through the closure -/
lemma Grow.closed (g : i.Grow (ball c t)) (tr : t < r) : i.Grow (closedBall c t) := by
  by_cases t0 : t ≤ 0
  · obtain ⟨u,u0,ur,g⟩ := i.grow_small
    exact g.mono (Metric.closedBall_subset_ball (by linarith))
  simp only [not_le] at t0
  obtain ⟨f, e, pf⟩ := g
  have b : Base p (ball c t) f := {
    convex := convex_ball _ _
    compact := by
      apply (isCompact_closedBall c r).of_isClosed_subset isClosed_closure
      simp only [closure_ball _ t0.ne', Metric.closedBall_subset_closedBall tr.le]
    congr := i.congr
    start := pf
    point := fun {x m} ↦ i.point t0 tr pf (by simpa [closure_ball _ t0.ne'] using m)
    unique := i.unique }
  refine ⟨b.u, ?_, ?_⟩
  · exact (b.uf.self_of_nhdsSet (mem_ball_self t0)).trans e
  · refine b.up.filter_mono (nhdsSet_mono ?_)
    simp only [closure_ball _ t0.ne', subset_refl]

/-- If we can grow through a closed ball, we can grow through a larger open ball -/
lemma Grow.open (g : i.Grow (closedBall c t)) : ∃ u > t, i.Grow (ball c u) := by
  obtain ⟨f, e, h⟩ := g
  obtain ⟨s',o,sub,h⟩ := eventually_nhdsSet_iff_exists.mp h
  obtain ⟨u,lt,sub'⟩ := exists_ball_superset sub o
  refine ⟨u, lt, f, e, ?_⟩
  simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal]
  intro x m
  exact h x (sub' m)

/-- If we grow up until everything before `t`, we grow to `t` -/
lemma Grow.sup {u : ℕ → ℝ} (mono : Monotone u) (tend : Tendsto u atTop (𝓝 t)) (t0 : 0 < t)
    (grow : ∀ n, i.Grow (ball c (u n))) : i.Grow (ball c t) := by
  have ut : ∀ n, u n ≤ t := fun n ↦ mono.ge_of_tendsto tend n
  have ex : ∀ t' < t, ∃ n, t' < u n := fun t' lt ↦ tend.exists_lt lt
  set n : E → ℕ := fun x ↦ if lt : ‖x - c‖ < t then Nat.find (ex _ lt) else Nat.find (ex 0 t0)
  have u0 : ∀ x, 0 < u (n x) := by
    intro x
    simp only [n]
    split_ifs with lt
    · exact lt_of_le_of_lt (norm_nonneg _) (Nat.find_spec (ex _ lt))
    · exact Nat.find_spec (ex 0 t0)
  have nlt : ∀ x, ‖x - c‖ < t → ‖x - c‖ < u (n x) := by
    intro x lt
    simp only [lt, n]
    exact Nat.find_spec (ex _ lt)
  set fn : E → E → α := fun x ↦ choose (grow (n x))
  have spec : ∀ x, fn x c = fs c ∧ ∀ᶠ y in 𝓝ˢ (ball c (u (n x))), p (fn x) y :=
    fun x ↦ choose_spec (grow (n x))
  set f : E → α := fun x ↦ fn x x
  refine ⟨f, (spec _).1, ?_⟩
  simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal, mem_ball, dist_eq_norm]
  intro x xlt
  apply i.congr (f := fn x) (g := f)
  · specialize spec x
    simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal, mem_ball, dist_eq_norm] at spec
    exact spec.2 x (nlt x xlt)
  · have elt : ∀ᶠ y in 𝓝 x, ‖y - c‖ < u (n x) :=
      ContinuousAt.eventually_lt (f := fun x ↦ ‖x - c‖) (by fun_prop) continuousAt_const (nlt x xlt)
    filter_upwards [elt] with y ylt
    have sx := (spec x).2
    have sy := (spec y).2
    simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal, mem_ball, dist_eq_norm] at sx sy
    refine i.unique (f0 := fn x) (f1 := fn y) (t := ball c (min (u (n x)) (u (n y)))) isOpen_ball
      (convex_ball _ _).isPreconnected ?_ ?_ ⟨c, ?_⟩ ?_
    · intro z m
      apply sx
      simp only [mem_ball, dist_eq_norm, lt_inf_iff] at m
      exact m.1
    · intro z m
      apply sy
      simp only [mem_ball, dist_eq_norm, lt_inf_iff] at m
      exact m.2
    · simp [u0, (spec _).1]
    · have yt := lt_of_lt_of_le ylt (ut _)
      simp only [yt, ↓reduceDIte, mem_ball, dist_eq_norm, lt_inf_iff, ylt, true_and, gt_iff_lt, n]
      simpa using Nat.find_spec (ex _ yt)

/-- We can grow through the whole ball -/
lemma grow : i.Grow (ball c r) := by
  set s : Set ℝ := {t | 0 < t ∧ t ≤ r ∧ i.Grow (ball c t)}
  have above : BddAbove s := bddAbove_def.mpr ⟨r, by aesop⟩
  obtain ⟨t0, t0p, t0r, g0⟩ := i.grow_small
  have start : t0 ∈ s := by aesop
  have ne : s.Nonempty := ⟨t0, start⟩
  have pos : 0 < sSup s := lt_csSup_of_lt above start t0p
  have sup_le : sSup s ≤ r := csSup_le ne (by aesop)
  have down : ∀ a b, 0 < a → a ≤ b → b ∈ s → a ∈ s := by
    intro a b a0 ab bs
    exact ⟨a0, le_trans ab bs.2.1, bs.2.2.mono (Metric.ball_subset_ball ab)⟩
  have self : sSup s ∈ s := by
    obtain ⟨u,mono,tend,grow⟩ := exists_seq_tendsto_sSup ne above
    exact ⟨pos, sup_le, Grow.sup mono tend pos (fun n ↦ (grow n).2.2)⟩
  by_cases sup_lt : sSup s < r
  · obtain ⟨t,sup_t,g⟩ := (self.2.2.closed sup_lt).open
    have lt : sSup s < min t r := by bound
    obtain ⟨u,su,utr⟩ := exists_between lt
    simp only [lt_inf_iff] at utr
    have us : u ∈ s := ⟨by linarith, by linarith, g.mono (Metric.ball_subset_ball utr.1.le)⟩
    linarith [le_csSup above us]
  · simp only [not_lt] at sup_lt
    exact (down r (sSup s) i.pos sup_lt self).2.2

end Continuation
end Continuation
end
end Ray_Ray_Misc_Continuation



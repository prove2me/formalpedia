-- Prove2me | Definitions.Def_ray_riemann_sphere_multibrot
-- name    : ray_riemann_sphere_multibrot
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:11:21.678337+00:00
-- url     : https://prove2.me/theorems/ea31aeee-c008-462e-87c5-8940a65846d1
-- title:
--   ray (10/12): the Riemann sphere and the Multibrot family
-- statement:
--   The Riemann sphere $\widehat{\mathbb{C}} = \mathbb{C} \cup \{\infty\}$ (`OnePoint ℂ`) as a compact complex manifold, with charts at $0$ and $\infty$ and analyticity of $z \mapsto 1/z$. The file defines the Multibrot family $f_c(z) = z^d + c$ extended to $\widehat{\mathbb{C}}$, with a superattracting fixed point at $\infty$. It defines the Multibrot set $M_d = \{c : f_c^{\,n}(c) \not\to \infty\}$ and its exterior $\widehat{\mathbb{C}} \setminus M_d$, the Böttcher map $\Phi(c) = b_c(c)$, and basic escape estimates: $M_d$ is contained in the closed disk of radius $2$, and orbits with large modulus escape.
--
--   This file is part 10 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_bottcher_continuation

/-!
# ray (10/12): the Riemann sphere and the Multibrot family

Part 10 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Misc.Cobounded`
* `Ray.Manifold.RiemannSphere`
* `Ray.Multibrot.D`
* `Ray.Multibrot.Defs`
* `Ray.Multibrot.Basic`
-/

-- ===== Ray.Misc.Cobounded =====
section Ray_Ray_Misc_Cobounded
/-!
## Facts about `Bornology.cobounded`
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Metric (ball closedBall)
open Set
open scoped Topology

variable {α : Type}
variable {X : Type} [NormedAddCommGroup X]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- `Filter.hasBasis_cobounded_norm` but with `r < ‖x‖` instead of `r ≤ ‖x‖` -/
lemma hasBasis_cobounded_norm_lt :
    (cobounded X).HasBasis (fun _ ↦ True) (fun r ↦ {x | r < ‖x‖}) := by
  have b := Filter.hasBasis_cobounded_norm (E := X)
  simp only [Filter.hasBasis_iff, ofPred_subset, true_and] at b ⊢
  intro s
  rw [b s]
  constructor
  all_goals exact fun ⟨r, h⟩ ↦ ⟨r + 1, fun x lt ↦ h x (by linarith)⟩

/-- Characterization of `→ cobounded` convergence -/
theorem tendsto_cobounded {f : α → X} {l : Filter α} :
    Tendsto f l (cobounded X) ↔ ∀ r, ∀ᶠ x in l, r < ‖f x‖ := by
  rw [hasBasis_cobounded_norm_lt.tendsto_right_iff]
  simp only [true_imp_iff, mem_ofPred]

/-- Characterization of `atTop → cobounded` convergence -/
theorem tendsto_atTop_cobounded {f : ℕ → X} :
    Tendsto f atTop (cobounded X) ↔ ∀ r, ∃ N, ∀ n, N ≤ n → r < ‖f n‖ := by
  simpa only [mem_Ici, mem_ofPred_eq, exists_true_left, forall_true_left, true_and] using
    Filter.HasBasis.tendsto_iff (f := f) Filter.atTop_basis hasBasis_cobounded_norm_lt

/-- `cobounded` convergence in terms of norm convergence -/
theorem tendsto_cobounded_iff_norm_tendsto_atTop {f : Filter α} {g : α → X} :
    Tendsto (fun x ↦ g x) f (cobounded X) ↔ Tendsto (fun x ↦ ‖g x‖) f atTop := by
  rw [Filter.atTop_basis_Ioi.tendsto_right_iff]
  simp only [hasBasis_cobounded_norm_lt.tendsto_right_iff, true_imp_iff, mem_ofPred, mem_Ioi]

/-- Characterization of `s ∈ cobounded` -/
theorem mem_cobounded_iff {s : Set X} : s ∈ cobounded X ↔ ∃ r, {x | r < ‖x‖} ⊆ s := by
  simp only [Filter.hasBasis_iff.mp hasBasis_cobounded_norm_lt s, true_and]

/-- Eventually `cobounded` the norm is as large as desired -/
theorem eventually_cobounded (r : ℝ) : ∀ᶠ x : X in cobounded X, r < ‖x‖ := by
  rw [Filter.eventually_iff, mem_cobounded_iff]; use r

/-- Eventually `cobounded` is the same as eventually `𝓝[≠] 0` for `x⁻¹` -/
theorem eventually_cobounded_iff_nhds_zero {p : 𝕜 → Prop} :
    (∀ᶠ x in cobounded 𝕜, p x) ↔ ∀ᶠ x in 𝓝[≠] 0, p x⁻¹ := by
  rw [hasBasis_cobounded_norm_lt.eventually_iff, Metric.nhdsWithin_basis_ball.eventually_iff]
  constructor
  · intro ⟨r,_,h⟩
    refine ⟨(max r 1)⁻¹, by bound, fun x ⟨m,x0⟩ ↦ ?_⟩
    refine @h x⁻¹ ?_
    simp only [Metric.mem_ball, dist_zero_right, mem_compl_iff, mem_singleton_iff, mem_ofPred_eq,
      norm_inv] at m x0 ⊢
    rw [← lt_inv_comm₀ (by bound) (by simpa)] at m
    exact lt_of_le_of_lt (le_max_left _ _) m
  · intro ⟨i,i0,h⟩
    refine ⟨i⁻¹, trivial, fun x m ↦ ?_⟩
    refine inv_inv x ▸ @h x⁻¹ ?_
    simp only [mem_ofPred_eq, mem_inter_iff, Metric.mem_ball, dist_zero_right, norm_inv,
      mem_compl_iff, mem_singleton_iff, inv_eq_zero] at m ⊢
    have x0 : x ≠ 0 := by have : 0 < ‖x‖ := lt_trans (by bound) m; simpa
    rw [← inv_lt_comm₀ i0 (by simpa)]
    exact ⟨m, x0⟩

/-- Convergence `cobounded` is the same as convergence at `0` for the reciprocal function -/
theorem tendsto_cobounded_iff_tendsto_nhds_zero {l : Filter α}
    {f : 𝕜 → α} : Tendsto f (cobounded 𝕜) l ↔ Tendsto (fun x ↦ f x⁻¹) (𝓝[{0}ᶜ] 0) l := by
  rw [Filter.HasBasis.tendsto_left_iff hasBasis_cobounded_norm_lt,
    Metric.nhdsWithin_basis_ball.tendsto_left_iff]
  constructor
  · intro h t tl; rcases h t tl with ⟨r, _, m⟩
    by_cases rp : 0 < r
    · use r⁻¹; simp only [rp, inv_pos, true_and]; intro x xs; refine m ?_
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs
      simp only [← lt_inv_comm₀ (norm_pos_iff.mpr xs.2) rp, xs.1, mem_ofPred_eq, norm_inv]
    · use 1; simp only [zero_lt_one, true_and]; intro x xs; refine m ?_
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs
      simp only [mem_ofPred_eq, norm_inv]; simp only [not_lt] at rp
      exact lt_of_le_of_lt rp (inv_pos.mpr (norm_pos_iff.mpr xs.2))
  · intro h t tl; rcases h t tl with ⟨r, rp, m⟩; use r⁻¹; simp only [true_and]
    intro x xs; simp only [mem_ofPred_eq] at xs
    have m := @m x⁻¹ ?_; · simp only [inv_inv] at m; exact m
    simp only [mem_inter_iff, mem_ball_zero_iff, norm_inv, mem_compl_iff, mem_singleton_iff,
      inv_eq_zero]
    have np : 0 < ‖x‖ := _root_.trans (inv_pos.mpr rp) xs
    simp [inv_lt_comm₀ np rp, xs, norm_pos_iff.mp np]

/-- `⁻¹` tendsto `cobounded` near `0` -/
theorem inv_tendsto_cobounded :
    Tendsto (fun x : 𝕜 ↦ x⁻¹) (𝓝[{(0 : 𝕜)}ᶜ] 0) (cobounded 𝕜) := by
  rw [← tendsto_cobounded_iff_tendsto_nhds_zero (f := fun x : 𝕜 ↦ x)]
  exact Filter.tendsto_id

/-- `⁻¹` tendsto `0` near `cobounded` -/
theorem inv_tendsto_cobounded' :
    Tendsto (fun x : 𝕜 ↦ x⁻¹) (cobounded 𝕜) (𝓝 0) := by
  simp only [tendsto_cobounded_iff_tendsto_nhds_zero, inv_inv]
  exact Filter.tendsto_id.mono_left nhdsWithin_le_nhds

/-- We either tend to infinity or have a cluster point -/
lemma tendsto_cobounded_or_mapClusterPt [ProperSpace X] (f : α → X) (l : Filter α) :
    Tendsto f l (cobounded X) ∨ ∃ z, MapClusterPt z l f := by
  by_cases t : Tendsto f l (cobounded X)
  · exact .inl t
  · simp only [t, false_or]
    simp only [tendsto_cobounded, not_forall, Filter.not_eventually, not_lt,
      ← add_mem_closedBall_iff_norm (a := (0 : X)), zero_add] at t
    obtain ⟨r,t⟩ := t
    have t := IsCompact.exists_mapClusterPt_of_frequently (isCompact_closedBall _ _) t
    obtain ⟨z,m,c⟩ := t
    exact ⟨z,c⟩

lemma eventually_cobounded_lt_norm (r : ℝ) : ∀ᶠ x in cobounded X, r < ‖x‖ := by
  filter_upwards [eventually_cobounded_le_norm (r + 1)]
  intro x le
  linarith

end Ray_Ray_Misc_Cobounded

-- ===== Ray.Manifold.RiemannSphere =====
section Ray_Ray_Manifold_RiemannSphere
/-!
## The Riemann sphere

We give `OnePoint ℂ` the natural analytic manifold structure with two charts,
namely `coe` and `inv ∘ coe`, giving the Riemann sphere `(OnePoint ℂ)`.
-/

open Bornology (cobounded)
open Classical
open Complex
open Filter (Tendsto atTop)
open Function (curry uncurry)
open OneDimension
open Set
open scoped Topology OnePoint
noncomputable section

variable {α : Type}

/-- A left inverse to `coe : ℂ → (OnePoint ℂ)`.
    We put this outside the `RiemannSphere` namespace so that `z.toComplex` works. -/
def OnePoint.toComplex (z : OnePoint ℂ) : ℂ := z.rec 0 id

namespace RiemannSphere

/-- The Riemann sphere, as a complex manifold -/

-- Basic instances for (OnePoint ℂ)
instance : Zero (OnePoint ℂ) := ⟨((0 : ℂ) : (OnePoint ℂ))⟩
instance : Inhabited (OnePoint ℂ) := ⟨0⟩
@[simp] theorem coe_zero : ((0 : ℂ) : (OnePoint ℂ)) = (0 : (OnePoint ℂ)) := rfl
@[simp] theorem coe_eq_coe {z w : ℂ} : (z : (OnePoint ℂ)) = w ↔ z = w := OnePoint.coe_eq_coe
@[simp] theorem coe_eq_zero (z : ℂ) : (z : (OnePoint ℂ)) = (0 : (OnePoint ℂ)) ↔ z = 0 := by
  simp only [← coe_zero, coe_eq_coe]

/-- `coe : ℂ → (OnePoint ℂ)` is injective -/
theorem injective_coe : Function.Injective (fun z : ℂ ↦ (z : (OnePoint ℂ))) := OnePoint.coe_injective

/-- `coe : ℂ → (OnePoint ℂ)` is continuous -/
theorem continuous_coe : Continuous (fun z : ℂ ↦ (z : (OnePoint ℂ))) := OnePoint.continuous_coe

-- Recursion lemmas
@[simp] theorem rec_coe {C : (OnePoint ℂ) → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : (OnePoint ℂ))} (z : ℂ) :
    (z : (OnePoint ℂ)).rec i f = f z := rfl
@[simp] theorem rec_inf {C : (OnePoint ℂ) → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : (OnePoint ℂ))} :
    (∞ : (OnePoint ℂ)).rec i f = i := rfl
theorem map_rec {A B : Sort*} (g : A → B) {f : ℂ → A} {i : A} {z : (OnePoint ℂ)} :
    g (z.rec i f) = (z.rec (g i) (g ∘ f)) := by
  induction z using OnePoint.rec
  · simp only [rec_inf]
  · simp only [rec_coe, Function.comp]

-- ∞ is not 0 or finite
@[simp] theorem inf_ne_coe {z : ℂ} : (∞ : (OnePoint ℂ)) ≠ ↑z := by
  simp only [Ne, OnePoint.infty_ne_coe, not_false_iff]
@[simp] theorem inf_ne_zero : (∞ : (OnePoint ℂ)) ≠ (0 : (OnePoint ℂ)) := by
  have e : (0 : (OnePoint ℂ)) = ((0 : ℂ) : (OnePoint ℂ)) := rfl; rw [e]; exact inf_ne_coe
@[simp] theorem zero_ne_inf : (0 : (OnePoint ℂ)) ≠ (∞ : (OnePoint ℂ)) := inf_ne_zero.symm
@[simp] theorem coe_ne_inf {z : ℂ} : (z : (OnePoint ℂ)) ≠ ∞ := inf_ne_coe.symm
@[simp] theorem coe_eq_inf_iff {z : ℂ} : (z : (OnePoint ℂ)) = ∞ ↔ False := ⟨coe_ne_inf, False.elim⟩

-- Conversion to ℂ, sending ∞ to 0
@[simp] theorem toComplex_coe {z : ℂ} : (z : (OnePoint ℂ)).toComplex = z := by rfl
@[simp] theorem toComplex_inf : (∞ : (OnePoint ℂ)).toComplex = 0 := by rfl
theorem coe_toComplex {z : (OnePoint ℂ)} (h : z ≠ ∞) : ↑z.toComplex = z := by
  induction z using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at h
  · simp only [toComplex_coe]
@[simp] lemma  toComplex_zero : (0 : (OnePoint ℂ)).toComplex = 0 := by rw [← coe_zero, toComplex_coe]
@[simp] lemma toComplex_eq_zero {z : (OnePoint ℂ)} : z.toComplex = 0 ↔ z = 0 ∨ z = ∞ := by
  induction z using OnePoint.rec
  · simp only [toComplex_inf, or_true]
  · simp only [toComplex_coe, coe_eq_zero, OnePoint.coe_ne_infty, or_false]
theorem continuousAt_toComplex {z : ℂ} : ContinuousAt OnePoint.toComplex z := by
  simp only [OnePoint.continuousAt_coe]; exact continuousAt_id
theorem continuousOn_toComplex : ContinuousOn OnePoint.toComplex ({∞}ᶜ) := by
  intro z m; induction z using OnePoint.rec
  · simp only [mem_compl_iff, mem_singleton_iff, not_true] at m
  · exact continuousAt_toComplex.continuousWithinAt

/-- `toComplex` is injective away from `∞` -/
lemma toComplex_inj {z w : (OnePoint ℂ)} (zi : z ≠ (∞ : (OnePoint ℂ))) (wi : w ≠ (∞ : (OnePoint ℂ))) :
    z.toComplex = w.toComplex ↔ z = w := by
  induction' z using OnePoint.rec
  all_goals induction' w using OnePoint.rec
  all_goals simp_all

/-- Inversion in `(OnePoint ℂ)`, interchanging `0` and `∞` -/
def inv (z : (OnePoint ℂ)) : (OnePoint ℂ) := if z = 0 then ∞ else ↑z.toComplex⁻¹
instance : Inv (OnePoint ℂ) := ⟨RiemannSphere.inv⟩
theorem inv_def (z : (OnePoint ℂ)) : z⁻¹ = RiemannSphere.inv z := by rfl
instance : InvolutiveInv (OnePoint ℂ) where
  inv := Inv.inv
  inv_inv := by
    simp_rw [inv_def, inv]; apply OnePoint.rec
    · simp only [inf_ne_zero, toComplex_inf, inv_zero, coe_zero, ite_false, toComplex_zero,
        ite_true]
    · intro z; by_cases z0 : z = 0
      · simp only [z0, coe_zero, toComplex_zero, inv_zero, ite_true, inf_ne_zero, toComplex_inf,
          ite_false]
      · simp only [coe_eq_zero, z0, toComplex_coe, ite_false, inv_eq_zero, inv_inv]
@[simp] lemma inv_zero' : (0 : (OnePoint ℂ))⁻¹ = ∞ := by simp only [inv_def, inv, if_true]
@[simp] lemma inv_inf : ((∞ : (OnePoint ℂ))⁻¹ : (OnePoint ℂ)) = 0 := by simp [inv_def, inv, inf_ne_zero]

theorem inv_coe {z : ℂ} (z0 : z ≠ 0) : (z : (OnePoint ℂ))⁻¹ = ↑(z : ℂ)⁻¹ := by
  simp only [inv_def, inv, z0, toComplex_coe, if_false, coe_eq_zero]
@[simp] lemma inv_eq_inf {z : (OnePoint ℂ)} : z⁻¹ = ∞ ↔ z = 0 := by
  induction z using OnePoint.rec
  · simp only [inv_inf]; exact ⟨Eq.symm, Eq.symm⟩
  · simp only [inv_def, inv, not_not, imp_false, ite_eq_left_iff, OnePoint.coe_ne_infty]
@[simp] lemma inv_eq_zero {z : (OnePoint ℂ)} : z⁻¹ = 0 ↔ z = ∞ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf]
  · simp only [inv_def, inv, toComplex_coe]
    by_cases z0 : (z : (OnePoint ℂ)) = 0; simp only [if_pos, z0, inf_ne_zero, inf_ne_zero.symm]
    simp only [if_neg z0, coe_ne_inf, iff_false]; rw [coe_eq_zero, _root_.inv_eq_zero]
    simpa only [coe_eq_zero] using z0
theorem toComplex_inv {z : (OnePoint ℂ)} : z⁻¹.toComplex = z.toComplex⁻¹ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf, toComplex_zero, toComplex_inf, inv_zero]
  · by_cases z0 : z = 0
    · simp only [z0, coe_zero, inv_zero', toComplex_inf, toComplex_zero, inv_zero]
    · simp only [z0, inv_coe, Ne, not_false_iff, toComplex_coe]

/-- `coe` tends to `∞` `cobounded` -/
theorem coe_tendsto_inf : Tendsto (fun z : ℂ ↦ (z : (OnePoint ℂ))) (cobounded ℂ) (𝓝 ∞) := by
  rw [Filter.tendsto_iff_comap, OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact]
  exact Metric.cobounded_le_cocompact

/-- `coe` tends to `∞` `cobounded`, but without touching `∞` -/
theorem coe_tendsto_inf' : Tendsto (fun z : ℂ ↦ (z : (OnePoint ℂ))) (cobounded _) (𝓝[{∞}ᶜ] ∞) := by
  have e : {(∞ : (OnePoint ℂ))}ᶜ = range (fun z : ℂ ↦ (z : (OnePoint ℂ))) := by
    ext z; induction' z using OnePoint.rec with z
    · simp only [mem_compl_iff, mem_singleton_iff, not_true, mem_range, OnePoint.coe_ne_infty,
        exists_false]
    · simp only [mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true,
        mem_range, coe_eq_coe, exists_eq]
  simp only [e, tendsto_nhdsWithin_range, coe_tendsto_inf]

@[simp] lemma map_some_cobounded : Filter.map OnePoint.some (cobounded ℂ) = 𝓝[{∞}ᶜ] ∞ := by
  rw [@OnePoint.nhdsNE_infty_eq, Metric.cobounded_eq_cocompact, Filter.coclosedCompact_eq_cocompact]

/-- Inversion is continuous -/
theorem continuous_inv : Continuous fun z : (OnePoint ℂ) ↦ z⁻¹ := by
  rw [← continuousOn_univ]; intro z _; apply ContinuousAt.continuousWithinAt
  induction' z using OnePoint.rec with z
  · simp only [OnePoint.continuousAt_infty', Function.comp_def, Filter.coclosedCompact_eq_cocompact,
      inv_inf, ← Metric.cobounded_eq_cocompact]
    have e : ∀ᶠ z : ℂ in cobounded ℂ, ↑z⁻¹ = (↑z : (OnePoint ℂ))⁻¹ := by
      refine (eventually_cobounded 0).mp (.of_forall fun z z0 ↦ ?_)
      simp only [norm_pos_iff] at z0; rw [inv_coe z0]
    apply Filter.Tendsto.congr' e
    exact Filter.Tendsto.comp continuous_coe.continuousAt inv_tendsto_cobounded'
  · simp only [OnePoint.continuousAt_coe, Function.comp_def, inv_def, inv, coe_eq_zero,
      toComplex_coe]
    by_cases z0 : z = 0
    · simp only [z0, ContinuousAt, OnePoint.nhds_infty_eq, if_true,
        Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      simp only [← nhdsNE_sup_pure, Filter.tendsto_sup]
      constructor
      · refine Filter.Tendsto.mono_right ?_ le_sup_left
        apply tendsto_nhdsWithin_congr (f := fun z : ℂ ↦ (↑z⁻¹ : (OnePoint ℂ)))
        · intro z m
          rw [mem_compl_singleton_iff] at m
          simp only [m, ite_false]
        · simp only [map_some_cobounded]
          apply coe_tendsto_inf'.comp
          rw [← @tendsto_cobounded_iff_tendsto_nhds_zero ℂ ℂ _ _ fun z : ℂ ↦ z]
          exact Filter.tendsto_id
      · refine Filter.Tendsto.mono_right ?_ le_sup_right
        simp only [Filter.pure_zero, Filter.tendsto_pure, ite_eq_left_iff, Filter.eventually_zero,
          not_true, IsEmpty.forall_iff]
    · have e : ∀ᶠ w : ℂ in 𝓝 z, (if w = 0 then ∞ else ↑w⁻¹ : (OnePoint ℂ)) = ↑w⁻¹ := by
        refine (continuousAt_id.eventually_ne z0).mp (.of_forall fun w w0 ↦ ?_)
        simp only [Ne, id_eq] at w0; simp only [w0, if_false]
      simp only [continuousAt_congr e]
      exact continuous_coe.continuousAt.comp (tendsto_inv₀ z0)
instance : ContinuousInv (OnePoint ℂ) := ⟨continuous_inv⟩

/-- Inversion as an equivalence -/
def invEquiv : (OnePoint ℂ) ≃ (OnePoint ℂ) where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

/-- Inversion as a homeomorphism -/
def invHomeomorph : (OnePoint ℂ) ≃ₜ (OnePoint ℂ) where
  toEquiv := invEquiv
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv
@[simp] lemma invEquiv_apply (z : (OnePoint ℂ)) : invEquiv z = z⁻¹ := by
  simp only [invEquiv, Equiv.coe_fn_mk]
@[simp] lemma invEquiv_symm : invEquiv.symm = invEquiv := by
  simp only [Equiv.ext_iff, invEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, forall_const]
@[simp] lemma invHomeomorph_apply (z : (OnePoint ℂ)) : invHomeomorph z = z⁻¹ := by
  simp only [invHomeomorph]
  exact invEquiv_apply z
@[simp] lemma invHomeomorph_symm : invHomeomorph.symm = invHomeomorph := Homeomorph.ext (by
  intro x
  show invEquiv.symm x = invEquiv x
  rw [invEquiv_symm])

/-- `coe : ℂ → (OnePoint ℂ)` as an equivalence -/
def coePartialEquiv : PartialEquiv ℂ (OnePoint ℂ) where
  toFun := fun x : ℂ ↦ x
  invFun := OnePoint.toComplex
  source := univ
  target := {∞}ᶜ
  map_source' z _ := by
    simp only [mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty, not_false_iff]
  map_target' z _ := mem_univ _
  left_inv' z _ := toComplex_coe
  right_inv' z m := coe_toComplex m

/-- `coe : ℂ → (OnePoint ℂ)` as a partial homeomorphism.  This is the first chart of `(OnePoint ℂ)`. -/
def coeOpenPartialHomeomorph : OpenPartialHomeomorph ℂ (OnePoint ℂ) where
  toPartialEquiv := coePartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  continuousOn_toFun := continuous_coe.continuousOn
  continuousOn_invFun := continuousOn_toComplex

/-- `inv ∘ coe : ℂ → (OnePoint ℂ)` as a partial homeomorphism.  This is the second chart of `(OnePoint ℂ)`. -/
def invCoeOpenPartialHomeomorph : OpenPartialHomeomorph ℂ (OnePoint ℂ) :=
  coeOpenPartialHomeomorph.trans invHomeomorph.toOpenPartialHomeomorph

@[simp] lemma coePartialEquiv_target : coePartialEquiv.target = {∞}ᶜ := rfl
@[simp] lemma coeOpenPartialHomeomorph_target : coeOpenPartialHomeomorph.target = {∞}ᶜ := by
  simp only [coeOpenPartialHomeomorph, coePartialEquiv_target]
@[simp] lemma invCoeOpenPartialHomeomorph_target : invCoeOpenPartialHomeomorph.target = {0}ᶜ := by
  ext z; simp only [invCoeOpenPartialHomeomorph, OpenPartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    invHomeomorph_symm, coeOpenPartialHomeomorph_target, preimage_compl, univ_inter, mem_compl_iff,
    mem_preimage, invHomeomorph_apply, mem_singleton_iff, inv_eq_inf]
@[simp] lemma coePartialEquiv_apply (z : ℂ) : coePartialEquiv z = ↑z := by rfl
@[simp] lemma coePartialEquiv_symm_apply (z : (OnePoint ℂ)) : coePartialEquiv.symm z = z.toComplex := by
  rfl
@[simp] lemma invCoeOpenPartialHomeomorph_apply (z : ℂ) :
    invCoeOpenPartialHomeomorph z = (z : (OnePoint ℂ))⁻¹ := by rfl
@[simp] lemma invCoeOpenPartialHomeomorph_symm_apply (z : (OnePoint ℂ)) :
    invCoeOpenPartialHomeomorph.symm z = (z⁻¹).toComplex := by rfl

/-- Chart structure for `(OnePoint ℂ)` -/
instance : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {e | e = coeOpenPartialHomeomorph.symm ∨ e = invCoeOpenPartialHomeomorph.symm}
  chartAt z := z.rec invCoeOpenPartialHomeomorph.symm (fun _ ↦ coeOpenPartialHomeomorph.symm)
  mem_chart_source := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        invCoeOpenPartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, inf_ne_zero,
        not_false_eq_true]
    · simp only [rec_coe, OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        coeOpenPartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty,
        not_false_eq_true]
  chart_mem_atlas := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, mem_ofPred_eq, or_true]
    · simp only [rec_coe, mem_ofPred_eq, true_or]

/-- There are just two charts on `(OnePoint ℂ)` -/
theorem two_charts {e : OpenPartialHomeomorph (OnePoint ℂ) ℂ} (m : e ∈ atlas ℂ (OnePoint ℂ)) :
    e = coeOpenPartialHomeomorph.symm ∨ e = invCoeOpenPartialHomeomorph.symm := m

-- Chart simplification lemmas
@[simp] lemma chartAt_coe {z : ℂ} : chartAt ℂ (z : (OnePoint ℂ)) = coeOpenPartialHomeomorph.symm := rfl
@[simp] lemma chartAt_inf : @chartAt ℂ _ (OnePoint ℂ) _ _ ∞ = invCoeOpenPartialHomeomorph.symm := rfl
theorem extChartAt_coe {z : ℂ} : extChartAt I (z : (OnePoint ℂ)) = coePartialEquiv.symm := by
  simp only [coeOpenPartialHomeomorph, extChartAt, OpenPartialHomeomorph.extend, chartAt_coe,
    OpenPartialHomeomorph.symm_toPartialEquiv, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl]
theorem extChartAt_zero : extChartAt I (0 : (OnePoint ℂ)) = coePartialEquiv.symm := by
  simp only [← coe_zero, extChartAt_coe]
theorem extChartAt_inf :
    extChartAt I (∞ : (OnePoint ℂ)) = invEquiv.toPartialEquiv.trans coePartialEquiv.symm := by
  apply PartialEquiv.ext
  · intro z
    simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      OpenPartialHomeomorph.extend, chartAt_inf, OpenPartialHomeomorph.symm_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.coe_trans_symm,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.homeomorph_mk_coe_symm,
      invEquiv_symm, PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, Function.comp_apply]
    show coePartialEquiv.symm (invEquiv.symm z) = coePartialEquiv.symm (invEquiv z)
    rw [invEquiv_symm]
  · intro z
    simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      invEquiv, OpenPartialHomeomorph.extend, chartAt_inf,
      OpenPartialHomeomorph.symm_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.symm_symm,
      PartialEquiv.coe_trans, OpenPartialHomeomorph.coe_toPartialEquiv,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
      PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply, Equiv.coe_fn_symm_mk]
  · simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      OpenPartialHomeomorph.extend, chartAt_inf, OpenPartialHomeomorph.symm_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.symm_source, PartialEquiv.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.homeomorph_mk_coe_symm,
      invEquiv_symm, PartialEquiv.trans_source, Equiv.toPartialEquiv_source,
      Equiv.toPartialEquiv_apply]
    show univ ∩ ⇑invEquiv.symm ⁻¹' coePartialEquiv.target
      = univ ∩ ⇑invEquiv ⁻¹' coePartialEquiv.target
    rw [invEquiv_symm]
theorem extChartAt_inf_apply {x : (OnePoint ℂ)} : extChartAt I ∞ x = x⁻¹.toComplex := by
  simp only [extChartAt_inf, PartialEquiv.trans_apply, coePartialEquiv_symm_apply,
    Equiv.toPartialEquiv_apply, invEquiv_apply]

/-- `(OnePoint ℂ)`'s charts have analytic groupoid structure -/
instance : HasGroupoid (OnePoint ℂ) (contDiffGroupoid ⊤ I) where
  compatible := by
    have e0 : ((fun z : ℂ ↦ (z : (OnePoint ℂ))) ⁻¹' {0})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, coe_eq_zero]
    have e1 : ((fun z : ℂ ↦ (z : (OnePoint ℂ))⁻¹) ⁻¹' {∞})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, inv_eq_inf, coe_eq_zero]
    have a : AnalyticOnNhd ℂ (fun z : ℂ ↦ OnePoint.toComplex (z : (OnePoint ℂ))⁻¹) {0}ᶜ := by
      apply AnalyticOnNhd.congr (f := fun z ↦ z⁻¹)
      · exact isOpen_compl_singleton
      · apply analyticOnNhd_inv
      · intro z z0; simp only [mem_compl_iff, mem_singleton_iff] at z0
        simp only [inv_coe z0, toComplex_coe]
    intro f g fa ga
    simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid, mfld_simps]
    refine ⟨AnalyticOnNhd.contDiffOn ?_ ?_, AnalyticOnNhd.contDiffOn ?_ ?_⟩
    all_goals cases' two_charts fa with fh fh
    all_goals cases' two_charts ga with gh gh
    all_goals try simp [fh, gh, coeOpenPartialHomeomorph, invCoeOpenPartialHomeomorph,
      coePartialEquiv, coeOpenPartialHomeomorph, invHomeomorph, invEquiv, Function.comp_def,
      analyticOnNhd_id, e0, e1, a, uniqueDiffOn_univ]
    all_goals try exact isOpen_compl_singleton.uniqueDiffOn
    all_goals apply IsOpen.uniqueDiffOn
    all_goals convert isOpen_univ
    all_goals aesop

/-- `(OnePoint ℂ)` is an analytic manifold -/
instance : IsManifold I ⊤ (OnePoint ℂ) where

/-- Composing with `coe` turns convergence `cobounded` into convergence to `𝓝 ∞` -/
theorem tendsto_inf_iff_tendsto_cobounded {X : Type} {f : Filter X} {g : X → ℂ} :
    Tendsto (fun x ↦ (g x : (OnePoint ℂ))) f (𝓝 ∞) ↔ Tendsto (fun x ↦ g x) f (cobounded ℂ) := by
  constructor
  · intro t; simp only [Filter.tendsto_iff_comap] at t ⊢
    rw [←Function.comp_def, ←Filter.comap_comap, OnePoint.comap_coe_nhds_infty,
      Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at t
    exact t
  · exact fun h ↦ coe_tendsto_inf.comp h

variable {X : Type} [TopologicalSpace X]
variable {Y : Type} [TopologicalSpace Y]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]

/-- `coe : ℂ → (OnePoint ℂ)` is an open map -/
theorem isOpenMap_coe : IsOpenMap (fun z : ℂ ↦ (z : (OnePoint ℂ))) := by
  intro s o
  have e : (fun z : ℂ ↦ (z : (OnePoint ℂ))) '' s = {∞}ᶜ ∩ OnePoint.toComplex ⁻¹' s := by
    apply Set.ext; intro z
    simp only [mem_image, mem_inter_iff, mem_compl_singleton_iff, mem_preimage]
    constructor
    intro ⟨x, m, e⟩; simp only [← e, toComplex_coe, m, and_true]; exact inf_ne_coe.symm
    intro ⟨n, m⟩; use z.toComplex, m, coe_toComplex n
  rw [e]; exact continuousOn_toComplex.isOpen_inter_preimage isOpen_compl_singleton o

theorem prod_nhds_eq {x : X} {z : ℂ} :
    𝓝 (x, (z : (OnePoint ℂ))) = Filter.map (fun p : X × ℂ ↦ (p.1, ↑p.2)) (𝓝 (x, z)) := by
  refine le_antisymm ?_
    (continuousAt_fst.prodMk (continuous_coe.continuousAt.comp continuousAt_snd))
  apply IsOpenMap.nhds_le; exact IsOpenMap.id.prodMap isOpenMap_coe

theorem mem_inf_of_mem_cobounded {s : Set ℂ} (f : s ∈ cobounded ℂ) :
    (fun z : ℂ ↦ (z : (OnePoint ℂ))) '' s ∪ {∞} ∈ 𝓝 (∞ : (OnePoint ℂ)) := by
  simp only [OnePoint.nhds_infty_eq, Filter.mem_sup, Filter.coclosedCompact_eq_cocompact, ←
    Metric.cobounded_eq_cocompact, Filter.mem_map]
  exact ⟨Filter.mem_of_superset f fun _ m ↦ Or.inl (mem_image_of_mem _ m), Or.inr rfl⟩

theorem prod_mem_inf_of_mem_cobounded {s : Set (X × ℂ)} {x : X} (f : s ∈ 𝓝 x ×ˢ cobounded ℂ) :
    (fun p : X × ℂ ↦ (p.1, (p.2 : (OnePoint ℂ)))) '' s ∪ univ ×ˢ {∞} ∈ 𝓝 (x, (∞ : (OnePoint ℂ))) := by
  rcases Filter.mem_prod_iff.mp f with ⟨t, tx, u, ui, sub⟩
  rw [nhds_prod_eq]
  refine Filter.mem_prod_iff.mpr ⟨t, tx, (fun z : ℂ ↦ (z : (OnePoint ℂ))) '' u ∪ {∞},
    mem_inf_of_mem_cobounded ui, ?_⟩
  intro ⟨y, z⟩ ⟨yt, m⟩
  simp only [mem_prod_eq, mem_image, mem_union, mem_singleton_iff, mem_univ, true_and,
    Prod.ext_iff] at yt m ⊢
  induction' z using OnePoint.rec with z
  · simp only [or_true]
  · simp only [coe_eq_inf_iff, or_false, coe_eq_coe] at m ⊢
    rcases m with ⟨w, wu, wz⟩; refine ⟨⟨y, z⟩, sub (mk_mem_prod yt ?_), rfl, rfl⟩; rw [← wz]
    exact wu

/-- `coe : ℂ → (OnePoint ℂ)` is analytic -/
theorem mAnalytic_coe : ContMDiff I I ⊤ (fun z : ℂ ↦ (z : (OnePoint ℂ))) := by
  rw [mAnalytic_iff_of_boundaryless]; use continuous_coe; intro z
  simp only [extChartAt_coe, extChartAt_eq_refl, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, id_eq]
  rw [← PartialEquiv.invFun_as_coe]
  simp only [coePartialEquiv]
  apply analyticAt_id

/-- `OnePoint.toComplex : (OnePoint ℂ) → ℂ` is analytic except at `∞` -/
theorem mAnalyticAt_toComplex {z : ℂ} :
    ContMDiffAt I I ⊤ (OnePoint.toComplex : (OnePoint ℂ) → ℂ) z := by
  rw [mAnalyticAt_iff_of_boundaryless]
  use continuousAt_toComplex
  simp only [toComplex_coe, extChartAt_coe, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.symm_symm, coePartialEquiv_symm_apply]
  apply analyticAt_id

/-- `OnePoint.toComplex : (OnePoint ℂ) → ℂ` is analytic except at `∞` -/
theorem mAnalyticAt_toComplex' {z : (OnePoint ℂ)} (ne : z ≠ ∞) :
    ContMDiffAt I I ⊤ (OnePoint.toComplex : (OnePoint ℂ) → ℂ) z := by
  induction z using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at ne
  · apply mAnalyticAt_toComplex

/-- Inversion is analytic -/
theorem mAnalytic_inv : ContMDiff I I ⊤ (fun z : (OnePoint ℂ) ↦ z⁻¹) := by
  rw [mAnalytic_iff_of_boundaryless]
  use continuous_inv
  intro z
  induction' z using OnePoint.rec with z
  · simp only [inv_inf, extChartAt_inf, ← coe_zero, extChartAt_coe, Function.comp_def,
      PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
      coePartialEquiv_symm_apply, toComplex_coe, PartialEquiv.coe_trans_symm,
      PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm,
      inv_inv]
    apply analyticAt_id
  · simp only [extChartAt_coe, PartialEquiv.symm_symm, Function.comp_def, coePartialEquiv_apply,
      coePartialEquiv_symm_apply, toComplex_coe]
    by_cases z0 : z = 0
    · simp only [z0, coe_zero, extChartAt_inf, PartialEquiv.trans_apply, coePartialEquiv_symm_apply,
        invEquiv_apply, Equiv.toPartialEquiv_apply, inv_zero', inv_inv, toComplex_coe]
      apply analyticAt_id
    · simp only [inv_coe z0, extChartAt_coe, coePartialEquiv_symm_apply]
      refine (analyticAt_id.inv z0).congr ?_
      refine (continuousAt_id.eventually_ne z0).mp (.of_forall fun w w0 ↦ ?_)
      rw [id] at w0
      simp only [Pi.inv_apply, id, inv_coe w0, toComplex_coe]

/-- Given `f : ℂ → X`, fill in the value at `∞` to get `(OnePoint ℂ) → X` -/
def fill {X : Type} (f : ℂ → X) (y : X) : (OnePoint ℂ) → X := fun z ↦ z.rec y f

/-- Lift `f : ℂ → ℂ` to `(OnePoint ℂ) → (OnePoint ℂ)` by filling in a value at `∞` -/
def lift (f : ℂ → ℂ) (y : (OnePoint ℂ)) : (OnePoint ℂ) → (OnePoint ℂ) := fun z ↦ z.rec y (fun z ↦ f z)

/-- Lift `f : X → ℂ → ℂ` to `X → (OnePoint ℂ) → (OnePoint ℂ)` by filling in a value at `∞` -/
def lift' (f : X → ℂ → ℂ) (y : (OnePoint ℂ)) : X → (OnePoint ℂ) → (OnePoint ℂ) := fun x z ↦ z.rec y (fun z ↦ f x z)

section Fill

variable {f : ℂ → ℂ}
variable {g : α → ℂ → ℂ}
variable {y : (OnePoint ℂ)} {x : α} {z : ℂ}

-- Values of `fill` and `lift` at `coe` and `∞`
@[simp] lemma fill_coe {f : ℂ → α} {y : α} : fill f y z = f z := by rfl
@[simp] lemma fill_inf {f : ℂ → α} {y : α} : fill f y ∞ = y := by rfl
@[simp] lemma lift_coe : lift f y z = ↑(f z) := by rfl
@[simp] lemma lift_coe' : lift' g y x z = ↑(g x z) := by rfl
@[simp] lemma lift_inf : lift f y ∞ = y := by rfl
@[simp] lemma lift_inf' : lift' g y x ∞ = y := by rfl

lemma toComplex_lift' {w : (OnePoint ℂ)} (ne : w ≠ ∞) :
    (lift' g y x w).toComplex = g x w.toComplex := by
  induction w using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at ne
  · simp only [lift', rec_coe, toComplex_coe]

end Fill

variable {f : ℂ → ℂ}
variable {g : X → ℂ → ℂ}
variable {y : (OnePoint ℂ)} {x : X} {z : ℂ}

/-- `lift` in terms of `fill` -/
theorem lift_eq_fill : lift f y = fill (fun z ↦ (f z : (OnePoint ℂ))) y := by rfl

/-- `fill` is continuous at finite values -/
theorem continuousAt_fill_coe {f : ℂ → X} {y : X} (fc : ContinuousAt f z) :
    ContinuousAt (fill f y) z := by
  simp only [OnePoint.continuousAt_coe, Function.comp_def, fill_coe, fc]

/-- `fill` is continuous at `∞` -/
theorem continuousAt_fill_inf {f : ℂ → X} {y : X} (fi : Tendsto f (cobounded ℂ) (𝓝 y)) :
    ContinuousAt (fill f y) ∞ := by
  simp only [OnePoint.continuousAt_infty', Filter.coclosedCompact_eq_cocompact, ←
    Metric.cobounded_eq_cocompact, Function.comp_def, fill_coe, fill_inf, fi]

/-- `fill` is continuous -/
theorem continuous_fill {f : ℂ → X} {y : X} (fc : Continuous f)
    (fi : Tendsto f (cobounded ℂ) (𝓝 y)) : Continuous (fill f y) := by
  rw [continuous_iff_continuousAt]; intro z; induction z using OnePoint.rec
  · exact continuousAt_fill_inf fi
  · exact continuousAt_fill_coe fc.continuousAt

/-- `fill` is analytic at finite values -/
theorem mAnalyticAt_fill_coe [IsManifold I ⊤ T] {f : ℂ → T} {y : T}
    (fa : ContMDiffAt I I ⊤ f z) : ContMDiffAt I I ⊤ (fill f y) z := by
  have e : (fun x : (OnePoint ℂ) ↦ f x.toComplex) =ᶠ[𝓝 ↑z] fill f y := by
    simp only [OnePoint.nhds_coe_eq, Filter.EventuallyEq, Filter.eventually_map, toComplex_coe,
      fill_coe, Filter.eventually_true]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ e.symm
  refine fa.comp_of_eq mAnalyticAt_toComplex ?_
  simp only [toComplex_coe]

/-- `fill` is analytic at `∞` -/
theorem mAnalyticAt_fill_inf [IsManifold I ⊤ T] {f : ℂ → T} {y : T}
    (fa : ∀ᶠ z in cobounded ℂ, ContMDiffAt I I ⊤ f z) (fi : Tendsto f (cobounded ℂ) (𝓝 y)) :
    ContMDiffAt I I ⊤ (fill f y) ∞ := by
  rw [mAnalyticAt_iff_of_boundaryless]
  use continuousAt_fill_inf fi
  simp only [Function.comp_def, extChartAt, OpenPartialHomeomorph.extend, fill, rec_inf,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, chartAt_inf,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_symm,
    OpenPartialHomeomorph.toFun_eq_coe, invCoeOpenPartialHomeomorph_apply,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, invCoeOpenPartialHomeomorph_symm_apply, inv_inf,
    toComplex_zero]
  have e : (fun z : ℂ ↦ chartAt ℂ y (OnePoint.rec y f (↑z)⁻¹)) = fun z : ℂ ↦
      extChartAt I y (if z = 0 then y else f z⁻¹) := by
    funext z; by_cases z0 : z = 0
    · simp only [z0, coe_zero, inv_zero', rec_inf, extChartAt, OpenPartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
        OpenPartialHomeomorph.toFun_eq_coe, if_true]
    · simp only [inv_coe z0, rec_coe, extChartAt, OpenPartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, z0, ite_false,
        OpenPartialHomeomorph.toFun_eq_coe]
  rw [e]; clear e
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · apply (inv_tendsto_cobounded.eventually fa).mp
    apply (inv_tendsto_cobounded.eventually (fi.eventually
      ((isOpen_extChartAt_source y).eventually_mem (mem_extChartAt_source (I := I) y)))).mp
    apply eventually_nhdsWithin_of_forall; intro z z0 m fa
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at z0
    have e : (fun z ↦ extChartAt I y (if z = 0 then y else f z⁻¹)) =ᶠ[𝓝 z]
        fun z ↦ extChartAt I y (f z⁻¹) := by
      refine (continuousAt_id.eventually_ne z0).mp (.of_forall fun w w0 ↦ ?_)
      simp only [Ne, id_eq] at w0; simp only [w0, if_false]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ e
    apply AnalyticAt.differentiableAt; apply ContMDiffAt.analyticAt I I
    refine (contMDiffAt_extChartAt' (extChartAt_source I y ▸ m)).comp _ ?_
    exact fa.comp _ (contMDiffAt_id.inv₀ z0)
  · refine (continuousAt_extChartAt' ?_).comp ?_
    · simp only [if_pos, mem_extChartAt_source]
    · simp only [← continuousWithinAt_compl_self, ContinuousWithinAt]
      apply tendsto_nhdsWithin_congr (f := fun z ↦ f z⁻¹)
      intro z z0; simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at z0
      simp only [z0, if_false]
      exact Filter.Tendsto.comp fi inv_tendsto_cobounded

/-- `fill` is analytic -/
theorem mAnalytic_fill [IsManifold I ⊤ T] {f : ℂ → T} {y : T} (fa : ContMDiff I I ⊤ f)
    (fi : Tendsto f (cobounded ℂ) (𝓝 y)) : ContMDiff I I ⊤ (fill f y) := by
  intro z; induction z using OnePoint.rec
  · exact mAnalyticAt_fill_inf (.of_forall fa) fi
  · exact mAnalyticAt_fill_coe (fa _)

/-- `lift'` is continuous at finite values -/
theorem continuousAt_lift_coe' (gc : ContinuousAt (uncurry g) (x, z)) :
    ContinuousAt (uncurry (lift' g y)) (x, ↑z) := by
  simp only [lift', ContinuousAt, uncurry, rec_coe, OnePoint.nhds_coe_eq, prod_nhds_eq,
    Filter.tendsto_map'_iff, Function.comp_def]
  exact Filter.Tendsto.comp Filter.tendsto_map gc

/-- `lift'` is continuous at `∞` -/
theorem continuousAt_lift_inf' (gi : Tendsto (uncurry g) (𝓝 x ×ˢ cobounded ℂ) (cobounded ℂ)) :
    ContinuousAt (uncurry (lift' g ∞)) (x, ∞) := by
  simp only [ContinuousAt, Filter.Tendsto, Filter.le_def, Filter.mem_map]; intro s m
  simp only [OnePoint.nhds_infty_eq, Filter.coclosedCompact_eq_cocompact, Filter.mem_sup,
    Filter.mem_map, Filter.mem_pure, ← Metric.cobounded_eq_cocompact, lift', rec_inf, uncurry] at m
  simp only [Tendsto] at gi; specialize gi m.1
  simp only [Filter.mem_map, preimage_preimage] at gi
  have e : uncurry (lift' g ∞) ⁻¹' s =
      (fun x : X × ℂ ↦ (x.1, (x.2 : (OnePoint ℂ)))) ''
        ((fun x : X × ℂ ↦ (g x.1 x.2 : (OnePoint ℂ))) ⁻¹' s) ∪ univ ×ˢ {∞} := by
    apply Set.ext; intro ⟨x, z⟩; induction z using OnePoint.rec
    · simp only [mem_preimage, mem_image, mem_union, mem_prod_eq, mem_univ, true_and,
      mem_singleton_iff, or_true, uncurry, lift', rec_inf, m.2]
    · simp only [uncurry, lift', mem_preimage, rec_coe, prod_singleton, image_univ, mem_union,
        mem_image, Prod.ext_iff, coe_eq_coe, Prod.exists, exists_eq_right_right, exists_eq_right,
        mem_range, OnePoint.infty_ne_coe, and_false, exists_false, or_false]
  rw [e]; exact prod_mem_inf_of_mem_cobounded gi

/-- `lift'` is continuous -/
theorem continuous_lift' (gc : Continuous (uncurry g))
    (gi : ∀ x, Tendsto (uncurry g) (𝓝 x ×ˢ cobounded ℂ) (cobounded ℂ)) :
    Continuous (uncurry (lift' g ∞)) := by
  rw [← continuousOn_univ]; intro ⟨x, z⟩ _; apply ContinuousAt.continuousWithinAt
  induction z using OnePoint.rec
  · exact continuousAt_lift_inf' (gi x)
  · exact continuousAt_lift_coe' gc.continuousAt

/-- `lift` is continuous at finite values -/
theorem continuousAt_lift_coe (fc : ContinuousAt f z) : ContinuousAt (lift f y) z :=
  haveI gc : ContinuousAt (uncurry fun _ : Unit ↦ f) ((), z) := by
    refine ContinuousAt.comp fc ?_; exact continuousAt_snd
  (continuousAt_lift_coe' gc).comp (ContinuousAt.prodMk continuousAt_const continuousAt_id)

/-- `lift` is continuous at `∞` -/
theorem continuousAt_lift_inf (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) :
    ContinuousAt (lift f ∞) ∞ :=
  haveI gi : Tendsto (uncurry fun _ : Unit ↦ f) (𝓝 () ×ˢ cobounded ℂ) (cobounded ℂ) :=
    fi.comp Filter.tendsto_snd
  (continuousAt_lift_inf' gi).comp (ContinuousAt.prodMk continuousAt_const continuousAt_id)

/-- `lift` is continuous -/
theorem continuous_lift (fc : Continuous f) (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) :
    Continuous (lift f ∞) := by
  rw [continuous_iff_continuousAt]; intro z; induction z using OnePoint.rec
  · exact continuousAt_lift_inf fi
  · exact continuousAt_lift_coe fc.continuousAt

/-- `lift` is analytic at finite values -/
theorem mAnalyticAt_lift_coe (fa : AnalyticAt ℂ f z) : ContMDiffAt I I ⊤ (lift f y) z := by
  rw [lift_eq_fill]
  exact mAnalyticAt_fill_coe ((mAnalytic_coe _).comp _ (fa.mAnalyticAt I I))

/-- `lift` is analytic at `∞` -/
theorem mAnalyticAt_lift_inf (fa : ∀ᶠ z in cobounded ℂ, AnalyticAt ℂ f z)
    (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) : ContMDiffAt I I ⊤ (lift f ∞) ∞ := by
  rw [lift_eq_fill]; apply mAnalyticAt_fill_inf
  exact fa.mp (.of_forall fun z fa ↦ (mAnalytic_coe _).comp _ (fa.mAnalyticAt I I))
  exact coe_tendsto_inf.comp fi

/-- `lift` is analytic -/
theorem mAnalytic_lift (fa : AnalyticOnNhd ℂ f univ)
    (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) : ContMDiff I I ⊤ (lift f ∞) := by
  intro z; induction z using OnePoint.rec
  · exact mAnalyticAt_lift_inf (.of_forall fun z ↦ fa z (mem_univ _)) fi
  · exact mAnalyticAt_lift_coe (fa _ (mem_univ _))

/-- `lift'` is analytic (the parameterized version) -/
theorem mAnalytic_lift' {f : ℂ → ℂ → ℂ} (fa : AnalyticOnNhd ℂ (uncurry f) univ)
    (fi : ∀ x, Tendsto (uncurry f) (𝓝 x ×ˢ cobounded ℂ) (cobounded ℂ)) :
    ContMDiff II I ⊤ (uncurry (lift' f ∞)) := by
  apply osgoodManifold (continuous_lift' fa.continuous fi)
  · intro x z
    induction z using OnePoint.rec
    · simp only [uncurry, lift_inf']; exact contMDiffAt_const
    · exact (mAnalytic_coe _).comp _ ((fa _ (mem_univ ⟨_,_⟩)).along_fst.mAnalyticAt _ _)
  · intro x z
    exact mAnalytic_lift (fun _ _ ↦ (fa _ (mem_univ ⟨_,_⟩)).along_snd)
      ((fi x).comp (tendsto_const_nhds.prodMk Filter.tendsto_id)) z

/-- `(OnePoint ℂ)` is path connected -/
instance : PathConnectedSpace (OnePoint ℂ) := by
  constructor; use ∞
  have i1 : Joined ∞ ((1 : ℂ) : (OnePoint ℂ)) := by
    generalize hp : (fun t : unitInterval ↦ (((t : ℝ) : ℂ) : (OnePoint ℂ))⁻¹) = p
    have pc : Continuous p := by
      rw [← hp]
      exact continuous_inv.comp (continuous_coe.comp (Complex.continuous_ofReal.comp
        continuous_subtype_val))
    use ⟨p, pc⟩
    simp only [← hp]; rw [Icc.coe_zero, Complex.ofReal_zero, coe_zero, inv_zero']
    simp only [← hp]; rw [Icc.coe_one, Complex.ofReal_one, inv_coe one_ne_zero, inv_one]
  have cc : ∀ x y : ℂ, Joined (x : (OnePoint ℂ)) (y : (OnePoint ℂ)) := by
    intro x y
    have p := PathConnectedSpace.somePath x y
    use p.map continuous_coe
    repeat simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.coe_coe, Path.source, Path.target]
  replace ic : ∀ x : ℂ, Joined ∞ (x : (OnePoint ℂ)) := fun x ↦ i1.trans (cc _ _)
  intro x y; induction x using OnePoint.rec
  · induction y using OnePoint.rec
    · exact Joined.refl _
    · apply ic
  · induction y using OnePoint.rec
    · exact (ic _).symm
    · apply cc

end RiemannSphere
end
end Ray_Ray_Manifold_RiemannSphere

-- ===== Ray.Multibrot.D =====
section Ray_Ray_Multibrot_D
/-!
## Facts about `d ≥ 2`

This is a separate file so I can import them separate from dynamics machinery.
-/

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

lemma two_le_d (d : ℕ) [h : Fact (2 ≤ d)] : 2 ≤ d := h.elim
lemma d_pos (d : ℕ) [Fact (2 ≤ d)] : 0 < d := by linarith [two_le_d d]
lemma d_ne_zero (d : ℕ) [Fact (2 ≤ d)] : d ≠ 0 := (d_pos d).ne'
lemma d_gt_one (d : ℕ) [Fact (2 ≤ d)] : 1 < d := by linarith [two_le_d d]
lemma d_ge_one (d : ℕ) [Fact (2 ≤ d)] : 1 ≤ d := (d_gt_one _).le
lemma d_minus_one_pos (d : ℕ) [Fact (2 ≤ d)] : 0 < d - 1 := by have h := two_le_d d; omega
lemma one_le_d_minus_one (d : ℕ) [Fact (2 ≤ d)] : 1 ≤ d - 1 := by have h := two_le_d d; omega
lemma two_le_cast_d (d : ℕ) [Fact (2 ≤ d)] : (2 : ℝ) ≤ d :=
  le_trans (by norm_num) (Nat.cast_le.mpr (two_le_d d))

-- Teach `bound` about `d`
attribute [bound] two_le_d d_gt_one d_ge_one d_pos two_le_cast_d one_le_d_minus_one
attribute [aesop norm apply (rule_sets := [Bound])] d_ne_zero  -- TODO: Make `@[bound]` work here

/-- `2` works -/
instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

end Ray_Ray_Multibrot_D

-- ===== Ray.Multibrot.Defs =====
section Ray_Ray_Multibrot_Defs
/-!
## Multibrot definitions, allowing minimal public imports
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Function (uncurry)
open OneDimension
open RiemannSphere
open Set
open scoped ContDiff OnePoint RiemannSphere Topology

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]
variable {c : ℂ}

/-!
## The defining iteration, the Multibrot set, and its complement
-/

/-- The Multibrot iteration, `ℂ → ℂ` version -/
def f' (d : ℕ) (c z : ℂ) : ℂ :=
  z ^ d + c

/-- The Multibrot iteration, `(OnePoint ℂ) → (OnePoint ℂ)` version -/
def f (d : ℕ) : ℂ → (OnePoint ℂ) → (OnePoint ℂ) :=
  lift' (f' d) ∞

/-- The Multibrot set is those points that do not escape to `∞` -/
def multibrot (d : ℕ) : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ (f d c)^[n] ↑c) atTop (𝓝 ∞)}

/-- The complement of the Multibrot set, including `∞` -/
def multibrotExt (d : ℕ) : Set (OnePoint ℂ) :=
  ((fun z : ℂ ↦ (z : (OnePoint ℂ))) '' multibrot d)ᶜ ∪ {(∞ : (OnePoint ℂ))}

/-!
## Basic properties of the iteration `f`

In particular, we show that `f d` has a superattracting fixpoint at `∞`.
-/

-- Basic properties of f
@[simp] lemma f_0' (d : ℕ) [Fact (2 ≤ d)] : f' d c 0 = c := by
  simp only [f', zero_pow (d_ne_zero _), zero_add]

@[simp] lemma f_0 (d : ℕ) [Fact (2 ≤ d)] : f d c 0 = c := by
  simp only [f, ← coe_zero, lift_coe', f', zero_pow (d_ne_zero _), zero_add]

theorem analytic_f' {d : ℕ} : AnalyticOnNhd ℂ (uncurry (f' d)) univ := fun _ _ ↦
  (analyticAt_snd.pow _).add analyticAt_fst

theorem tendsto_f'_cobounded (c : ℂ) :
    Tendsto (uncurry (f' d)) (𝓝 c ×ˢ cobounded ℂ) (cobounded ℂ) := by
  simp only [hasBasis_cobounded_norm_lt.tendsto_right_iff, Set.mem_ofPred_eq,
    forall_true_left, uncurry, Metric.eventually_nhds_prod_iff]
  intro r; use 1, zero_lt_one, fun z ↦ max r 0 + ‖c‖ + 1 < ‖z‖; constructor
  · refine (eventually_cobounded (max r 0 + ‖c‖ + 1)).mp (.of_forall fun w h ↦ ?_)
    exact h
  · intro e ec z h
    simp only [Complex.dist_eq] at ec
    have zz : ‖z‖ ≤ ‖z ^ d‖ := by
      rw [norm_pow]
      refine le_self_pow₀ ?_ (d_ne_zero _)
      exact le_trans (le_add_of_nonneg_left (add_nonneg (le_max_right _ _) (norm_nonneg _))) h.le
    calc ‖f' d e z‖
      _ = ‖z ^ d + e‖ := rfl
      _ = ‖z ^ d + (c + (e - c))‖ := by ring_nf
      _ ≥ ‖z ^ d‖ - ‖c + (e - c)‖ := by bound
      _ ≥ ‖z ^ d‖ - (‖c‖ + ‖e - c‖) := by bound
      _ ≥ ‖z‖ - (‖c‖ + 1) := by bound
      _ > max r 0 + ‖c‖ + 1 - (‖c‖ + 1) := by bound
      _ = max r 0 := by ring_nf
      _ ≥ r := le_max_left _ _

theorem mAnalyticAt_f : ContMDiff II I ω (uncurry (f d)) :=
  mAnalytic_lift' analytic_f' tendsto_f'_cobounded

theorem writtenInExtChartAt_coe_f {d : ℕ} {z : ℂ} :
    writtenInExtChartAt I I (z : (OnePoint ℂ)) (f d c) = f' d c := by
  simp only [writtenInExtChartAt, f, Function.comp_def, lift_coe', RiemannSphere.extChartAt_coe,
    PartialEquiv.symm_symm, coePartialEquiv_apply, coePartialEquiv_symm_apply, toComplex_coe]

lemma fl_f : fl (f d) ∞ = fun c z : ℂ ↦ z^d / (1 + c * z^d) := by
  funext c z
  simp only [fl, RiemannSphere.extChartAt_inf, Function.comp_def, invEquiv_apply,
    PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, PartialEquiv.coe_trans_symm,
    coePartialEquiv_symm_apply, PartialEquiv.symm_symm, coePartialEquiv_apply,
    Equiv.toPartialEquiv_symm_apply, invEquiv_symm, RiemannSphere.inv_inf, toComplex_zero,
    add_zero, sub_zero]
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', f, lift_inf', RiemannSphere.inv_inf, toComplex_zero,
      zero_pow (d_ne_zero _), zero_div]
  simp only [f, f', inv_coe z0, lift_coe', inv_pow]
  have zd := pow_ne_zero d z0
  by_cases h : (z ^ d)⁻¹ + c = 0
  · simp only [h, coe_zero, inv_zero', toComplex_inf]
    simp only [← add_eq_zero_iff_neg_eq.mp h, neg_mul, inv_mul_cancel₀ zd, ← sub_eq_add_neg,
      sub_self, div_zero]
  rw [inv_coe h, toComplex_coe, eq_div_iff, inv_mul_eq_iff_eq_mul₀ h, right_distrib,
    inv_mul_cancel₀ zd]
  contrapose h
  rw [add_comm, add_eq_zero_iff_eq_neg, ← eq_div_iff zd, neg_div, ←
    inv_eq_one_div, ← add_eq_zero_iff_eq_neg, add_comm] at h
  exact h

/-- `f` near `∞` with the `z^d` factor removed -/
noncomputable def gl (d : ℕ) (c z : ℂ) :=
  (1 + c * z ^ d)⁻¹

theorem gl_f {z : ℂ} : g (fl (f d) ∞ c) d z = gl d c z := by
  simp only [fl_f, gl, g]
  by_cases z0 : z = 0
  simp only [if_pos, z0, zero_pow (d_ne_zero _), MulZeroClass.mul_zero, add_zero, inv_one]
  rw [if_neg z0, div_eq_mul_inv _ (_ + _), mul_comm, mul_div_assoc, div_self (pow_ne_zero _ z0),
    mul_one]

theorem analyticAt_gl : AnalyticAt ℂ (gl d c) 0 := by
  apply (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow _))).inv
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq, zero_pow (d_ne_zero _), mul_zero,
    add_zero, ne_eq, one_ne_zero, not_false_eq_true]

theorem fl_f' : fl (f d) ∞ = fun c z : ℂ ↦ (z - 0) ^ d • gl d c z := by
  funext c z; simp only [fl_f, gl, sub_zero, smul_eq_mul, div_eq_mul_inv]

theorem gl_zero : gl d c 0 = 1 := by
  simp only [gl, zero_pow (d_ne_zero _), MulZeroClass.mul_zero]; norm_num

theorem gl_frequently_ne_zero : ∃ᶠ z in 𝓝 0, gl d c z ≠ 0 := by
  refine (analyticAt_gl.continuousAt.eventually_ne ?_).frequently; simp only [gl_zero]
  exact one_ne_zero

lemma fc_f : leadingCoeff (fl (f d) ∞ c) 0 = 1 := by
  rw [fl_f', analyticAt_gl.monomial_mul_leadingCoeff gl_frequently_ne_zero, leadingCoeff_of_ne_zero]
  exact gl_zero; rw [gl_zero]; exact one_ne_zero

lemma fd_f : orderAt (fl (f d) ∞ c) 0 = d := by
  rw [fl_f', analyticAt_gl.monomial_mul_orderAt gl_frequently_ne_zero, orderAt_eq_zero, add_zero]
  rw [gl_zero]; exact one_ne_zero

theorem f_inf {d : ℕ} : f d c ∞ = (∞ : (OnePoint ℂ)) := by
  simp only [f, lift_inf']

-- f has a superattracting fixpoint at ∞
theorem superF (d : ℕ) [Fact (2 ≤ d)] : Super (f d) d ∞ :=
  { d2 := two_le_d d
    fa := mAnalyticAt_f
    fc := fun _ ↦ fc_f
    fd := fun _ ↦ fd_f
    f0 := fun _ ↦ f_inf }

/-- `f` has one preimage of `∞` -/
instance onePreimageF : OnePreimage (superF d) where
  eq_a := by
    intro c z; induction z using OnePoint.rec
    · simp only [imp_true_iff]
    · simp only [f, lift_coe', OnePoint.coe_ne_infty, IsEmpty.forall_iff]

/-!
## Bottcher coordinates!
-/

/-- The Böttcher map for the Multibrot set is the diagonal of the dynamical map (`ℂ → ℂ` version) -/
noncomputable def bottcher' (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) : ℂ :=
  (superF d).bottcher c c

/-- The Böttcher map for the Multibrot set is the diagonal of the dynamical map (`(OnePoint ℂ) → ℂ` version) -/
noncomputable def bottcher (d : ℕ) [Fact (2 ≤ d)] : (OnePoint ℂ) → ℂ :=
  fill (bottcher' d) 0

/-- `bottcher` near `∞` as an analytic `ℂ → ℂ` function -/
noncomputable def bottcher_inv (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ :=
  fun z ↦ bottcher d (↑z)⁻¹

/-- `s.bottcher_inv` as an analytic `ℂ → ℂ → ℂ` function -/
noncomputable def sbottcher_inv (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ → ℂ :=
  fun c z ↦ (superF d).bottcher c (z : (OnePoint ℂ))⁻¹

lemma bottcher_inv_def : bottcher_inv d = fun z : ℂ ↦ bottcher d (↑z)⁻¹ := by rfl
lemma sbottcher_inv_def :
    sbottcher_inv d = fun c z : ℂ ↦ (superF d).bottcher c (z : (OnePoint ℂ))⁻¹ := by rfl

/-- `s.inv_ray` as an analytic `ℂ → ℂ` function -/
noncomputable def sinv_ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ → ℂ :=
  fun c z ↦ ((superF d).ray c z)⁻¹.toComplex


/-!
## Error bound functions for iterates and potentials
-/

/-- Weird bound that we use below to be reasonably tight -/
noncomputable def f_error (d : ℕ) (z : ℂ) :=
  -Real.log (1 - -Real.log (1 - 1/‖z‖) / (d * Real.log (‖z‖)))

/-- The infinite sum of `f_error` -/
noncomputable def iter_error (d : ℕ) (c z : ℂ) :=
  ∑' n, f_error d ((f' d c)^[n] z)

/-- We will use this function below to produce bounds on `s.potential` approximates -/
noncomputable def ene (x : ℝ) : ℝ := Real.exp (-Real.exp x)

/-- The (negated) derivative of `ene` -/
noncomputable def dene (x : ℝ) : ℝ := Real.exp (x - Real.exp x)

/-- Error term in the `potential` approximate -/
noncomputable def potential_error (d : ℕ) (c z : ℂ) : ℝ :=
  dene (Real.log (Real.log ‖z‖) - iter_error d c z) * iter_error d c z

/-!
## Balls whose size depends on an inverse

These work correctly if the inverse would be infinite.
-/

/-- `min r ‖c‖⁻¹`, but do the right thing if `c = 0` -/
noncomputable def rinv (r : ℝ) (c : ℂ) : ℝ :=
  if c = 0 then r else min r ‖c‖⁻¹

end Ray_Ray_Multibrot_Defs

-- ===== Ray.Multibrot.Basic =====
section Ray_Ray_Multibrot_Basic
/-!
## The Multibrot sets and their basic properties

We define the Multibrot set as points `c` where `z ↦ z^d + c` does not escape to `∞` starting from
`c` (or 0), both as a subset of `ℂ` and of the Riemann sphere `(OnePoint ℂ)`.  We then lift the dynamical
results from `Ray.lean` and `Bottcher.lean` about fixed `c` behavior into parameter results about
the Multibrot set.  This file contains only basics; see
`Multibrot/{Iterates,Potential,Postcritical,Bottcher}.lean` for effective bounds and
`Multibrot/Isomorphism.lean`, `Multibrot/Connected.lean`, and `Mandelbrot.lean` for the main
theoretical results.

In detail, this file contains:

1. Definitions of the Multibrot set and complement, and their `potential` and `bottcher` functions.
2. Superattraction from the fixpoint at `∞`, in an effective region of `∞`.
3. An initial exponential growth bound on iterates (`iter_large`).
4. Specific points that are inside or out of the Multibrot set, including all points with
   `2 < abs c` (`multibrot_two_lt`), points that repeat, etc.
5. Analyticity and surjectivity of `bottcher`.
6. Ineffective estimates for `bottcher` and `potential` near `∞`.
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Function (uncurry)
open Metric (ball closedBall mem_ball_self mem_ball mem_closedBall)
open Real (exp log)
open RiemannSphere
open OneDimension
open Set
open scoped ContDiff OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
## Basic properties of the sets
-/

-- Basic properties of multibrot_ext
@[simp] theorem multibrotExt_inf {d : ℕ} : (∞ : (OnePoint ℂ)) ∈ multibrotExt d :=
  subset_union_right rfl
theorem multibrotExt_coe {d : ℕ} {c : ℂ} : ↑c ∈ multibrotExt d ↔ c ∉ multibrot d := by
  simp only [multibrotExt, mem_union, mem_singleton_iff, coe_eq_inf_iff, or_false, mem_image,
    mem_compl_iff, coe_eq_coe, not_iff_not]
  constructor; intro ⟨x, m, e⟩; rw [e] at m; exact m; intro m; use c, m
theorem coe_preimage_multibrotExt {d : ℕ} :
    (fun z : ℂ ↦ (z : (OnePoint ℂ))) ⁻¹' multibrotExt d = (multibrot d)ᶜ := by
  apply Set.ext; intro z; simp only [mem_compl_iff, mem_preimage, multibrotExt_coe]

/-!
## Basic properties of the iteration `f`
-/

theorem deriv_f' {d : ℕ} {z : ℂ} : deriv (f' d c) z = d * z ^ (d - 1) := by
  have h : HasDerivAt (f' d c) (d * z ^ (d - 1) + 0) z :=
    (hasDerivAt_pow _ _).add (hasDerivAt_const _ _)
  simp only [add_zero] at h; exact h.deriv

/-- Bound on `(1 + z)⁻¹ - 1` used in `superNearF` -/
lemma inv_sub_one_le {z : ℂ} {b : ℝ} (zb : ‖z‖ ≤ b / (1 + b)) (b0 : 0 ≤ b) :
    ‖(1 + z)⁻¹ - 1‖ ≤ b := by
  have z1 : ‖z‖ < 1 := lt_of_le_of_lt zb (by bound)
  have a0 : 1 + z ≠ 0 := by contrapose z1; simp [(by grind : z = -1)]
  nth_rw 2 [← div_self a0]
  simp only [← one_div, ← sub_div, sub_add_cancel_left, Complex.norm_div, norm_neg,
    div_le_iff₀ (norm_pos_iff.mpr a0), ge_iff_le]
  trans b * (‖(1 : ℂ)‖ - ‖z‖)
  · simp only [norm_one]
    suffices h : ‖z‖ * (1 + b) ≤ b by grind
    rwa [← le_div_iff₀ (by linarith)]
  · bound

/-- The set of `z`s for which `superNearF` holds -/
def superNearT (d : ℕ) (c : ℂ) : Set ℂ :=
  {z | ‖z‖ < 1 / 3 ∧ ‖c‖ * ‖z‖ ^ d < 2 / 5}

/-- An explicit bound on the near region near `∞`, giving an explicit region where the
    infinite product formula for `s.bottcher` will hold -/
theorem superNearF (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    SuperNear (fl (f d) ∞ c) d (superNearT d c) (1 / 3) (2 / 3) := by
  set s := superF d
  have zb : ∀ {z}, z ∈ superNearT d c → ‖z‖ < 1 / 3 := by
    intro z m; simp [superNearT] at m ⊢; linarith
  have cz : ∀ {z}, z ∈ superNearT d c → ‖c * z ^ d‖ ≤ 2 / 5 := by
    intro z m; simp [superNearT] at m ⊢; linarith
  have cz1 : ∀ {z}, z ∈ superNearT d c → 3 / 5 ≤ ‖1 + c * z ^ d‖ := by
    intro z m
    trans ‖(1 : ℂ)‖ - ‖c * z ^ d‖
    · specialize cz m
      simp only [norm_one] at cz ⊢
      linarith
    · bound
  exact
    { d2 := two_le_d d
      a1 := by norm_num
      b0 := by norm_num
      b1 := by norm_num
      c1' := by norm_num
      fa0 := (s.fla c).along_snd
      fd := fd_f
      fc := fc_f
      o := by
        simp only [← norm_pow, ← norm_mul, superNearT]
        apply IsOpen.inter
        · exact isOpen_lt continuous_norm continuous_const
        · exact isOpen_lt (continuous_norm.comp (by continuity)) continuous_const
      t0 := by
        simp only [superNearT, one_div, mem_ofPred_eq, norm_zero, inv_pos, Nat.ofNat_pos,
          zero_pow (d_ne_zero d), mul_zero, div_pos_iff_of_pos_left, and_self]
      t2 := fun {z} m ↦ le_trans (zb m).le (by norm_num)
      fa := by
        intro z m
        rw [fl_f]
        refine (analyticAt_id.pow _).div (analyticAt_const.add
          (analyticAt_const.mul (analyticAt_id.pow _))) ?_
        specialize cz m
        contrapose cz
        norm_num [(by grind : c * z ^ d = -1)]
      ft := by
        intro z m
        specialize cz1 m
        specialize zb m
        simp only [fl_f, mem_ofPred, norm_div, norm_pow, superNearT] at m ⊢
        have le : ‖z‖ ^ d / ‖1 + c * z ^ d‖ ≤ 5 / 27 := by
          calc ‖z‖ ^ d / ‖1 + c * z ^ d‖
            _ ≤ (1 / 3) ^ d / (3 / 5) := by bound
            _ ≤ (1 / 3) ^ 2 / (3 / 5) := by bound
            _ = 5 / 27 := by norm_num
        refine ⟨by linarith, ?_⟩
        have le1 : ‖z‖ ^ d / ‖1 + c * z ^ d‖ ≤ 1 := by linarith
        calc ‖c‖ * (‖z‖ ^ d / ‖1 + c * z ^ d‖) ^ d
          _ ≤ ‖c‖ * (‖z‖ ^ d / ‖1 + c * z ^ d‖) ^ 2 := by bound
          _ = ‖c‖ * ‖z‖ ^ d * (‖z‖ ^ d / ‖1 + c * z ^ d‖ / ‖1 + c * z ^ d‖) := by ring
          _ ≤ ‖c‖ * ‖z‖ ^ d * (5 / 27 / (3 / 5)) := by bound
          _ ≤ ‖c‖ * ‖z‖ ^ d := mul_le_of_le_one_right (by bound) (by norm_num)
          _ < 2 / 5 := by bound
      gs' := by
        intro z z0 m
        simp only [fl_f, div_div_cancel_left' (pow_ne_zero d z0)]
        refine inv_sub_one_le ?_ (by norm_num)
        norm_num
        simpa using cz m }

/-- `0, ∞` are the only critical points of `f` -/
theorem critical_f {z : (OnePoint ℂ)} : Critical (f d c) z ↔ z = 0 ∨ z = (∞ : (OnePoint ℂ)) := by
  induction' z using OnePoint.rec with z
  · simp only [(superF d).critical_a, or_true]
  · have zx : ∀ x : ℂ, (0 : ℂ →L[ℂ] ℂ) x = 0 := fun x ↦ rfl
    simp only [Critical, mfderiv, (mAnalyticAt_f (c, z)).along_snd.mdifferentiableAt (by decide),
      if_pos, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ,
      writtenInExtChartAt_coe_f, RiemannSphere.extChartAt_coe, coePartialEquiv_symm_apply,
      toComplex_coe, coe_eq_zero, coe_eq_inf_iff, or_false, ← toSpanSingleton_deriv, deriv_f',
      ContinuousLinearMap.ext_iff, zx, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_eq_zero, Nat.cast_eq_zero, d_ne_zero, ne_eq, (d_minus_one_pos _).ne', not_false_eq_true,
      pow_eq_zero_iff, false_or]
    constructor
    · intro h
      have h1 : (if True then ContinuousLinearMap.toSpanSingleton ℂ ((d : ℂ) * z ^ (d - 1))
          else 0 : ℂ →L[ℂ] ℂ) (1 : ℂ) = 0 := h (1 : ℂ)
      rw [if_pos trivial] at h1
      have h2 : (1 : ℂ) • ((d : ℂ) * z ^ (d - 1)) = 0 := h1
      rw [one_smul, mul_eq_zero] at h2
      rcases h2 with h2 | h2
      · exact absurd (Nat.cast_eq_zero.mp h2) (d_ne_zero _)
      · exact (pow_eq_zero_iff (d_minus_one_pos _).ne').mp h2
    · intro h x
      have e : ∀ y : ℂ, (if True then ContinuousLinearMap.toSpanSingleton ℂ ((d : ℂ) * z ^ (d - 1))
          else 0 : ℂ →L[ℂ] ℂ) y = 0 := by
        intro y
        rw [if_pos trivial]
        show y • ((d : ℂ) * z ^ (d - 1)) = 0
        simp only [h, zero_pow (d_minus_one_pos _).ne', mul_zero, smul_zero]
      exact e x

/-- The multibrot set is all `c`'s s.t. `0` doesn't reach `∞` -/
theorem multibrot_basin' : c ∈ multibrot d ↔ (c, (c : (OnePoint ℂ))) ∉ (superF d).basin := by
  simp only [multibrot, mem_ofPred, Super.basin_iff_attracts, Attracts]

theorem multibrot_basin : c ∈ multibrot d ↔ (c, (0 : (OnePoint ℂ))) ∉ (superF d).basin := by
  set s := superF d
  simp only [multibrot_basin', not_iff_not, Super.basin, mem_ofPred]
  have e : ∀ n, (f d c)^[n] c = (f d c)^[n + 1] 0 := by
    intro n; induction' n with n h
    · simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one, f_0]
    · simp only [Function.iterate_succ_apply', h]
  simp only [e]
  apply Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ (f d c)^[n] 0))

/-- The critical potential is the potential of 0 (as 0 is the only nontrivial critical point) -/
theorem multibrot_p : (superF d).p c = (superF d).potential c 0 := by
  set s := superF d
  have e : s.ps c = {1, s.potential c 0} := by
    apply Set.ext; intro p
    simp only [Super.ps, mem_singleton_iff, mem_ofPred, critical_f, Ne, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · intro h; cases' h with h h; left; exact h; right; rcases h with ⟨p0, z, e, h⟩
      cases' h with h h; rw [h] at e; exact e.symm
      rw [h, s.potential_a] at e; exfalso; exact p0 e.symm
    · intro h; cases' h with h h; left; exact h; right; constructor
      · simp only [h, s.potential_ne_zero]; exact inf_ne_zero.symm
      · use 0, h.symm, Or.inl rfl
  simp only [Super.p, e, csInf_pair]
  exact inf_of_le_right s.potential_le_one

/-- `(c,c)` is postcritical for `c` outside multibrot -/
theorem multibrotPost (m : c ∉ multibrot d) : Postcritical (superF d) c c := by
  set s := superF d
  simp only [Postcritical, multibrot_p, ← f_0 d, s.potential_eqn]
  simp only [multibrot_basin, not_not] at m
  exact pow_lt_self_of_lt_one₀ ((s.potential_pos c).mpr inf_ne_zero.symm)
    (s.potential_lt_one m) (d_gt_one d)

/-!
## The diagonal Böttcher map
-/

-- `bottcher` at `ℂ` and `∞`
theorem bottcher_coe {c : ℂ} : bottcher d c = bottcher' d c := by
  simp only [bottcher, fill_coe, bottcher']
@[simp] theorem bottcher_inf : bottcher d ∞ = 0 := by simp only [bottcher, fill_inf]

/-!
## Exponential lower and upper bounds on iterates
-/

/-- A warmup exponential lower bound on iterates -/
lemma iter_large (d : ℕ) [Fact (2 ≤ d)] (b : ℝ) {c z : ℂ} (b2 : 2 ≤ b) (bz : b ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) : (b-1)^n * ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  induction' n with n h
  · simp only [pow_zero, one_mul, Function.iterate_zero_apply, le_refl]
  · simp only [Function.iterate_succ_apply']
    generalize hw : (f' d c)^[n] z = w; rw [hw] at h; clear hw
    have z1 : 1 ≤ ‖z‖ := le_trans (by norm_num) (le_trans b2 bz)
    have b1 : 1 ≤ b - 1 := by linarith
    have b0 : 0 ≤ b - 1 := by linarith
    have nd : n + 1 ≤ n * d + 1 := by bound
    calc ‖w ^ d + c‖
      _ ≥ ‖w ^ d‖ - ‖c‖ := by bound
      _ = ‖w‖ ^ d - ‖c‖ := by rw [norm_pow]
      _ ≥ ((b-1) ^ n * ‖z‖) ^ d - ‖c‖ := by bound
      _ = (b-1) ^ (n*d) * ‖z‖ ^ d - ‖c‖ := by rw [mul_pow, pow_mul]
      _ ≥ (b-1) ^ (n*d) * ‖z‖ ^ 2 - ‖c‖ := by bound
      _ = (b-1) ^ (n*d) * (‖z‖ * ‖z‖) - ‖c‖ := by rw [pow_two]
      _ ≥ (b-1) ^ (n*d) * (b * ‖z‖) - ‖c‖ := by bound
      _ = (b-1) ^ (n*d) * (b-1) * ‖z‖ + ((b-1) ^ (n*d) * ‖z‖ - ‖c‖) := by ring
      _ = (b-1) ^ (n*d + 1) * ‖z‖ + ((b-1) ^ (n * d) * ‖z‖ - ‖c‖) := by rw [pow_succ]
      _ ≥ (b-1) ^ (n + 1) * ‖z‖ + (1 * ‖z‖ - ‖c‖) := by bound
      _ = (b-1) ^ (n + 1) * ‖z‖ + (‖z‖ - ‖c‖) := by rw [one_mul]
      _ ≥ (b-1) ^ (n + 1) * ‖z‖ := by bound

/-- Ap exponential upper bound on a single iteration -/
lemma iter_small (d : ℕ) (c z : ℂ) : ‖(f' d c z)‖ ≤ ‖z‖ ^ d + ‖c‖ := by
  calc ‖z ^ d + c‖
    _ ≤ ‖z ^ d‖ + ‖c‖ := by bound
    _ ≤ ‖z‖ ^ d + ‖c‖ := by rw [norm_pow]

/-!
## Explicit points that are inside or outside the Multibrot set
-/

/-- Multibrot membership in terms of the `ℂ → ℂ` iteration `f'`, not `f` -/
theorem f_f'_iter {d : ℕ} (n : ℕ) {z : ℂ} : (f d c)^[n] ↑z = ↑((f' d c)^[n] z) := by
  induction' n with n h; simp only [Function.iterate_zero, id]
  simp only [h, Function.iterate_succ_apply']
  simp only [f, lift_coe']

theorem multibrot_coe {d : ℕ} :
    c ∈ multibrot d ↔ ¬Tendsto (fun n ↦ (f' d c)^[n] c) atTop (cobounded ℂ) := by
  simp only [multibrot, mem_ofPred, f_f'_iter, tendsto_inf_iff_tendsto_cobounded]

/-- Closed Julia sets are not outside radius `max 2 (abs c)` -/
theorem julia_two_lt {z : ℂ} (z2 : 2 < ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    (c,↑z) ∈ (superF d).basin := by
  simp only [(superF d).basin_iff_attracts, Attracts, f_f'_iter, tendsto_inf_iff_tendsto_cobounded,
    tendsto_cobounded_iff_norm_tendsto_atTop] at z2 ⊢
  apply Filter.tendsto_atTop_mono (iter_large d ‖z‖ z2.le (le_refl _) cz)
  refine Filter.Tendsto.atTop_mul_pos (by linarith) ?_ tendsto_const_nhds
  apply tendsto_pow_atTop_atTop_of_one_lt; linarith

/-- Closed Julia sets are inside radius `max 2 (abs c)` -/
theorem julia_le_two {z : ℂ} (m : (c,↑z) ∉ (superF d).basin) (cz : ‖c‖ ≤ ‖z‖) : ‖z‖ ≤ 2 := by
  contrapose m
  simp only [not_le] at m ⊢
  exact julia_two_lt m cz

/-- `0 < s.potential` at finite values -/
@[bound] lemma potential_pos {z : ℂ} : 0 < (superF d).potential c z :=
  ((superF d).potential_pos _).mpr RiemannSphere.coe_ne_inf

/-- `s.potential < 1` outside radius `max 2 (abs c)` -/
lemma potential_lt_one_of_two_lt {z : ℂ} (z2 : 2 < ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    (superF d).potential c z < 1 :=
  (superF d).potential_lt_one (julia_two_lt z2 cz)

/-- The Multibrot set is inside radius 2 -/
theorem multibrot_le_two (m : c ∈ multibrot d) : ‖c‖ ≤ 2 := by
  rw [multibrot_basin' (d := d)] at m
  exact julia_le_two m (le_refl _)

/-- The Multibrot set is a subset of `closedBall 0 2` -/
theorem multibrot_subset_closedBall : multibrot d ⊆ closedBall 0 2 := by
  intro c m; simp only [mem_closedBall, Complex.dist_eq, sub_zero]; exact multibrot_le_two m

/-- Points with absolute value `> 2` are not in the Multibrot set -/
theorem multibrot_two_lt (a : 2 < ‖c‖) : c ∉ multibrot d := by
  contrapose a; simp only [not_lt] at a ⊢; exact multibrot_le_two a

/-- If the iteration repeats, we're in the Multibrot set -/
theorem multibrot_of_repeat {d a b : ℕ} (ab : a < b) (h : (f d c)^[a] c = (f d c)^[b] c) :
    c ∈ multibrot d := by
  generalize hg : (fun n ↦ (f' d c)^[n] c) = g
  replace hg : ∀ n, (f' d c)^[n] c = g n := fun n ↦ by rw [← hg]
  simp only [f_f'_iter, coe_eq_coe, hg] at h
  have lo : ∀ n : ℕ, ∃ k, k ≤ b ∧ g n = g k := by
    intro n; induction' n with n h
    · use 0, Nat.zero_le _
    · rcases h with ⟨k, kb, nk⟩
      by_cases e : k = b; use a + 1, Nat.succ_le_iff.mpr ab
      rw [← hg, ← hg, Function.iterate_succ_apply', Function.iterate_succ_apply', hg, hg, nk, e, h]
      use k + 1, Nat.succ_le_iff.mpr (Ne.lt_of_le e kb)
      rw [← hg, ← hg, Function.iterate_succ_apply', Function.iterate_succ_apply', hg, hg, nk]
  simp only [multibrot_coe, hasBasis_cobounded_norm_lt.tendsto_right_iff, true_imp_iff, not_forall,
    Filter.not_eventually, mem_ofPred, not_lt, hg]
  use partialSups (fun k ↦ ‖g k‖) b
  refine .of_forall ?_; intro k; rcases lo k with ⟨l, lb, kl⟩
  rw [kl]; exact le_partialSups_of_le (fun k ↦ ‖g k‖) lb

/-- If the iteration hits zero, we're in the Multibrot set -/
theorem multibrot_of_zero {n : ℕ} (h : (f d c)^[n] c = 0) : c ∈ multibrot d := by
  have i0 : (f d c)^[0] c = c := by rw [Function.iterate_zero_apply]
  have i1 : (f d c)^[n + 1] c = c := by simp only [Function.iterate_succ_apply', h, f_0]
  exact multibrot_of_repeat (Nat.zero_lt_succ _) (_root_.trans i0 i1.symm)

/-- `0 ∈ multbrot d` -/
@[simp] theorem multibrot_zero : (0 : ℂ) ∈ multibrot d := by
  apply multibrot_of_zero; rw [Function.iterate_zero_apply, coe_zero]

/-- `0 ∉ multibrotExt d` -/
@[simp] theorem multibrotExt_zero : (0 : (OnePoint ℂ)) ∉ multibrotExt d := by
  simp only [← coe_zero, multibrotExt_coe, not_not, multibrot_zero]

theorem not_multibrot_of_two_lt {n : ℕ} (h : 2 < ‖(f' d c)^[n] c‖) : c ∉ multibrot d := by
  by_cases c2 : 2 < ‖c‖; exact multibrot_two_lt c2
  simp only [multibrot_coe, not_not]; simp only [not_lt] at c2
  generalize hs : ‖((f' d c)^[n] c)‖ = s; rw [hs] at h
  have s1 : 1 ≤ s := by linarith
  have s1' : 1 ≤ s - 1 := by linarith
  have s0 : 0 ≤ s := by linarith
  have b : ∀ k, s * (s - 1) ^ k ≤ ‖(f' d c)^[k + n] c‖ := by
    intro k; induction' k with k p
    · simp only [pow_zero, mul_one, zero_add, hs, le_refl]
    · simp only [Nat.succ_add, Function.iterate_succ_apply']
      generalize hz : (f' d c)^[k + n] c = z; rw [hz] at p
      have ss1 : 1 ≤ s * (s - 1) ^ k := by bound
      have k2 : k ≤ k * 2 := by linarith
      calc ‖(f' d c z)‖
        _ = ‖z ^ d + c‖ := rfl
        _ ≥ ‖z ^ d‖ - ‖c‖ := by bound
        _ = ‖z‖ ^ d - ‖c‖ := by rw [norm_pow]
        _ ≥ (s * (s - 1) ^ k) ^ d - 2 := by bound
        _ ≥ (s * (s - 1) ^ k) ^ 2 - 2 := by bound
        _ = s ^ 2 * (s - 1) ^ (k * 2) - 2 * 1 := by rw [mul_pow, pow_mul, mul_one]
        _ ≥ s ^ 2 * (s - 1) ^ k - s * (s - 1) ^ k := by bound
        _ = s * ((s - 1) ^ k * (s - 1)) := by ring
        _ = s * (s - 1) ^ (k + 1) := by rw [pow_succ]
  simp only [tendsto_cobounded_iff_norm_tendsto_atTop]
  rw [← Filter.tendsto_add_atTop_iff_nat n]; apply Filter.tendsto_atTop_mono b
  refine Filter.Tendsto.pos_mul_atTop (by linarith) tendsto_const_nhds ?_
  apply tendsto_pow_atTop_atTop_of_one_lt; linarith

theorem multibrot_eq_le_two :
    multibrot d = ⋂ n : ℕ, (fun c : ℂ ↦ (f' d c)^[n] c) ⁻¹' closedBall 0 2 := by
  apply Set.ext; intro c
  simp only [mem_iInter, mem_preimage, mem_closedBall, Complex.dist_eq, sub_zero]
  constructor; · intro m n; contrapose m; simp only [not_le] at m; exact not_multibrot_of_two_lt m
  · intro h; contrapose h
    simp only [multibrot_coe, tendsto_cobounded_iff_norm_tendsto_atTop, not_not, not_forall, not_le,
      Filter.tendsto_atTop, not_exists] at h ⊢
    rcases(h 3).exists with ⟨n, h⟩; use n; linarith

/-- `multibrot d` is compact -/
theorem isCompact_multibrot : IsCompact (multibrot d) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall _ _) ?_ multibrot_subset_closedBall
  rw [multibrot_eq_le_two]; apply isClosed_iInter; intro n
  refine IsClosed.preimage ?_ Metric.isClosed_closedBall
  induction' n with n h; simp only [Function.iterate_zero_apply]; exact continuous_id
  simp only [Function.iterate_succ_apply']; rw [continuous_iff_continuousAt]; intro c
  exact (analytic_f' _ (mem_univ _)).continuousAt.comp₂ continuousAt_id h.continuousAt

/-- The exterior of the Multibrot set is open -/
theorem isOpen_multibrotExt : IsOpen (multibrotExt d) := by
  rw [OnePoint.isOpen_iff_of_mem']
  simp only [coe_preimage_multibrotExt, compl_compl]
  use isCompact_multibrot, isCompact_multibrot.isClosed.isOpen_compl
  exact multibrotExt_inf

/-!
## Analyticity of our Böttcher coordinates
-/

lemma mem_superNearT {c : ℂ} (lo : 3 < ‖c‖) : c⁻¹ ∈ superNearT d c := by
  simp only [superNearT, one_div, mem_ofPred_eq, norm_inv, inv_pow]
  refine ⟨by bound, ?_⟩
  calc ‖c‖ * (‖c‖ ^ d)⁻¹
    _ ≤ ‖c‖ * (‖c‖ ^ 2)⁻¹ := by bound
    _ = ‖c‖⁻¹ := by grind
    _ < 3⁻¹ := by bound
    _ < 2 / 5 := by norm_num

def superK : ℝ :=
  Real.exp (2 * (psg (2 / 3) 2⁻¹ * (2 / 3) / 2))

/-- `bottcher' d c` is small for large `c` -/
theorem bottcher_bound {c : ℂ} (lo : 3 < ‖c‖) : ‖bottcher' d c‖ ≤ superK * ‖c⁻¹‖ := by
  set s := superF d
  generalize hg : fl (f d) ∞ c = g
  -- Facts about c and f
  have ct : c⁻¹ ∈ superNearT d c := mem_superNearT lo
  have mem : c ∉ multibrot d := multibrot_two_lt (lt_trans (by norm_num) lo)
  have nz : ∀ n, (f d c)^[n] c ≠ 0 := by
    intro n; contrapose mem; exact multibrot_of_zero mem
  have iter : ∀ n, ((f d c)^[n] ↑c)⁻¹ = ↑(g^[n] c⁻¹) := by
    intro n; induction' n with n h
    have cp : c ≠ 0 := norm_ne_zero_iff.mp (lt_trans (by norm_num) lo).ne'
    simp only [Function.iterate_zero_apply, inv_coe cp]
    have e : (f d c)^[n] ↑c = ((g^[n] c⁻¹ : ℂ) : (OnePoint ℂ))⁻¹ := by rw [← h, inv_inv]
    simp only [Function.iterate_succ_apply', e]
    generalize hz : g^[n] c⁻¹ = z
    simp only [← hg, fl, extChartAt_inf, PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply,
      invEquiv_apply, RiemannSphere.inv_inf, coePartialEquiv_symm_apply, toComplex_zero, sub_zero,
      Function.comp_def, add_zero, PartialEquiv.coe_trans_symm, PartialEquiv.symm_symm,
      coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm]
    rw [coe_toComplex]
    simp only [Ne, inv_eq_inf, ← hz, ← h, inv_inv, ← Function.iterate_succ_apply' (f d c)]
    apply nz
  -- Find an n that gets us close enough to ∞ for s.bottcher = bottcher_near
  have b := mem
  simp only [multibrot_basin', not_not] at b
  have attracts := (s.basin_attracts b).eventually (s.bottcher_eq_bottcherNear c)
  rcases (attracts.and (s.basin_stays b)).exists with ⟨n, eq, _⟩; clear attracts b
  simp only [Super.bottcherNear, extChartAt_inf, PartialEquiv.trans_apply,
    coePartialEquiv_symm_apply, Equiv.toPartialEquiv_apply, invEquiv_apply, RiemannSphere.inv_inf,
    toComplex_zero, sub_zero, Super.fl, hg, iter, toComplex_coe] at eq
  -- Translate our bound across n iterations
  have e0 : s.bottcher c ((f d c)^[n] ↑c) = bottcher' d c ^ d ^ n := s.bottcher_eqn_iter n
  have e1 : bottcherNear g d (g^[n] c⁻¹) = bottcherNear g d c⁻¹ ^ d ^ n := by
    rw [← hg]; exact bottcherNear_eqn_iter (superNearF d c) ct n
  rw [e0, e1] at eq; clear e0 e1 iter
  have ae : ‖bottcher' d c‖ = ‖bottcherNear g d c⁻¹‖ := by
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
      (pow_ne_zero n (d_ne_zero d))).mp
    simp only [← norm_pow, eq]
  simpa only [ae, ← hg, SuperNear.k, SuperNear.kt, superK] using bottcherNear_le (superNearF d c) ct

/-- `bottcher' d c → 0` as `c → ∞` -/
theorem bottcher_tendsto_zero : Tendsto (bottcher' d) (cobounded ℂ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro r rp
  rw [hasBasis_cobounded_norm_lt.eventually_iff]
  use max 3 (superK / r)
  simp only [true_and, mem_ofPred, Complex.dist_eq, sub_zero, max_lt_iff]
  intro z ⟨lo, rz⟩; apply lt_of_le_of_lt (bottcher_bound lo)
  rw [div_lt_iff₀ rp] at rz
  rw [norm_inv, mul_inv_lt_iff₀ (lt_trans (by norm_num) lo)]
  linarith

/-- `bottcher' d` is analytic outside the Multibrot set -/
theorem bottcher_analytic : AnalyticOnNhd ℂ (bottcher' d) (multibrot d)ᶜ := by
  set s := superF d
  intro c m
  apply ContMDiffAt.analyticAt I I
  exact (s.bottcher_mAnalyticOn (c, c) (multibrotPost m)).comp₂_of_eq contMDiffAt_id
    (mAnalytic_coe _) rfl

/-- `bottcher d` is analytic outside the Multibrot set -/
theorem bottcherMAnalytic (d : ℕ) [Fact (2 ≤ d)] :
    ContMDiffOnNhd I I (bottcher d) (multibrotExt d) := by
  intro c m; induction c using OnePoint.rec
  · refine mAnalyticAt_fill_inf ?_ bottcher_tendsto_zero
    rw [hasBasis_cobounded_norm_lt.eventually_iff]; use 2
    simp only [true_and, mem_ofPred]
    intro z a; exact (bottcher_analytic _ (multibrot_two_lt a)).mAnalyticAt I I
  · simp only [multibrotExt_coe] at m
    exact mAnalyticAt_fill_coe ((bottcher_analytic (d := d) _ m).mAnalyticAt I I)

/-!
## The Multibrot potential map
-/

/-- The potential map on (OnePoint ℂ), defined as the diagonal of `s.potential` -/
def potential (d : ℕ) [Fact (2 ≤ d)] : (OnePoint ℂ) → ℝ :=
  fill (fun c ↦ (superF d).potential c c) 0

theorem norm_bottcher {c : (OnePoint ℂ)} : ‖bottcher d c‖ = potential d c := by
  set s := superF d
  induction c using OnePoint.rec
  · simp only [bottcher, potential, fill_inf, norm_zero]
  · simp only [bottcher, potential, fill_coe]; exact s.norm_bottcher

theorem potential_continuous : Continuous (potential d) := by
  set s := superF d; rw [continuous_iff_continuousAt]; intro c; induction c using OnePoint.rec
  · have e : potential d =ᶠ[𝓝 (∞ : (OnePoint ℂ))] fun c ↦ ‖bottcher d c‖ := by
      refine .of_forall fun c ↦ ?_; rw [← norm_bottcher]
    rw [continuousAt_congr e]
    exact continuous_norm.continuousAt.comp
      (bottcherMAnalytic d _ multibrotExt_inf).continuousAt
  · exact continuousAt_fill_coe ((Continuous.potential s).comp₂
      continuous_id continuous_coe).continuousAt

@[simp, bound] lemma potential_le_one {c : (OnePoint ℂ)} : potential d c ≤ 1 := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, zero_le_one]
  · simp only [potential, fill_coe, (superF d).potential_le_one]

theorem potential_lt_one {c : (OnePoint ℂ)} : potential d c < 1 ↔ c ∈ multibrotExt d := by
  set s := superF d
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, zero_lt_one, multibrotExt_inf]
  · constructor
    · intro h; contrapose h
      simp only [not_not, not_lt, multibrot_basin', potential, fill_coe, Super.basin,
        mem_ofPred, multibrotExt_coe] at h ⊢
      rw [s.potential_eq_one]; exact h
    · intro m; rw [← norm_bottcher]; simp only [bottcher, fill_coe]
      simp only [multibrotExt_coe] at m
      exact s.bottcher_lt_one (multibrotPost m)

@[simp, bound] theorem potential_nonneg {c : (OnePoint ℂ)} : 0 ≤ potential d c := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, le_refl]
  · simp only [potential, fill_coe]; exact (superF d).potential_nonneg

theorem potential_eq_zero {c : (OnePoint ℂ)} : potential d c = 0 ↔ c = (∞ : (OnePoint ℂ)) := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf]
  · simp only [potential, fill_coe, (superF d).potential_eq_zero_of_onePreimage]

theorem potential_eq_one {c : ℂ} : potential d c = 1 ↔ c ∈ multibrot d := by
  contrapose
  simp only [← multibrotExt_coe, ← potential_lt_one]
  have le : potential d c ≤ 1 := by bound
  grind

/-!
## Dynamical space bottcher facts
-/

@[simp] lemma spotential_coe_ne_zero {z : ℂ} : (superF d).potential c z ≠ 0 := by
  simp [(superF d).potential_eq_zero_of_onePreimage]

@[simp] lemma sbottcher_coe_ne_zero {z : ℂ} : (superF d).bottcher c z ≠ 0 := by
  rw [← norm_ne_zero_iff, (superF d).norm_bottcher]
  exact spotential_coe_ne_zero

/-!
## Surjectivity of `bottcher d`
-/

/-- `bottcher d` is nontrivial everywhere in `multibrotExt`,
    as otherwise trivality spreads throughout `(OnePoint ℂ)` -/
theorem bottcherNontrivial {c : (OnePoint ℂ)} (m : c ∈ multibrotExt d) :
    NontrivialMAnalyticAt (bottcher d) c := by
  by_cases h : ∃ᶠ e in 𝓝 c, bottcher d e ≠ bottcher d c
  exact
    { mAnalyticAt := bottcherMAnalytic d _ m
      nonconst := h }
  exfalso; simp only [Filter.not_frequently, not_not] at h
  set b := bottcher d c
  have b1 : ‖b‖ < 1 := by simp only [norm_bottcher, potential_lt_one, m, b]
  -- From bottcher d c = y near a point, show that bottcher d c = y everywhere in (OnePoint ℂ)
  set t := {c | c ∈ multibrotExt d ∧ ∀ᶠ e in 𝓝 c, bottcher d e = b}
  have tu : t = univ := by
    refine IsClopen.eq_univ ?_ ⟨c, m, h⟩; constructor
    · rw [isClosed_iff_frequently]; intro x e; by_contra xt
      have pb : potential d x = ‖b‖ := by
        apply tendsto_nhds_unique_of_frequently_eq potential_continuous.continuousAt
          continuousAt_const
        refine e.mp (.of_forall ?_); intro z ⟨_, h⟩; rw [← h.self_of_nhds, norm_bottcher]
      rw [← pb, potential_lt_one] at b1
      have e' : ∃ᶠ y in 𝓝[{x}ᶜ] x, y ∈ t := by
        simp only [frequently_nhdsWithin_iff, mem_compl_singleton_iff]
        refine e.mp (.of_forall fun z zt ↦ ⟨zt, ?_⟩)
        contrapose xt; rwa [← xt]
      contrapose xt; clear xt; use b1
      cases' ContMDiffAt.eventually_eq_or_eventually_ne (bottcherMAnalytic d _ b1)
        contMDiffAt_const with h h
      use h; contrapose h; simp only [Filter.not_eventually, not_not] at h ⊢
      exact e'.mp (.of_forall fun y yt ↦ yt.2.self_of_nhds)
    · rw [isOpen_iff_eventually]; intro e ⟨m, h⟩
      apply (isOpen_multibrotExt.eventually_mem m).mp
      apply (eventually_eventually_nhds.mpr h).mp
      exact .of_forall fun f h m ↦ ⟨m, h⟩
  -- Contradiction!
  have m0 : (0 : (OnePoint ℂ)) ∈ multibrotExt d :=
    haveI m : (0 : (OnePoint ℂ)) ∈ t := by simp only [tu, mem_univ]
    m.1
  simp only [← coe_zero, multibrotExt_coe, multibrot_zero, not_true] at m0

/-- `bottcher d` surjects onto `ball 0 1` -/
theorem bottcher_surj (d : ℕ) [Fact (2 ≤ d)] : bottcher d '' multibrotExt d = ball 0 1 := by
  set s := superF d
  apply subset_antisymm
  · intro w; simp only [mem_image]; intro ⟨c, m, e⟩; rw [← e]; clear e w
    induction c using OnePoint.rec
    · simp only [bottcher, fill_inf]; exact mem_ball_self one_pos
    · simp only [multibrotExt_coe] at m
      simp only [bottcher, fill_coe, bottcher', mem_ball, Complex.dist_eq, sub_zero]
      exact s.bottcher_lt_one (multibrotPost m)
  · refine _root_.trans ?_ interior_subset
    refine IsPreconnected.relative_clopen (convex_ball _ _).isPreconnected ?_ ?_ ?_
    · use 0, mem_ball_self one_pos, ∞
      simp only [multibrotExt_inf, bottcher, fill_inf, true_and]
    · -- Relative openness
      rw [IsOpen.interior_eq]; exact inter_subset_right
      rw [isOpen_iff_eventually]; intro z ⟨c, m, e⟩
      rw [← e, (bottcherNontrivial m).nhds_eq_map_nhds, Filter.eventually_map]
      exact
        (isOpen_multibrotExt.eventually_mem m).mp (.of_forall fun e m ↦ by use e, m)
    · -- Relative closedness
      intro x ⟨x1, m⟩; simp only [mem_ball, Complex.dist_eq, sub_zero] at x1
      rcases exists_between x1 with ⟨b, xb, b1⟩
      set t := {e | potential d e ≤ b}
      have ct : IsCompact t := (isClosed_le potential_continuous continuous_const).isCompact
      have ts : t ⊆ multibrotExt d := by
        intro c m; rw [← potential_lt_one]; exact lt_of_le_of_lt m b1
      have mt : x ∈ closure (bottcher d '' t) := by
        rw [mem_closure_iff_frequently] at m ⊢; apply m.mp
        have lt : ∀ᶠ y : ℂ in 𝓝 x, ‖y‖ < b :=
          continuous_norm.continuousAt.eventually_lt continuousAt_const xb
        refine lt.mp (.of_forall fun y lt m ↦ ?_)
        rcases m with ⟨c, _, cy⟩; rw [← cy]; rw [← cy, norm_bottcher] at lt
        exact ⟨c, lt.le, rfl⟩
      apply image_mono ts; rw [IsClosed.closure_eq] at mt; exact mt
      apply IsCompact.isClosed; apply IsCompact.image_of_continuousOn ct
      refine ContinuousOn.mono ?_ ts; exact (bottcherMAnalytic d).continuousOn

/-!
### Ineffective approximations
-/

/-- `s.bottcher c z ~ z⁻¹` for large `z` -/
theorem bottcher_large_approx (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).bottcher c z * z) (cobounded ℂ) (𝓝 1) := by
  set s := superF d
  have e : ∀ᶠ z : ℂ in cobounded ℂ, s.bottcher c z * z = s.bottcherNear c z * z := by
    suffices e : ∀ᶠ z : ℂ in cobounded ℂ, s.bottcher c z = s.bottcherNear c z by
      exact e.mp (.of_forall fun z e ↦ by rw [e])
    refine coe_tendsto_inf.eventually (p := fun z ↦ s.bottcher c z = s.bottcherNear c z) ?_
    apply s.bottcher_eq_bottcherNear
  rw [Filter.tendsto_congr' e]; clear e
  have m := bottcherNear_monic (s.superNearC.s (mem_univ c))
  simp only [hasDerivAt_iff_tendsto, sub_zero, bottcherNear_zero, smul_eq_mul, mul_one,
    Metric.tendsto_nhds_nhds, Real.dist_eq, Complex.dist_eq] at m
  simp only [Metric.tendsto_nhds, hasBasis_cobounded_norm_lt.eventually_iff, true_and, mem_ofPred,
    Complex.dist_eq]
  intro e ep; rcases m e ep with ⟨r, rp, h⟩; use 1 / r; intro z zr
  have az0 : ‖z‖ ≠ 0 := (lt_trans (one_div_pos.mpr rp) zr).ne'
  have z0 : z ≠ 0 := norm_ne_zero_iff.mp az0
  have zir : ‖z⁻¹‖ < r := by
    simp only [one_div, norm_inv] at zr ⊢; exact inv_lt_of_inv_lt₀ rp zr
  specialize @h z⁻¹ zir
  simp only [norm_inv, inv_inv, ← norm_mul, sub_mul, inv_mul_cancel₀ z0, abs_norm,
    mul_comm z _] at h
  simp only [Super.bottcherNear, extChartAt_inf, PartialEquiv.trans_apply,
    coePartialEquiv_symm_apply, Equiv.toPartialEquiv_apply, invEquiv_apply, RiemannSphere.inv_inf,
    toComplex_zero, sub_zero, inv_coe z0, toComplex_coe]
  exact h

/-- `s.potential c z ~ ‖z‖⁻¹` for large `z` -/
theorem potential_tendsto (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).potential c z * ‖z‖) (cobounded ℂ) (𝓝 1) := by
  set s := superF d
  have c := continuous_norm.continuousAt.tendsto.comp (bottcher_large_approx d c)
  simpa only [s.norm_bottcher, norm_mul, norm_one, Function.comp_def] using c

end
end Ray_Ray_Multibrot_Basic



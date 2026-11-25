-- Prove2me | solution 1 for Arxiv2412_03183.imaging_problem_convex
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:46:09.640334+00:00
-- url     : https://prove2.me/submissions/9fc4076a-b822-4c5b-bab4-1bcf616858c7

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace S71IC
open Arxiv2412_03183

variable {Nx Ny : ℕ}

lemma cvx_sum {ι : Type*} (t : Finset ι) (f : ι → Image Nx Ny → ℝ)
    (h : ∀ i ∈ t, ConvexOn ℝ univ (f i)) : ConvexOn ℝ univ (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) convex_univ
  | insert a t ha ih =>
    have h1 := h a (Finset.mem_insert_self a t)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine (h1.add h2).congr fun x _ => ?_
    simp [Finset.sum_insert ha]

lemma sq_cvx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : Image Nx Ny → E)
    (hφ : ∀ x y (a b : ℝ), a + b = 1 → φ (a • x + b • y) = a • φ x + b • φ y) :
    ConvexOn ℝ univ (fun x => ‖φ x‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  show ‖φ (a • x + b • y)‖ ^ 2 ≤ a • ‖φ x‖ ^ 2 + b • ‖φ y‖ ^ 2
  rw [hφ x y a b hab]
  have := ((convexOn_univ_norm (E := E)).pow (fun _ _ => norm_nonneg _) 2).2 (mem_univ (φ x))
    (mem_univ (φ y)) ha hb hab
  simpa using this

lemma abs_cvx (φ : Image Nx Ny → ℝ)
    (hφ : ∀ x y (a b : ℝ), a + b = 1 → φ (a • x + b • y) = a • φ x + b • φ y) :
    ConvexOn ℝ univ (fun x => |φ x|) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  show |φ (a • x + b • y)| ≤ a • |φ x| + b • |φ y|
  rw [hφ x y a b hab]
  have := (convexOn_univ_norm (E := ℝ)).2 (mem_univ (φ x)) (mem_univ (φ y)) ha hb hab
  simpa using this

end S71IC

open Arxiv2412_03183 S71IC in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ}
    {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (g : Gains N) (lam1 lam2 : ℝ)
    (hlam1 : 0 < lam1) (hlam2 : 0 < lam2) :
    ConvexOn ℝ nonnegImages (imagingObjective D lam1 lam2 g) := by
  have hvis : ∀ (x y : Image Nx Ny) (a b : ℝ) (k : Fin M),
      visFT D (a • x + b • y) k = (a : ℂ) * visFT D x k + (b : ℂ) * visFT D y k := by
    intro x y a b k
    simp only [visFT, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  have hdata : ConvexOn ℝ univ (fun x => dataLoss D x g) := by
    unfold dataLoss
    apply cvx_sum
    intro k _
    have h1 := sq_cvx (fun x : Image Nx Ny =>
      D.vobs k * g (D.first k) * starRingEnd ℂ (g (D.second k)) - visFT D x k) (by
        intro x y a b hab
        simp only [hvis, Complex.real_smul]
        have : (a : ℂ) + b = 1 := by exact_mod_cast hab
        linear_combination (-(D.vobs k * g (D.first k) * starRingEnd ℂ (g (D.second k)))) * this)
    have h2 := h1.smul (c := 1 / (2 * D.sigma k ^ 2)) (by positivity)
    refine h2.congr fun x _ => ?_
    simp only [smul_eq_mul]; ring
  have hl1 : ConvexOn ℝ univ (fun x : Image Nx Ny => l1Norm x) := by
    unfold l1Norm
    apply cvx_sum; intro i _
    apply cvx_sum; intro j _
    exact abs_cvx (fun x => x i j) (by intro x y a b _; simp)
  have htsv : ConvexOn ℝ univ (fun x : Image Nx Ny => tsv x) := by
    unfold tsv
    apply cvx_sum; intro i _
    apply cvx_sum; intro j _
    have hsq : ∀ (p q : Fin Nx × Fin Ny),
        ConvexOn ℝ univ (fun x : Image Nx Ny => (x p.1 p.2 - x q.1 q.2) ^ 2) := by
      intro p q
      have := sq_cvx (fun x : Image Nx Ny => x p.1 p.2 - x q.1 q.2) (by
        intro x y a b _; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
      simpa only [Real.norm_eq_abs, sq_abs] using this
    apply ConvexOn.add
    · by_cases h : 0 < i.val
      · simp only [h, if_true]; exact hsq (i, j) (_, j)
      · simp only [h, if_false]; exact convexOn_const 0 convex_univ
    · by_cases h : 0 < j.val
      · simp only [h, if_true]; exact hsq (i, j) (i, _)
      · simp only [h, if_false]; exact convexOn_const 0 convex_univ
  have hall : ConvexOn ℝ univ (imagingObjective D lam1 lam2 g) := by
    have := hdata.add ((hl1.smul hlam1.le).add (htsv.smul hlam2.le))
    refine this.congr fun x _ => ?_
    simp [imagingObjective, imgReg, smul_eq_mul]
  refine hall.subset (subset_univ _) ?_
  intro x hx y hy a b ha hb _ i j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx i j)) (mul_nonneg hb (hy i j))

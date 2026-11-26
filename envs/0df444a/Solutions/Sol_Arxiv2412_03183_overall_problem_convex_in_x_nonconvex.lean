-- Prove2me | solution 1 for Arxiv2412_03183.overall_problem_convex_in_x_nonconvex
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:43:00.754803+00:00
-- url     : https://prove2.me/submissions/61bddf16-d6b9-4310-b8be-c41b48118a24

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



variable {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ} {M : ℕ}

lemma dl_single (D : ObsSetup S N M Nx Ny) (a : GainIdx N) (c : ℂ) :
    dataLoss D 0 (c • Pi.single a 1) = 0 := by
  unfold dataLoss
  apply Finset.sum_eq_zero
  intro k _
  have hv : visFT D 0 k = 0 := by simp [visFT]
  have hp : (c • Pi.single a (1 : ℂ) : Gains N) (D.first k) *
      starRingEnd ℂ ((c • Pi.single a (1 : ℂ) : Gains N) (D.second k)) = 0 := by
    by_cases h : D.first k = a
    · have h2 : D.second k ≠ a := by
        intro h2; apply D.first_ne_second k; rw [h, h2]
      simp [Pi.single_apply, h2]
    · simp [Pi.single_apply, h]
  rw [hv, mul_assoc, hp]; simp

lemma reg_hom (D : ObsSetup S N M Nx Ny) (mu1 mu2 s : ℝ) (hs : 0 ≤ s) (g : Gains N) :
    gainReg D mu1 mu2 ((s : ℂ) • g) = s ^ 2 * gainReg D mu1 mu2 g := by
  unfold gainReg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs]
    ring
  · simp

lemma reg_nonneg (D : ObsSetup S N M Nx Ny) (mu1 mu2 : ℝ) (h1 : 0 ≤ mu1) (h2 : 0 ≤ mu2)
    (g : Gains N) : 0 ≤ gainReg D mu1 mu2 g := by
  unfold gainReg
  apply Finset.sum_nonneg
  intro p _
  split_ifs with h
  · have hw : 0 < stepWeight D p h := by
      unfold stepWeight
      apply one_div_pos.mpr
      apply sub_pos.mpr
      exact D.time_lt p.1 _ _ (by simp [predIdx, Fin.lt_def]; omega)
    positivity
  · exact le_refl _

end S71IC

open Arxiv2412_03183 S71IC in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    {N : S → ℕ} {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (hv : ∃ k, D.vobs k ≠ 0)
    (lam1 lam2 mu1 mu2 : ℝ) (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2) (hmu1 : 0 ≤ mu1)
    (hmu2 : 0 ≤ mu2) :
    (∀ g ∈ gainFeasible N,
      ConvexOn ℝ nonnegImages (fun x => jointObjective D lam1 lam2 mu1 mu2 (x, g))) ∧
    ¬ ConvexOn ℝ (nonnegImages ×ˢ gainFeasible N) (jointObjective D lam1 lam2 mu1 mu2) ∧
    ¬ ConvexOn ℝ (nonnegImages ×ˢ (Set.univ : Set (Gains N)))
      (jointObjective D lam1 lam2 mu1 mu2) := by
  obtain ⟨k0, hk0⟩ := hv
  refine ⟨fun g _ => ?_, ?_, ?_⟩
  · have hvis : ∀ (x y : Image Nx Ny) (a b : ℝ) (k : Fin M),
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
      have h2 := h1.smul (c := 1 / (2 * D.sigma k ^ 2)) (by have := D.sigma_pos k; positivity)
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
    have hall : ConvexOn ℝ univ (fun x => jointObjective D lam1 lam2 mu1 mu2 (x, g)) := by
      have := (hdata.add ((hl1.smul hlam1).add (htsv.smul hlam2))).add_const (gainReg D mu1 mu2 g)
      refine this.congr fun x _ => ?_
      simp [jointObjective, imgReg, smul_eq_mul]
    refine hall.subset (subset_univ _) ?_
    intro x hx y hy a b ha hb _ i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx i j)) (mul_nonneg hb (hy i j))
  · intro hc
    have hf1 : (fun _ => (1 : ℂ)) ∈ gainFeasible N := by intro α; simp
    have hf2 : (fun _ => (-1 : ℂ)) ∈ gainFeasible N := by intro α; simp
    have h0 : (0 : Image Nx Ny) ∈ nonnegImages := fun i j => le_refl _
    have := hc.1 (Set.mk_mem_prod h0 hf1) (Set.mk_mem_prod h0 hf2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have h2 := (Set.mem_prod.mp this).2 (D.first k0).1
    have hpos : 0 < N (D.first k0).1 := Fin.pos (D.first k0).2
    simp at h2
    norm_cast at h2
    omega
  · intro hc
    have hab : D.first k0 ≠ D.second k0 := fun h => D.first_ne_second k0 (by rw [h])
    let e : GainIdx N → Gains N := fun p => Pi.single p (1 : ℂ)
    have hJ : ∀ g, jointObjective D lam1 lam2 mu1 mu2 (0, g) = dataLoss D 0 g + gainReg D mu1 mu2 g := by
      intro g; simp [jointObjective, imgReg, l1Norm, tsv]
    set R := gainReg D mu1 mu2 (e (D.first k0)) + gainReg D mu1 mu2 (e (D.second k0)) with hR
    have hR0 : 0 ≤ R := add_nonneg (reg_nonneg D mu1 mu2 hmu1 hmu2 _) (reg_nonneg D mu1 mu2 hmu1 hmu2 _)
    have hσ : 0 < D.sigma k0 := D.sigma_pos k0
    have hvpos : 0 < ‖D.vobs k0‖ := norm_pos_iff.mpr hk0
    have key : ∀ s : ℝ, 0 < s → ‖D.vobs k0‖ ^ 2 * ((s / 2) ^ 2) ^ 2 / (2 * D.sigma k0 ^ 2) ≤ s ^ 2 * R / 2 := by
      intro s hs
      have h0 : (0 : Image Nx Ny) ∈ nonnegImages := fun i j => le_refl _
      have := hc.2 (Set.mk_mem_prod h0 (Set.mem_univ ((s : ℂ) • e (D.first k0))))
        (Set.mk_mem_prod h0 (Set.mem_univ ((s : ℂ) • e (D.second k0))))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      have hmid : (1 / 2 : ℝ) • ((0 : Image Nx Ny), (s : ℂ) • e (D.first k0)) +
          (1 / 2 : ℝ) • ((0 : Image Nx Ny), (s : ℂ) • e (D.second k0)) =
          (0, ((s / 2 : ℝ) : ℂ) • (e (D.first k0) + e (D.second k0))) := by
        refine Prod.ext ?_ ?_
        · simp
        · funext p
          simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Complex.real_smul]
          push_cast; ring
      rw [hmid, hJ, hJ, hJ, dl_single, dl_single, reg_hom _ _ _ s hs.le,
        reg_hom _ _ _ s hs.le] at this
      have hreg := reg_nonneg D mu1 mu2 hmu1 hmu2 (((s / 2 : ℝ) : ℂ) • (e (D.first k0) + e (D.second k0)))
      have hdl : ‖D.vobs k0‖ ^ 2 * ((s / 2) ^ 2) ^ 2 / (2 * D.sigma k0 ^ 2) ≤
          dataLoss D 0 (((s / 2 : ℝ) : ℂ) • (e (D.first k0) + e (D.second k0))) := by
        unfold dataLoss
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ k0))
        have hv0 : visFT D 0 k0 = 0 := by simp [visFT]
        simp only [hv0, sub_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul, e, Pi.single_apply,
          hab, hab.symm, if_true, if_false, add_zero, zero_add, mul_one, norm_mul, map_mul,
          Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < s / 2)]
        ring
      simp only [smul_eq_mul] at this
      linarith
    set A := 16 * D.sigma k0 ^ 2 * R / ‖D.vobs k0‖ ^ 2 with hA
    have hA0 : 0 ≤ A := by positivity
    have hs : 0 < A + 1 := by linarith
    have hk := key (A + 1) hs
    have h1 : ‖D.vobs k0‖ ^ 2 * (A + 1) ^ 2 ≤ 16 * D.sigma k0 ^ 2 * R := by
      have hs2 : 0 < (A + 1) ^ 2 := by positivity
      have h2 : ‖D.vobs k0‖ ^ 2 * ((A + 1) ^ 2) * (A + 1) ^ 2 ≤ 16 * D.sigma k0 ^ 2 * R * (A + 1) ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at hk
        nlinarith [hk]
      exact le_of_mul_le_mul_right h2 hs2
    have h3 : 16 * D.sigma k0 ^ 2 * R = ‖D.vobs k0‖ ^ 2 * A := by
      rw [hA]; field_simp
    have h4 : ‖D.vobs k0‖ ^ 2 * (A + 1) ≤ ‖D.vobs k0‖ ^ 2 * (A + 1) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have h5 : 0 < ‖D.vobs k0‖ ^ 2 := by positivity
    nlinarith

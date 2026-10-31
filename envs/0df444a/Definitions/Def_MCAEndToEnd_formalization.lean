-- Prove2me | Definitions.Def_MCAEndToEnd_formalization
-- name    : MCAEndToEnd_formalization
-- status  : Definition
-- author  : @chenyu
-- created : 2026-10-30T15:44:40.968163+00:00
-- url     : https://prove2.me/theorems/8120d8dc-2662-435f-baa8-a5f55e1785c5
-- title:
--   End-to-end metabolic control analysis formalization
-- statement:
--   A Lean 4 formalization of metabolic control analysis from differentiable enzyme rate functions, steady-state maps, and flux maps. The module defines derivative matrices using Mathlib fderiv and proves the steady-state linearization, concentration connectivity, concentration summation, flux summation, and flux connectivity identities under explicit differentiability, homogeneity, nondegeneracy, and left-inverse hypotheses.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Sections 2-3; https://arxiv.org/abs/2501.12519

import Mathlib

open scoped BigOperators
open Matrix

namespace MCAEndToEnd

noncomputable section

abbrev Vec (ι : Type) := ι → ℝ

def basis {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) : Vec ι :=
  Pi.single i 1

def derivativeMatrix {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (g : Vec κ → Vec ι) (x : Vec κ) : Matrix ι κ ℝ :=
  fun i j => (fderiv ℝ g x (basis j)) i

def scalarDerivativeMatrix {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (g : ι → Vec κ → ℝ) (x : Vec κ) : Matrix ι κ ℝ :=
  fun i j => fderiv ℝ (g i) x (basis j)

lemma clm_apply_eq_sum {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (L : (Vec κ) →L[ℝ] (Vec ι)) (x : Vec κ) (i : ι) :
    L x i = ∑ j, L (basis j) i * x j := by
  classical
  have hx : x = ∑ j, x j • basis j := by
    funext j
    simp [basis, Finset.sum_apply, Pi.single_apply]
  rw [hx]
  simp only [map_sum, map_smul, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp [smul_eq_mul, basis, Pi.single_apply, Finset.sum_apply,
    Finset.sum_ite_eq']
  ring

lemma scalar_clm_apply_eq_sum {κ : Type} [Fintype κ] [DecidableEq κ]
    (L : (Vec κ) →L[ℝ] ℝ) (x : Vec κ) :
    L x = ∑ j, L (basis j) * x j := by
  classical
  have hx : x = ∑ j, x j • basis j := by
    funext j
    simp [basis, Finset.sum_apply, Pi.single_apply]
  calc
    L x = L (∑ j, x j • basis j) := congrArg L hx
    _ = ∑ j, L (x j • basis j) := by
      rw [map_sum]
    _ = ∑ j, x j * L (basis j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [smul_eq_mul]
    _ = ∑ j, L (basis j) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma derivativeMatrix_apply {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (g : Vec κ → Vec ι) (x : Vec κ) (i : ι) (j : κ) :
    derivativeMatrix g x i j = (fderiv ℝ g x (basis j)) i := rfl

lemma scalarDerivativeMatrix_apply {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (g : ι → Vec κ → ℝ) (x : Vec κ) (i : ι) (j : κ) :
    scalarDerivativeMatrix g x i j = fderiv ℝ (g i) x (basis j) := rfl

section Core

variable {n m : ℕ}
variable (f : Fin n → Vec (Fin m) → ℝ)
variable (s : Vec (Fin n) → Vec (Fin m))
variable (N : Matrix (Fin m) (Fin n) ℝ)

def rate (p : Vec (Fin n)) (k : Fin n) : ℝ := p k * f k (s p)

def elasticityDerivative (p : Vec (Fin n)) : Matrix (Fin n) (Fin m) ℝ :=
  scalarDerivativeMatrix f (s p)

def sensitivityDerivative (p : Vec (Fin n)) : Matrix (Fin m) (Fin n) ℝ :=
  derivativeMatrix s p

def rateDerivative (p : Vec (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun k l =>
    (f k (s p)) * (if k = l then 1 else 0)
      + p k * ∑ j, elasticityDerivative f s p k j * sensitivityDerivative s p j l

lemma rate_hasFDerivAt
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p) :
    HasFDerivAt (fun q k => rate f s q k)
      (ContinuousLinearMap.pi (fun k =>
        (p k) • ((fderiv ℝ (f k) (s p)).comp (fderiv ℝ s p))
        + (f k (s p)) • (ContinuousLinearMap.proj k : Vec (Fin n) →L[ℝ] ℝ))) p := by
  change HasFDerivAt (fun q k => q k * f k (s q)) _ _
  apply (hasFDerivAt_pi).2
  intro k
  have hp : HasFDerivAt (fun q : Vec (Fin n) => q k)
      (ContinuousLinearMap.proj k : Vec (Fin n) →L[ℝ] ℝ) p := hasFDerivAt_apply k p
  have hcomp : HasFDerivAt (fun q : Vec (Fin n) => f k (s q))
      ((fderiv ℝ (f k) (s p)).comp (fderiv ℝ s p)) p := by
    simpa [Function.comp_def] using (hf k).comp p hs
  have hmul := hp.mul hcomp
  convert hmul using 1 <;> try { rfl } <;> try { apply Subsingleton.elim }

lemma steady_state_linearization
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q, N.mulVec (fun k => rate f s q k) = 0) :
    (N * Matrix.diagonal p * elasticityDerivative f s p) * sensitivityDerivative s p
        + N * Matrix.diagonal (fun k => f k (s p)) = 0 := by
  classical
  let L : (Vec (Fin n)) →L[ℝ] (Vec (Fin m)) :=
    (Matrix.mulVecLin N).toContinuousLinearMap
  let R : (Vec (Fin n)) →L[ℝ] (Vec (Fin n)) :=
    ContinuousLinearMap.pi (fun k =>
      (p k) • ((fderiv ℝ (f k) (s p)).comp (fderiv ℝ s p))
        + (f k (s p)) • (ContinuousLinearMap.proj k))
  have hrate : HasFDerivAt (fun q k => rate f s q k) R p := by
    simpa [R] using rate_hasFDerivAt f s p hf hs
  have hN : HasFDerivAt (fun q => N.mulVec (fun k => rate f s q k))
      (L.comp R) p := by
    have hc : HasFDerivAt (fun _ : Vec (Fin n) => L)
        (0 : Vec (Fin n) →L[ℝ] (Vec (Fin n) →L[ℝ] Vec (Fin m))) p :=
      hasFDerivAt_const L p
    have h := hc.clm_apply hrate
    simpa [L, R, ContinuousLinearMap.zero_apply, add_zero,
      Function.comp_def] using h
  have hconst : HasFDerivAt (fun _ : Vec (Fin n) => (0 : Vec (Fin m)))
      (0 : Vec (Fin n) →L[ℝ] Vec (Fin m)) p :=
    hasFDerivAt_const (0 : Vec (Fin m)) p
  have hfun : (fun q => N.mulVec (fun k => rate f s q k)) =
      (fun _ => (0 : Vec (Fin m))) := funext hsteady
  have hzero : (L.comp R) = 0 := by
    rw [hfun] at hN
    exact (hconst.unique hN).symm
  ext i l
  let D : Matrix (Fin n) (Fin m) ℝ := elasticityDerivative f s p
  let S : Matrix (Fin m) (Fin n) ℝ := sensitivityDerivative s p
  have hz := congrArg (fun K : (Vec (Fin n)) →L[ℝ] (Vec (Fin m)) => K (basis l) i) hzero
  simp only [ContinuousLinearMap.zero_apply, Pi.zero_apply] at hz
  have hsum : ∀ k, (R (basis l)) k =
      f k (s p) * (if k = l then 1 else 0)
        + p k * ∑ j, D k j * S j l := by
    intro k
    simp only [R, ContinuousLinearMap.pi_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    have hderiv :
        (fderiv ℝ (f k) (s p)) ((fderiv ℝ s p) (basis l)) =
          ∑ j, D k j * S j l := by
      rw [scalar_clm_apply_eq_sum]
      simp [D, S, elasticityDerivative, sensitivityDerivative,
        scalarDerivativeMatrix, derivativeMatrix]
    rw [hderiv]
    change p k * (∑ j, D k j * S j l) + f k (s p) * (basis l k) = _
    simp only [basis, Pi.single_apply]
    by_cases hkl : k = l
    · subst k
      simp
      ring
    · simp [hkl]
  have hz' : (∑ k, N i k * (R (basis l)) k) = 0 := by
    simpa [L, Matrix.mulVecLin, ContinuousLinearMap.comp_apply,
      Matrix.mulVec, dotProduct] using hz
  simp_rw [hsum] at hz'
  change ((N * Matrix.diagonal p * D) * S +
      N * Matrix.diagonal (fun k => f k (s p))) i l = 0
  have hmat :
      ((N * Matrix.diagonal p * D) * S +
        N * Matrix.diagonal (fun k => f k (s p))) i l =
        ∑ k, N i k *
          (f k (s p) * (if k = l then 1 else 0) +
            p k * ∑ j, D k j * S j l) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    have hdiag : ∀ a : Fin n, (∑ b, N i b * if b = a then p b else 0) = N i a * p a := by
      intro a
      simp [eq_comm]
    have hA :
        (∑ x, (∑ x₁, (∑ b, N i b * if b = x₁ then p b else 0) * D x₁ x) * S x l) =
          ∑ k, N i k * p k * ∑ j, D k j * S j l := by
      simp_rw [hdiag]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ x, N i k * p k * D k x * S x l) =
            ∑ x, (N i k * p k) * (D k x * S x l) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
        _ = N i k * p k * ∑ x, D k x * S x l := by
              rw [← Finset.mul_sum]
    have hB :
        (∑ k, N i k * (f k (s p) * if k = l then 1 else 0)) =
          N i l * f l (s p) := by
      simp [eq_comm]
    calc
      (∑ x, (∑ x₁, (∑ b, N i b * if b = x₁ then p b else 0) * D x₁ x) * S x l +
          ∑ j, N i j * if j = l then f j (s p) else 0) =
          (∑ k, N i k * p k * ∑ j, D k j * S j l) +
            N i l * f l (s p) := by rw [hA]; simp [hB, eq_comm]
      _ = (∑ k, N i k * p k * ∑ j, D k j * S j l) +
          (∑ k, N i k * (f k (s p) * if k = l then 1 else 0)) := by rw [← hB]
      _ = ∑ k, ((N i k * p k * ∑ j, D k j * S j l) +
          (N i k * (f k (s p) * if k = l then 1 else 0))) :=
        (Finset.sum_add_distrib).symm
      _ = ∑ k, N i k *
          (f k (s p) * (if k = l then 1 else 0) +
            p k * ∑ j, D k j * S j l) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [hmat]
  exact hz'

def elasticity (f : Fin n → Vec (Fin m) → ℝ)
    (state : Vec (Fin n) → Vec (Fin m)) (p : Vec (Fin n)) :
    Matrix (Fin n) (Fin m) ℝ :=
  fun k j => state p j / f k (state p) * elasticityDerivative f state p k j

def concentrationControl (state : Vec (Fin n) → Vec (Fin m))
    (p : Vec (Fin n)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i l => p l / state p i * sensitivityDerivative state p i l

def fluxVector {q : ℕ} (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → Vec (Fin m) → ℝ) (state : Vec (Fin n) → Vec (Fin m))
    (p : Vec (Fin n)) : Vec (Fin q) :=
  R.mulVec (fun k => rate f state p k)

def flux {q : ℕ} (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → Vec (Fin m) → ℝ) (state : Vec (Fin n) → Vec (Fin m))
    (p : Vec (Fin n)) (r : Fin q) : ℝ :=
  fluxVector R f state p r

def fluxDerivative {q : ℕ} (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → Vec (Fin m) → ℝ) (state : Vec (Fin n) → Vec (Fin m))
    (p : Vec (Fin n)) : Matrix (Fin q) (Fin n) ℝ :=
  fun r l => (fderiv ℝ (fluxVector R f state) p (basis l)) r

def fluxControl {q : ℕ} (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → Vec (Fin m) → ℝ) (state : Vec (Fin n) → Vec (Fin m))
    (p : Vec (Fin n)) : Matrix (Fin q) (Fin n) ℝ :=
  fun r l => p l / flux R f state p r * fluxDerivative R f state p r l

lemma flux_hasFDerivAt {q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p) :
    HasFDerivAt (fun q' => fluxVector R f s q')
      (((Matrix.mulVecLin R).toContinuousLinearMap).comp
        (ContinuousLinearMap.pi (fun k =>
          (p k) • ((fderiv ℝ (f k) (s p)).comp (fderiv ℝ s p))
            + (f k (s p)) •
                (ContinuousLinearMap.proj k : Vec (Fin n) →L[ℝ] ℝ)))) p := by
  let Rd : (Vec (Fin n)) →L[ℝ] (Vec (Fin n)) :=
    ContinuousLinearMap.pi (fun k =>
      (p k) • ((fderiv ℝ (f k) (s p)).comp (fderiv ℝ s p))
        + (f k (s p)) • (ContinuousLinearMap.proj k : Vec (Fin n) →L[ℝ] ℝ))
  have hrate : HasFDerivAt (fun q' k => rate f s q' k) Rd p := by
    simpa [Rd] using rate_hasFDerivAt f s p hf hs
  let L : (Vec (Fin n)) →L[ℝ] (Vec (Fin q)) :=
    (Matrix.mulVecLin R).toContinuousLinearMap
  have hc : HasFDerivAt (fun _ : Vec (Fin n) => L)
      (0 : Vec (Fin n) →L[ℝ] (Vec (Fin n) →L[ℝ] Vec (Fin q))) p :=
    hasFDerivAt_const L p
  have h := hc.clm_apply hrate
  simpa [fluxVector, L, Rd, ContinuousLinearMap.zero_apply, add_zero,
    Function.comp_def] using h

lemma flux_derivative_formula {q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p) :
    fluxDerivative R f s p =
      R * (Matrix.diagonal (fun k => f k (s p)) +
        Matrix.diagonal p * elasticityDerivative f s p * sensitivityDerivative s p) := by
  classical
  let Rd : (Vec (Fin n)) →L[ℝ] (Vec (Fin n)) :=
    ContinuousLinearMap.pi (fun k =>
      (p k) • ((fderiv ℝ (f k) (s p)).comp (fderiv ℝ s p))
        + (f k (s p)) • (ContinuousLinearMap.proj k : Vec (Fin n) →L[ℝ] ℝ))
  let L : (Vec (Fin n)) →L[ℝ] (Vec (Fin q)) :=
    (Matrix.mulVecLin R).toContinuousLinearMap
  have hrate : HasFDerivAt (fun q' k => rate f s q' k) Rd p := by
    simpa [Rd] using rate_hasFDerivAt f s p hf hs
  have hflux : HasFDerivAt (fun q' => fluxVector R f s q') (L.comp Rd) p := by
    have hc : HasFDerivAt (fun _ : Vec (Fin n) => L)
        (0 : Vec (Fin n) →L[ℝ] (Vec (Fin n) →L[ℝ] Vec (Fin q))) p :=
      hasFDerivAt_const L p
    have h := hc.clm_apply hrate
    simpa [fluxVector, L, Rd, ContinuousLinearMap.zero_apply, add_zero,
      Function.comp_def] using h
  have hderiv := hflux.fderiv
  ext r l
  have hcomp : ∀ k,
      (fderiv ℝ (f k) (s p)) ((fderiv ℝ s p) (basis l)) =
        ∑ j, elasticityDerivative f s p k j * sensitivityDerivative s p j l := by
    intro k
    rw [scalar_clm_apply_eq_sum]
    simp [elasticityDerivative, sensitivityDerivative, scalarDerivativeMatrix,
      derivativeMatrix, basis]
  have hRd : ∀ k, Rd (basis l) k =
      f k (s p) * (if k = l then 1 else 0) +
        p k * ∑ j, elasticityDerivative f s p k j * sensitivityDerivative s p j l := by
    intro k
    simp [Rd, ContinuousLinearMap.pi_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    rw [hcomp k]
    simp [basis, Pi.single_apply]
    ring
  have hentry := congrArg
      (fun K : (Vec (Fin n)) →L[ℝ] Vec (Fin q) => K (basis l) r) hderiv
  simp only [fluxDerivative, fluxVector] at hentry
  change fluxDerivative R f s p r l = _ at hentry
  have hentry' : fluxDerivative R f s p r l =
      ∑ k, R r k * Rd (basis l) k := by
    simpa [L, ContinuousLinearMap.comp_apply, Matrix.mulVecLin,
      Matrix.mulVec, dotProduct] using hentry
  simp_rw [hRd] at hentry'
  simpa [Matrix.mul_apply, Matrix.add_apply, Matrix.diagonal_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, scalarDerivativeMatrix, derivativeMatrix,
    basis, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hentry'

lemma homogeneous_vector_euler {q : ℕ}
    (g : Vec (Fin n) → Vec (Fin q)) (p : Vec (Fin n))
    (hg : HasFDerivAt g (fderiv ℝ g p) p)
    (hscale : ∀ c : ℝ, 0 < c → g (c • p) = c • g p) :
    ∀ r, ∑ l, (fderiv ℝ g p (basis l)) r * p l = g p r := by
  classical
  have hscalar : HasFDerivAt (fun c : ℝ => c • p)
      (ContinuousLinearMap.toSpanSingleton ℝ p) 1 := by
    simpa [id] using (hasDerivAt_id (1 : ℝ)).smul_const p |>.hasFDerivAt
  have hcomp : HasFDerivAt (fun c : ℝ => g (c • p))
      ((fderiv ℝ g p).comp (ContinuousLinearMap.toSpanSingleton ℝ p)) 1 := by
    have hg' : HasFDerivAt g (fderiv ℝ g p) ((1 : ℝ) • p) := by simpa using hg
    simpa [Function.comp_def] using hg'.comp (1 : ℝ) hscalar
  have hpos : ∀ᶠ c : ℝ in nhds (1 : ℝ), 0 < c :=
    eventually_gt_nhds (by norm_num)
  have hev : (fun c : ℝ => g (c • p)) =ᶠ[nhds (1 : ℝ)]
      (fun c : ℝ => c • g p) := by
    filter_upwards [hpos] with c hc
    exact hscale c hc
  have hconst : HasFDerivAt (fun c : ℝ => c • g p)
      (ContinuousLinearMap.toSpanSingleton ℝ (g p)) 1 := by
    simpa [id] using (hasDerivAt_id (1 : ℝ)).smul_const (g p) |>.hasFDerivAt
  have hsame := hcomp.congr_of_eventuallyEq hev.symm
  have hzero : (fderiv ℝ g p).comp (ContinuousLinearMap.toSpanSingleton ℝ p) =
      ContinuousLinearMap.toSpanSingleton ℝ (g p) :=
    (hconst.unique hsame).symm
  intro r
  have hr := congrArg
      (fun K : (ℝ →L[ℝ] Vec (Fin q)) => K 1 r) hzero
  have happly : (fderiv ℝ g p) p r =
      ∑ l, (fderiv ℝ g p (basis l)) r * p l := by
    rw [clm_apply_eq_sum]
  calc
    ∑ l, (fderiv ℝ g p (basis l)) r * p l = (fderiv ℝ g p) p r := happly.symm
    _ = g p r := by simpa [ContinuousLinearMap.comp_apply] using hr

theorem flux_summation {q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hscale : ∀ c : ℝ, 0 < c → s (c • p) = s p)
    (hJ0 : ∀ r, flux R f s p r ≠ 0) :
    ∀ r, ∑ l, fluxControl R f s p r l = 1 := by
  classical
  have hscaleJ : ∀ c : ℝ, 0 < c →
      fluxVector R f s (c • p) = c • fluxVector R f s p := by
    intro c hc
    ext r
    simp [fluxVector, rate, hscale c hc, Matrix.mulVec, Pi.smul_apply,
      dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hflux := flux_hasFDerivAt f s R p hf hs
  have hfluxf : HasFDerivAt (fluxVector R f s)
      (fderiv ℝ (fluxVector R f s) p) p := by
    rw [hflux.fderiv]
    exact hflux
  have heuler := homogeneous_vector_euler (fluxVector R f s) p hfluxf hscaleJ
  intro r
  calc
    ∑ l, fluxControl R f s p r l =
        (1 / flux R f s p r) *
          ∑ l, fluxDerivative R f s p r l * p l := by
            simp only [fluxControl, flux]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l hl
            field_simp
    _ = (1 / flux R f s p r) * fluxVector R f s p r := by
      change (1 / flux R f s p r) *
        ∑ l, (fderiv ℝ (fluxVector R f s) p (basis l)) r * p l = _
      rw [heuler r]
    _ = 1 := by
      simpa [flux] using (inv_mul_cancel₀ (hJ0 r))

lemma homogeneous_concentration_sum
    (p : Vec (Fin n))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hscale : ∀ c : ℝ, 0 < c → s (c • p) = s p) :
    ∀ i, ∑ l, sensitivityDerivative s p i l * p l = 0 := by
  classical
  have hscalar : HasFDerivAt (fun c : ℝ => c • p)
      (ContinuousLinearMap.toSpanSingleton ℝ p) 1 := by
    simpa [id] using (hasDerivAt_id (1 : ℝ)).smul_const p |>.hasFDerivAt
  have hcomp : HasFDerivAt (fun c : ℝ => s (c • p))
      ((fderiv ℝ s p).comp (ContinuousLinearMap.toSpanSingleton ℝ p)) 1 := by
    have hs' : HasFDerivAt s (fderiv ℝ s p) ((1 : ℝ) • p) := by simpa using hs
    simpa [Function.comp_def] using hs'.comp (1 : ℝ) hscalar
  have hpos : ∀ᶠ c : ℝ in nhds (1 : ℝ), 0 < c :=
    eventually_gt_nhds (by norm_num)
  have hev : (fun c : ℝ => s (c • p)) =ᶠ[nhds (1 : ℝ)]
      (fun _ : ℝ => s p) := by
    filter_upwards [hpos] with c hc
    exact hscale c hc
  have hconst : HasFDerivAt (fun _ : ℝ => s p)
      (0 : ℝ →L[ℝ] Vec (Fin m)) (1 : ℝ) :=
    hasFDerivAt_const (s p) 1
  have hsame : HasFDerivAt (fun _ : ℝ => s p)
      ((fderiv ℝ s p).comp (ContinuousLinearMap.toSpanSingleton ℝ p)) 1 :=
    hcomp.congr_of_eventuallyEq hev.symm
  have hzero : (fderiv ℝ s p).comp (ContinuousLinearMap.toSpanSingleton ℝ p) = 0 :=
    (hconst.unique hsame).symm
  intro i
  have hi := congrArg
      (fun L : (ℝ →L[ℝ] Vec (Fin m)) => L 1 i) hzero
  simp only [ContinuousLinearMap.zero_apply, Pi.zero_apply] at hi
  have happly : (fderiv ℝ s p) p i =
      ∑ l, sensitivityDerivative s p i l * p l := by
    rw [clm_apply_eq_sum]
    simp [sensitivityDerivative, derivativeMatrix, basis]
  have hi' : (fderiv ℝ s p) p i = 0 := by
    simpa [ContinuousLinearMap.comp_apply] using hi
  calc
    ∑ l, sensitivityDerivative s p i l * p l = (fderiv ℝ s p) p i := happly.symm
    _ = 0 := hi'

theorem concentration_summation
    (p : Vec (Fin n))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hscale : ∀ c : ℝ, 0 < c → s (c • p) = s p)
    (hs0 : ∀ i, s p i ≠ 0) :
    ∀ i, ∑ l, concentrationControl s p i l = 0 := by
  intro i
  have hsum := homogeneous_concentration_sum s p hs hscale i
  simp only [concentrationControl]
  calc
    ∑ l, p l / s p i * sensitivityDerivative s p i l =
        (1 / s p i) * ∑ l, sensitivityDerivative s p i l * p l := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          field_simp
    _ = 0 := by rw [hsum]; simp

lemma diagonal_inverse_left
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    Matrix.diagonal (fun i => 1 / a i) * Matrix.diagonal a = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ha i]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

lemma diagonal_inverse_right
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    Matrix.diagonal a * Matrix.diagonal (fun i => 1 / a i) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ha i]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

lemma sensitivity_core_identity
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q, N.mulVec (fun k => rate f s q k) = 0)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hAinv : Ainv * (N * Matrix.diagonal p * elasticityDerivative f s p) = 1)
    (hf0 : ∀ k, f k (s p) ≠ 0) :
    sensitivityDerivative s p * Matrix.diagonal p *
        Matrix.diagonal (fun k => 1 / f k (s p)) *
        elasticityDerivative f s p =
      -(1 : Matrix (Fin m) (Fin m) ℝ) := by
  classical
  let D := elasticityDerivative f s p
  let S := sensitivityDerivative s p
  let F := Matrix.diagonal (fun k => f k (s p))
  let P := Matrix.diagonal p
  let Finv := Matrix.diagonal (fun k => 1 / f k (s p))
  have hlin := steady_state_linearization f s N p hf hs hsteady
  have hlin' : N * P * D * S = -(N * F) := by
    have h := eq_neg_of_add_eq_zero_left hlin
    simpa [D, S, F, P, Matrix.mul_assoc] using h
  have hPFinv : F * P * Finv = P := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [F, P, Finv]
      field_simp [hf0 i]
    · simp [F, P, Finv, Matrix.diagonal_apply_ne _ hij]
  calc
    S * P * Finv * D = (1 : Matrix (Fin m) (Fin m) ℝ) *
        (S * P * Finv * D) := (Matrix.one_mul _).symm
    _ = (Ainv * (N * P * D)) * S * P * Finv * D := by
      rw [hAinv]
      simp
    _ = Ainv * (N * P * D * S) * P * Finv * D := by
      simp [Matrix.mul_assoc]
    _ = Ainv * (-(N * F)) * P * Finv * D := by rw [hlin']
    _ = -(Ainv * N) * (F * P * Finv) * D := by
      simp [Matrix.mul_assoc]
    _ = -(Ainv * N) * P * D := by rw [hPFinv]
    _ = -(Ainv * (N * P * D)) := by simp [Matrix.mul_assoc]
    _ = -1 := by rw [hAinv]

lemma normalized_connectivity
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q, N.mulVec (fun k => rate f s q k) = 0)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hAinv : Ainv * (N * Matrix.diagonal p * elasticityDerivative f s p) = 1)
    (_hp : ∀ k, p k ≠ 0)
    (hf0 : ∀ k, f k (s p) ≠ 0)
    (hs0 : ∀ i, s p i ≠ 0) :
    concentrationControl s p * elasticity f s p = -1 := by
  classical
  let D := elasticityDerivative f s p
  let S := sensitivityDerivative s p
  let F := Matrix.diagonal (fun k => f k (s p))
  let P := Matrix.diagonal p
  let Finv := Matrix.diagonal (fun k => 1 / f k (s p))
  have hcore := sensitivity_core_identity f s N p hf hs hsteady Ainv hAinv hf0
  have hCS : concentrationControl s p =
      Matrix.diagonal (fun i => 1 / s p i) * S * P := by
    ext a b
    simp [concentrationControl, S, P, sensitivityDerivative,
      Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply,
      hs0 a]
    field_simp [hs0 a]
  have hE : elasticity f s p =
      Finv * D * Matrix.diagonal (s p) := by
    ext a b
    change s p b / f a (s p) * D a b =
      (Finv * D * Matrix.diagonal (s p)) a b
    rw [Matrix.mul_diagonal]
    rw [Matrix.diagonal_mul]
    simp [Finv, hf0 a]
    field_simp [hf0 a]
  rw [hCS, hE]
  calc
    (Matrix.diagonal (fun i => 1 / s p i) * S * P) *
        (Finv * D * Matrix.diagonal (s p)) =
      Matrix.diagonal (fun i => 1 / s p i) * (S * P * Finv * D) *
        Matrix.diagonal (s p) := by simp [Matrix.mul_assoc]
    _ = -1 := by
      rw [hcore]
      ext a b
      by_cases hab : a = b
      · subst b
        simp [hs0 a]
      · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply, hab]

theorem flux_connectivity {q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (p : Vec (Fin n))
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q', N.mulVec (fun k => rate f s q' k) = 0)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hAinv : Ainv * (N * Matrix.diagonal p * elasticityDerivative f s p) = 1)
    (_hp : ∀ k, p k ≠ 0)
    (hf0 : ∀ k, f k (s p) ≠ 0)
    (hJ0 : ∀ r, flux R f s p r ≠ 0) :
    ∀ r j, ∑ l, fluxControl R f s p r l * elasticity f s p l j = 0 := by
  classical
  let D := elasticityDerivative f s p
  let S := sensitivityDerivative s p
  let F := Matrix.diagonal (fun k => f k (s p))
  let P := Matrix.diagonal p
  let Finv := Matrix.diagonal (fun k => 1 / f k (s p))
  let V := F + P * D * S
  have hcore := sensitivity_core_identity f s N p hf hs hsteady Ainv hAinv hf0
  have hcore' : S * P * Finv * D =
      -(1 : Matrix (Fin m) (Fin m) ℝ) := by
    simpa [S, P, Finv, D] using hcore
  have hPFinv : F * P * Finv = P := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [F, P, Finv]
      field_simp [hf0 i]
    · simp [F, P, Finv, Matrix.diagonal_apply_ne _ hij]
  have hVzero : V * P * Finv * D = 0 := by
    calc
      V * P * Finv * D = F * P * Finv * D + P * D * (S * P * Finv * D) := by
        simp [V, Matrix.add_mul, Matrix.mul_assoc]
      _ = P * D + P * D * (-(1 : Matrix (Fin m) (Fin m) ℝ)) := by
        rw [hPFinv, hcore']
      _ = 0 := by simp [Matrix.mul_assoc]
  have hzero : R * V * P * Finv * D = 0 := by
    calc
      R * V * P * Finv * D = R * (V * P * Finv * D) := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [hVzero]; simp
  have hfd := flux_derivative_formula f s R p hf hs
  have hzero' : fluxDerivative R f s p * P * Finv * D = 0 := by
    rw [hfd]
    exact hzero
  intro r j
  have hz := congrArg (fun M : Matrix (Fin q) (Fin m) ℝ => M r j) hzero'
  have hz' : ∑ l, fluxDerivative R f s p r l *
        (p l * (1 / f l (s p))) * D l j = 0 := by
    simpa [P, Finv, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.mul_assoc] using hz
  calc
    ∑ l, fluxControl R f s p r l * elasticity f s p l j =
        (1 / flux R f s p r) * (s p j) *
          ∑ l, fluxDerivative R f s p r l *
            (p l * (1 / f l (s p))) * D l j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [fluxControl, elasticity, flux]
      field_simp [hJ0 r, hf0 l]
      ring
    _ = 0 := by rw [hz']; simp

end Core

end

end MCAEndToEnd



-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_Fourier
-- name    : OptimalTraceDistance_Estimation_Fourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:41:57.173204+00:00
-- url     : https://prove2.me/theorems/1577805c-feda-491c-b9f6-63c3cf5fec68
-- title:
--   Weighted operator bases, contractions and Fourier weights
-- statement:
--   An operator basis has identity as index zero and is orthonormal for $\operatorname{tr}(\tau A^*B)$; its spanning property makes it a basis of the full complex operator space. It need not consist of Hermitian matrices. Tensor Fourier coefficients are computed in this basis; support counts nonzero indices and weights sum squared moduli at each support size.
--
--   The contraction of a $k$-register kernel to $j$ registers is the partial trace against $\tau^{\otimes(k-j)}$, given by explicit finite coordinate sums. Effective kernels are $B_j=\sum_{k=j}^D\binom{k}{j}(h_k)_{\tau\to j}$. The cycle factor is $\prod_{\ell=0}^{j-1}(1+\ell\beta)/(j-1)!$. There are no variance identities or analytic bounds among these definitions. Full rank is required only in theorem clauses involving a genuine weighted basis.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), §4.1, pp.13–16, equations (30)–(39).

import Definitions.Def_OptimalTraceDistance_Estimation_Observables

open scoped BigOperators Matrix Classical
noncomputable section

namespace OptimalTraceDistance.Estimation

structure FourierBasis (m : ℕ) (τ : Mat m) where
  operator : Fin (m*m) → Mat m
  identity : ∀ i, i.val = 0 → operator i = 1
  orthonormal : ∀ a b, (τ * (operator a)ᴴ * operator b).trace = if a=b then 1 else 0
  spanning : ∀ B : Mat m, ∃ c : Fin (m*m) → ℂ, B = ∑ i, c i • operator i

def fourierCoeff {m : ℕ} {τ : Mat m} (F : FourierBasis m τ) {r : ℕ}
    (G : Op m r) (α : Fin r → Fin (m*m)) : ℂ :=
  weightedInner τ r (tensor r (fun i => F.operator (α i))) G

def supportSize {m r : ℕ} (α : Fin r → Fin (m*m)) : ℕ :=
  (Finset.univ.filter (fun i => (α i).val ≠ 0)).card

def fourierWeight {m : ℕ} {τ : Mat m} (F : FourierBasis m τ) {r : ℕ}
    (G : Op m r) (j : ℕ) : ℝ :=
  ∑ α : Fin r → Fin (m*m), if supportSize α = j then ‖fourierCoeff F G α‖^2 else 0

def glue {m k j : ℕ} (x : Register m j) (z : Register m (k-j)) : Register m k :=
  fun i => if h : i.val < j then x ⟨i.val,h⟩ else z ⟨i.val-j, by omega⟩

def contraction {m : ℕ} (τ : Mat m) (k j : ℕ) (H : Op m k) : Op m j :=
  fun x y => ∑ z : Register m (k-j), ∑ w : Register m (k-j),
    H (glue x z) (glue y w) * powerState τ (k-j) w z

def effectiveKernel {m : ℕ} (τ : Mat m) (D : ℕ) (h : (k : ℕ) → Op m k) (j : ℕ) : Op m j :=
  ∑ k ∈ Finset.Icc j D, (Nat.choose k j : ℂ) • contraction τ k j (h k)

def kernelSum {m : ℕ} (n D : ℕ) (f₀ : ℝ) (h : (k : ℕ) → Op m k) : Op m n :=
  (f₀ : ℂ) • 1 + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)

def symmetric {m k : ℕ} (H : Op m k) : Prop :=
  ∀ π : Equiv.Perm (Fin k), permutationOp π * H * (permutationOp π)ᴴ = H

def varianceSum {m : ℕ} (τ : Mat m) (n D : ℕ) (h : (k : ℕ) → Op m k) : ℝ :=
  ∑ j ∈ Finset.Icc 1 D, (Nat.choose n j : ℝ)⁻¹ *
    weightedNormSq τ j (effectiveKernel τ D h j)

def cycleFactor (β : ℝ) (j : ℕ) : ℝ :=
  (∏ l ∈ Finset.range j, (1 + (l : ℝ)*β)) / ((j-1).factorial : ℝ)

end OptimalTraceDistance.Estimation



-- Prove2me | Definitions.Def_GabidulinProx_UniqueDecoding_Codes
-- name    : GabidulinProx_UniqueDecoding_Codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:46.499106+00:00
-- url     : https://prove2.me/theorems/f0401843-7641-4bd9-87b4-791420ae073c
-- title:
--   Gabidulin codes and the exact parameter thresholds
-- statement:
--   Let $q=|K|$ for a finite base field $K$, and let $\alpha_1,\ldots,\alpha_n\in L$. Evaluation of message coefficients defines an $L$-linear map, and its range is
--
--   $$G(A,k)=\left\{\left(\sum_{i<k}c_i\alpha_r^{q^i}\right)_{r<n}:c\in L^k\right\}.$$
--
--   The definition does not assume a minimum-distance formula. Source theorems require $1\le k\le n$ and $K$-linear independence of the evaluation points. The zero coefficient family gives a codeword even at $k=0$.
--
--   The exact thresholds are
--
--   $$\sigma_r=\sum_{i=0}^r q^i,\qquad B=(\sigma_e-1)\sigma_{k-1}+1,\qquad
--   \tau_e=(\sigma_e-1)+\sigma_e B.$$
--
--   All source uses of $\sigma_{k-1}$ assume $k\ge1$. For $e=0$ one has $\sigma_0=\tau_0=1$.
--
--   Given a line and an integer radius, the good set $S$ is constructed by testing distance to this Gabidulin code. For an input polynomial $a_0$, its regular subset is $S_0=\{z\in S:a_0(z)\ne0\}$. These definitions fix the objects used throughout the proof chain and contain no theorem as an assumed code property.
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Definition 2.4 p.13; Theorem 1.3 p.5; §3.2 pp.19,21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Polynomials
import Definitions.Def_GabidulinProx_UniqueDecoding_RankMetric

open scoped BigOperators

namespace GabidulinProx.UniqueDecoding

/-- Definition 2.4, p.13: evaluation of all k message coefficients. -/
noncomputable def gabidulinEncoder (K : Type*) {L : Type*} [Field K] [Fintype K]
    [Field L] {n : ℕ} (α : Fin n → L) (k : ℕ) : (Fin k → L) →ₗ[L] (Fin n → L) where
  toFun c r := ∑ i, c i * (α r) ^ (Fintype.card K ^ i.val)
  map_add' c d := by
    ext r
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext r
    simp [Finset.mul_sum, mul_assoc]

/-- Gabidulin code as a linear code. No distance or MRD property is assumed in this definition. -/
noncomputable def gabidulin (K : Type*) {L : Type*} [Field K] [Fintype K] [Field L]
    {n : ℕ} (α : Fin n → L) (k : ℕ) : Submodule L (Fin n → L) :=
  LinearMap.range (gabidulinEncoder K α k)

/-- σ_r from Theorem 1.3, p.5 and §3.2, p.19. -/
def sigma (q r : ℕ) : ℕ := ∑ i ∈ Finset.range (r + 1), q ^ i

/-- τ_e; all source uses assume k≥1. At e=0 and q≥2 this is 1. -/
def tau (q k e : ℕ) : ℕ :=
  (sigma q e - 1) + sigma q e * ((sigma q e - 1) * sigma q (k - 1) + 1)

/-- The degree threshold in Lemmas 3.6 and 3.7. -/
def clearingBound (q k e : ℕ) : ℕ := (sigma q e - 1) * sigma q (k - 1) + 1

/-- S on p.19: constructed from the line and its distance to G(A,k). -/
noncomputable def goodParameters (K : Type*) {L : Type*} [Field K] [Fintype K]
    [Field L] [Fintype L] [Algebra K L] {n : ℕ} (α : Fin n → L) (k e : ℕ)
    (u₀ u₁ : Fin n → L) : Finset L := by
  classical
  exact Finset.univ.filter (fun z => codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e)

/-- S₀ on p.21; a₀ is an input, never chosen from an unproved lemma. -/
noncomputable def regularParameters {L : Type*} [Field L]
    (S : Finset L) (a₀ : Polynomial L) : Finset L := by
  classical
  exact S.filter (fun z => a₀.eval z ≠ 0)

end GabidulinProx.UniqueDecoding



-- Prove2me | Definitions.Def_WalkTreeCluster_ComputeCorrelation
-- name    : WalkTreeCluster_ComputeCorrelation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:48:54.191621+00:00
-- url     : https://prove2.me/theorems/dc21a66e-e1b9-4f8f-9e38-32fcc8d5c13b
-- title:
--   ComputeCorrelation (Algorithm 6): $N$, $b_h$, its samples and its median-of-means output
-- statement:
--   The uncapped call ComputeCorrelation$(u,v,i,h)$ sets $N=\lceil16384\,\alpha^2a^{-40}\rceil$ and $b_h=2\lceil\log_4(300(h+1))\rceil+1$, draws $b_hN$ independent filter path collisions $\langle X_{r,\ell},X'_{r,\ell}\rangle_w$ with $X_{r,\ell}\sim X_{u,i}$ and $X'_{r,\ell}\sim X_{v,i}$ independent (Algorithm 4), forms the averages $A_r=N^{-1}\sum_{\ell=1}^N\langle X_{r,\ell},X'_{r,\ell}\rangle_w$, and returns
--   $$\langle F_i\mathbb 1_u,F_i\mathbb 1_v\rangle_{w,h}=\operatorname{median}(A_1,\dots,A_{b_h}).$$
--   The module records the joint law of the $b_hN$ sample pairs and the output as a function of the samples.
--
--   **Formalization Note.** $b_h$ is odd, so the median is the middle order statistic. Probabilities of events about the output are measures of sets of samples.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Algorithm 6, p.61; Algorithm 4, p.19

import Mathlib
import Definitions.Def_WalkTreeCluster_Laws

open MeasureTheory

namespace WalkTreeCluster

/-!
# ComputeCorrelation (Algorithm 6)

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Algorithm 6, p.61; Algorithm 4, p.19.

The uncapped call `ComputeCorrelation(u, v, i, h)` sets `N = ⌈16384 α² a^{−40}⌉`,
`b_h = 2⌈log₄(300(h + 1))⌉ + 1`, draws `b_h · N` independent filter path collisions
`⟨X_{r,ℓ}, X'_{r,ℓ}⟩_w` with `X_{r,ℓ} ∼ X_{u,i}`, `X'_{r,ℓ} ∼ X_{v,i}` independent (Algorithm 4),
averages them in `b_h` groups of `N`, `A_r = N⁻¹ Σ_ℓ ⟨X_{r,ℓ}, X'_{r,ℓ}⟩_w`, and returns the median
of `A_1, …, A_{b_h}`.

**Formalization Note.** `corrSampleLaw` is the joint law of the `b_h · N` sample pairs and
`corrEstimate` the returned value as a function of the samples; probabilities about the output are
measures of sets of samples (outer measures when a set is not measurable). Since `b_h = 2k + 1` is
odd, the median is the `(k + 1)`-th smallest value, the entry `k` of the sorted list.
-/

/-- `N = ⌈16384 α² a^{−40}⌉` (Algorithm 6, line 1). -/
noncomputable def corrN (ϵ ϕ : ℝ) : ℕ :=
  ⌈16384 * alphaParam ϵ ϕ ^ 2 * aParam ϵ ϕ ^ (-(40 : ℝ))⌉₊

/-- `k` with `b_h = 2k + 1`, `k = ⌈log₄(300(h + 1))⌉` (Algorithm 6, line 1). -/
noncomputable def corrHalf (h : ℕ) : ℕ :=
  ⌈Real.logb 4 (300 * ((h : ℝ) + 1))⌉₊

/-- The median of an odd number `2k + 1` of reals: the entry `k` of the sorted list. -/
noncomputable def medianOdd {k : ℕ} (A : Fin (2 * k + 1) → ℝ) : ℝ :=
  ((List.ofFn A).mergeSort (fun x y => decide (x ≤ y))).getD k 0

/-- The joint law of the samples of an uncapped `ComputeCorrelation(u, v, i, h)`: `b_h × N`
independent pairs `(X, X')`, `X ∼ X_{u,i}`, `X' ∼ X_{v,i}` independent. -/
noncomputable def corrSampleLaw {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
    (u v : Fin n) (i h : ℕ) :
    Measure (Fin (2 * corrHalf h + 1) → Fin (corrN ϵ ϕ) → Mat n i × Mat n i) :=
  Measure.pi (fun _ => Measure.pi (fun _ =>
    (walkLaw nbr ϵ ϕ i u).prod (walkLaw nbr ϵ ϕ i v)))

/-- The output `⟨F_i 1_u, F_i 1_v⟩_{w,h} = median(A_1, …, A_{b_h})` on the samples `S`
(Algorithm 6, lines 3–4). -/
noncomputable def corrEstimate (ϵ ϕ : ℝ) {n i : ℕ} (h : ℕ)
    (S : Fin (2 * corrHalf h + 1) → Fin (corrN ϵ ϕ) → Mat n i × Mat n i) : ℝ :=
  medianOdd (fun r => (1 / (corrN ϵ ϕ : ℝ)) *
    ∑ ℓ, wInner (aParam ϵ ϕ) (S r ℓ).1 (S r ℓ).2)

end WalkTreeCluster



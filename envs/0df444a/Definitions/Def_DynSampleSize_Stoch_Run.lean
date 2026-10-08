-- Prove2me | Definitions.Def_DynSampleSize_Stoch_Run
-- name    : DynSampleSize_Stoch_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:28.976061+00:00
-- url     : https://prove2.me/theorems/4dedc718-2976-43a0-af9d-0e547f2665c3
-- title:
--   (4.24) — the dynamic batch steepest descent run with i.i.d. batches
-- statement:
--   Let $L>0$, a sample-size sequence $(n_k)_{k\ge0}$ of natural numbers, a starting point $w_0\in\mathbb R^m$ and an array of draws $\xi=(\xi_{k,i})_{k,i\ge0}$ from the data space $Z$ be given. The **dynamic batch steepest descent run** (4.24), p. 11, is
--   $$
--   w_{k+1}=w_k-\frac1L\,g_k,\qquad g_k=\frac1{n_k}\sum_{i=0}^{n_k-1}\nabla\ell(w_k;\xi_{k,i}),
--   $$
--   so iteration $k$ uses the batch $S_k=(\xi_{k,0},\dots,\xi_{k,n_k-1})$ of size $n_k$ and evaluates the batch gradient (4.19) at the current iterate.
--
--   The **sampling law** makes all draws $\xi_{k,i}$ independent, each with law $P$: the infinite product measure $\bigotimes_{(k,i)\in\mathbb N\times\mathbb N}P$. Batches are therefore drawn with replacement and independently across iterations, and $w_k$ depends only on the batches of iterations $0,\dots,k-1$, which is what the paper's "if we condition on $w_k$, the only random quantity … is $g_k$" (p. 11) expresses.
--
--   The expectations $\mathbb E[J(w_k)]$ of Theorem 4.2 are taken under this law.
--
--   **Formalization Note** The paper's sampling (3.5) is without replacement from a training set of size $N$; on p. 5 it lets $N\to\infty$ and notes the resulting condition "also corresponds to the case of sampling with replacement". The proof of Theorem 4.2 uses only $\|\mathrm{Var}(g_k)\|_1\le\|\mathrm{Var}(\nabla\ell)\|_1/n_k$, which i.i.d. sampling satisfies. The sampling law is `Measure.infinitePi (fun _ : ℕ × ℕ => P)`.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 10, (4.19); p. 11, (4.24); p. 5, sampling with replacement after (3.9)

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_Model

open MeasureTheory

namespace DynSampleSize.Stoch

/-- (4.24), p. 11: the dynamic batch steepest descent run `w_{k+1} = w_k − (1/L) g_k`, where `g_k` is
the batch gradient (4.19) at `w_k` of the `n_k` draws `ξ(k, 0), …, ξ(k, n_k − 1)` of iteration `k`. -/
noncomputable def run {m : ℕ} {Z : Type*} (L : ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m)) (n : ℕ → ℕ)
    (w0 : EuclideanSpace ℝ (Fin m)) (ξ : ℕ × ℕ → Z) : ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => w0
  | k + 1 => run L gradℓ n w0 ξ k -
      (1 / L) • batchGrad gradℓ (n k) (run L gradℓ n w0 ξ k) (fun i => ξ (k, (i : ℕ)))

/-- The sampling law: all draws `ξ(k, i)` are independent with law `P` (i.i.d. sampling with
replacement, independent across iterations). -/
noncomputable def sampleLaw {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P] :
    Measure (ℕ × ℕ → Z) :=
  Measure.infinitePi (fun _ : ℕ × ℕ => P)

end DynSampleSize.Stoch



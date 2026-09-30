-- Prove2me | Definitions.Def_StochQuasiNewton_SQN_Algorithm
-- name    : StochQuasiNewton_SQN_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:51:17.359213+00:00
-- url     : https://prove2.me/theorems/93c12bcc-9add-4396-811a-1a6a6b8a74f9
-- title:
--   Algorithm 1 (SQN Method) and the expectation over its samples
-- statement:
--   **Algorithm 1 (SQN Method).** Inputs: the losses $f_i$, positive integers $M$ (memory) and $L$ (pair interval), step lengths $\alpha^k$, an initial point $w^1$, gradient samples $\mathcal S_k$ ($k\ge1$) and Hessian samples $\mathcal S_{H,t}$ ($t\ge1$). For $k=1,2,\dots$:
--
--   1. the pair counter at the start of iteration $k$ is $t=\lfloor (k-1)/L\rfloor-1$;
--   2. if $t<1$ (i.e. $k\le 2L$), take a stochastic gradient step $w^{k+1}=w^k-\alpha^k\nabla F_{\mathcal S_k}(w^k)$; otherwise $w^{k+1}=w^k-\alpha^kH_t\nabla F_{\mathcal S_k}(w^k)$ with $H_t$ from Algorithm 2;
--   3. every $L$ iterations a new pair is formed from the block averages
--   $$\bar w_t=\frac1L\sum_{j=tL+1}^{(t+1)L}w^j\quad(t\ge0),\qquad s_t=\bar w_t-\bar w_{t-1},\qquad y_t=\nabla^2F_{\mathcal S_{H,t}}(\bar w_t)\,s_t\quad(t\ge1).$$
--
--   The file defines the iterates $w^k$ (`sqnIterate`), the matrix applied at iteration $k$ (`sqnAppliedMatrix`: the identity or $H_t$), the pairs $s_t,y_t$ (`sqnPairS`, `sqnPairY`), and $H_t$ (`sqnHessianApprox`).
--
--   **Expectation.** `sampleExpectation N b bH k Φ` is the average of $\Phi(\mathcal S,\mathcal S_H)$ over all sample histories in which $\mathcal S_0,\dots,\mathcal S_{k-1}$ are $b$-element subsets and $\mathcal S_{H,0},\dots,\mathcal S_{H,k-1}$ are $b_H$-element subsets of $\{1,\dots,N\}$: this is the expectation when every sample is drawn uniformly among subsets of its size, all independently. The iterate $w^k$ depends only on samples with index $<k$, so $E[F(w^k)]$ is exactly such an average.
--
--   **Formalization Note** The iterate sequence is built through histories: `sqnHistory … m j` equals $w^j$ for $1\le j\le m+1$. Indices $k$ and $t$ start at $1$ as in the paper; Algorithm 1's initial $t=-1$ is encoded by the offset $t=\lfloor (k-1)/L\rfloor-1$. The averaging of step 12 is used; Eq. (2.1) of the paper writes $\bar w_t=\sum_{i=k-L}^{k}w^i$ ($L+1$ terms, no $1/L$), which disagrees with Algorithm 1; the algorithm is followed. Unused sample indices (index $0$, indices $\ge k$) do not affect $w^k$.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1012, Algorithm 1; p. 1011, Eqs. (2.1)–(2.3); p. 1009, (1.4) and the sentence after it

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- Step 12 of Algorithm 1: the average `w̄_t = ∑_{j = tL+1}^{(t+1)L} w_j / L` of the `t`-th block
of `L` iterates (`t = 0, 1, …`), read from an iterate history `h` (`h j = w_j`). -/
noncomputable def blockAverage {n : ℕ} (L : ℕ) (h : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (1 / (L : ℝ)) • ∑ j ∈ Finset.Icc (t * L + 1) ((t + 1) * L), h j

/-- Step 15 of Algorithm 1: `s_t = w̄_t − w̄_{t−1}` (used for `t ≥ 1`). -/
noncomputable def corrS {n : ℕ} (L : ℕ) (h : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  blockAverage L h t - blockAverage L h (t - 1)

/-- Steps 14–15 of Algorithm 1: `y_t = ∇²F_{S_{H,t}}(w̄_t)(w̄_t − w̄_{t−1})`, with the Hessian
sample `SH t` drawn for the `t`-th pair (used for `t ≥ 1`). -/
noncomputable def corrY {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (L : ℕ)
    (SH : ℕ → Finset (Fin N)) (h : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  subsampledHessian f (SH t) (blockAverage L h t) (corrS L h t)

/-- The matrix Algorithm 1 applies at iteration `k ≥ 1`. When iteration `k` starts, the pair
counter is `t = ⌊(k − 1)/L⌋ − 1`. If `t < 1` (i.e. `⌊(k − 1)/L⌋ < 2`) the step is a stochastic
gradient step (step 6), i.e. the matrix is the identity; otherwise it is `H_t` of Algorithm 2
built from the pairs `(s_j, y_j)` of the history (step 8). -/
noncomputable def stepMatrix {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ)
    (SH : ℕ → Finset (Fin N)) (h : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  if (k - 1) / L < 2 then 1
  else lbfgsMatrix M ((k - 1) / L - 1) (corrS L h) (corrY f L SH h)

/-- The iterate histories of Algorithm 1 (SQN Method) for the losses `f`, memory `M`, pair
interval `L`, step lengths `α` (`α k` is `α^k`), initial point `w1`, gradient samples `S k`
(drawn at iteration `k ≥ 1`) and Hessian samples `SH t` (drawn for pair `t ≥ 1`).
`sqnHistory … m j = w_j` for `1 ≤ j ≤ m + 1`: history `m + 1` extends history `m` by
`w^{m+2} = w^{m+1} − α^{m+1} H ∇F_{S_{m+1}}(w^{m+1})`, with `H` given by `stepMatrix`. -/
noncomputable def sqnHistory {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ)
    (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)) :
    ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => fun _ => w1
  | m + 1 => fun j =>
      if j = m + 2 then
        sqnHistory f M L α w1 S SH m (m + 1) -
          α (m + 1) • Matrix.toEuclideanLin
            (stepMatrix f M L SH (sqnHistory f M L α w1 S SH m) (m + 1))
            (miniBatchGrad f (S (m + 1)) (sqnHistory f M L α w1 S SH m (m + 1)))
      else sqnHistory f M L α w1 S SH m j

/-- The iterate `w^k` of Algorithm 1, for `k ≥ 1`. -/
noncomputable def sqnIterate {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ)
    (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  sqnHistory f M L α w1 S SH (k - 1) k

/-- The matrix applied by Algorithm 1 at iteration `k ≥ 1` (the identity or `H_t`). -/
noncomputable def sqnAppliedMatrix {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (M L : ℕ) (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  stepMatrix f M L SH (sqnHistory f M L α w1 S SH (k - 1)) k

/-- The correction vector `s_t` computed by Algorithm 1 (formed at iteration `(t + 1) L`). -/
noncomputable def sqnPairS {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ)
    (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)) (t : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  corrS L (sqnHistory f M L α w1 S SH ((t + 1) * L)) t

/-- The correction vector `y_t` computed by Algorithm 1 (formed at iteration `(t + 1) L`). -/
noncomputable def sqnPairY {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ)
    (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)) (t : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  corrY f L SH (sqnHistory f M L α w1 S SH ((t + 1) * L)) t

/-- The Hessian approximation `H_t` (`t ≥ 1`) generated by Algorithm 1: Algorithm 2 applied to
the correction pairs `(s_j, y_j)` of the run. -/
noncomputable def sqnHessianApprox {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (M L : ℕ) (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  lbfgsMatrix M t (sqnPairS f M L α w1 S SH) (sqnPairY f M L α w1 S SH)

/-- Extends a finite sample history `σ 0, …, σ (k − 1)` to a sequence indexed by `ℕ`
(empty samples from index `k` on). -/
def extendSamples {N k : ℕ} (σ : Fin k → Finset (Fin N)) : ℕ → Finset (Fin N) :=
  fun j => if h : j < k then σ ⟨j, h⟩ else ∅

/-- Expectation over the sampling of Algorithm 1 up to index `k − 1`: the gradient samples
`S 0, …, S (k − 1)` are independent and uniform among the `b`-element subsets of `{1, …, N}`, the
Hessian samples `SH 0, …, SH (k − 1)` are independent and uniform among the `b_H`-element subsets,
and the two families are independent. `sampleExpectation N b bH k Φ` is the average of
`Φ S SH` over all such histories. It is the expectation of any quantity (such as `F(w^k)`) that
depends only on the samples with index `< k`. -/
noncomputable def sampleExpectation (N b bH k : ℕ)
    (Φ : (ℕ → Finset (Fin N)) → (ℕ → Finset (Fin N)) → ℝ) : ℝ :=
  (∑ σ ∈ Fintype.piFinset (fun _ : Fin k => Finset.powersetCard b (Finset.univ : Finset (Fin N))),
      ∑ τ ∈ Fintype.piFinset
          (fun _ : Fin k => Finset.powersetCard bH (Finset.univ : Finset (Fin N))),
        Φ (extendSamples σ) (extendSamples τ)) /
    (((Fintype.piFinset
          (fun _ : Fin k => Finset.powersetCard b (Finset.univ : Finset (Fin N)))).card : ℝ) *
      ((Fintype.piFinset
          (fun _ : Fin k => Finset.powersetCard bH (Finset.univ : Finset (Fin N)))).card : ℝ))

end StochQuasiNewton.SQN



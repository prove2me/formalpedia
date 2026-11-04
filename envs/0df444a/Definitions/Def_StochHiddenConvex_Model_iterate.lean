-- Prove2me | Definitions.Def_StochHiddenConvex_Model_iterate
-- name    : StochHiddenConvex_Model_iterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:42.269839+00:00
-- url     : https://prove2.me/theorems/e52d592f-3935-460d-b652-5ae66b882d3d
-- title:
--   Mirror Stochastic Gradient (Algorithm 2) as a random process
-- statement:
--   Mirror Stochastic Gradient (MSG) with $T$ iterations, constant stepsize $\gamma$, initialization $x^1$, regularization $\lambda$ and truncation level $K$ runs, for $t=1,\dots,T$:
--
--   1. draw $k_1,k_2$ independently and uniformly from $\{0,\dots,K-1\}$ and i.i.d. samples $\{\tilde\xi^{ti}\}_{i=1}^{k_1}$, $\{\tilde\xi^{tj}\}_{j=1}^{k_2}$, and form the two estimators (9) with $c=2$,
--   $$[\nabla\hat g^A(x^t)]^{-1}=\frac{K}{2L_\phi}\prod_{i=1}^{k_1}\Big(I-\frac{\nabla\phi(x^t,\tilde\xi^{ti})}{2L_\phi}\Big),\qquad[\nabla\hat g^B(x^t)]^{-1}=\frac{K}{2L_\phi}\prod_{j=1}^{k_2}\Big(I-\frac{\nabla\phi(x^t,\tilde\xi^{tj})}{2L_\phi}\Big);$$
--   2. draw $\xi^t\sim\mathbb P(\xi)$ and form $v_G(u^t)=[\nabla\hat g^B(x^t)]^{-\top}\nabla\phi(x^t,\xi^t)^\top\nabla f(\phi(x^t,\xi^t))$ and $v_F(x^t)=[\nabla\hat g^A(x^t)]^{-\top}v_G(u^t)+\lambda x^t$;
--   3. update $x^{t+1}=\Pi_{\mathcal X}(x^t-\gamma v_F(x^t))$.
--
--   The output $\hat x^T$ is selected uniformly from $\{x^t\}_{t=1}^T$. The definition provides the law of one iteration's randomness, $v_G$, $v_F$, the update, the iterates, the law of a run (independent randomness at every iteration) and the law of the run together with the uniformly drawn output index.
--
--   **Formalization Note** All matrices are diagonal and carried as vectors of diagonal entries. Each sample block has $K-1$ samples of which the first $k_1$ (resp. $k_2$) are used. The iterate with Lean index $n$ is the paper's $x^{n+1}$, and $\hat x^T=x^{\tau+1}$ for an independent index $\tau$ uniform on $\{0,\dots,T-1\}$. $\Pi_{\mathcal X}$ is coordinatewise clamping.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Algorithm 2, p.14; Eq. (22), p.38

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_invEst

open MeasureTheory ProbabilityTheory

namespace StochHiddenConvex

/-- The fresh randomness of one iteration of MSG (Chen, He, Hu & Ye, arXiv:2205.01774v3,
Algorithm 2, p.14), `ω = (k₁, k₂, a, b, ξ)`: the two truncation levels `k₁, k₂ ∈ {0, …, K − 1}`,
the two sample blocks `a = (ξ̃^{ti})ᵢ` and `b = (ξ̃^{tj})ⱼ` (each `K − 1` samples, of which the
first `k₁`, resp. `k₂`, are used), and the sample `ξ^t`. -/
abbrev Noise (d K : ℕ) :=
  Fin K × Fin K × (Fin (K - 1) → Fin d → ℝ) × (Fin (K - 1) → Fin d → ℝ) × (Fin d → ℝ)

namespace Model

variable {d : ℕ} (M : Model d)

/-- The law of one iteration's randomness (arXiv:2205.01774v3, Algorithm 2, line 2–3, p.14):
`k₁, k₂` independent and uniform on `{0, …, K − 1}`, two independent blocks of i.i.d. samples
from `ℙ(ξ)`, and an independent sample `ξ^t ∼ ℙ(ξ)`. -/
noncomputable def iterMeasure [IsProbabilityMeasure M.P] (K : ℕ) : Measure (Noise d K) :=
  (uniformOn (Set.univ : Set (Fin K))).prod ((uniformOn (Set.univ : Set (Fin K))).prod
    ((Measure.pi fun _ : Fin (K - 1) => M.P).prod
      ((Measure.pi fun _ : Fin (K - 1) => M.P).prod M.P)))

/-- `v_G` of the proof of Theorem 3.2 (arXiv:2205.01774v3, p.38):
`v_G(u^t) := [∇ĝ^B(x^t)]^{−⊤} ∇ϕ(x^t, ξ^t)ᵀ ∇f(ϕ(x^t, ξ^t))`, with the estimator `[∇ĝ^B]⁻¹` of
(9) at `c = 2` built from `(k₂, b)`. All matrices are diagonal, so the `i`-th coordinate is
`[∇ĝ^B]⁻¹ᵢᵢ · ∂ϕᵢ(xᵢ, ξᵢ^t) · (∇f(ϕ(x, ξ^t)))ᵢ`. -/
noncomputable def vG (Lphi : ℝ) (K : ℕ) (x : Vec d) (ω : Noise d K) : Vec d :=
  WithLp.toLp 2 (fun i => M.invEst 2 Lphi K x ω.2.1 ω.2.2.2.1 i *
    M.dphi i (x i) (ω.2.2.2.2 i) * (gradient M.f (M.phiVec x ω.2.2.2.2)) i)

/-- The gradient estimator of MSG (arXiv:2205.01774v3, Algorithm 2, line 3, p.14, and (22), p.38):
`v_F(x^t) = [∇ĝ^A(x^t)]^{−⊤}[∇ĝ^B(x^t)]^{−⊤} ∇ϕ(x^t, ξ^t)ᵀ ∇f(ϕ(x^t, ξ^t)) + λ x^t
= [∇ĝ^A(x^t)]^{−⊤} v_G(u^t) + λ x^t`, with `[∇ĝ^A]⁻¹` built from `(k₁, a)`. -/
noncomputable def vF (Lphi lam : ℝ) (K : ℕ) (x : Vec d) (ω : Noise d K) : Vec d :=
  WithLp.toLp 2 (fun i => M.invEst 2 Lphi K x ω.1 ω.2.2.1 i * M.vG Lphi K x ω i + lam * x i)

/-- One MSG update (arXiv:2205.01774v3, Algorithm 2, line 4, p.14):
`x^{t+1} = Π_𝒳(x^t − γ v_F(x^t))`, with the constant stepsize `γ_t = γ` of Theorem 3.2. -/
noncomputable def msgStep (Lphi lam γ : ℝ) (K : ℕ) (x : Vec d) (ω : Noise d K) : Vec d :=
  M.projBox (x - γ • M.vF Lphi lam K x ω)

/-- The MSG iterates (arXiv:2205.01774v3, Algorithm 2, p.14) driven by the per-iteration
randomness `w : Fin T → Noise d K`: `iterate … 0 w = x¹` and
`iterate … (n + 1) w = msgStep (iterate … n w) (w n)` for `n < T`.

**Formalization Note.** Index shift: `iterate … n` is the paper's `x^{n+1}`, and `w n` is the
randomness of the paper's iteration `t = n + 1`. Beyond `T` the sequence is frozen (never used). -/
noncomputable def iterate (Lphi lam γ : ℝ) (K T : ℕ) (x1 : Vec d) :
    ℕ → (Fin T → Noise d K) → Vec d
  | 0, _ => x1
  | n + 1, w =>
    if h : n < T then M.msgStep Lphi lam γ K (iterate Lphi lam γ K T x1 n w) (w ⟨n, h⟩)
    else iterate Lphi lam γ K T x1 n w

/-- The law of a run of `T` iterations: fresh, independent randomness at every iteration. -/
noncomputable def runMeasure [IsProbabilityMeasure M.P] (K T : ℕ) : Measure (Fin T → Noise d K) :=
  Measure.pi fun _ : Fin T => M.iterMeasure K

/-- The law of a run together with the output index: the run, and an independent index `τ`
uniform on `{0, …, T − 1}` (the paper's "x̂^T is selected uniformly from {x^t}_{t=1}^T"). -/
noncomputable def outMeasure [IsProbabilityMeasure M.P] (K T : ℕ) :
    Measure ((Fin T → Noise d K) × Fin T) :=
  (M.runMeasure K T).prod (uniformOn (Set.univ : Set (Fin T)))

/-- The output `x̂^T` of MSG (arXiv:2205.01774v3, Algorithm 2, p.14): the iterate `x^{τ+1}` for the
uniform index `τ`. -/
noncomputable def output (Lphi lam γ : ℝ) (K T : ℕ) (x1 : Vec d)
    (p : (Fin T → Noise d K) × Fin T) : Vec d :=
  M.iterate Lphi lam γ K T x1 (p.2 : ℕ) p.1

end Model

end StochHiddenConvex



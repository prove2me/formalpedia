-- Prove2me | Definitions.Def_RegMCBSDE_Projection_Scheme
-- name    : RegMCBSDE_Projection_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:45.300978+00:00
-- url     : https://prove2.me/theorems/5c76416e-c528-4aff-a2b8-59a3e5958842
-- title:
--   Definition 1 and (9), pp. 10–11 — the projection-Picard scheme Y^{N,i,I}, Z^{N,i,I} and A^N(S_0)
-- statement:
--   This file defines the projection–Picard scheme of Definition 1 by the least-squares rule (9).
--
--   Fix the number $I$ of Picard iterations. The scheme is described by deterministic coefficient vectors $\alpha^{i,I}_{l,k}\in\mathbb R^{n_{l,k}}$ ($i\ge0$, $0\le k\le N-1$, $0\le l\le q$), which define
--   $$Y^{N,i,I}_{t_k}=\alpha^{i,I}_{0,k}\cdot p_{0,k}(P^N_{t_k}),\qquad Z^{N,i,I}_{l,t_k}=\alpha^{i,I}_{l,k}\cdot p_{l,k}(P^N_{t_k})\quad(1\le l\le q),$$
--   with the convention $Y^{N,i,I}_{t_N}=\Phi^N(P^N_{t_N})$ for every $i$ and $I$.
--
--   The family $\alpha$ is a **projection–Picard scheme with $I$ iterations** if:
--
--   1. $\alpha^{0,I}_{l,k}=0$ for all $l$ and $k<N$, so $Y^{N,0,I}_{t_k}=0$ and $Z^{N,0,I}_{t_k}=0$;
--   2. for every $i\ge1$ and $k<N$, $\alpha^{i,I}_k=(\alpha^{i,I}_{l,k})_{0\le l\le q}$ minimizes over $(\alpha_0,\dots,\alpha_q)$ the quantity
--   $$\mathbb E\Big(Y^{N,I,I}_{t_{k+1}}-\alpha_0\cdot p_{0,k}+h\,f_k(\alpha^{i-1,I}_k)-\sum_{l=1}^q\alpha_l\cdot p_{l,k}\,\Delta W_{l,k}\Big)^2,\tag{9}$$
--   where $h=T/N$ and $f_k(\alpha^{i-1,I}_k)=f(t_k,S^N_{t_k},Y^{N,i-1,I}_{t_k},Z^{N,i-1,I}_{t_k})$.
--
--   Thus $Y^{N,I,I}$ is obtained backwards in time, by $I$ regressions at each date. The file also defines
--   $$\mathcal A^N(S_0)=1+|S_0|^2+\mathbb E|\Phi^N(P^N_{t_N})|^2,$$
--   the size of the data that the error bounds of §4 are expressed in.
--
--   **Formalization Note** The paper runs $i=1,\dots,I$; the rule is imposed for every $i\ge1$ (the Picard iterations simply continue), which the bound (19) over $i\ge0$ refers to. The expectation in (9) is taken in $[0,\infty]$; under the standing hypotheses it is finite. The scheme is the relation (9), not the closed form (10)–(11), which is a milestone.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, pp. 10–11, Definition 1 and Eq. (9); p. 11, Proof of Theorem 2 (definition of A^N(S_0))

import Mathlib
import Definitions.Def_RegMCBSDE_Projection_Projection

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- **The iterate `Y^{N,i,I}_{t_k}`** of Definition 1 (pp. 10–11), read off its projection
coefficients `α i k 0 = α^{i,I}_{0,k}`: `Y^{N,i,I}_{t_k} = α^{i,I}_{0,k} · p_{0,k}(P^N_{t_k})` for
`k < N`, and `Y^{N,i,I}_{t_N} = Φ^N(P^N_{t_N})` independently of `i` (and of `I`). -/
noncomputable def schemeY {Ω : Type*} {d' q : ℕ} (N : ℕ) (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d'))
    (ΦN : EuclideanSpace ℝ (Fin d') → ℝ) {n : Fin (q + 1) → ℕ → ℕ}
    (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ)
    (α : ℕ → (k : ℕ) → (l : Fin (q + 1)) → Fin (n l k) → ℝ) (i k : ℕ) : Ω → ℝ :=
  if N ≤ k then fun ω => ΦN (PN N ω) else fun ω => α i k 0 ⬝ᵥ p 0 k (PN k ω)

/-- **The iterate `Z^{N,i,I}_{t_k} ∈ ℝ^q`** of Definition 1: its component `m : Fin q` (the
paper's `l = m + 1`) is `Z^{N,i,I}_{l,t_k} = α^{i,I}_{l,k} · p_{l,k}(P^N_{t_k})`. -/
noncomputable def schemeZ {Ω : Type*} {d' q : ℕ} (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d'))
    {n : Fin (q + 1) → ℕ → ℕ}
    (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ)
    (α : ℕ → (k : ℕ) → (l : Fin (q + 1)) → Fin (n l k) → ℝ) (i k : ℕ) :
    Ω → EuclideanSpace ℝ (Fin q) :=
  fun ω => WithLp.toLp 2 (fun m : Fin q => α i k m.succ ⬝ᵥ p m.succ k (PN k ω))

/-- **The least-squares criterion (9)** (p. 10) at time `t_k` and Picard step `i ≥ 1`, evaluated
at candidate coefficients `β = (β_0, …, β_q)`:
`𝔼( Y^{N,I,I}_{t_{k+1}} - β_0 · p_{0,k} + h f_k(α^{i-1,I}_k) - ∑_{l=1}^q β_l · p_{l,k} ΔW_{l,k} )^2`,
where `h = T/N` and `f_k(α^{i-1,I}_k) = f(t_k, S^N_{t_k}, Y^{N,i-1,I}_{t_k}, Z^{N,i-1,I}_{t_k})`.
The expectation is taken in `[0, ∞]`. -/
noncomputable def objective9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d q d' : ℕ}
    (T : ℝ) (N : ℕ)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (S0 : EuclideanSpace ℝ (Fin d)) (ΔW : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (ΦN : EuclideanSpace ℝ (Fin d') → ℝ)
    {n : Fin (q + 1) → ℕ → ℕ}
    (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ)
    (I : ℕ) (α : ℕ → (k : ℕ) → (l : Fin (q + 1)) → Fin (n l k) → ℝ) (i k : ℕ)
    (β : (l : Fin (q + 1)) → Fin (n l k) → ℝ) : ENNReal :=
  ∫⁻ ω, ‖schemeY N PN ΦN p α I (k + 1) ω - β 0 ⬝ᵥ p 0 k (PN k ω)
      + (T / N) * f (gridTime T N k) (euler T N b σ S0 ΔW k ω)
          (schemeY N PN ΦN p α (i - 1) k ω) (schemeZ PN p α (i - 1) k ω)
      - ∑ m : Fin q, (β m.succ ⬝ᵥ p m.succ k (PN k ω)) * ΔW k ω m‖ₑ ^ 2 ∂P

/-- **The projection-Picard scheme with `I` iterations** (Definition 1 and (9), pp. 10–11), as a
relation on the coefficient family `α i k l = α^{i,I}_{l,k}` (`i ≥ 0`, `0 ≤ k ≤ N - 1`,
`0 ≤ l ≤ q`):

* `α^{0,I}_{l,k} = 0`, i.e. `Y^{N,0,I}_{t_k} = 0` and `Z^{N,0,I}_{t_k} = 0`;
* for every `i ≥ 1`, `α^{i,I}_k` is an arg min over `(β_0, …, β_q)` of the criterion (9), which
  involves `Y^{N,I,I}_{t_{k+1}}` (the output of `I` iterations at the next time) and the previous
  iterate `α^{i-1,I}_k`.

The paper runs `i = 1, …, I`; the rule is imposed for every `i ≥ 1` (the Picard iterations simply
continue), which the bound (19) over `i ≥ 0` refers to. -/
def IsProjectionScheme {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d q d' : ℕ}
    (T : ℝ) (N : ℕ)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (S0 : EuclideanSpace ℝ (Fin d)) (ΔW : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (ΦN : EuclideanSpace ℝ (Fin d') → ℝ)
    {n : Fin (q + 1) → ℕ → ℕ}
    (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ)
    (I : ℕ) (α : ℕ → (k : ℕ) → (l : Fin (q + 1)) → Fin (n l k) → ℝ) : Prop :=
  (∀ k < N, ∀ l, α 0 k l = 0) ∧
    ∀ i ≥ 1, ∀ k < N, ∀ β : (l : Fin (q + 1)) → Fin (n l k) → ℝ,
      objective9 P T N b σ f S0 ΔW PN ΦN p I α i k (α i k)
        ≤ objective9 P T N b σ f S0 ΔW PN ΦN p I α i k β

/-- `𝒜^N(S_0) = 1 + |S_0|^2 + 𝔼|Φ^N(P^N_{t_N})|^2` (Proof of Theorem 2, p. 11), in `[0, ∞]`. -/
noncomputable def calA {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d d' : ℕ}
    (N : ℕ) (S0 : EuclideanSpace ℝ (Fin d)) (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d'))
    (ΦN : EuclideanSpace ℝ (Fin d') → ℝ) : ENNReal :=
  1 + ‖S0‖ₑ ^ 2 + ∫⁻ ω, ‖ΦN (PN N ω)‖ₑ ^ 2 ∂P

end RegMCBSDE.Projection



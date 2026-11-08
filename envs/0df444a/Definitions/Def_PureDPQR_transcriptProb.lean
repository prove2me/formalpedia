-- Prove2me | Definitions.Def_PureDPQR_transcriptProb
-- name    : PureDPQR_transcriptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:36.434648+00:00
-- url     : https://prove2.me/theorems/a5582e7b-f851-4d6c-a978-7725d4b569f6
-- title:
--   Algorithm 1 (SelectMW): iterates $p_t$, transcript law $p_v(y)$ and decoder $D(y)$
-- statement:
--   Fix public $N,T\ge1$, $\lambda>0$, $0<\rho\le\frac12$ and a list $s_1,\dots,s_K\in\mathbb R^d$. **Algorithm 1** (SelectMW) on an input $v\in\mathbb R^d$ starts from $p_1=(1/d,\dots,1/d)$ and, in rounds $t=1,\dots,T$, sets $H_t=Np_t$, draws a label $i_t\in[K]$ with
--
--   $$P_v(i_t=i\mid i_1,\dots,i_{t-1})=\frac{\exp(\lambda\langle H_t-v,s_i\rangle)}{\sum_{a=1}^K\exp(\lambda\langle H_t-v,s_a\rangle)},$$
--
--   and, if $t<T$, updates $p_{t+1}(j)=p_t(j)(1-\rho s_{i_t}(j))/\sum_a p_t(a)(1-\rho s_{i_t}(a))$. The iterates $p_t$ depend only on $i_1,\dots,i_{t-1}$. The **transcript law** is
--
--   $$p_v(y)=\prod_{t=1}^T\frac{\exp(\lambda\langle H_t-v,s_{i_t}\rangle)}{\sum_{a=1}^K\exp(\lambda\langle H_t-v,s_a\rangle)},\qquad y=(i_1,\dots,i_T)\in[K]^T,$$
--
--   and the **decoder** is $D(y)=\frac1T\sum_{t=1}^Tp_t$.
--
--   These are the objects of Lemmas 17, 19 and Proposition 21, and the inner process of Algorithm 2.
--
--   **Formalization Note** Rounds, labels and coordinates are 0-based; `iterate ρ s y t` is the paper's $p_{t+1}$ and depends on $y_0,\dots,y_{t-1}$ only. The definitions are total in the parameters; the Require line of Algorithm 1 appears as hypotheses where a theorem needs it. $\lambda$ is written `lam`.
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Algorithm 1, p.19 (PDF p.20); (2.7), p.7; (5.2), p.18

import Mathlib

namespace PureDPQR

/-!
# The selection-only multiplicative-weights process `SelectMW(v)`: iterates, transcript law, decoder

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…), Algorithm 1, p.19 (PDF p.20); the transcript law (2.7), p.7, and
`p_v(y)`, p.18; the decoder (5.2), p.18 (PDF p.19).

Algorithm 1 takes an input `v ∈ ℝ^d`, public `N, T ∈ ℕ_{≥1}`, `λ > 0`, `0 < ρ ≤ 1/2` and a signed
list `s_1, …, s_K`. It starts from the uniform `p_1`, and in round `t` it sets `H_t = N p_t`, draws
`i_t ∈ [K]` with probability `exp(λ⟨H_t − v, s_i⟩) / ∑_a exp(λ⟨H_t − v, s_a⟩)`, and, if `t < T`,
updates `p_{t+1}(j) ∝ p_t(j)(1 − ρ s_{i_t}(j))`.

**Formalization Note.**
* Indices are 0-based: labels `Fin K`, coordinates `Fin d`, rounds `Fin T`; a transcript
  `y = (i_1, …, i_T)` is `y : Fin T → Fin K`.
* `iterate ρ s y t` is the paper's `p_{t+1}`: `iterate … 0` is the uniform vector and
  `iterate … (t+1)` applies the update with the label `y t`. So the iterate of 0-based round `t`
  depends only on `y 0, …, y (t−1)`, i.e. on `i_1, …, i_{t−1}` in the paper's indexing.
  `iterate … T` is the auxiliary `p_{T+1}` of the proof of Lemma 19; no definition below uses it.
* The definitions are total in the parameters; the Require line of Algorithm 1 is stated as
  hypotheses wherever a theorem needs it. `λ` is written `lam` (a Lean keyword).
-/

/-- The Euclidean inner product `⟨x, y⟩ = ∑_j x_j y_j` on `ℝ^d`. -/
def dot {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ∑ j, x j * y j

/-- One multiplicative-weights update (Algorithm 1, line 6):
`p'(j) = p(j)(1 − ρ s_a(j)) / ∑_b p(b)(1 − ρ s_a(b))`. -/
noncomputable def mwStep {K d : ℕ} (ρ : ℝ) (s : Fin K → Fin d → ℝ) (p : Fin d → ℝ) (a : Fin K) :
    Fin d → ℝ :=
  fun j => p j * (1 - ρ * s a j) / ∑ b, p b * (1 - ρ * s a b)

/-- The iterates of Algorithm 1 along a transcript `y`: `iterate ρ s y t = p_{t+1}`, with
`p_1 = (1/d, …, 1/d)` (line 1) and `p_{t+1}` obtained from `p_t` by the update with the label of
round `t` (lines 5–7). -/
noncomputable def iterate {K d T : ℕ} (ρ : ℝ) (s : Fin K → Fin d → ℝ) (y : Fin T → Fin K) :
    ℕ → Fin d → ℝ
  | 0 => fun _ => 1 / (d : ℝ)
  | t + 1 =>
      if ht : t < T then mwStep ρ s (iterate ρ s y t) (y ⟨t, ht⟩) else iterate ρ s y t

/-- The softmax selection probability of label `a` (Algorithm 1, line 4), given the candidate
histogram `H` and the input `v`: `exp(λ⟨H − v, s_a⟩) / ∑_b exp(λ⟨H − v, s_b⟩)`. -/
noncomputable def selectProb {K d : ℕ} (lam : ℝ) (s : Fin K → Fin d → ℝ) (H v : Fin d → ℝ)
    (a : Fin K) : ℝ :=
  Real.exp (lam * dot (H - v) (s a)) / ∑ b, Real.exp (lam * dot (H - v) (s b))

/-- The transcript law `p_v(y)` of Algorithm 1 (display (2.7), p.7; p.18):
`p_v(y) = ∏_{t=1}^T exp(λ⟨H_t − v, s_{i_t}⟩) / ∑_a exp(λ⟨H_t − v, s_a⟩)` with `H_t = N p_t`.
It is defined for every real input `v ∈ ℝ^d`. -/
noncomputable def transcriptProb {K d T : ℕ} (N : ℕ) (lam ρ : ℝ) (s : Fin K → Fin d → ℝ)
    (v : Fin d → ℝ) (y : Fin T → Fin K) : ℝ :=
  ∏ t : Fin T, selectProb lam s ((N : ℝ) • iterate ρ s y t) v (y t)

/-- The deterministic decoder (5.2): `D(y) = (1/T) ∑_{t=1}^T p_t`. -/
noncomputable def decoder {K d T : ℕ} (ρ : ℝ) (s : Fin K → Fin d → ℝ) (y : Fin T → Fin K) :
    Fin d → ℝ :=
  fun j => (1 / (T : ℝ)) * ∑ t : Fin T, iterate ρ s y t j

end PureDPQR



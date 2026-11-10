-- Prove2me | Definitions.Def_MulticlassOmni_Lipschitz_StatLowerBound
-- name    : MulticlassOmni_Lipschitz_StatLowerBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:13:54.157238+00:00
-- url     : https://prove2.me/theorems/d3b48809-1002-49c1-b27c-fa608b82ae6b
-- title:
--   Lemma B.4 — the hard data distributions $D_\theta$, randomized bit estimators and their Hamming failure probability
-- statement:
--   The domain is enumerated as `Fin N`; $\theta:X\to\{0,1\}$ is `Fin N → Fin 2`; label vectors are a family $q_b(x_i)$ (`q : Fin 2 → Fin N → ℝ^k`).
--
--   - `qGLM x ε b i` $=q_b(x_i)=\bar v+\tfrac{4R_b}{k}x_i$ with $R_b=\tfrac1{32}+48\varepsilon b$ (64).
--   - `dataDist q θ` $=D_\theta$: $D_\theta(x_i,y)=q_{\theta(x_i)}(x_i)_y/N$, i.e. uniform marginal on $X$ and conditional label law $q_{\theta(x)}(x)$ (24).
--   - A **possibly randomized estimator** based on $n$ examples (`IsRandEstimator`) is, for each data set $S$, the conditional law of its output $\hat\theta:X\to\{0,1\}$ given $S$: an arbitrary probability vector on the finite set of such functions (private randomness of any kind enters only through this law).
--   - `hammingErr t θ` $=|\{x:t(x)\ne\theta(x)\}|$.
--   - `hammingFailProb q est` $=\Pr_{\theta^\star,S,\hat\theta}\big[|\{x:\hat\theta(x)\ne\theta^\star(x)\}|\ge N/4\big]$ with $\theta^\star$ uniform on $X\to\{0,1\}$, $S\sim D_{\theta^\star}^n$ and $\hat\theta\sim$ `est S`.
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma B.4 (p. 58); equation (24) (p. 17); equation (64) (p. 27)

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings

noncomputable section

open Classical

namespace MulticlassOmni.Lipschitz

/-! # The statistical experiment of Lemma B.4

Hu, Luo, Schneider, Yang (2026), *Sample Complexity of Multiclass Omniprediction*, supplied PDF,
Lemma B.4 (p. 58), with the Section 5.1 label vectors (64) (pp. 26–27).

The domain is enumerated as `Fin N` (point `i` is `x_i`); `θ : X → {0, 1}` is `Fin N → Fin 2`.
Label vectors are given as a family `q : Fin 2 → Fin N → ℝ^k`, `q b i = q_b(x_i)`. -/

variable {k N : ℕ}

/-- The GLM-construction label vectors `q_b(x) := v̄ + (4 R_b / k) x` with
`R_b := 1/32 + 48 ε b`, equation (64), at `x = x_i`. -/
def qGLM (x : Fin N → Fin k → ℝ) (ε : ℝ) (b : Fin 2) (i : Fin N) : Fin k → ℝ :=
  vbar k + (4 * (1 / 32 + 48 * ε * ((b : ℕ) : ℝ)) / (k : ℝ)) • x i

/-- `D_θ(x_i, y) = q_{θ(x_i)}(x_i)_y / N`: uniform marginal on the domain and conditional label
distribution `q_{θ(x)}(x)` (equation (24); Lemma B.4). -/
def dataDist (q : Fin 2 → Fin N → Fin k → ℝ) (θ : Fin N → Fin 2) (z : Fin N × Fin k) : ℝ :=
  q (θ z.1) z.1 z.2 / (N : ℝ)

/-- A possibly randomized estimator `θ̂` based on `n` examples: for every data set `S` the
conditional law of its output `θ̂ : X → {0, 1}` given `S`, an arbitrary probability vector on the
finite set of such functions (independent private randomness enters only through this law). -/
def IsRandEstimator {n : ℕ} (est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ) : Prop :=
  ∀ S, (∀ t, 0 ≤ est S t) ∧ ∑ t, est S t = 1

/-- The Hamming error `|{x ∈ X : θ̂(x) ≠ θ(x)}|`. -/
def hammingErr (t θ : Fin N → Fin 2) : ℕ :=
  (Finset.univ.filter (fun i => t i ≠ θ i)).card

/-- `Pr_{θ*, S, θ̂}[|{x : θ̂(x) ≠ θ*(x)}| ≥ N/4]` where `θ*` is uniform on `X → {0, 1}`,
`S ∼ D_{θ*}^n` and `θ̂ ∼ est S` (Lemma B.4, (157)). -/
def hammingFailProb (q : Fin 2 → Fin N → Fin k → ℝ) {n : ℕ}
    (est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ) : ℝ :=
  ∑ θ : Fin N → Fin 2, (1 / (2 : ℝ) ^ N) *
    ∑ S : Fin n → Fin N × Fin k, (∏ j, dataDist q θ (S j)) *
      ∑ t : Fin N → Fin 2, est S t * (if (N : ℝ) / 4 ≤ (hammingErr t θ : ℝ) then 1 else 0)

end MulticlassOmni.Lipschitz



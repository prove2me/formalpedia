-- Prove2me | Definitions.Def_GaussPart_hellingerSq
-- name    : GaussPart_hellingerSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:27.098251+00:00
-- url     : https://prove2.me/theorems/a3467095-6bd2-40c9-888f-5800c9e7bd89
-- title:
--   Gaussian good splits and the constants of Lemma 3.5
-- statement:
--   For $p,q\in[0,1]$, $H^2(p,q)=1-\sqrt{pq}-\sqrt{(1-p)(1-q)}$ is the squared Hellinger distance between $\mathrm{Bern}(p)$ and $\mathrm{Bern}(q)$. For a distribution $Q$ on $\mathbb R$ and $\kappa>0$, a threshold $t$ is a **$\kappa$-Gaussian good split** if $H^2(p_t,q_t)\ge\kappa$, where $p_t=\Pr_{z\sim N(0,1)}[z\ge t]$ and $q_t=\Pr_{z\sim Q}[z\ge t]$. With $\Lambda=q\,(k\log(2qk)+\log(16/(\sigma\Delta)))$, the proposition `GoodSplitConstants C₀ C` says: for all $k\ge1$, $q\ge1$, $\sigma\in(0,1]$, $\Delta\in(0,1)$ and every $(q,\sigma)$-smooth $Q$ on $\mathbb R$ with $|\mathbb E_{N(0,1)}[z^i]-\mathbb E_Q[z^i]|\ge\Delta$ for some $i\in[k]$, every $b\ge C_0\sqrt\Lambda$ admits $t\in[-b,b]$ with $|p_t-q_t|\ge\Delta/(4b^k)$ that is a $\Delta^2/(C\Lambda)^k$-Gaussian good split. Also defined: the embedding of $\mathbb R$ into $\mathbb R^1$ and the input list of the threshold-finding program.
--
--   The good split is what makes the potential of Algorithm 1 decrease; Lemma 3.5 is the statement that suitable constants exist.
--
--   **Formalization Note** `GoodSplitConstants` is a named proposition so that the existence item and the algorithm item of Lemma 3.5 refer to the same constants.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 3.4, p.16 (PDF p.18); Lemma 3.5, p.16

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_Cell

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- The squared Hellinger distance between `Bern(p)` and `Bern(q)` in the normalization of
**Definition 3.4**, arXiv:2611.05264 (sha256 7e0ca6d4…), p.16 (PDF p.18):
`H²(p, q) = 1 − √(pq) − √((1−p)(1−q))`. -/
noncomputable def hellingerSq (p q : ℝ) : ℝ :=
  1 - Real.sqrt (p * q) - Real.sqrt ((1 - p) * (1 - q))

/-- The Gaussian upper tail `Pr_{z∼N(0,1)}[z ≥ s]`. -/
noncomputable def gaussianTail (s : ℝ) : ℝ := (gaussianReal 0 1 (Set.Ici s)).toReal

/-- `Pr_{z∼Q}[z ≥ s]`. -/
noncomputable def upperTail (Q : Measure ℝ) (s : ℝ) : ℝ := (Q (Set.Ici s)).toReal

/-- A threshold `t` is a `κ`-**Gaussian good split** of `Q` (Definition 3.4, p.16):
`H²(p_t, q_t) ≥ κ` with `p_t = Pr_{N(0,1)}[z ≥ t]` and `q_t = Pr_Q[z ≥ t]`. -/
def IsGoodSplit (Q : Measure ℝ) (κ t : ℝ) : Prop :=
  κ ≤ hellingerSq (gaussianTail t) (upperTail Q t)

/-- `Λ := q (k log(2qk) + log(16/(σΔ)))` of Lemma 3.5, p.16. -/
noncomputable def goodSplitLambda (k : ℕ) (q σ Δ : ℝ) : ℝ :=
  q * ((k : ℝ) * Real.log (2 * q * k) + Real.log (16 / (σ * Δ)))

/-- The existence part of **Lemma 3.5**, p.16 (PDF p.18), for the constants `C₀, C`: if `Q` on `ℝ` is
`(q, σ)`-smooth with respect to `N(0, 1)`, `q ≥ 1`, `σ ∈ (0, 1]`, `k ≥ 1`, `Δ ∈ (0, 1)` and
`|E_P[zⁱ] − E_Q[zⁱ]| ≥ Δ` for some `i ∈ [k]`, then for every `b ≥ C₀ √Λ` some `t ∈ [−b, b]` has
`|Pr_P[z ≥ t] − Pr_Q[z ≥ t]| ≥ Δ/(4bᵏ)` and is a `κ`-Gaussian good split, `κ = Δ²/(CΛ)ᵏ`.

**Formalization Note.** It is a named proposition so that the existence item `lemma_3_5` and the
algorithm item `lemma_3_5_finder` are about the same constants. -/
def GoodSplitConstants (C₀ C : ℝ) : Prop :=
  ∀ (k : ℕ) (q σ Δ : ℝ), 1 ≤ k → 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < Δ → Δ < 1 →
    ∀ (Q : Measure ℝ) [IsProbabilityMeasure Q], IsSmooth (gaussianReal 0 1) Q q σ →
      (∃ i : ℕ, 1 ≤ i ∧ i ≤ k ∧ Δ ≤ |∫ z, z ^ i ∂(gaussianReal 0 1) - ∫ z, z ^ i ∂Q|) →
      ∀ b : ℝ, C₀ * Real.sqrt (goodSplitLambda k q σ Δ) ≤ b →
        ∃ t ∈ Set.Icc (-b) b,
          Δ / (4 * b ^ k) ≤ |gaussianTail t - upperTail Q t| ∧
          IsGoodSplit Q (Δ ^ 2 / (C * goodSplitLambda k q σ Δ) ^ k) t

/-- A real number as a point of `ℝ¹`: the threshold-finding program reads its one-dimensional
samples through the `sample` instruction of the `d = 1` machine. -/
noncomputable def lineEmbed (z : ℝ) : Vec 1 := WithLp.toLp 2 fun _ => z

/-- The input of the threshold-finding program of Lemma 3.5, in memory from cell `0`:
`k, q, σ, Δ, δ`. -/
noncomputable def splitInput (k : ℕ) (q σ Δ δ : ℝ) : List ℝ := [(k : ℝ), q, σ, Δ, δ]

end GaussPart



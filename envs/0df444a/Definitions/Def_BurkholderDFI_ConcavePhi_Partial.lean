-- Prove2me | Definitions.Def_BurkholderDFI_ConcavePhi_Partial
-- name    : BurkholderDFI_ConcavePhi_Partial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:34.697228+00:00
-- url     : https://prove2.me/theorems/6057a4af-5ca7-48a6-b0c3-c012e92b0cb8
-- title:
--   Partial sums Z_n = Σ_{k≤n} z_k, W_n = Σ_{k≤n} E(z_k | 𝒜_{k−1}) and τ = inf{n ≥ 0 : W_{n+1} > λ}
-- statement:
--   These are the auxiliary objects of the proof of Theorem 20.1 in Burkholder (1973).
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\mathcal A_0\subseteq\mathcal A_1\subseteq\cdots$ sub-$\sigma$-fields of $\mathcal A$, and $z_1,z_2,\dots$ functions on $\Omega$ with values in $[0,\infty]$. For $0\le n\le\infty$ put
--   $$Z_n=\sum_{k=1}^n z_k,\qquad W_n=\sum_{k=1}^n E(z_k\mid\mathcal A_{k-1}),$$
--   so that $Z_0=W_0=0$, $Z=Z_\infty=\sum_{k=1}^\infty z_k$ and $W=W_\infty=\sum_{k=1}^\infty E(z_k\mid\mathcal A_{k-1})$. For $\lambda>0$ let
--   $$\tau=\inf\{n\ge0: W_{n+1}>\lambda\},$$
--   with $\inf\emptyset=\infty$.
--
--   Since $W_{n+1}$ is $\mathcal A_n$-measurable, $\tau$ is a stopping time; evaluating the partial sums at the random index $\tau$ gives $Z_\tau=\sum_{k\ge1}I(\tau\ge k)z_k$ and $W_\tau=\sum_{k\ge1}I(\tau\ge k)E(z_k\mid\mathcal A_{k-1})$, the quantities compared in the proof of (20.2).
--
--   **Formalization Note** The index $n$ ranges over $\mathbb N\cup\{\infty\}$ (`ℕ∞`) and $Z_n$ is the sum of $z_k$ over $1\le k\le n$; the sequence `z` is indexed so that `z k` is $z_k$ for $k\ge1$ (the value `z 0` is never used). The conditional expectation is the $[0,\infty]$-valued `condLExp` with respect to `ℱ (k-1)` $=\mathcal A_{k-1}$; it is defined for non-integrable $z_k$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §20, proof of Theorem 20.1, p. 38

import Mathlib

namespace BurkholderDFI.ConcavePhi

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*}

/-- §20, proof of Theorem 20.1, p. 38: the partial sums `Z_n = Σ_{k=1}^n z_k`, `0 ≤ n ≤ ∞`, of a
sequence `z_1, z_2, …` of `[0, ∞]`-valued functions (`z k` is `z_k`; the index `0` is unused).
For `n = ⊤` this is `Z = Z_∞ = Σ_{k=1}^∞ z_k`; `Z_0 = 0`. -/
noncomputable def Zpart (z : ℕ → Ω → ℝ≥0∞) (n : ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' k : ℕ, if (((k + 1 : ℕ) : ℕ∞) ≤ n) then z (k + 1) ω else 0

/-- §20, proof of Theorem 20.1, p. 38: `W_n = Σ_{k=1}^n E(z_k | 𝒜_{k−1})`, `0 ≤ n ≤ ∞`, where
`ℱ k = 𝒜_k` and the conditional expectation of the nonnegative, possibly non-integrable `z_k` is
taken in `[0, ∞]` (`condLExp`). For `n = ⊤` this is `W = W_∞`; `W_0 = 0`. -/
noncomputable def Wpart [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (z : ℕ → Ω → ℝ≥0∞) (n : ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' k : ℕ, if (((k + 1 : ℕ) : ℕ∞) ≤ n) then condLExp (ℱ k) P (z (k + 1)) ω else 0

/-- §20, proof of Theorem 20.1, p. 38: `τ = inf {n ≥ 0 : W_{n+1} > λ}`, with `inf ∅ = ∞`
(`⊤ : ℕ∞`). -/
noncomputable def stopIdx [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : (l : ℝ≥0∞) < Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞) ω), (n : ℕ∞)

end BurkholderDFI.ConcavePhi



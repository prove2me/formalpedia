-- Prove2me | Definitions.Def_OnlineRealSampling_Exact_Oracle
-- name    : OnlineRealSampling_Exact_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:56:02.444491+00:00
-- url     : https://prove2.me/theorems/64398818-a093-43d7-8da1-72d877f7d391
-- title:
--   CDF oracles, the clamped logarithm, fair coins and the uniform input state
-- statement:
--   This file fixes the objects of Section 3 of the paper.
--
--   **Logarithms.** $\lg x$ is the base-two logarithm, and the paper's clamped logarithm is $\log x := \ln\max\{x,e\}\ge 1$, so $\log 0=\log 1=1$.
--
--   **Distributions on $\mathbb N$.** A *CDF* is a nondecreasing $F:\mathbb N\to\mathbb R$ with $F(0)\ge 0$ and $F(i)\to 1$. With $F(-1):=0$, its mass function is $f(x)=F(x)-F(x-1)$, so $f(0)=F(0)$. Zero masses, finite or countably infinite support and irrational masses are all allowed.
--
--   **CDF oracles.** An oracle for $F$ returns, for $x,k\in\mathbb N$, a dyadic rational $\phi(x,k)$ with denominator $2^k$ and
--   $$|F(x)-\phi(x,k)|<2^{-k};$$
--   it is stored as the integer numerator of $\phi(x,k)$. Each oracle also carries the number of word operations $\mathrm{cost}(x,k)$ its evaluation takes, charged at every call. No monotonicity, consistency across precisions or range condition is imposed on $\phi$. The bound oracles of (5) are $F^\mp(x,k)=\phi(x,k+1)\mp 2^{-(k+1)}$, and $\phi(-1,k):=0$.
--
--   **Fair coins and the input state.** The entropy source $B_1,B_2,\dots$ is an i.i.d. sequence of fair bits ($B_{j+1}=\omega_j$), with the countable product law. For the single-step analysis of Section 5, $Z$ is uniform on $\{0,\dots,M-1\}$ and independent of the bits, and
--   $$Q=\frac{Z+\sum_{j\ge1}B_j2^{-j}}{M}$$
--   is the analysis variable of (12). $Q$ is never handed to a program.
--
--   **Formalization Note** The oracle is split into the access data (answers and evaluation costs, the only thing a program reads) and the real CDF it approximates. The uniform law on $\{0,\dots,M-1\}$ is the zero measure when $M=0$; every theorem assumes $M\ge 1$.
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), §3, PDF 7–8 / printed 6–7, eqs. (5)–(6); §5, PDF 9 / printed 8, eq. (12); notation p. 6

import Mathlib

namespace OnlineRealSampling.Exact

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Logarithms (Section 3, PDF 7 / printed 6) -/

/-- Base-two logarithm `lg x`. -/
def lg (x : ℝ) : ℝ := Real.logb 2 x

/-- The paper's clamped logarithm `log x := ln (max {x, e}) ≥ 1` (Section 3, "Notation").
In particular `slog 0 = slog 1 = 1`. -/
def slog (x : ℝ) : ℝ := Real.log (max x (Real.exp 1))

/-! ## Distributions on `ℕ` given by their CDF (Section 3, PDF 7 / printed 6) -/

/-- A CDF on `ℕ`: nondecreasing, `F 0 ≥ 0`, and `F i → 1`. Zero masses, finite support,
countably infinite support and irrational masses are all allowed. -/
structure IsCDF (F : ℕ → ℝ) : Prop where
  mono : Monotone F
  nonneg_zero : 0 ≤ F 0
  tendsto_one : Filter.Tendsto F Filter.atTop (nhds 1)

/-- `F (x - 1)` with the convention `F (-1) = 0`. -/
def cdfPrev (F : ℕ → ℝ) (x : ℕ) : ℝ := if x = 0 then 0 else F (x - 1)

/-- The probability mass function `f x = F x - F (x - 1)`; in particular `f 0 = F 0`. -/
def pmf (F : ℕ → ℝ) (x : ℕ) : ℝ := F x - cdfPrev F x

/-! ## CDF oracles (Section 3, PDF 7–8) -/

/-- What a sampler may touch of an oracle: the answer `φ x k`, which is the *numerator* of the
dyadic rational `φ(x,k) = (φ x k) / 2^k`, and `cost x k`, the number of word operations needed to
evaluate the oracle at `(x,k)` (charged as running time at every call). The convention
`φ(-1,k) = 0` is applied by the algorithms themselves, without a call. -/
structure OracleAccess where
  φ : ℕ → ℕ → ℤ
  cost : ℕ → ℕ → ℕ

/-- A CDF oracle: the access data together with the real CDF `F` it approximates. The CDF is
analysis data only; the machines of this mission read nothing but `φ` (and are charged `cost`). -/
structure CDFOracle extends OracleAccess where
  F : ℕ → ℝ

/-- The dyadic value `φ(x,k) = φ x k / 2^k`. -/
def CDFOracle.approx (O : CDFOracle) (x k : ℕ) : ℝ := (O.φ x k : ℝ) / 2 ^ k

/-- Validity of a CDF oracle: `F` is a CDF and `|F x - φ(x,k)| < 2^{-k}` for all `x k : ℕ`.
No monotonicity, consistency across precisions, or range condition is imposed on `φ`. -/
structure CDFOracle.Valid (O : CDFOracle) : Prop where
  cdf : IsCDF O.F
  approx_err : ∀ x k : ℕ, |O.F x - O.approx x k| < 1 / 2 ^ k

/-- The bound oracle `F⁻(x,k) = φ(x,k+1) - 2^{-(k+1)}` of (5), for `x ≥ 0`. -/
def CDFOracle.lower (O : CDFOracle) (x k : ℕ) : ℝ := O.approx x (k + 1) - 1 / 2 ^ (k + 1)

/-- The bound oracle `F⁺(x,k) = φ(x,k+1) + 2^{-(k+1)}` of (5), for `x ≥ 0`. -/
def CDFOracle.upper (O : CDFOracle) (x k : ℕ) : ℝ := O.approx x (k + 1) + 1 / 2 ^ (k + 1)

/-! ## Fair coins and the uniform input state (Section 5, (12), PDF 9) -/

/-- The law of one fair bit. -/
def fairBit : Measure Bool := (1 / 2 : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

/-- The entropy source: i.i.d. fair bits `B₁, B₂, …`, stored as `ω : ℕ → Bool` with
`B_{j+1} = ω j`; the countable product measure. -/
def coinMeasure : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => fairBit)

/-- The uniform law on `{0, …, M - 1}` (the zero measure when `M = 0`). -/
def uniformNat (M : ℕ) : Measure ℕ :=
  ((M : ℝ≥0∞)⁻¹) • ∑ z ∈ Finset.range M, Measure.dirac z

/-- The single-step probability space of Section 5: `Z ∼ Unif{0,…,M-1}` independent of the
fresh bits. -/
def stepMeasure (M : ℕ) : Measure (ℕ × (ℕ → Bool)) := (uniformNat M).prod coinMeasure

/-- The real value of a bit. -/
def bitReal (b : Bool) : ℝ := if b then 1 else 0

/-- `∑_{j ≥ 1} B_j 2^{-j}`. -/
def coinFraction (ω : ℕ → Bool) : ℝ := ∑' j : ℕ, bitReal (ω j) / 2 ^ (j + 1)

/-- The analysis variable `Q = (Z + ∑_{j≥1} B_j 2^{-j}) / M` of (12). It is never handed to any
program. -/
def Qvar (M z : ℕ) (ω : ℕ → Bool) : ℝ := ((z : ℝ) + coinFraction ω) / M

/-- The integer `∑_{j<m} ω(start+j) 2^{m-1-j}` formed by `m` consecutive fresh bits read
most-significant first. -/
def bitsValue (ω : ℕ → Bool) (start m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, if ω (start + j) then 2 ^ (m - 1 - j) else 0

end

end OnlineRealSampling.Exact



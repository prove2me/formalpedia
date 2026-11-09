-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_Parameters
-- name    : RSListDecodingCapacity_AllRates_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:55.633182+00:00
-- url     : https://prove2.me/theorems/6431e96e-5275-4975-8bef-8f2065dcbdec
-- title:
--   The parameters $d,A,m,B,W$, the set $\mathcal B$, the count $\Lambda(z)$ and condition (21) of Section 3
-- statement:
--   Fix $\varepsilon,\theta\in(0,1)$, a blocklength $n$ and a dimension $k$. Section 3 sets
--   $$d=\lceil\varepsilon^{-3/\theta}\rceil,\qquad A=\lceil\varepsilon n\rceil,\qquad m=d^3,\qquad B=\Big\lceil\frac{mA}{k-1}\Big\rceil,\qquad W=\Big\lfloor\frac{(1+\theta/2)\,dm}{\log(ed)}\Big\rfloor$$
--   ((11), (12), (18); $\log$ is the natural logarithm, and $B$ is defined for $k\ge2$). For $c=(c_2,\dots,c_d)\in\mathbb Z_{\ge0}^{d-1}$ let
--   $$\omega(c)=\sum_{j=2}^d(j-1)c_j,\qquad |c|=\sum_{j=2}^dc_j .$$
--   1. $\mathcal B=\{c\in\mathbb Z_{\ge0}^{d-1}:\omega(c)\le W,\ |c|\le\lceil(1+3\theta/4)m\rceil\}$ (p.15).
--   2. For real $z\ge0$, $\Lambda(z)=|\{c\in\mathbb Z_{\ge0}^{d-1}:\omega(c)\le z\}|$, a cardinality (p.17).
--   3. Condition (21) (identical to (27)): $\displaystyle\varepsilon<\Big(\frac{\theta^3(1-\theta)}{768}\Big)^{\frac{5+\theta}{1-\theta}}$.
--
--   These quantities control the degree bounds of the interpolation space and the rank count of the local constraints.
--
--   **Formalization Note** A vector $c$ is a function on `Fin (d-1)`; Lean index $i$ is the source's $c_{i+2}$ with weight $i+1$. The sets are built inside a finite box only to make them `Finset`s; since every weight is at least $1$, the box removes nothing. The quotient in $B$ is a real quotient; every statement using $B$ assumes $k\ge2$.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), §3, List of Parameters, p.13, (11)–(13); §3.1, p.15, (18) and the set B; §3.2, p.17, Λ(z) and (21)

import Mathlib

namespace RSListDecodingCapacity.AllRates

/-!
# The parameters of Section 3

Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, §3 "List of Parameters",
p.13, (11)–(13); §3.1, p.15, (18) and the set `𝓑`; §3.2, p.17, `Λ(z)` and condition (21).

A vector `c = (c₂, …, c_d) ∈ ℤ_{≥0}^{d−1}` is a function `Fin (d − 1) → ℕ`; the coordinate with Lean
index `i` is the source's `c_{i+2}`, so the source weight `j − 1` of `c_j` is `i + 1`.
-/

/-- `d = ⌈ε^{−3/θ}⌉` ((11), p.13). -/
noncomputable def paramD (ε θ : ℝ) : ℕ := ⌈ε ^ (-3 / θ)⌉₊

/-- `A = ⌈εn⌉` ((11), p.13). -/
noncomputable def paramA (ε : ℝ) (n : ℕ) : ℕ := ⌈ε * n⌉₊

/-- `m = d³` ((11), p.13). -/
def paramM (d : ℕ) : ℕ := d ^ 3

/-- `B = ⌈mA/(k − 1)⌉` ((12), p.13). The quotient is a real quotient; it is undefined in the
source at `k = 1`, and every statement using `B` assumes `k ≥ 2`. -/
noncomputable def paramB (m A k : ℕ) : ℕ := ⌈((m * A : ℕ) : ℝ) / ((k : ℝ) - 1)⌉₊

/-- `W = ⌊(1 + θ/2) d m / log(e d)⌋` ((18), p.15), with the natural logarithm. -/
noncomputable def paramW (θ : ℝ) (d m : ℕ) : ℕ :=
  ⌊(1 + θ / 2) * d * m / Real.log (Real.exp 1 * d)⌋₊

/-- `ω(c) = ∑_{j=2}^{d} (j − 1) c_j` (§3.1, p.15). -/
def omegaW {d : ℕ} (c : Fin (d - 1) → ℕ) : ℕ := ∑ i : Fin (d - 1), ((i : ℕ) + 1) * c i

/-- `|c| = ∑_{j=2}^{d} c_j` (§3.1, p.15). -/
def absC {d : ℕ} (c : Fin (d - 1) → ℕ) : ℕ := ∑ i : Fin (d - 1), c i

/-- `⌈(1 + 3θ/4) m⌉`, the bound on `|c|` in `𝓑` (p.15). -/
noncomputable def cBound (θ : ℝ) (m : ℕ) : ℕ := ⌈(1 + 3 * θ / 4) * m⌉₊

/-- **The set `𝓑`** (p.15): `𝓑 = {c ∈ ℤ_{≥0}^{d−1} : ω(c) ≤ W, |c| ≤ ⌈(1 + 3θ/4) m⌉}`.
The ambient box `{0, …, W}^{d−1}` only makes the set a `Finset`: `ω(c) ≤ W` already forces
`c_j ≤ W`, since every weight is at least `1`. -/
noncomputable def scriptB (θ : ℝ) (d m W : ℕ) : Finset (Fin (d - 1) → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin (d - 1) => Finset.range (W + 1)).filter
    fun c => omegaW c ≤ W ∧ absC c ≤ cBound θ m

/-- **`Λ(z)`** (p.17): the number of `c ∈ ℤ_{≥0}^{d−1}` with `ω(c) ≤ z`, for real `z ≥ 0`. A
cardinality, not a set. The ambient box `{0, …, ⌊z⌋}^{d−1}` only makes the set a `Finset`
(`ω(c) ≤ z` forces `c_j ≤ ⌊z⌋`); at `z < 0` the count is `0`. -/
noncomputable def Lambda (d : ℕ) (z : ℝ) : ℕ := by
  classical
  exact ((Fintype.piFinset fun _ : Fin (d - 1) => Finset.range (⌊z⌋₊ + 1)).filter
    fun c => (omegaW c : ℝ) ≤ z).card

/-- **Condition (21)** (p.17; the same as (27), p.26):
`ε < (θ³(1 − θ)/768)^{(5+θ)/(1−θ)}`. -/
def Cond21 (ε θ : ℝ) : Prop :=
  ε < (θ ^ 3 * (1 - θ) / 768) ^ ((5 + θ) / (1 - θ))

end RSListDecodingCapacity.AllRates



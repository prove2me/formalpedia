-- Prove2me | Definitions.Def_PeriodicMAB_Upper_Spectral
-- name    : PeriodicMAB_Upper_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:57.411166+00:00
-- url     : https://prove2.me/theorems/81a6889d-785a-4199-b3bd-619780d52c0f
-- title:
--   Algorithm 1, pp. 8–12, 18–19 — DFTs, threshold $\tau_k$, $\mathcal V_k$, $\mathcal U_k$, the period estimator $\hat T_k$, Assumptions 3–4, parameters (7)
-- statement:
--   Stage one of the two-stage policy (§3.1) and the objects of §4.1.
--
--   **Stage one.** Each arm is pulled $n$ times in a row: arm $k$ (0-based index) at the epochs $nk+1,\dots,n(k+1)$. For that block of rewards the **discrete Fourier transform** and its mean and noise parts are
--   $$
--   \tilde y_k(v)=\frac1n\sum_{s=nk+1}^{n(k+1)}Y_{k,s}\,e^{-2\pi i vs},\qquad
--   \tilde\mu_k(v)=\frac1n\sum_{s}\mu_{k,s}\,e^{-2\pi i vs},\qquad
--   \tilde\epsilon_k(v)=\frac1n\sum_{s}\epsilon_{s}\,e^{-2\pi i vs},
--   $$
--   so that $\tilde y_k=\tilde\mu_k+\tilde\epsilon_k$ (displays (3)–(4) and Step 8). The component of the present frequency $j/T_k$ is $\tilde\mu_{k,j}(v)=\frac1n\sum_s b_{k,j}e^{2\pi i(j/T_k-v)s}$ (display (5)).
--
--   **Threshold** (Step 10). With $A_j=\sup\{|\sin(\pi\nu)|/(\pi\nu):\nu\in[j,j+1]\}$,
--   $$
--   U_1=\sum_{j=0}^{\lfloor (n-2g-1)/(4g)\rfloor}A_{(2j+1)g},\qquad U_2=\sum_{j=1}^{\lfloor (n-1)/(4g)\rfloor}A_{2jg-1},\qquad
--   \bar\epsilon_v=\frac{2\sigma H}{1-\pi/24}\sqrt{\frac{\log n}{n}},
--   $$
--   $$
--   \tau_k=\bar\epsilon_v+\frac{\pi U_1}{1-\pi U_2}\Big(\bar\epsilon_v+\sup_{v\in[0,1/2]}|\tilde y_k(v)|\Big).
--   $$
--
--   **Algorithm 1** (p. 11). The candidate frequencies are $\mathcal F=\{j_1/j_2: 1\le j_1<j_2<n/(2g)\}$. The domain $\mathcal D=\{v: g/n\le v\le 1/2,\ |\tilde y_k(v)|>\tau_k\}$ is scanned repeatedly: take the global maximizer $v^*$ of $|\tilde y_k|$ on $\mathcal D$, snap it to the closest candidate $\hat v\in\mathcal F$, and remove $(\hat v-g/n,\hat v+g/n)$ from $\mathcal D$, until $\mathcal D$ is empty. The estimated period is $\hat T_k=\mathrm{LCM}(\hat v_1^{-1},\hat v_2^{-1},\dots)$. The event that every period is identified is $\Lambda=\{\hat T_k=T_k\ \forall k\}$.
--
--   **Neighbourhoods** (pp. 18–19): $\mathcal V_k=[0,1/2]\cap\bigcup_{j:|b_{k,j}|>0}[j/T_k-g/n,\ j/T_k+g/n]$, $\bar{\mathcal V}_k=[0,1/2]\setminus\mathcal V_k$, and $\mathcal U_k=[0,1/2]\cap\bigcup_{j=1}^{\lfloor T_k/2\rfloor}[j/T_k-g/n,\ j/T_k+g/n]$.
--
--   **Assumption 3** (p. 12): $T>4K$, $g$ is an integer with $g\ge\max\{2,\sqrt n\}$, and $T_k<n/(2g)$ for every arm. **Assumption 4** (display (14), p. 20): for every arm,
--   $$
--   b_k\ge\Big(\frac{2\pi U_1}{1-\pi U_2}+2\Big)\bar\epsilon_v+\max\Big\{\frac{8\pi}{3}U_2,\ \frac{\pi U_1}{1-\pi U_2}\max\{\pi U_1,\pi U_2+1\}+\pi U_2\Big\}B_k .
--   $$
--   **Parameters** (7): $n=\lfloor\sqrt{T/K}\rfloor$, $g=\lceil\sqrt n\rceil$, $H=\sqrt{1+\log n}$.
--
--   **Formalization Note** Every DFT uses the absolute epoch $s$ of the block, as in Step 8; displays (3)–(5) index the block from $1$, which multiplies each component by a unimodular factor. The algorithm's unspecified choices are fixed canonically: $v^*$ is the smallest global maximizer on the current domain, $\hat v$ is the smallest of the closest candidates, and the loop stops (with nothing selected) if $\mathcal F$ is empty. The while-loop runs for at most $n$ passes. The LCM of the reciprocals $\hat v_i^{-1}=j_2/j_1$ is read as the least common multiple of the reduced denominators of the $\hat v_i$, i.e. the least $T'$ with $T'\hat v_i\in\mathbb Z$ for all $i$, and $1$ when nothing is selected. $U_1$ and $U_2$ use natural-number floor division and subtraction; under Assumption 3, $n\ge 2g+1$, so they agree with the paper's sums. In (14) the factor $B_k$ multiplies the whole maximum. $\log$ is the natural logarithm. $B_k$ and $b_k$ are taken with respect to the true period $T_k$ of the arm.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, pp. 8–12, 18–20, Algorithm 1, (3)–(5), (7), (14), Assumptions 3–4

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model

open MeasureTheory ProbabilityTheory Finset

namespace PeriodicMAB.Upper

/-! Chen, Wang and Wang, *Learning and Optimization with Seasonal Patterns*,
arXiv:2005.08088v4: the spectral objects of §3.1 (pp. 8–11, (3)–(5)), Algorithm 1 (p. 11),
the parameters (7) (p. 12) and the sets `𝒱_k`, `𝒱̄_k` (p. 18) and `𝒰_k` (Lemma 6, p. 19).

Arms are 0-based: arm index `k` (the paper's arm `k + 1`) is explored in stage one at the
epochs `n k + 1, …, n (k + 1)` (Algorithm 1, Steps 3–6). Every DFT is taken over that block
with the absolute epoch `s` in `exp(−2πivs)`, exactly as in Step 8; displays (3)–(5) index the
block from `1`, which multiplies each DFT by a unimodular factor and changes no modulus. -/

/-- The stage-one block of epochs of arm index `k`: `{n k + 1, …, n (k + 1)}`. -/
def block (n k : ℕ) : Finset ℕ := Icc (n * k + 1) (n * (k + 1))

/-- `exp(−2πivs)`. -/
noncomputable def cexpNeg (v : ℝ) (s : ℕ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * (s : ℂ)))

/-- The DFT `ỹ_k(v) = (1/n) ∑_{s ∈ block} Y_{k,s} exp(−2πivs)` of the stage-one rewards
`Y_{k,s} = μk s + ε s ω` of arm index `k` (Algorithm 1, Step 8; display (3)). -/
noncomputable def yTilde {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (n k : ℕ) (v : ℝ) (ω : Ω) : ℂ :=
  (1 / (n : ℂ)) * ∑ s ∈ block n k, ((μk s + ε s ω : ℝ) : ℂ) * cexpNeg v s

/-- The mean part `µ̃_k(v) = (1/n) ∑_{s ∈ block} µ_{k,s} exp(−2πivs)` of (4). -/
noncomputable def muTilde (μk : ℕ → ℝ) (n k : ℕ) (v : ℝ) : ℂ :=
  (1 / (n : ℂ)) * ∑ s ∈ block n k, (μk s : ℂ) * cexpNeg v s

/-- The noise part `ε̃_k(v) = (1/n) ∑_{s ∈ block} ε_s exp(−2πivs)` of (4). -/
noncomputable def epsTilde {Ω : Type*} (ε : ℕ → Ω → ℝ) (n k : ℕ) (v : ℝ) (ω : Ω) : ℂ :=
  (1 / (n : ℂ)) * ∑ s ∈ block n k, (ε s ω : ℂ) * cexpNeg v s

/-- The frequency component `µ̃_{k,j}(v) = (1/n) ∑_{s ∈ block} b_{k,j} exp(2πi(j/p − v)s)`
of (5), where `b_{k,j} = fourierCoeff μk p j` and `p` is the period of arm `k`. -/
noncomputable def muTildeJ (μk : ℕ → ℝ) (p n k j : ℕ) (v : ℝ) : ℂ :=
  (1 / (n : ℂ)) * ∑ s ∈ block n k, fourierCoeff μk p j *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((j : ℝ) / p - v : ℝ) : ℂ) * (s : ℂ))

/-- `A_j = sup { |sin(πν)|/(πν) : ν ∈ [j, j + 1] }` (Algorithm 1, Step 10), for `j ≥ 1`. -/
noncomputable def Aj (j : ℕ) : ℝ :=
  sSup ((fun ν : ℝ => |Real.sin (Real.pi * ν)| / (Real.pi * ν)) '' Set.Icc (j : ℝ) (j + 1))

/-- `U₁ = ∑_{j=0}^{⌊(n−2g−1)/(4g)⌋} A_{(2j+1)g}` (Step 10). Natural-number arithmetic: this is
the paper's sum whenever `n ≥ 2g + 1`, which Assumption 3 forces. -/
noncomputable def U1 (n g : ℕ) : ℝ :=
  ∑ j ∈ range ((n - 2 * g - 1) / (4 * g) + 1), Aj ((2 * j + 1) * g)

/-- `U₂ = ∑_{j=1}^{⌊(n−1)/(4g)⌋} A_{2jg−1}` (Step 10); `2jg − 1 ≥ 1` since `g ≥ 1`, `j ≥ 1`. -/
noncomputable def U2 (n g : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 ((n - 1) / (4 * g)), Aj (2 * j * g - 1)

/-- `ε̄_v = (2σH/(1 − π/24)) √(log(n)/n)` (Step 10). -/
noncomputable def epsBar (σ H : ℝ) (n : ℕ) : ℝ :=
  2 * σ * H / (1 - Real.pi / 24) * Real.sqrt (Real.log n / n)

/-- `sup_{v ∈ [0,1/2]} |ỹ_k(v)|`. -/
noncomputable def supY {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  sSup ((fun v => ‖yTilde μk ε n k v ω‖) '' Set.Icc (0 : ℝ) (1 / 2))

/-- `sup_{v ∈ [0,1/2]} |ε̃_k(v)|`. -/
noncomputable def supEps {Ω : Type*} (ε : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  sSup ((fun v => ‖epsTilde ε n k v ω‖) '' Set.Icc (0 : ℝ) (1 / 2))

/-- The threshold `τ_k = ε̄_v + (πU₁/(1 − πU₂)) (ε̄_v + sup_{v∈[0,1/2]} |ỹ_k(v)|)` (Step 10). -/
noncomputable def tau {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ H : ℝ) (n g k : ℕ)
    (ω : Ω) : ℝ :=
  epsBar σ H n + Real.pi * U1 n g / (1 - Real.pi * U2 n g) * (epsBar σ H n + supY μk ε n k ω)

/-- The candidate frequencies `ℱ = { j₁/j₂ : j₁, j₂ ∈ ℕ⁺, 1 ≤ j₁ < j₂ < n/(2g) }` (Step 9). -/
def candF (n g : ℕ) : Finset ℚ :=
  ((Icc 1 n ×ˢ Icc 1 n).filter (fun q : ℕ × ℕ => q.1 < q.2 ∧ ((q.2 : ℚ) < (n : ℚ) / (2 * g)))).image
    (fun q => (q.1 : ℚ) / q.2)

/-- `𝒱_k = [0,1/2] ∩ ⋃_{j : |b_{k,j}|>0} [j/p − g/n, j/p + g/n]` (p. 18). -/
noncomputable def nbhdV (μk : ℕ → ℝ) (p n g : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) (1 / 2) ∩
    ⋃ j ∈ presentSet μk p, Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n)

/-- `𝒱̄_k = [0,1/2] \ 𝒱_k` (p. 18). -/
noncomputable def nbhdVbar (μk : ℕ → ℝ) (p n g : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) (1 / 2) \ nbhdV μk p n g

/-- `𝒰_k = [0,1/2] ∩ ⋃_{j=1}^{⌊p/2⌋} [j/p − g/n, j/p + g/n]` (Lemma 6, p. 19; the index range
`j = 1, …, ⌊T_k/2⌋` is the one of its proof, p. 37). -/
def nbhdU (p n g : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) (1 / 2) ∩
    ⋃ j ∈ Icc 1 (p / 2), Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n)

section Algorithm1

variable {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ H : ℝ) (n g k : ℕ) (ω : Ω)

/-- The frequency domain `𝒟` of Algorithm 1 after the frequencies `sel` have been selected:
`𝒟₀ = { v : g/n ≤ v ≤ 1/2, |ỹ_k(v)| > τ_k }` (Step 11) with the neighbourhoods
`(v̂ − g/n, v̂ + g/n)` of every `v̂ ∈ sel` removed (Step 17). -/
noncomputable def domain (sel : List ℚ) : Set ℝ :=
  {v | v ∈ Set.Icc ((g : ℝ) / n) (1 / 2) ∧ tau μk ε σ H n g k ω < ‖yTilde μk ε n k v ω‖ ∧
    ∀ q ∈ sel, v ∉ Set.Ioo ((q : ℝ) - (g : ℝ) / n) ((q : ℝ) + (g : ℝ) / n)}

/-- Step 16: the candidate frequency in `ℱ` closest to `v`; ties are broken by taking the
smallest closest candidate; `none` if `ℱ` is empty. -/
noncomputable def snap (v : ℝ) : Option ℚ :=
  let C := (candF n g).filter (fun q : ℚ => ∀ q' ∈ candF n g, |(q : ℝ) - v| ≤ |(q' : ℝ) - v|)
  if h : C.Nonempty then some (C.min' h) else none

open Classical in
/-- One pass of the while-loop (Steps 13–17). If the current domain is empty the loop stops
(`none`). Otherwise `v*` is the smallest global maximizer of `|ỹ_k|` on the domain (Step 15)
and the loop selects `v̂ = snap v*` (Step 16). -/
noncomputable def alg1Step (sel : List ℚ) : Option ℚ :=
  if (domain μk ε σ H n g k ω sel).Nonempty then
    snap n g (sInf {v | v ∈ domain μk ε σ H n g k ω sel ∧
      ∀ w ∈ domain μk ε σ H n g k ω sel, ‖yTilde μk ε n k w ω‖ ≤ ‖yTilde μk ε n k v ω‖})
  else none

/-- The list of frequencies `v̂₁, v̂₂, …` selected by the first `i` passes of the loop; once a
pass stops, the list stays fixed. -/
noncomputable def alg1Run : ℕ → List ℚ
  | 0 => []
  | i + 1 =>
    match alg1Step μk ε σ H n g k ω (alg1Run i) with
    | none => alg1Run i
    | some q => alg1Run i ++ [q]

/-- **Algorithm 1** (p. 11) for arm index `k`: the estimated period
`T̂_k = LCM(v̂₁⁻¹, v̂₂⁻¹, …)` (Step 19), read as the least common multiple of the reduced
denominators of the selected `v̂_i` (the least `T'` with `T' v̂_i ∈ ℤ` for all `i`; `1` when no
frequency is selected). The while-loop is run for at most `n` passes. -/
noncomputable def estPeriodArm : ℕ :=
  (alg1Run μk ε σ H n g k ω n).foldr (fun q acc => Nat.lcm q.den acc) 1

end Algorithm1

/-- Algorithm 1 run on arm `k : Fin K` of the means `μ`. -/
noncomputable def estPeriod {Ω : Type*} {K : ℕ} (μ : Fin K → ℕ → ℝ) (ε : ℕ → Ω → ℝ)
    (σ H : ℝ) (n g : ℕ) (k : Fin K) (ω : Ω) : ℕ :=
  estPeriodArm (μ k) ε σ H n g k ω

/-- The event `Λ = { T̂_k = T_k for all k }` (Theorem 2, p. 20). -/
def eventLambda {Ω : Type*} {K : ℕ} (μ : Fin K → ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ H : ℝ)
    (n g : ℕ) (Tper : Fin K → ℕ) : Set Ω :=
  {ω | ∀ k, estPeriod μ ε σ H n g k ω = Tper k}

/-- The arm-wise part of **Assumption 3** (p. 12): `g ≥ max{2, √n}` (an integer) and
`p < n/(2g)` for the period `p` of the arm. -/
def Assumption3Arm (n g p : ℕ) : Prop :=
  2 ≤ g ∧ Real.sqrt n ≤ g ∧ (p : ℝ) < (n : ℝ) / (2 * g)

/-- **Assumption 3** (p. 12): `T > 4K`, `g ≥ max{2, √n}` and `T_k < n/(2g)` for every arm. -/
def Assumption3 {K : ℕ} (T n g : ℕ) (Tper : Fin K → ℕ) : Prop :=
  4 * K < T ∧ 2 ≤ g ∧ Real.sqrt n ≤ g ∧ ∀ k, (Tper k : ℝ) < (n : ℝ) / (2 * g)

/-- **Assumption 4**, display (14), p. 20: for every arm,
`b_k ≥ (2πU₁/(1 − πU₂) + 2) ε̄_v + max{(8π/3) U₂, (πU₁/(1 − πU₂)) max{πU₁, πU₂ + 1} + πU₂} · B_k`. -/
def Assumption4 {K : ℕ} (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (σ H : ℝ) (n g : ℕ) : Prop :=
  ∀ k, (2 * Real.pi * U1 n g / (1 - Real.pi * U2 n g) + 2) * epsBar σ H n +
      max (8 * Real.pi / 3 * U2 n g)
        (Real.pi * U1 n g / (1 - Real.pi * U2 n g) *
            max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) + Real.pi * U2 n g) *
        bigB (μ k) (Tper k) ≤ smallB (μ k) (Tper k)

/-- The exploration length `n = ⌊√(T/K)⌋` of (7), p. 12 (real square root, real division). -/
noncomputable def nPar (T K : ℕ) : ℕ := ⌊Real.sqrt ((T : ℝ) / K)⌋₊

/-- `g = ⌈√n⌉` of (7). -/
noncomputable def gPar (n : ℕ) : ℕ := ⌈Real.sqrt n⌉₊

/-- `H = √(1 + log n)` of (7). -/
noncomputable def HPar (n : ℕ) : ℝ := Real.sqrt (1 + Real.log n)

end PeriodicMAB.Upper



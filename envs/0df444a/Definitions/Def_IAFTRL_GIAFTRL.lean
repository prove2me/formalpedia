-- Prove2me | Definitions.Def_IAFTRL_GIAFTRL
-- name    : IAFTRL_GIAFTRL
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-17T08:36:04.086504+00:00
-- url     : https://prove2.me/theorems/d0fdc566-a723-41c9-a0bc-9a9f6b829dc0
-- title:
--   GIA-FTRL (Algorithm 2): generators, sharpness, centered allocations, reference measure, program (3.6), runs
-- statement:
--   This file fixes the objects of GIA-FTRL (Algorithm 2) and of its analysis for compact action sets (Sections 1.1 and 3.1 of the source).
--
--   **Geometry.** Let $\mathcal A\subseteq\mathbb B^d$ be a compact action set with $\mathrm{span}(\mathcal A)=\mathbb R^d$. A *generator* is a set $\mathcal B$ with $\mathcal B\subseteq\mathcal A\subseteq\mathrm{Conv}(\mathcal B)$. Write $\mathcal K=\mathrm{Conv}(\mathcal B)$, $\mathcal S=\mathrm{Conv}(\mathcal B\cup(-\mathcal B))$, $\|x\|_{\mathcal S}$ for the Minkowski functional of $\mathcal S$, and $k=\dim\operatorname{aff}(\mathcal K)$. The instance $(\mathcal A,\theta)$ with unique optimal action $a^*$ is *sharp* if, for some $\varsigma>0$,
--   $$
--   (a-a^*)^\top\theta\ \ge\ \varsigma\,\|a-a^*\|_{\mathcal S}\qquad\text{for all } a\in\mathcal K. \tag{1.3}
--   $$
--
--   **Centered information-acquisition complexity (Definition 1.2).** For a finite Borel measure $n$ on $\mathcal A$, let $H_n=\int aa^\top n(da)$ and $c^n_{\mathrm{ctr}}=\int\Delta(a)\,n(da)$, where $\Delta(a)=(a-a^*)^\top\theta$. The allocation $n$ is *feasible* if $H_n\succ0$ and $\|u-a^*\|^2_{H_n^{-1}}\le\Delta(u)^2/2$ for all $u\in\mathrm{Conv}(\mathcal A)$. Then
--   $$
--   c^*_{\mathrm{ctr}}(\mathcal A,\theta)=\inf\{c^n_{\mathrm{ctr}}(\mathcal A,\theta):\ n\text{ feasible}\}.
--   $$
--
--   **Reference measure (3.2)–(3.3).** Fix an enumeration $(v^{(m)})$ of $\mathbb Q^d$.
--   1. For each $m$, let $b_m$ be the lexicographically least minimizer of $a\mapsto a^\top v^{(m)}$ on $\mathcal B$.
--   2. Let $J$ be the set of first occurrences of these candidates.
--   3. Set $h_j=j+1+\sum_{i\in J,i<j}\exp(\|b_j-b_i\|_{\mathcal S}^{-8})$ and $\pi_j=e^{-h_j}$.
--   4. Set $\mu=\sum_{j\in J}\pi_j\delta_{b_j}+\omega_\mu\mu_{16}$, where $\omega_\mu=1-\sum_j\pi_j$ and $\mu_{16}$ is the law of the mean of $16$ i.i.d. uniform points of $\mathcal K$ (the normalized $k$-dimensional volume).
--
--   **Program (3.6) at round $t$.** The input is the cumulative estimate $S=\sum_{s<t}\hat\theta_s$, so that $\hat L_{t-1,x}=x^\top S$.
--   - The FTRL update (3.1) is $q_t(dx)\propto e^{-x^\top S/\beta_t}\mu(dx)$, with $\beta_t=16d+\sqrt t$.
--   - The reference action is $b_{r_t}$, the least index minimizing $\hat L_{t-1,b_j}+\beta_th_j$.
--   - The empirical gap is $\hat\Delta_t(x)=\min\{2,Z_t(x)/t\}$, where $Z_t(x)=[\hat L_{t-1,x}-\hat L_{t-1,b_{r_t}}]_+$.
--   - The constraint budgets are $U_t,W_t$ of (3.5), with $B=2^{36}(d+1)$ and $\Gamma_t=4d/\beta_t$.
--   - For a measure $p$, write $M(p)=\int xx^\top p(dx)$ and $v_x(p)=M(p)^{-1}x$.
--
--   A probability measure $p$ on $\mathcal K$ is feasible if:
--   1. $p=(1-\gamma)q_t+w$ for a finite measure $w\ge0$ on $\mathcal K$ with $\gamma=w(\mathcal K)\le\Gamma_t$;
--   2. $M(p)\succ0$;
--   3. $|(u-b_{r_t})^\top v_x(p)|\le U_t(u)$ for all $u,x\in\mathcal K$;
--   4. $\int((u-b_{r_t})^\top v_x(p))^2p(dx)\le W_t(u)$ for all $u\in\mathcal K$;
--   5. $\mathcal C_t(p)\le2d/\beta_t$, as in (3.7).
--
--   GIA-FTRL samples from a feasible $p$ that minimizes $\int\hat\Delta_t\,dp$.
--
--   **Runs.** A run records the virtual actions $X_t$, the physical actions $A_t$, the feedback $Y_t$, the loss vectors $\theta_t$, the sampling laws $p_t$ and the pre-action $\sigma$-algebras $\mathcal G_t$. It executes GIA-FTRL if, in every round:
--   - $p_t$ is a history-measurable minimizer of (3.6);
--   - $X_t\sim p_t$ given $\mathcal G_t$;
--   - $A_t\in\mathcal B$ with $\mathbb E[A_t\mid\mathcal G_t,X_t]=X_t$;
--   - $|Y_t|\le1$ with $\mathbb E[Y_t\mid\mathcal G_t,X_t,A_t]=A_t^\top\theta_t$;
--   - $\|\theta_t\|_{\mathcal A}\le1$.
--
--   The estimates are $\hat\theta_t=v_{X_t}(p_t)Y_t$. The corrupted stochastic regime requires $\|\theta\|_{\mathcal A}\le1$ and $\sum_{t\le T}\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely. The regret against $u$ is $\mathbb E\sum_t(A_t-u)^\top\theta_t$.
--
--   These objects are shared by Theorem 3.1, Proposition 3.1 and their lemmas.
--
--   **Formalization Note.**
--   - The suprema over feedback laws in (3.6d)–(3.6e) are replaced by the computable forms obtained at $|Y|=1$, and (3.6f) by (3.7), as the source states.
--   - The uniform measure on $\mathcal K$ is the normalized $k$-dimensional Hausdorff measure restricted to $\mathcal K$. On $\operatorname{aff}(\mathcal K)$ it is proportional to the $k$-dimensional Lebesgue measure, and the normalization removes the constant.
--   - Paper rounds $t\ge1$ are explicit; a run is indexed by $s=t-1$.
--   - The paper's 1-based enumeration index $j$ is $m+1$ for the 0-based index $m$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 1.1 (Definition 1.1 (1.3), Definition 1.2 (1.4)), pp. 6–7; Section 3.1, Algorithm 2 and (3.1)–(3.7), pp. 21–24

import Mathlib
import Definitions.Def_IAFTRL_chi
import Definitions.Def_IAFTRL_LinEnv

/-!
# GIA-FTRL: geometry, reference measure, program (3.6), runs

Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition,
Corruption, and Geometry* (STOC submission version), Section 1.1 (generators, sharpness,
Definition 1.2) and Section 3.1 (Algorithm 2, (3.1)–(3.7)), pp. 6–7 and 21–24.

Vectors are `Fin d → ℝ` with the dot product `⬝ᵥ`. Paper rounds `t ≥ 1` are passed explicitly;
a run is indexed by `s = t - 1 ≥ 0`.

* Geometry of a generator `ℬ` (`ℬ ⊆ 𝒜 ⊆ Conv ℬ`): `Kset ℬ = Conv ℬ`, `Sset ℬ = Conv(ℬ ∪ -ℬ)`,
  `‖x‖_𝒮 = gauge (Sset ℬ) x`, `kdim ℬ = dim aff 𝒦`.
* Centered allocations (Definition 1.2): finite Borel measures `n` on `𝒜` with
  `H_n = ∫ aaᵀ dn ≻ 0` and `(u - a*)ᵀ H_n⁻¹ (u - a*) ≤ Δ(u)²/2` for all `u ∈ Conv 𝒜`;
  `c^n_ctr = ∫ Δ dn` and `c*_ctr = inf c^n_ctr`.
* Reference measure (3.2)–(3.3): an enumeration `e` of `ℚ^d` selects, for each `e m`, the
  lexicographically least minimizer `cand m` of `a ↦ aᵀ e m` on `ℬ`; `Jset` keeps first
  occurrences; `h_m = (m+1) + 1 + Σ_{i ∈ J, i < m} exp(‖b_m - b_i‖_𝒮^{-8})` (the paper's 1-based
  index `j = m + 1`), `π_m = e^{-h_m}`; `μ = Σ_{m ∈ J} π_m δ_{b_m} + ω μ_16`, where `μ_16` is the
  law of the mean of 16 i.i.d. uniform (normalized `k`-dimensional Hausdorff) points of `𝒦`.
* Program (3.6) at paper round `t` and cumulative estimate `S = Σ_{s<t} θ̂_s`
  (`L̂_{t-1,x} = xᵀS`): `q_t` (3.1), `r_t`, `Z_t`, `Δ̂_t` (3.4), `U_t`, `W_t` (3.5), and the
  feasible set (3.6b)–(3.6f) in the computable forms given by the paper (with `|Y| ≤ 1`, the
  suprema over feedback laws in (3.6d)–(3.6e) are attained at `|Y| = 1`; (3.6f) is (3.7)).
* Runs: `GRun` records the virtual action `X_t ~ p_t`, the physical action `A_t ∈ ℬ` with
  `E[A_t | G_t, X_t] = X_t`, the feedback, the loss vectors, the sampling laws and the pre-action
  σ-algebras; `IsGIAFTRLRun` states that the run executes Algorithm 2.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace IAFTRL

variable {d : ℕ}

/-! ### Geometry -/

/-- `𝒦 = Conv ℬ` -/
def Kset (ℬ : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := convexHull ℝ ℬ

/-- `𝒮 = Conv(ℬ ∪ -ℬ)` -/
def Sset (ℬ : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := convexHull ℝ (ℬ ∪ -ℬ)

/-- the Minkowski functional `‖x‖_𝒮` -/
noncomputable def sNorm (ℬ : Set (Fin d → ℝ)) (x : Fin d → ℝ) : ℝ := gauge (Sset ℬ) x

/-- `k = dim aff 𝒦` -/
noncomputable def kdim (ℬ : Set (Fin d → ℝ)) : ℕ := Module.finrank ℝ (vectorSpan ℝ (Kset ℬ))

/-- `ℬ` is a generator of `𝒜`: `ℬ ⊆ 𝒜 ⊆ Conv ℬ` -/
def IsGenerator (𝒜 ℬ : Set (Fin d → ℝ)) : Prop := ℬ ⊆ 𝒜 ∧ 𝒜 ⊆ convexHull ℝ ℬ

/-- the instance `(𝒜, θ)` is geometrically sharp on `𝒦 = Conv ℬ` with modulus `ς > 0`, (1.3):
`(a - a*)ᵀθ ≥ ς ‖a - a*‖_𝒮` for all `a ∈ 𝒦` -/
def IsSharp (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : Prop :=
  ∃ ς : ℝ, 0 < ς ∧ ∀ a ∈ Kset ℬ, ς * sNorm ℬ (a - astar) ≤ (a - astar) ⬝ᵥ θ

/-! ### Centered information-acquisition complexity (Definition 1.2) -/

/-- the design matrix `H_n = ∫ aaᵀ n(da)` -/
noncomputable def designMat (n : Measure (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ a, a i * a j ∂n

/-- `n` is a finite feasible centered sampling allocation on `𝒜` for `(θ, a*)`, (1.4) -/
def IsCtrAlloc (𝒜 : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) (n : Measure (Fin d → ℝ)) : Prop :=
  IsFiniteMeasure n ∧ n 𝒜ᶜ = 0 ∧ (designMat n).PosDef ∧
    ∀ u ∈ convexHull ℝ 𝒜,
      (u - astar) ⬝ᵥ (designMat n)⁻¹ *ᵥ (u - astar) ≤ ((u - astar) ⬝ᵥ θ) ^ 2 / 2

/-- the information-acquisition cost `c^n_ctr = ∫ Δ dn` -/
noncomputable def ctrCost (θ astar : Fin d → ℝ) (n : Measure (Fin d → ℝ)) : ℝ :=
  ∫ a, (a - astar) ⬝ᵥ θ ∂n

/-- `c*_ctr(𝒜, θ)`, (1.4) -/
noncomputable def cstarCtr (𝒜 : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : ℝ :=
  sInf (ctrCost θ astar '' {n | IsCtrAlloc 𝒜 θ astar n})

/-! ### Reference measure (3.2)–(3.3) -/

/-- the lexicographically least minimizer of `a ↦ aᵀv` on `ℬ` (junk `0` if none exists) -/
noncomputable def lexMinimizer (ℬ : Set (Fin d → ℝ)) (v : Fin d → ℝ) : Fin d → ℝ :=
  open Classical in
  if h : ∃ b ∈ ℬ, (∀ a ∈ ℬ, b ⬝ᵥ v ≤ a ⬝ᵥ v) ∧
      ∀ b' ∈ ℬ, (∀ a ∈ ℬ, b' ⬝ᵥ v ≤ a ⬝ᵥ v) → toLex b ≤ toLex b'
  then Classical.choose h else 0

/-- the candidate selected by the `m`-th rational direction `e m` -/
noncomputable def cand (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (m : ℕ) : Fin d → ℝ :=
  lexMinimizer ℬ (fun i => (e m i : ℝ))

/-- first-occurrence indices `J` -/
def Jset (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) : Set ℕ :=
  {m | ∀ i < m, cand ℬ e i ≠ cand ℬ e m}

/-- the prior penalty `h_j` of (3.2), with the paper's index `j = m + 1` -/
noncomputable def hPen (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (m : ℕ) : ℝ :=
  open Classical in
  ((m : ℝ) + 1) + 1 + ∑ i ∈ (Finset.range m).filter (· ∈ Jset ℬ e),
    Real.exp ((sNorm ℬ (cand ℬ e m - cand ℬ e i))⁻¹ ^ 8)

/-- the prior weight `π_j = e^{-h_j}` -/
noncomputable def piW (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (m : ℕ) : ℝ :=
  Real.exp (-hPen ℬ e m)

/-- the discrete part `Σ_{j ∈ J} π_j δ_{b_j}` -/
noncomputable def muDisc (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) : Measure (Fin d → ℝ) :=
  open Classical in
  Measure.sum fun m => if m ∈ Jset ℬ e then
    ENNReal.ofReal (piW ℬ e m) • Measure.dirac (cand ℬ e m) else 0

/-- `ω_μ = 1 - Σ_{j ∈ J} π_j` -/
noncomputable def omegaMu (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) : ℝ :=
  1 - (muDisc ℬ e Set.univ).toReal

/-- the uniform (normalized `k`-dimensional Hausdorff) measure `λ_𝒦` on `𝒦` -/
noncomputable def lamK (ℬ : Set (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  (Measure.hausdorffMeasure (kdim ℬ : ℝ))[|Kset ℬ]

/-- `μ_16`: the law of the mean of `16` i.i.d. `λ_𝒦` points -/
noncomputable def mu16 (ℬ : Set (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  (Measure.pi fun _ : Fin 16 => lamK ℬ).map fun u => (16 : ℝ)⁻¹ • ∑ i, u i

/-- the reference measure `μ = Σ_{j∈J} π_j δ_{b_j} + ω_μ μ_16`, (3.3) -/
noncomputable def refMu (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) : Measure (Fin d → ℝ) :=
  muDisc ℬ e + ENNReal.ofReal (omegaMu ℬ e) • mu16 ℬ

/-! ### Program (3.6) at paper round `t` and cumulative estimate `S` -/

/-- the learning rate `β_t = 16d + √t` -/
noncomputable def gbeta (d t : ℕ) : ℝ := 16 * (d : ℝ) + Real.sqrt t

/-- `Γ_t = 4d/β_t` -/
noncomputable def gGam (d t : ℕ) : ℝ := 4 * (d : ℝ) / gbeta d t

/-- `B = 2^36 (d + 1)` -/
noncomputable def gB (d : ℕ) : ℝ := 2 ^ 36 * ((d : ℝ) + 1)

/-- the FTRL update (3.1): `q_t(dx) ∝ exp(-xᵀS/β_t) μ(dx)` -/
noncomputable def gq (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ) :
    Measure (Fin d → ℝ) :=
  (refMu ℬ e).withDensity fun x => ENNReal.ofReal
    (Real.exp (-(x ⬝ᵥ S) / gbeta d t) /
      ∫ z, Real.exp (-(z ⬝ᵥ S) / gbeta d t) ∂(refMu ℬ e))

/-- the index `r_t` of the reference action, (3.4): the least `j ∈ J` minimizing
`b_jᵀS + β_t h_j` -/
noncomputable def rIdx (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ) : ℕ :=
  sInf {m | m ∈ Jset ℬ e ∧ ∀ i ∈ Jset ℬ e,
    cand ℬ e m ⬝ᵥ S + gbeta d t * hPen ℬ e m ≤ cand ℬ e i ⬝ᵥ S + gbeta d t * hPen ℬ e i}

/-- the reference action `b_{r_t}` -/
noncomputable def gref (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ) :
    Fin d → ℝ :=
  cand ℬ e (rIdx ℬ e t S)

/-- `Z_t(x) = [L̂_{t-1,x} - L̂_{t-1,b_{r_t}}]_+` -/
noncomputable def gZ (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S x : Fin d → ℝ) : ℝ :=
  max 0 (x ⬝ᵥ S - gref ℬ e t S ⬝ᵥ S)

/-- the empirical gap `Δ̂_t(x) = min{2, Z_t(x)/t}` -/
noncomputable def gGapHat (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S x : Fin d → ℝ) :
    ℝ :=
  min 2 (gZ ℬ e t S x / t)

/-- `U_t(x) = (β_t/2)‖x - b_{r_t}‖_𝒮 + Z_t(x)/B`, (3.5) -/
noncomputable def gU (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S x : Fin d → ℝ) : ℝ :=
  gbeta d t / 2 * sNorm ℬ (x - gref ℬ e t S) + gZ ℬ e t S x / gB d

/-- `W_t(x) = (β_t/4)‖x - b_{r_t}‖_𝒮² + Z_t(x)²/(Bt)`, (3.5) -/
noncomputable def gW (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S x : Fin d → ℝ) : ℝ :=
  gbeta d t / 4 * sNorm ℬ (x - gref ℬ e t S) ^ 2 + gZ ℬ e t S x ^ 2 / (gB d * t)

/-- `M(p) = ∫ xxᵀ p(dx)` -/
noncomputable def gM (p : Measure (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ := designMat p

/-- `v_x(p) = M(p)⁻¹ x` -/
noncomputable def gv (p : Measure (Fin d → ℝ)) (x : Fin d → ℝ) : Fin d → ℝ := (gM p)⁻¹ *ᵥ x

/-- the barycenter `x̄_t = ∫ x q_t(dx)` -/
noncomputable def gxbar (q : Measure (Fin d → ℝ)) : Fin d → ℝ := fun i => ∫ x, x i ∂q

/-- the proxy function `C_t(p)`, (3.7) -/
noncomputable def gC (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ)
    (p : Measure (Fin d → ℝ)) : ℝ :=
  gbeta d t * ∫ x, ∫ u, chi ((u - gxbar (gq ℬ e t S)) ⬝ᵥ gv p x / gbeta d t) ∂(gq ℬ e t S) ∂p

/-- the feasible set of program (3.6) at paper round `t` -/
def IsFeasible3_6 (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ)
    (p : Measure (Fin d → ℝ)) : Prop :=
  IsProbabilityMeasure p ∧ p (Kset ℬ)ᶜ = 0 ∧
    (∃ w : Measure (Fin d → ℝ), IsFiniteMeasure w ∧ w (Kset ℬ)ᶜ = 0 ∧
      (w Set.univ).toReal ≤ gGam d t ∧
      p = ENNReal.ofReal (1 - (w Set.univ).toReal) • gq ℬ e t S + w) ∧
    (gM p).PosDef ∧
    (∀ u ∈ Kset ℬ, ∀ x ∈ Kset ℬ, |(u - gref ℬ e t S) ⬝ᵥ gv p x| ≤ gU ℬ e t S u) ∧
    (∀ u ∈ Kset ℬ, ∫ x, ((u - gref ℬ e t S) ⬝ᵥ gv p x) ^ 2 ∂p ≤ gW ℬ e t S u) ∧
    gC ℬ e t S p ≤ 2 * (d : ℝ) / gbeta d t

/-- `p` is a minimizer of program (3.6): feasible, with minimal `∫ Δ̂_t dp` -/
def IsMin3_6 (ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ)
    (p : Measure (Fin d → ℝ)) : Prop :=
  IsFeasible3_6 ℬ e t S p ∧
    ∀ p', IsFeasible3_6 ℬ e t S p' → ∫ x, gGapHat ℬ e t S x ∂p ≤ ∫ x, gGapHat ℬ e t S x ∂p'

/-! ### Runs -/

/-- a run of a linear bandit learner with virtual actions -/
structure GRun (d : ℕ) (Ω : Type*) where
  /-- the virtual action `X_{t+1} ∈ 𝒦` -/
  X : ℕ → Ω → (Fin d → ℝ)
  /-- the physical action `A_{t+1}` -/
  A : ℕ → Ω → (Fin d → ℝ)
  /-- the feedback `Y_{t+1}` -/
  Y : ℕ → Ω → ℝ
  /-- the loss vector `θ_{t+1}` -/
  θs : ℕ → Ω → (Fin d → ℝ)
  /-- the sampling law `p_{t+1}` -/
  p : ℕ → Ω → Measure (Fin d → ℝ)
  /-- the pre-action σ-algebra of round `t + 1` -/
  G : ℕ → MeasurableSpace Ω

/-- the learner's history before round `t + 1`: `σ(X_s, A_s, Y_s : s < t)` -/
def GRun.hist {Ω : Type*} (R : GRun d Ω) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ s, ⨆ (_ : s < t), MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance

/-- `θ̂_t = v_{X_t}(p_t) Y_t` -/
noncomputable def GRun.thetaHat {Ω : Type*} (R : GRun d Ω) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  R.Y t ω • gv (R.p t ω) (R.X t ω)

/-- the cumulative estimate `Σ_{s<t} θ̂_s` -/
noncomputable def GRun.cumEst {Ω : Type*} (R : GRun d Ω) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  ∑ s ∈ Finset.range t, R.thetaHat s ω

/-- `R` executes GIA-FTRL (Algorithm 2) on the generator `ℬ` of the action set `𝒜`, with the
enumeration `e` of `ℚ^d`, for `T` rounds, against an adaptive environment: for every round,
the sampling law is a history-measurable minimizer of (3.6); `X_t ~ p_t` given `G_t`; the
physical action lies in `ℬ` with `E[A_t | G_t, X_t] = X_t`; `|Y_t| ≤ 1` and
`E[Y_t | G_t, X_t, A_t] = A_tᵀθ_t`; and `‖θ_t‖_𝒜 ≤ 1`. -/
def IsGIAFTRLRun {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ) (T : ℕ) (R : GRun d Ω) : Prop :=
  ∀ t < T,
    (Measurable (R.X t) ∧ Measurable (R.A t) ∧ Measurable (R.Y t) ∧ Measurable (R.θs t) ∧
      R.G t ≤ mΩ ∧ R.hist t ≤ R.G t ∧ Measurable[R.G t] (R.θs t) ∧ R.G t ≤ R.G (t + 1) ∧
      Measurable[R.G (t + 1)] (R.X t) ∧ Measurable[R.G (t + 1)] (R.A t) ∧
      Measurable[R.G (t + 1)] (R.Y t)) ∧
    (Measurable[R.hist t] (R.p t) ∧ ∀ ω, IsMin3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω)) ∧
    (∀ s : Set (Fin d → ℝ), MeasurableSet s →
      P[(R.X t ⁻¹' s).indicator (fun _ => (1 : ℝ)) | R.G t] =ᵐ[P]
        fun ω => (R.p t ω s).toReal) ∧
    ((∀ ω, R.A t ω ∈ ℬ) ∧
      P[R.A t | R.G t ⊔ MeasurableSpace.comap (R.X t) inferInstance] =ᵐ[P] R.X t) ∧
    ((∀ ω, |R.Y t ω| ≤ 1) ∧
      P[R.Y t | R.G t ⊔ MeasurableSpace.comap (fun ω => (R.X t ω, R.A t ω)) inferInstance]
        =ᵐ[P] fun ω => R.A t ω ⬝ᵥ R.θs t ω) ∧
    (∀ ω, setNorm 𝒜 (R.θs t ω) ≤ 1)

/-- the corrupted stochastic regime with fixed loss vector `θ` and budget `C`:
`‖θ‖_𝒜 ≤ 1` and `Σ_{t<T} ‖θ_t - θ‖_𝒜 ≤ C` almost surely -/
def IsCorruptedG {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (𝒜 : Set (Fin d → ℝ))
    (θ : Fin d → ℝ) (C : ℝ) (T : ℕ) (R : GRun d Ω) : Prop :=
  setNorm 𝒜 θ ≤ 1 ∧ ∀ᵐ ω ∂P, ∑ t ∈ Finset.range T, setNorm 𝒜 (R.θs t ω - θ) ≤ C

/-- the regret against a fixed comparator `u`: `E[Σ_{t<T} (A_t - u)ᵀθ_t]` -/
noncomputable def gRegretVs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (R : GRun d Ω) (u : Fin d → ℝ) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.range T, (R.A t ω - u) ⬝ᵥ R.θs t ω ∂P

end IAFTRL



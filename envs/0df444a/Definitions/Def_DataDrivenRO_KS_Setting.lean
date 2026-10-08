-- Prove2me | Definitions.Def_DataDrivenRO_KS_Setting
-- name    : DataDrivenRO_KS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:27:30.360697+00:00
-- url     : https://prove2.me/theorems/e614368d-2b09-4725-80b1-4518ee8f8dd9
-- title:
--   §5.1, pp. 15–16 — the KS regions 𝒫^{KS}_i, the product region 𝒫^I, q^L, q^R of (17), relative entropy and the set 𝒰^I_ε of (18)
-- statement:
--   Fix a dimension $d$ and a sample size $N\ge 1$. For each coordinate $i=1,\dots,d$ we are given $N+2$ real numbers
--   $$\hat u^{(0)}_i<\hat u^{(1)}_i<\dots<\hat u^{(N)}_i<\hat u^{(N+1)}_i,$$
--   where $[\hat u^{(0)}_i,\hat u^{(N+1)}_i]$ is a known interval containing the support of the $i$-th marginal of the unknown distribution, and $\hat u^{(1)}_i,\dots,\hat u^{(N)}_i$ are the order statistics of the $i$-th coordinates of the $N$ data points. Let $\Gamma=\Gamma^{KS}$ be the Kolmogorov–Smirnov threshold and $0<\epsilon<1$.
--
--   1. **Value at Risk.** For a measure $\mathbb P$ on $\mathbb R^d$ and $v\in\mathbb R^d$, $\mathrm{VaR}^{\mathbb P}_\epsilon(v)=\inf\{t:\mathbb P(\tilde u^{\mathsf T}v\le t)\ge 1-\epsilon\}$, where $\tilde u$ is the identity on $\mathbb R^d$.
--   2. **KS confidence region of marginal $i$.** $\mathcal P^{KS}_i$ is the set of Borel probability measures $\mathbb P_i$ on $\mathbb R$ carried by $[\hat u^{(0)}_i,\hat u^{(N+1)}_i]$ such that for $j=1,\dots,N$
--   $$\mathbb P_i(\tilde u_i\le\hat u^{(j)}_i)\ge\frac jN-\Gamma,\qquad \mathbb P_i(\tilde u_i<\hat u^{(j)}_i)\le\frac{j-1}N+\Gamma .$$
--   3. **Independent region.** $\mathcal P^I$ is the set of product measures $\mathbb P=\prod_{i=1}^d\mathbb P_i$ on $\mathbb R^d$ with $\mathbb P_i\in\mathcal P^{KS}_i$ for every $i$.
--   4. **The vectors $q^L(\Gamma),q^R(\Gamma)\in\mathbb R^{N+2}$** (indices $j=0,\dots,N+1$), with $k=\lfloor N(1-\Gamma)\rfloor$:
--   $$q^L_j(\Gamma)=\begin{cases}\Gamma & j=0,\\ 1/N & 1\le j\le k,\\ 1-\Gamma-k/N & j=k+1,\\ 0&\text{otherwise,}\end{cases}\qquad q^R_j(\Gamma)=q^L_{N+1-j}(\Gamma).$$
--   For $\theta\in[0,1]$ write $p(\theta)=\theta q^L(\Gamma)+(1-\theta)q^R(\Gamma)$. The discrete law with masses $q_j$ at the points $x_j$ is $\sum_j q_j\delta_{x_j}$.
--   5. **Relative entropy.** For vectors $q,p$, $D(q,p)=\sum_j q_j\log(q_j/p_j)$ with $0\log(0/\cdot)=0$; it is finite only when $q_j>0$ implies $p_j>0$.
--   6. **The uncertainty set** $\mathcal U^I_\epsilon\subseteq\mathbb R^d$ is the set of $u$ for which there are $\theta_i\in[0,1]$ and $q^i\in\Delta_{N+2}$ ($i=1,\dots,d$) with every $D(q^i,p(\theta_i))$ finite and
--   $$\sum_{j=0}^{N+1}\hat u^{(j)}_iq^i_j=u_i\ (i=1,\dots,d),\qquad \sum_{i=1}^dD\big(q^i,\theta_iq^L(\Gamma)+(1-\theta_i)q^R(\Gamma)\big)\le\log(1/\epsilon).$$
--   7. **The bound of (19)** at a multiplier $\lambda>0$:
--   $$B(\lambda)=\lambda\log(1/\epsilon)+\lambda\sum_{i=1}^d\log\Big[\max\Big(\sum_{j=0}^{N+1}q^L_j(\Gamma)e^{v_i\hat u^{(j)}_i/\lambda},\ \sum_{j=0}^{N+1}q^R_j(\Gamma)e^{v_i\hat u^{(j)}_i/\lambda}\Big)\Big].$$
--
--   These are the objects of Theorem 5 of Bertsimas, Gupta and Kallus: $\mathcal P^I$ is the confidence region of the combined KS tests, and $\mathcal U^I_\epsilon$ is the uncertainty set whose support function equals $\inf_\lambda B(\lambda)$.
--
--   **Formalization Note** Coordinates are `Fin d` and the points are `uhat i j` with `j : Fin (N + 2)`, so the page's $j=0,\dots,N+1$ is kept; the KS constraints quantify over `j : Fin N`, which is the page's $j-1$ (the point is `obsIdx j` $=j+1$). The KS bounds are compared in $[0,\infty]$ through `ENNReal.ofReal`; when $j/N-\Gamma<0$ the lower constraint becomes vacuous, as on the page. The floor is `Nat.floor`. $D$ is `relEntropy` together with the finiteness predicate `AbsCont`, which is required wherever $D$ appears, so Lean's `log 0 = 0` cannot make an infinite divergence look finite. The Value at Risk is the published `MultistageStochastic.valueAtRisk` at level $1-\epsilon$; the support function used with these objects is the published `RobustMDP.Shared.supportFunction`. Independence is built into `Measure.pi`.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §5.1, p. 15 (box, 𝒫^{KS}_i, 𝒫^I); (17), (18), (19), p. 16; (6), p. 10 (VaR); D of §4, p. 12

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RobustMDP_Shared_supportFunction

open MeasureTheory

namespace DataDrivenRO.KS

/-- Value at Risk at level `ε` in direction `v`, display (6), p. 10:
`VaR^ℙ_ε(v) = inf {t : ℙ(ũᵀv ≤ t) ≥ 1 − ε}`, where `ũ` is the identity on `ℝᵈ = Fin d → ℝ`.
It is the published `MultistageStochastic.valueAtRisk` at level `1 − ε` applied to `u ↦ uᵀv`. -/
noncomputable def VaR {d : ℕ} (P : Measure (Fin d → ℝ)) (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  MultistageStochastic.valueAtRisk P (fun u => u ⬝ᵥ v) (1 - ε)

/-- The index of the `j`-th order statistic (the page's `j = 1, …, N`, here `j : Fin N` is the
page's `j − 1`) among the points `û^(0), …, û^(N+1)`, indexed by `Fin (N + 2)`. -/
def obsIdx {N : ℕ} (j : Fin N) : Fin (N + 2) := ⟨(j : ℕ) + 1, by omega⟩

/-- The confidence region `𝒫^{KS}_i` of the Kolmogorov–Smirnov test for the `i`-th marginal,
§5.1, p. 15. `uhat i j = û^(j)_i` for `j = 0, …, N + 1`: `û^(0)_i`, `û^(N+1)_i` are the ends of the
known box and `û^(1)_i, …, û^(N)_i` the order statistics of the `i`-th coordinate of the sample.
A measure `Q` on `ℝ` is in the region when it is a Borel probability measure carried by
`[û^(0)_i, û^(N+1)_i]` and, for `j = 1, …, N` (page index),
`Q(ũᵢ ≤ û^(j)_i) ≥ j/N − Γ` and `Q(ũᵢ < û^(j)_i) ≤ (j − 1)/N + Γ`. -/
def ksRegion {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d) :
    Set (Measure ℝ) :=
  {Q | IsProbabilityMeasure Q ∧
    Q (Set.Icc (uhat i 0) (uhat i (Fin.last (N + 1))))ᶜ = 0 ∧
    ∀ j : Fin N,
      ENNReal.ofReal (((j : ℝ) + 1) / N - Γ) ≤ Q (Set.Iic (uhat i (obsIdx j))) ∧
      Q (Set.Iio (uhat i (obsIdx j))) ≤ ENNReal.ofReal ((j : ℝ) / N + Γ)}

/-- The confidence region `𝒫^I` of the multivariate test, §5.1, p. 15: the product measures
`ℙ = ∏ᵢ ℙᵢ` on `ℝᵈ` whose marginals `ℙᵢ` lie in the KS regions `𝒫^{KS}_i`. Independence of the
components is built into `Measure.pi`. -/
def productRegion {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) :
    Set (Measure (Fin d → ℝ)) :=
  {P | ∃ (Q : Fin d → Measure ℝ) (_ : ∀ i, IsProbabilityMeasure (Q i)),
    (∀ i, Q i ∈ ksRegion uhat Γ i) ∧ P = Measure.pi Q}

/-- The vector `q^L(Γ) ∈ ℝ^{N+2}` of (17), p. 16, indexed `j = 0, …, N + 1`:
`Γ` at `j = 0`, `1/N` for `1 ≤ j ≤ ⌊N(1 − Γ)⌋`, `1 − Γ − ⌊N(1 − Γ)⌋/N` at `j = ⌊N(1 − Γ)⌋ + 1`,
and `0` otherwise. -/
noncomputable def qL (N : ℕ) (Γ : ℝ) (j : Fin (N + 2)) : ℝ :=
  if (j : ℕ) = 0 then Γ
  else if (j : ℕ) ≤ ⌊(N : ℝ) * (1 - Γ)⌋₊ then 1 / N
  else if (j : ℕ) = ⌊(N : ℝ) * (1 - Γ)⌋₊ + 1 then 1 - Γ - (⌊(N : ℝ) * (1 - Γ)⌋₊ : ℝ) / N
  else 0

/-- The vector `q^R(Γ)` of (17), p. 16: `q^R_j(Γ) = q^L_{N+1−j}(Γ)`. -/
noncomputable def qR (N : ℕ) (Γ : ℝ) (j : Fin (N + 2)) : ℝ :=
  qL N Γ (Fin.rev j)

/-- The mixture `θ q^L(Γ) + (1 − θ) q^R(Γ)` appearing in (18). -/
noncomputable def mix (N : ℕ) (Γ θ : ℝ) (j : Fin (N + 2)) : ℝ :=
  θ * qL N Γ j + (1 - θ) * qR N Γ j

/-- The discrete probability law that puts mass `q j` on the point `x j`. -/
noncomputable def lawOn {n : ℕ} (x : Fin n → ℝ) (q : Fin n → ℝ) : Measure ℝ :=
  ∑ j, ENNReal.ofReal (q j) • Measure.dirac (x j)

/-- Finiteness condition of the relative entropy `D(q, p)`: `q j > 0` only where `p j > 0`.
When it fails, `D(q, p) = +∞`. -/
def AbsCont {n : ℕ} (q p : Fin n → ℝ) : Prop :=
  ∀ j, 0 < q j → 0 < p j

/-- The relative entropy `D(q, p) = Σⱼ qⱼ log(qⱼ/pⱼ)` of §4, p. 12, with `0 · log(0/·) = 0`.
It is the true value only under `AbsCont q p`; every use below carries that condition. -/
noncomputable def relEntropy {n : ℕ} (q p : Fin n → ℝ) : ℝ :=
  ∑ j, q j * Real.log (q j / p j)

/-- The uncertainty set `𝒰^I_ε` of (18), p. 16: the `u ∈ ℝᵈ` for which there are `θᵢ ∈ [0, 1]`
and `qⁱ ∈ Δ_{N+2}` with `Σⱼ û^(j)_i qⁱ_j = uᵢ` for every `i` and
`Σᵢ D(qⁱ, θᵢ q^L(Γ) + (1 − θᵢ) q^R(Γ)) ≤ log(1/ε)` (each `D` finite). -/
def UI {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∃ (θ : Fin d → ℝ) (q : Fin d → Fin (N + 2) → ℝ),
    (∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ i, q i ∈ stdSimplex ℝ (Fin (N + 2))) ∧
    (∀ i, ∑ j, uhat i j * q i j = u i) ∧
    (∀ i, AbsCont (q i) (mix N Γ (θ i))) ∧
    ∑ i, relEntropy (q i) (mix N Γ (θ i)) ≤ Real.log (1 / ε)}

/-- The expression inside the infimum of (19), p. 16, at multiplier `lam > 0`:
`lam log(1/ε) + lam Σᵢ log max(Σⱼ q^L_j e^{vᵢû^(j)_i/lam}, Σⱼ q^R_j e^{vᵢû^(j)_i/lam})`. -/
noncomputable def boundKS {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ ε : ℝ)
    (v : Fin d → ℝ) (lam : ℝ) : ℝ :=
  lam * Real.log (1 / ε) + lam * ∑ i, Real.log (max
    (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
    (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam)))

end DataDrivenRO.KS



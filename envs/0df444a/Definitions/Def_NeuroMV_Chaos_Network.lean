-- Prove2me | Definitions.Def_NeuroMV_Chaos_Network
-- name    : NeuroMV_Chaos_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:05.958125+00:00
-- url     : https://prove2.me/theorems/7a8e9f41-a017-4f58-826a-35e74befee95
-- title:
--   §1–§3, pp. 2–21 — the network (1), the mean-field limit (5), (H6), Hypothesis 1.6, chaotic initial condition, C₁, C₂, I^θ_α, I^β_α, I^η_α
-- statement:
--   This module defines the finite neuronal network (1), its mean-field limit (5), and the hypotheses and quantities of the propagation-of-chaos theorem.
--
--   **The network (1).** Neurons carry labels $i\in\mathbb N$ with positions $\mathrm{pos}(i)\in\Gamma$; the $N$-th network is a set $\mathcal A_N$ of $N$ labels, and $\mathcal S_{\mathcal A_N,\alpha}\neq0$ are the weights. Writing $\#(\mathcal A_N\cap A)$ for the number of neurons of $\mathcal A_N$ placed in $A$, the network equation is
--   $$dX^{r,\mathcal A_N}_t = f\,dt + g\,dW^r_t + \int_U h\,\tilde N^r(dt,d\xi) + \sum_{\alpha}\frac{1}{\mathcal S_{\mathcal A_N,\alpha}}\sum_{\tilde r\in\mathcal A_N\cap\Gamma_\alpha}\Big[\theta(t,r,\tilde r,X^{r,\mathcal A_N}_{t-},X^{\tilde r,\mathcal A_N}_{(t-\tau)^-:t^-})dt + \beta(\cdots)dB^{r,\alpha}_t + \int_U\eta(\cdots,\xi)\tilde N^{r,\alpha}(dt,d\xi)\Big],$$
--   with $X^{r,\mathcal A_N}=z^r$ on $[-\tau,0]$. The standing assumptions (p. 2, Appendix A) are: positions distinct and in $\Gamma$, $\#\mathcal A_N=N$, the filtration satisfies the usual conditions, all $W^r, B^{r,\alpha}$ are standard Brownian motions forming one independent $(\mathcal F_t)$-Brownian family, all $N^r, N^{r,\alpha}$ are independent $(\mathcal F_t)$-Poisson measures with intensity $dt\otimes\nu$, and the $z^r$ are càdlàg, $\mathcal F_0$-measurable and in $L^2(\Omega;\mathrm{Càdlàg}([-\tau,0];\mathbb R^d))$.
--
--   **The limit (5).** For a label $i$ with $r=\mathrm{pos}(i)$, $\bar X^r$ starts from the same $z^r$, is driven by the same $W^r, B^{r,\alpha}, N^r, N^{r,\alpha}$, and replaces the network sums by $\int_{\Gamma_\alpha}\tilde{\mathbb E}[\Theta(t,r,r',\bar X^r_{t-},\hat X^{r'}_{(t-\tau)^-:t^-})]\mathcal R(dr')$, where $\hat X$ is a solution of (6) on its own probability space.
--
--   **Hypotheses.** (H6) asks $\sup_N\sum_\alpha(\#\mathcal A_N\cap\Gamma_\alpha)^2/\mathcal S^2_{\mathcal A_N,\alpha}<\infty$ and, for every $T>0$,
--   $$\mathcal E\exp\int_0^T\Big[2L_s+\bar L_s\Big(P+6\sup_N\sum_\alpha\frac{(\#\mathcal A_N\cap\Gamma_\alpha)^2}{\mathcal S^2_{\mathcal A_N,\alpha}}\Big)+K_s+3P\bar K_s\Big]ds<\infty.$$
--   Hypothesis 1.1 is (H1)–(H6). Hypothesis 1.6 adds $\mathcal S_{\mathcal A_N,\alpha}\to\infty$ and, for every $\varepsilon>0$, measurable partitions $\{\Gamma^{m,\varepsilon}_\alpha\}_{m<M^{(\varepsilon)}_\alpha}$ of each $\Gamma_\alpha$ with $\#(\mathcal A_N\cap\Gamma^{m,\varepsilon}_\alpha)/\mathcal S_{\mathcal A_N,\alpha}\to\mathcal R(\Gamma^{m,\varepsilon}_\alpha)$ (10) and the cell-wise conditions (H1′), (H4′): within a cell, the (H1) and (H4) bounds hold between different positions up to an extra $\varepsilon(1+|x|^2)$, resp. $\varepsilon(1+|x|^2+\int(|y_s|^2+1_{s<0}|y_{s+}|^2)\lambda(ds))$. The *chaotic initial condition* says the $z^r$, $r\in\bigcup_N\mathcal A_N$, are independent and $z^r$ has the law of $\hat z^\alpha$ when $r\in\Gamma_\alpha$.
--
--   **Constants and terms of §3.** $C_1(t,\omega')=(\sup_{u,\zeta}\mathbb E|\hat z^\zeta(u)|^2+1)\exp\int_0^t(K_s+3P\bar K_s+P)ds$ (7), $C_2(t,\omega')=\exp[\int_0^t(L_s+P\bar L_s+P)ds](1+3C_1(t,\omega'))$, the bracket $\#\mathcal A_N\cap\Gamma_\alpha/\mathcal S^2+\varepsilon(\#\mathcal A_N\cap\Gamma_\alpha)^2/\mathcal S^2+M^{(\varepsilon)}_\alpha\sum_m(\#(\mathcal A_N\cap\Gamma^{m,\varepsilon}_\alpha)/\mathcal S-\mathcal R(\Gamma^{m,\varepsilon}_\alpha))^2$, and
--   $$I^\theta_\alpha=\mathbb E\int_0^t\Big|\frac1{\mathcal S_{\mathcal A_N,\alpha}}\sum_{\tilde r\in\mathcal A_N\cap\Gamma_\alpha}\theta(s,r,\tilde r,\bar X^r_{s-},\bar X^{\tilde r}_{(s-\tau)^-:s^-})-\tilde{\mathbb E}\int_{\Gamma_\alpha}\theta(s,r,r',\bar X^r_{s-},\tilde X^{r'}_{(s-\tau)^-:s^-})\mathcal R(dr')\Big|^2ds,$$
--   with $I^\beta_\alpha$ and $I^\eta_\alpha$ (the latter with an extra $\int_U\cdot\,\nu(d\xi)$) alike.
--
--   **Formalization Note.** Labels stand for positions (the position map is injective). All expectations, suprema and $I$-terms are in $[0,\infty]$; (H6) states the boundedness of the supremum explicitly so that the real supremum is genuine. The Poisson measures of all neurons are one Poisson measure on the mark space $(\mathbb N\times\mathrm{Option}(\mathrm{Fin}\,P))\times U$ with intensity $dt\otimes(\mathrm{count}\otimes\nu)$. In (H1′) the page prints $2\langle x-y,\dots\rangle$; the variable $y$ does not occur there and $x-\tilde x$ (as in (H1)) is meant and used. On p. 20 $I^\eta_\alpha$ is printed without the expectation $\mathbb E$ that (17) has; the definition includes it. The usual conditions on the filtration are the standing assumption of Appendix A, which provides Proposition 1.2.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, (1), p. 2; (H6), p. 4; (5), p. 5; (7), p. 6; Hypothesis 1.6 and Lemma 1.7, pp. 7–8; Theorem 1.8, p. 9; §3, pp. 17–21; Appendix A, p. 21

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-! ### The network (1), p. 2

Neurons carry labels `i : ℕ`; `pos i ∈ Γ` is the position of neuron `i`, and `𝒜 N` is the finite
set of labels of the `N` neurons of the `N`-th network (the paper's `𝒜_N ⊂ Γ`). -/

/-- The labels of the neurons of `𝒜_N` whose position lies in `A` (the paper's `𝒜_N ∩ A`). -/
noncomputable def nbr {k : ℕ} (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (N : ℕ) (A : Set (NeuroMV.WellPosed.Pos k)) :
    Finset ℕ := by
  classical
  exact (𝒜 N).filter (fun i => pos i ∈ A)

/-- `#(𝒜_N ∩ A)`. -/
noncomputable def cnt {k : ℕ} (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (N : ℕ) (A : Set (NeuroMV.WellPosed.Pos k)) :
    ℕ :=
  (nbr pos 𝒜 N A).card

/-- The scalar coordinates of all Brownian motions of the network: `W^i` (in `ℝᵐ`) and
`B^{i,α}` (in `ℝⁿ`), for every label `i`. -/
def coordsNet {Ω : Type*} {m n P : ℕ} (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m)
    (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n) :
    ℕ × (Fin m ⊕ (Fin P × Fin n)) → ℝ≥0 → Ω → ℝ :=
  fun c => coords6 (W c.1) (B c.1) c.2

/-- The filtration satisfies the usual conditions (Appendix A, p. 21): every `ℙ`-null set is in
`𝓕₀` (so `ℙ` is complete), and `𝓕_t = ⋂_{s > t} 𝓕_s`. -/
def UsualConditions {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) : Prop :=
  (∀ A : Set Ω, Pr A = 0 → MeasurableSet[𝓕 0] A) ∧ ∀ t : ℝ≥0, 𝓕 t = ⨅ s > t, 𝓕 s

/-- The standing assumptions on the network data (p. 2, Appendix A p. 21):
1. distinct neurons have distinct positions, all in `Γ`; `𝒜_N` has `N` neurons; `𝒮_{𝒜_N,α} ≠ 0`;
2. `(Ω, 𝓕, (𝓕_t), ℙ)` is a probability space whose filtration satisfies the usual conditions;
3. the `W^i` (in `ℝᵐ`) and `B^{i,α}` (in `ℝⁿ`) are standard Brownian motions whose coordinates
   form one `(𝓕_t)`-Brownian family (all independent);
4. one `(𝓕_t)`-Poisson random measure on `[0, ∞) × ((ℕ × Option (Fin P)) × U)` with intensity
   `dt ⊗ (count ⊗ ν)`: its mark `(i, none)` is `N^i`, its mark `(i, some α)` is `N^{i,α}`, so
   all these are independent Poisson measures with intensity `dt ⊗ ν`;
5. the initial conditions `z^i` are càdlàg on `[-τ, 0]`, `𝓕₀`-measurable (hence independent of
   the noise) and in `L²(Ω, ℙ; Càdlàg([-τ, 0]; ℝᵈ))`. -/
def NetSetup {d m n k P : ℕ} {U Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (G : Geometry k P) (ν : Measure U) (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d) :
    Prop :=
  Function.Injective pos ∧ (∀ N, ∀ i ∈ 𝒜 N, pos i ∈ G.Γ) ∧ (∀ N, (𝒜 N).card = N) ∧
    (∀ N α, S N α ≠ 0) ∧
    IsProbabilityMeasure Pr ∧ UsualConditions Pr 𝓕 ∧
    (∀ i, EthierKurtz.IsStandardBrownian Pr (W i)) ∧
    (∀ i α, EthierKurtz.IsStandardBrownian Pr (B i α)) ∧
    IsFBrownianFamily Pr 𝓕 (coordsNet W B) ∧
    JacodTodorov10.LLN.IsFPoisson 𝓕 Pr (Measure.count.prod ν) Nall ∧
    IsInit Pr 𝓕 G.τ z

/-- The network drift `(1/𝒮_{𝒜_N,α}) Σ_{r̃ ∈ 𝒜_N ∩ Γ_α} θ(s, r, r̃, x, Y^{r̃}_{(s−τ)⁻:s⁻}(ω), ω')`. -/
noncomputable def netθ {d m n k P : ℕ} {U Ω' Ω : Type*} (G : Geometry k P)
    (C : Coeffs d m n k P U Ω') (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ)
    (Y : ℕ → ℝ → Ω → EthierKurtz.SDEState d) (N : ℕ) (α : Fin P) (s : ℝ≥0) (r : NeuroMV.WellPosed.Pos k)
    (x : EthierKurtz.SDEState d) (ω : Ω) (ω' : Ω') : EthierKurtz.SDEState d :=
  (S N α)⁻¹ • ∑ i' ∈ nbr pos 𝒜 N (G.Γα α), C.θ s r (pos i') x (seg (Y i') s ω) ω'

/-- The network diffusion `(1/𝒮_{𝒜_N,α}) Σ_{r̃ ∈ 𝒜_N ∩ Γ_α} β(s, r, r̃, x, Y^{r̃}_{(s−τ)⁻:s⁻}(ω), ω')`. -/
noncomputable def netβ {d m n k P : ℕ} {U Ω' Ω : Type*} (G : Geometry k P)
    (C : Coeffs d m n k P U Ω') (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ)
    (Y : ℕ → ℝ → Ω → EthierKurtz.SDEState d) (N : ℕ) (α : Fin P) (s : ℝ≥0) (r : NeuroMV.WellPosed.Pos k)
    (x : EthierKurtz.SDEState d) (ω : Ω) (ω' : Ω') : Matrix (Fin d) (Fin n) ℝ :=
  (S N α)⁻¹ • ∑ i' ∈ nbr pos 𝒜 N (G.Γα α), C.β s r (pos i') x (seg (Y i') s ω) ω'

/-- The network jump integrand
`(1/𝒮_{𝒜_N,α}) Σ_{r̃ ∈ 𝒜_N ∩ Γ_α} η(s, r, r̃, x, Y^{r̃}_{(s−τ)⁻:s⁻}(ω), ω', ξ)`. -/
noncomputable def netη {d m n k P : ℕ} {U Ω' Ω : Type*} (G : Geometry k P)
    (C : Coeffs d m n k P U Ω') (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ)
    (Y : ℕ → ℝ → Ω → EthierKurtz.SDEState d) (N : ℕ) (α : Fin P) (s : ℝ≥0) (r : NeuroMV.WellPosed.Pos k)
    (x : EthierKurtz.SDEState d) (ω : Ω) (ω' : Ω') (ξ : U) : EthierKurtz.SDEState d :=
  (S N α)⁻¹ • ∑ i' ∈ nbr pos 𝒜 N (G.Γα α), C.η s r (pos i') x (seg (Y i') s ω) ω' ξ

/-- `XN = (X^{i,𝒜_N})_{i ∈ 𝒜_N}` is a strong solution of the network equation (1) on `[-τ, T]`
at the disorder `ω'`: for every `i ∈ 𝒜_N`, `X^{i,𝒜_N}` starts from `z^i`, is driven by `W^i`,
`N^i`, `B^{i,α}`, `N^{i,α}`, and its interaction terms are the pathwise network sums over the
current states of the other neurons (same `ω`), every coefficient at `X^{i,𝒜_N}_{s−}`. -/
def IsNetSol {d m n k P : ℕ} {U Ω' Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (G : Geometry k P) (ν : Measure U) (C : Coeffs d m n k P U Ω') (pos : ℕ → NeuroMV.WellPosed.Pos k)
    (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Pr : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m)
    (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (N : ℕ) (ω' : Ω') (T : ℝ) (XN : ℕ → ℝ → Ω → EthierKurtz.SDEState d) : Prop :=
  ∀ i ∈ 𝒜 N,
    IsJumpItoSol Pr 𝓕 ν G.τ T (W i) (B i) (markSlice Nall (i, none))
      (fun α => markSlice Nall (i, some α)) (z i)
      (fun s ω => C.f s (pos i) (lft (XN i) s ω) ω' +
        ∑ α, netθ G C pos 𝒜 S XN N α s (pos i) (lft (XN i) s ω) ω ω')
      (fun s ω => C.g s (pos i) (lft (XN i) s ω) ω')
      (fun s ω ξ => C.h s (pos i) (lft (XN i) s ω) ω' ξ)
      (fun α s ω => netβ G C pos 𝒜 S XN N α s (pos i) (lft (XN i) s ω) ω ω')
      (fun α s ω ξ => netη G C pos 𝒜 S XN N α s (pos i) (lft (XN i) s ω) ω ω' ξ)
      (XN i)

/-! ### The mean-field limit (5), p. 5 -/

/-- `Y = X̄^i` solves the mean-field equation (5) on `[-τ, T]` at the disorder `ω'` for the
neuron with label `i`: it starts from the same `z^i` and is driven by the same `W^i`, `N^i`,
`B^{i,α}`, `N^{i,α}` as neuron `i` of the network, and its interaction terms are the mean-field
terms of (5), computed from the law of the solution `X` of (6) (on its own probability space
`PrX`, the copy `X̂`), evaluated at `X̄^i_{s−}`. -/
def IsLimitSol {d m n k P : ℕ} {U Ω' Ω ΩX : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    [MeasurableSpace ΩX] (G : Geometry k P) (ν : Measure U) (C : Coeffs d m n k P U Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d) (ω' : Ω') (T : ℝ) (i : ℕ)
    (Y : ℝ → Ω → EthierKurtz.SDEState d) : Prop :=
  IsJumpItoSol Pr 𝓕 ν G.τ T (W i) (B i) (markSlice Nall (i, none))
    (fun α => markSlice Nall (i, some α)) (z i)
    (fun s ω => C.f s (pos i) (lft Y s ω) ω' + ∑ α, meanθ G C PrX X α s (pos i) (lft Y s ω) ω')
    (fun s ω => C.g s (pos i) (lft Y s ω) ω')
    (fun s ω ξ => C.h s (pos i) (lft Y s ω) ω' ξ)
    (fun α s ω => meanβ G C PrX X α s (pos i) (lft Y s ω) ω')
    (fun α s ω ξ => meanη G C PrX X α s (pos i) (lft Y s ω) ω' ξ)
    Y

/-! ### Hypotheses 1.1 (H6) and 1.6 -/

/-- `Σ_α (#𝒜_N ∩ Γ_α)² / 𝒮²_{𝒜_N,α}`. -/
noncomputable def sqSum {k P : ℕ} (G : Geometry k P) (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ)
    (S : ℕ → Fin P → ℝ) (N : ℕ) : ℝ :=
  ∑ α, (cnt pos 𝒜 N (G.Γα α) : ℝ) ^ 2 / S N α ^ 2

/-- **(H6)** (p. 4): `sup_N Σ_α (#𝒜_N ∩ Γ_α)²/𝒮²_{𝒜_N,α}` is finite, and for every `T > 0`
`𝓔 exp ∫_0^T [2L_s + L̄_s (P + 6 sup_N Σ_α (#𝒜_N ∩ Γ_α)²/𝒮²_{𝒜_N,α}) + K_s + 3P K̄_s] ds < ∞`. -/
def H6 {k P : ℕ} {Ω' : Type*} [MeasurableSpace Ω'] (G : Geometry k P) (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Pr' : Measure Ω') : Prop :=
  BddAbove (Set.range (sqSum G pos 𝒜 S)) ∧
    ∀ T : ℝ, 0 < T →
      (∫⁻ ω', ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..T,
        (2 * R.L s.toNNReal ω' + R.Lb s.toNNReal ω' * ((P : ℝ) + 6 * ⨆ N, sqSum G pos 𝒜 S N) +
          R.K s.toNNReal ω' + 3 * (P : ℝ) * R.Kb s.toNNReal ω'))) ∂Pr') < ⊤

/-- **Hypothesis 1.1** (pp. 3–4) for the network: (H1)–(H5) and (H6). -/
def Hyp11 {d m n k P : ℕ} {U Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω']
    (G : Geometry k P) (ν : Measure U) (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Pr' : Measure Ω') : Prop :=
  Hyp G ν C R ∧ H6 G R pos 𝒜 S Pr'

/-- For every `ε` and `α`, a finite family `Γ^{m,ε}_α`, `m : Fin (M^{(ε)}_α)` (0-based), of
subsets of `ℝᵏ` (Hypothesis 1.6). -/
structure Partitions (k P : ℕ) where
  M : ℝ → Fin P → ℕ
  part : (ε : ℝ) → (α : Fin P) → Fin (M ε α) → Set (NeuroMV.WellPosed.Pos k)

/-- **Hypothesis 1.6** (pp. 7–8): Hypothesis 1.1 holds, `𝒮_{𝒜_N,α} → ∞` for every `α`, and for
every `ε > 0` and `α` the sets `Γ^{m,ε}_α` form a measurable partition of `Γ_α` such that
1. (10): `#(𝒜_N ∩ Γ^{m,ε}_α) / 𝒮_{𝒜_N,α} → 𝓡(Γ^{m,ε}_α)` as `N → ∞`, for every `m`;
2. (H1′): for `r, r̃ ∈ Γ^{m,ε}_α`,
   `2⟨x − x̃, f(t,r,x,ω') − f(t,r̃,x̃,ω')⟩ + |g(t,r,x,ω') − g(t,r̃,x̃,ω')|²
     + ∫_U |h(t,r,x,ω',ξ) − h(t,r̃,x̃,ω',ξ)|² ν(dξ) ≤ L_t(ω') [|x − x̃|² + ε(1 + |x|²)]`;
3. (H4′): for `r, r̃ ∈ Γ^{m,ε}_α` and `r', r̃' ∈ Γ^{m',ε}_{α'}`, the (H4) left-hand side with
   `(r, r')` against `(r̃, r̃')` is at most
   `L̄_t(ω') [|x − x̃|² + ∫(|y_s − ỹ_s|² + 1_{s<0}|y_{s+} − ỹ_{s+}|²) λ(ds)
     + ε(1 + |x|² + ∫(|y_s|² + 1_{s<0}|y_{s+}|²) λ(ds))]`.

The measure `𝓡` is the one of (5)–(6) (`G.𝓡`). -/
def Hyp16 {d m n k P : ℕ} {U Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω']
    (G : Geometry k P) (ν : Measure U) (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Pr' : Measure Ω')
    (Q : Partitions k P) : Prop :=
  Hyp11 G ν C R pos 𝒜 S Pr' ∧ (∀ α, Tendsto (fun N => S N α) atTop atTop) ∧
    ∀ ε : ℝ, 0 < ε → ∀ α : Fin P,
      (∀ m, MeasurableSet (Q.part ε α m)) ∧ Pairwise (Function.onFun Disjoint (Q.part ε α)) ∧
      (⋃ m, Q.part ε α m) = G.Γα α ∧
      -- (10)
      (∀ m, Tendsto (fun N => (cnt pos 𝒜 N (Q.part ε α m) : ℝ) / S N α) atTop
        (𝓝 (G.𝓡 (Q.part ε α m)).toReal)) ∧
      -- (H1′)
      (∀ m, ∀ r ∈ Q.part ε α m, ∀ r' ∈ Q.part ε α m, ∀ t x x' ω',
        (∫⁻ ξ, ‖C.h t r x ω' ξ - C.h t r' x' ω' ξ‖ₑ ^ 2 ∂ν) < ⊤ ∧
        2 * inner ℝ (x - x') (C.f t r x ω' - C.f t r' x' ω') +
            frob2 (C.g t r x ω' - C.g t r' x' ω') +
            (∫⁻ ξ, ‖C.h t r x ω' ξ - C.h t r' x' ω' ξ‖ₑ ^ 2 ∂ν).toReal ≤
          R.L t ω' * (‖x - x'‖ ^ 2 + ε * (1 + ‖x‖ ^ 2))) ∧
      -- (H4′)
      (∀ m, ∀ r ∈ Q.part ε α m, ∀ rt ∈ Q.part ε α m, ∀ α' : Fin P, ∀ m',
        ∀ r' ∈ Q.part ε α' m', ∀ rt' ∈ Q.part ε α' m', ∀ t x xt y yt ω',
        IsCagladOn G.τ y → IsCagladOn G.τ yt →
        ENNReal.ofReal (‖C.θ t r r' x y ω' - C.θ t rt rt' xt yt ω'‖ ^ 2 +
            frob2 (C.β t r r' x y ω' - C.β t rt rt' xt yt ω')) +
            ∫⁻ ξ, ‖C.η t r r' x y ω' ξ - C.η t rt rt' xt yt ω' ξ‖ₑ ^ 2 ∂ν ≤
          ENNReal.ofReal (R.Lb t ω') *
            (ENNReal.ofReal (‖x - xt‖ ^ 2) + lamDist2 R.lam y yt +
              ENNReal.ofReal ε * (1 + ENNReal.ofReal (‖x‖ ^ 2) + lamDist2 R.lam y 0)))

/-! ### The chaotic initial condition (Theorem 1.8, p. 9) -/

/-- The initial path `u ↦ z_u(ω)`, `u ∈ [-τ, 0]`, as a random element of `(ℝᵈ)^{[-τ, 0]}`. -/
def initPath {Ω : Type*} {d : ℕ} (τ : ℝ) (z : ℝ → Ω → EthierKurtz.SDEState d) (ω : Ω) :
    Set.Icc (-τ) 0 → EthierKurtz.SDEState d :=
  fun u => z u ω

/-- The **chaotic initial condition assumption** of Theorem 1.8: the initial conditions `z^i`,
`i ∈ ⋃_N 𝒜_N`, are independent, and `z^i` has the law of `ẑ^α` (on the space `PrX` of (6))
when `pos i ∈ Γ_α`. -/
def ChaoticInit {d k P : ℕ} {Ω ΩX : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (Pr : Measure Ω)
    (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d) (PrX : Measure ΩX)
    (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d) : Prop :=
  iIndepFun (fun i : {i : ℕ // ∃ N, i ∈ 𝒜 N} => initPath G.τ (z i)) Pr ∧
    ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) → ∀ α, pos i ∈ G.Γα α →
      IdentDistrib (initPath G.τ (z i)) (initPath G.τ (zh α)) Pr PrX

/-! ### The constants of Lemmas 1.4 and 1.7 and the terms of §3 -/

/-- `C₁(t, ω') = (sup_{u ∈ [-τ,0], 1 ≤ ζ ≤ P} 𝔼|ẑ^ζ(u)|² + 1) exp(∫_0^t (K_s + 3P K̄_s + P) ds)`
((7), Lemma 1.4, p. 6), in `[0, ∞]`. -/
noncomputable def C1 {d k P : ℕ} {Ω' ΩX : Type*} [MeasurableSpace ΩX] (G : Geometry k P)
    (R : Rates Ω') (PrX : Measure ΩX) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d) (t : ℝ)
    (ω' : Ω') : ℝ≥0∞ :=
  ((⨆ u ∈ Set.Icc (-G.τ) 0, ⨆ ζ, ∫⁻ ω, ‖zh ζ u ω‖ₑ ^ 2 ∂PrX) + 1) *
    ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..t,
      (R.K s.toNNReal ω' + 3 * (P : ℝ) * R.Kb s.toNNReal ω' + P)))

/-- `C₂(t, ω') = exp[∫_0^t (L_s + P L̄_s + P) ds] (1 + 3 C₁(t, ω'))` (Lemma 1.7, p. 8). -/
noncomputable def C2 {d k P : ℕ} {Ω' ΩX : Type*} [MeasurableSpace ΩX] (G : Geometry k P)
    (R : Rates Ω') (PrX : Measure ΩX) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d) (t : ℝ)
    (ω' : Ω') : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..t,
      (R.L s.toNNReal ω' + (P : ℝ) * R.Lb s.toNNReal ω' + P))) *
    (1 + 3 * C1 G R PrX zh t ω')

/-- The bracket of §3 (pp. 20–21):
`#𝒜_N ∩ Γ_α / 𝒮²_{𝒜_N,α} + ε (#𝒜_N ∩ Γ_α)² / 𝒮²_{𝒜_N,α}
  + M^{(ε)}_α Σ_m (#(𝒜_N ∩ Γ^{m,ε}_α) / 𝒮_{𝒜_N,α} − 𝓡(Γ^{m,ε}_α))²`. -/
noncomputable def bracket {k P : ℕ} (G : Geometry k P) (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ)
    (S : ℕ → Fin P → ℝ) (Q : Partitions k P) (N : ℕ) (ε : ℝ) (α : Fin P) : ℝ :=
  (cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α ^ 2 + ε * (cnt pos 𝒜 N (G.Γα α) : ℝ) ^ 2 / S N α ^ 2 +
    (Q.M ε α : ℝ) * ∑ mm, ((cnt pos 𝒜 N (Q.part ε α mm) : ℝ) / S N α -
      (G.𝓡 (Q.part ε α mm)).toReal) ^ 2

/-- `I^θ_α = 𝔼 ∫_0^t |(1/𝒮_{𝒜_N,α}) Σ_{r̃ ∈ 𝒜_N ∩ Γ_α} θ(s, r, r̃, X̄^r_{s−}, X̄^{r̃}_{(s−τ)⁻:s⁻}, ω')
 − 𝔼̃ ∫_{Γ_α} θ(s, r, r', X̄^r_{s−}, X̃^{r'}_{(s−τ)⁻:s⁻}, ω') 𝓡(dr')|² ds` (p. 18), for the neuron
`r = pos i`, in `[0, ∞]`. -/
noncomputable def Iθ {d m n k P : ℕ} {U Ω' Ω ΩX : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (C : Coeffs d m n k P U Ω') (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ)
    (S : ℕ → Fin P → ℝ) (Pr : Measure Ω) (Xbar : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d) (ω' : Ω') (N : ℕ)
    (α : Fin P) (i : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t,
    ‖netθ G C pos 𝒜 S Xbar N α s.toNNReal (pos i) (lft (Xbar i) s ω) ω ω' -
      meanθ G C PrX X α s.toNNReal (pos i) (lft (Xbar i) s ω) ω'‖ₑ ^ 2 ∂volume ∂Pr

/-- `I^β_α`, as `I^θ_α` with `β` and the Hilbert–Schmidt norm (p. 18). -/
noncomputable def Iβ {d m n k P : ℕ} {U Ω' Ω ΩX : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (C : Coeffs d m n k P U Ω') (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ)
    (S : ℕ → Fin P → ℝ) (Pr : Measure Ω) (Xbar : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d) (ω' : Ω') (N : ℕ)
    (α : Fin P) (i : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t,
    ENNReal.ofReal (frob2 (netβ G C pos 𝒜 S Xbar N α s.toNNReal (pos i) (lft (Xbar i) s ω) ω ω' -
      meanβ G C PrX X α s.toNNReal (pos i) (lft (Xbar i) s ω) ω')) ∂volume ∂Pr

/-- `I^η_α = 𝔼 ∫_0^t ∫_U |(1/𝒮_{𝒜_N,α}) Σ_{r̃} η(s, r, r̃, X̄^r_{s−}, X̄^{r̃}_{(s−τ)⁻:s⁻}, ω', ξ)
 − 𝔼̃ ∫_{Γ_α} η(s, r, r', X̄^r_{s−}, X̃^{r'}_{(s−τ)⁻:s⁻}, ω', ξ) 𝓡(dr')|² ν(dξ) ds` (pp. 18, 20). -/
noncomputable def Iη {d m n k P : ℕ} {U Ω' Ω ΩX : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    [MeasurableSpace ΩX] (G : Geometry k P) (ν : Measure U) (C : Coeffs d m n k P U Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Pr : Measure Ω)
    (Xbar : ℕ → ℝ → Ω → EthierKurtz.SDEState d) (PrX : Measure ΩX)
    (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d) (ω' : Ω') (N : ℕ) (α : Fin P) (i : ℕ)
    (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t, ∫⁻ ξ,
    ‖netη G C pos 𝒜 S Xbar N α s.toNNReal (pos i) (lft (Xbar i) s ω) ω ω' ξ -
      meanη G C PrX X α s.toNNReal (pos i) (lft (Xbar i) s ω) ω' ξ‖ₑ ^ 2 ∂ν ∂volume ∂Pr

end NeuroMV.Chaos



-- Prove2me | Definitions.Def_Peng1990_SMP_Stochastic
-- name    : Peng1990_SMP_Stochastic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:29:46.382653+00:00
-- url     : https://prove2.me/theorems/ad3f2b0f-c3f4-4ddb-a2c9-f3490e9536bb
-- title:
--   Standard Wiener process, its natural filtration, $L^2_{\mathcal F}$, the Itô integral, Itô processes, SDE and BSDE solutions
-- statement:
--   This file fixes the stochastic calculus in which the whole mission is stated. Time runs over $[0,\infty)$; only $[0,T]$ matters.
--
--   1. **Standard Wiener process.** $B=(B^1,\dots,B^d)$ is an $\mathbb R^d$-valued process on a probability space $(\Omega,\mathcal F,P)$ such that every $B(t)$ is measurable, every coordinate $B^j$ is a real standard Brownian motion ($B^j(0)=0$ a.s., Gaussian finite-dimensional laws with covariance $\min(s,t)$, a.s. continuous paths), and the coordinate processes are mutually independent.
--
--   2. **Filtration.** $\mathcal F^t=\sigma\{B(s);\,0\le s\le t\}$, the natural filtration of $B$ (not completed).
--
--   3. **$L^2_{\mathcal F}(0,T;E)$.** For a finite-dimensional normed space $E$, the space of progressively measurable $E$-valued processes $\varphi$ with
--   $$E\int_0^T|\varphi(t)|^2\,dt<\infty .$$
--
--   4. **Itô integral.** For $H\in L^2_{\mathcal F}(0,T;\mathbb R)$ and a real process $W$ (a coordinate of $B$), a process $J$ is an Itô integral $J(t)=\int_0^t H\,dW$, $0\le t\le T$, when $J$ is adapted and there are simple adapted integrands $H_m=\sum_i\xi_i\mathbf 1_{(t_i,t_{i+1}]}$ (a partition $0=t_0\le\dots\le t_r=T$, each $\xi_i$ square integrable and $\mathcal F^{t_i}$-measurable) with
--   $$E\int_0^T|H_m-H|^2\,ds\to0,\qquad E\Big|\sum_i\xi_i\big(W(t_{i+1}\wedge t)-W(t_i\wedge t)\big)-J(t)\Big|^2\to0\quad(0\le t\le T).$$
--
--   5. **Itô process / SDE solution.** A process $x$ with values in $\mathbb R^\iota$ ($\iota$ finite) solves $dx=b(s,x)\,ds+\sum_j c_j(s,x)\,dB^j$, $x(0)=\xi$, on $[0,T]$ when $x$ is progressive, $\sup_{0\le t\le T}E|x(t)|^2<\infty$, and for every $t\in[0,T]$, almost surely,
--   $$x(t)=\xi+\int_0^t b(s,x(s))\,ds+\sum_{j=1}^d\int_0^t c_j(s,x(s))\,dB^j(s),$$
--   with the stochastic integrals in the sense of item 4 (componentwise) and the $ds$-integrand integrable on $[0,t]$. The coefficients may depend on $(s,\omega)$, e.g. through a control.
--
--   6. **BSDE solution.** $(p,K_1,\dots,K_d)$ solves $-dp=F(t,p,K)\,dt-\sum_jK_j\,dB^j$, $p(T)=\xi$, when $p$ and all $K_j$ lie in $L^2_{\mathcal F}(0,T)$ and for every $t\in[0,T]$, almost surely,
--   $$p(t)=\xi+\int_t^T F(s,p(s),K(s))\,ds-\sum_{j=1}^d\int_t^T K_j(s)\,dB^j(s).$$
--
--   Matrix-valued processes are read entrywise.
--
--   These objects are general (no control problem enters) and are meant to be reused by later missions on controlled diffusions and backward SDEs.
--
--   **Formalization Note** Time is `ℝ≥0`; time integrals are over `Set.Icc (0:ℝ) T` of `s.toNNReal`. Square integrability is an `ℝ≥0∞` lower integral, so no junk value can occur. "Adapted" for processes that are integrated in $dt$ is read as progressively measurable (`IsStronglyProgressive`). The paper writes "an $R^n$-valued standard Wiener process" on p. 967; since $\sigma(x,v)\in\mathcal L(R^d,R^n)$, $B$ is $\mathbb R^d$-valued and that is what is formalized. The Itô integral follows the $L^2$ construction of Ikeda–Watanabe, the reference the paper cites.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 967, Section 2 (Wiener process, filtration $\mathcal F^t=\sigma\{B(s);0\le s\le t\}$); p. 972 (definition of $L^2_{\mathcal F}(0,T;R^n)$); the Itô integral and SDE/BSDE solution notions are those of Ikeda–Watanabe [9] and Bensoussan [2], [3] as used on pp. 968–975

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A standard `d`-dimensional Wiener process `B = (B¹, …, Bᵈ)` on `(Ω, 𝓕, P)`, time `ℝ≥0`:
each `B t` is measurable, each coordinate is a real Brownian motion (Mathlib's
`IsBrownianReal`: Brownian finite-dimensional laws, `B 0 = 0` a.s., a.s. continuous paths),
and the `d` coordinate processes are mutually independent. -/
structure IsStdBrownian {d : ℕ} (P : Measure Ω) (B : ℝ≥0 → Ω → Fin d → ℝ) : Prop where
  meas : ∀ t, Measurable (B t)
  brownian : ∀ j : Fin d, IsBrownianReal (fun t ω => B t ω j) P
  indep : iIndepFun (fun (j : Fin d) (ω : Ω) (t : ℝ≥0) => B t ω j) P

/-- The natural (uncompleted) filtration `𝓕ᵗ = σ{B(s); 0 ≤ s ≤ t}` of the Wiener process. -/
noncomputable def brownianFiltration {d : ℕ} {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ}
    (hB : IsStdBrownian P B) : Filtration ℝ≥0 mΩ :=
  Filtration.natural B (fun t => (hB.meas t).stronglyMeasurable)

/-- `L²_𝓕(0, T; E)`: progressively measurable processes `φ` with `E ∫₀ᵀ |φ(t)|² dt < ∞`
(computed as a lower Lebesgue integral in `ℝ≥0∞`, time integral over `[0, T] ⊂ ℝ`). -/
def L2F {E : Type*} [NormedAddCommGroup E] (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (T : ℝ≥0) (φ : ℝ≥0 → Ω → E) : Prop :=
  IsStronglyProgressive 𝓕 φ ∧
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖φ s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P < ⊤

/-- A simple adapted integrand on `[0, T]`: a partition `0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_r = T` and
square-integrable random variables `ξᵢ`, each `𝓕^{tᵢ}`-measurable; the process is
`Σᵢ ξᵢ 1_{(tᵢ, tᵢ₊₁]}`. -/
structure SimpleIntegrand (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) where
  r : ℕ
  t : Fin (r + 1) → ℝ≥0
  mono : Monotone t
  start : t 0 = 0
  finish : t (Fin.last r) = T
  ξ : Fin r → Ω → ℝ
  meas : ∀ i, StronglyMeasurable[𝓕 (t i.castSucc)] (ξ i)
  sq : ∀ i, ∫⁻ ω, ‖ξ i ω‖ₑ ^ 2 ∂P < ⊤

namespace SimpleIntegrand

variable {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {T : ℝ≥0}

/-- The value `Σᵢ ξᵢ(ω) 1_{(tᵢ, tᵢ₊₁]}(s)` of a simple integrand. -/
noncomputable def eval (H : SimpleIntegrand 𝓕 P T) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin H.r, if H.t i.castSucc < s ∧ s ≤ H.t i.succ then H.ξ i ω else 0

/-- The elementary stochastic integral `∫₀ᵘ H dW = Σᵢ ξᵢ (W(tᵢ₊₁ ∧ u) − W(tᵢ ∧ u))`. -/
noncomputable def integral (H : SimpleIntegrand 𝓕 P T) (W : ℝ≥0 → Ω → ℝ) (u : ℝ≥0)
    (ω : Ω) : ℝ :=
  ∑ i : Fin H.r, H.ξ i ω * (W (min (H.t i.succ) u) ω - W (min (H.t i.castSucc) u) ω)

end SimpleIntegrand

/-- `J` is an Itô integral process `J(t) = ∫₀ᵗ H dW`, `0 ≤ t ≤ T` (the L² construction of
Ikeda–Watanabe): `H ∈ L²_𝓕(0, T; ℝ)`, `J` is adapted, and some sequence of simple adapted
integrands `Hₘ` satisfies `E ∫₀ᵀ |Hₘ − H|² ds → 0` and, for every `t ∈ [0, T]`,
`E |∫₀ᵗ Hₘ dW − J(t)|² → 0`. -/
def IsItoIntegral (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (H : ℝ≥0 → Ω → ℝ) (J : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F 𝓕 P T H ∧ StronglyAdapted 𝓕 J ∧
    ∃ Hs : ℕ → SimpleIntegrand 𝓕 P T,
      Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ‖(Hs m).eval s.toNNReal ω - H s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P) atTop (𝓝 0) ∧
      ∀ t ≤ T, Tendsto (fun m => ∫⁻ ω, ‖(Hs m).integral W t ω - J t ω‖ₑ ^ 2 ∂P)
          atTop (𝓝 0)

/-- `x` is an Itô process on `[0, T]` with initial value `ξ`, drift process `a` and diffusion
processes `γ = (γ₁, …, γ_d)` driven by `B = (B¹, …, Bᵈ)`:
`x` is progressive with `sup_{t ≤ T} E|x(t)|² < ∞`, and for every `t ∈ [0, T]`, almost surely,
`x(t) = ξ + ∫₀ᵗ a(s) ds + Σⱼ ∫₀ᵗ γⱼ(s) dBʲ(s)` (componentwise; the stochastic integrals are
Itô integrals in the sense of `IsItoIntegral`, and `a` is Lebesgue integrable on `[0, t]`). -/
def IsItoProcess {ι : Type*} [Fintype ι] {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (T : ℝ≥0) (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : ι → ℝ) (a : ℝ≥0 → Ω → ι → ℝ)
    (γ : Fin d → ℝ≥0 → Ω → ι → ℝ) (x : ℝ≥0 → Ω → ι → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 x ∧
    (⨆ t ≤ T, ∫⁻ ω, ‖x t ω‖ₑ ^ 2 ∂P) < ⊤ ∧
    ∃ J : ι → Fin d → ℝ≥0 → Ω → ℝ,
      (∀ i j, IsItoIntegral 𝓕 P T (fun s ω => B s ω j) (fun s ω => γ j s ω i) (J i j)) ∧
      ∀ t ≤ T, ∀ᵐ ω ∂P,
        MeasureTheory.IntegrableOn (fun s : ℝ => a s.toNNReal ω) (Set.Icc 0 (t : ℝ)) ∧
        ∀ i, x t ω i = ξ i + (∫ s in Set.Icc (0 : ℝ) t, a s.toNNReal ω) i + ∑ j, J i j t ω

/-- `x` solves the SDE `dx = b(s, x) ds + Σⱼ cⱼ(s, x) dBʲ`, `x(0) = ξ`, on `[0, T]`; the
coefficients may depend on `(s, ω)` (e.g. through a control). -/
def SolvesSDE {ι : Type*} [Fintype ι] {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (T : ℝ≥0) (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : ι → ℝ)
    (b : ℝ≥0 → Ω → (ι → ℝ) → (ι → ℝ)) (c : Fin d → ℝ≥0 → Ω → (ι → ℝ) → (ι → ℝ))
    (x : ℝ≥0 → Ω → ι → ℝ) : Prop :=
  IsItoProcess 𝓕 P T B ξ (fun s ω => b s ω (x s ω)) (fun j s ω => c j s ω (x s ω)) x

/-- `(p, K)` solves the backward SDE `−dp(t) = F(t, p(t), K(t)) dt − Σⱼ Kⱼ(t) dBʲ(t)`,
`p(T) = ξ`, on `[0, T]`: `p` and every `Kⱼ` lie in `L²_𝓕(0, T)` (in particular they are
progressive for `𝓕`), and for every `t ∈ [0, T]`, almost surely,
`p(t) = ξ + ∫ₜᵀ F(s, p(s), K(s)) ds − Σⱼ ∫ₜᵀ Kⱼ(s) dBʲ(s)`, where `∫ₜᵀ Kⱼ dBʲ = Jⱼ(T) − Jⱼ(t)`
for Itô integral processes `Jⱼ` of `Kⱼ` against `Bʲ`. -/
def SolvesBSDE {ι : Type*} [Fintype ι] {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (T : ℝ≥0) (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ι → ℝ)
    (F : ℝ≥0 → Ω → (ι → ℝ) → (Fin d → ι → ℝ) → (ι → ℝ))
    (p : ℝ≥0 → Ω → ι → ℝ) (K : Fin d → ℝ≥0 → Ω → ι → ℝ) : Prop :=
  L2F 𝓕 P T p ∧ (∀ j, L2F 𝓕 P T (K j)) ∧
    ∃ J : ι → Fin d → ℝ≥0 → Ω → ℝ,
      (∀ i j, IsItoIntegral 𝓕 P T (fun s ω => B s ω j) (fun s ω => K j s ω i) (J i j)) ∧
      ∀ t ≤ T, ∀ᵐ ω ∂P,
        MeasureTheory.IntegrableOn
          (fun s : ℝ => F s.toNNReal ω (p s.toNNReal ω) (fun j => K j s.toNNReal ω))
          (Set.Icc (t : ℝ) T) ∧
        ∀ i, p t ω i = ξ ω i
          + (∫ s in Set.Icc (t : ℝ) T,
              F s.toNNReal ω (p s.toNNReal ω) (fun j => K j s.toNNReal ω)) i
          - ∑ j, (J i j T ω - J i j t ω)

/-- The entries of an `n × n` matrix as a vector indexed by `Fin n × Fin n`; used to read
matrix-valued Itô processes and BSDEs entrywise. -/
def matEntries {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℝ :=
  fun q => M q.1 q.2

/-- The inverse of `matEntries`. -/
def entriesMat {n : ℕ} (z : Fin n × Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => z (i, j)

end Peng1990.SMP



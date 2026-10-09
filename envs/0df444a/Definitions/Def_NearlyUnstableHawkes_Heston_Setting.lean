-- Prove2me | Definitions.Def_NearlyUnstableHawkes_Heston_Setting
-- name    : NearlyUnstableHawkes_Heston_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:24.652137+00:00
-- url     : https://prove2.me/theorems/554c77ef-e1e6-4ae5-88d3-ed0143fa631a
-- title:
--   §3.2, p. 13 — the bidimensional Hawkes process (N^{T+}, N^{T−}); (6) P^T; §4.4 C^T, X^T, M̄^T, (B^i)^T, brackets, R^T; Skorohod convergence in law and u.c.p. on [0,1]; the limit SDEs
-- statement:
--   This file fixes the probabilistic objects of §3.2 and §4.4 of Jaisson and Rosenbaum.
--
--   1. **The bidimensional Hawkes process** (p. 13). For an observation interval $[0,T]$, $(N^{T+},N^{T-})$ are two counting processes with $N^{T\pm}_0=0$, nondecreasing, right-continuous, with unit jumps and without common jumps, whose intensities with respect to the joint natural filtration $\mathcal F_t=\sigma(N^{T+}_s,N^{T-}_s:s\le t)$ are
--   $$\begin{pmatrix}\lambda^{T+}_t\\ \lambda^{T-}_t\end{pmatrix}=\begin{pmatrix}\mu\\ \mu\end{pmatrix}+\int_0^t\begin{pmatrix}\phi^T_1(t-s)&\phi^T_2(t-s)\\ \phi^T_2(t-s)&\phi^T_1(t-s)\end{pmatrix}\begin{pmatrix}dN^{T+}_s\\ dN^{T-}_s\end{pmatrix},$$
--   in the sense of p. 5: for all $0\le a<b\le T$ and $A\in\mathcal F_a$, $\mathbb E[(N^{T\pm}_b-N^{T\pm}_a)\mathbf 1_A]=\mathbb E[\int_a^b\lambda^{T\pm}_s\mathbf 1_A\,ds]$.
--   2. **Rescaled processes.** The price $P^T_t=\frac1T(N^{T+}_{Tt}-N^{T-}_{Tt})$ (display (6)); $C^T_t=(\lambda^{T+}_{tT}+\lambda^{T-}_{tT})/T$; $X^T_s=(\lambda^{T+}_{sT}-\lambda^{T-}_{sT})/T$; the martingales $M^{T\pm}_s=N^{T\pm}_s-\int_0^s\lambda^{T\pm}_u\,du$ and $\overline M^{T\pm}_t=M^{T\pm}_{Tt}/T$.
--   3. **Integrals against $dM$.** For a function $f$, $\int_0^t f(u)\,dM^{T\pm}_u=\sum_{\text{jumps }u\in(0,t]\text{ of }N^{T\pm}} f(u)-\int_0^t f(u)\lambda^{T\pm}_u\,du$. With it,
--   $$(B^1)^T_t=\int_0^{tT}\frac{dM^{T+}_s+dM^{T-}_s}{\sqrt{T(\lambda^{T+}_s+\lambda^{T-}_s)}},\qquad (B^2)^T_t=\int_0^{tT}\frac{dM^{T+}_s-dM^{T-}_s}{\sqrt{T(\lambda^{T+}_s+\lambda^{T-}_s)}},$$
--   their quadratic co-variations $[(B^i)^T,(B^j)^T]_t$ (sums over jump times of the products of the jumps), and $R^T_t=\int_0^t\int_{T(t-u)}^{\infty}\psi^T(s)\,ds\,d(\overline M^{T+}_u-\overline M^{T-}_u)$.
--   4. **Convergence notions on $[0,1]$.** Skorohod ($J_1$) convergence of cadlag paths on $[0,1]$; convergence in law for the Skorohod topology, in Skorohod-representation form; and uniform convergence in probability (u.c.p.) to $0$ on $[0,1]$.
--   5. **The limit equations.** The coefficients of the Heston-type system of Theorem 3.1 in the state $(C,P)$, driven by $(B^1,B^2)$: drift $\big((\tfrac{2\mu}{\lambda}-C)\tfrac{\lambda}{m},0\big)$ and diffusion $\mathrm{diag}\big(\tfrac1m\sqrt C,\tfrac{1}{1-\|\phi\|_1}\sqrt C\big)$; and those of the pair $(C,B^2)$ of Lemma 4.15, driven by $(W,B^2)$: the same drift and diffusion $\mathrm{diag}(\tfrac1m\sqrt C,1)$.
--
--   **Formalization Note** Time is real, with every condition imposed for $t\ge0$; counting processes are $\mathbb N$-valued. The joint filtration of the bidimensional process is the natural one, which p. 13 delegates to the construction of [5]. The intensity identity is written with lower Lebesgue integrals in $[0,\infty]$, so no integrability is assumed. The intensity used for $C^T$, $X^T$ and $dM$ includes jumps at $s\le t$ (cadlag version); inside integrands against $dN$ or $dM$ (in $(B^i)^T$ and the brackets) the predictable version, over jumps $s<t$, is used, as a stochastic integral of a predictable integrand requires. Integrals against $dM$ are pathwise Stieltjes integrals. Index $0$ of `Fin 2` is $B^1$ and index $1$ is $B^2$. The quadratic co-variation is defined as the sum of products of jumps, which for $N^{T\pm}$ with unit, non-simultaneous jumps equals the paper's $\int_0^{tT}(dN^{T+}_s\pm dN^{T-}_s)/(T(\lambda^{T+}_s+\lambda^{T-}_s))$ (p. 28). Paths on $[0,1]$ are functions on $\mathbb R$ of which only $[0,1]$ matters; a time change is continuous and strictly increasing on $[0,1]$ with $0\mapsto0$, $1\mapsto1$. Convergence in law is stated in coupling form (a probability space carrying copies of the laws of the paths that converge almost surely in $D[0,1]$), equivalent to weak convergence of the laws on the Polish space $D[0,1]$; laws are taken on the product σ-algebra of $[0,1]\to E$, whose trace on $D[0,1]$ is the Borel σ-algebra. Joint convergence of a pair uses one time change for both coordinates. $\sqrt{\cdot}$ is `Real.sqrt`, which is $0$ on negative arguments; the limit $C$ is nonnegative. The drift and diffusion of Lemma 4.15's pair coincide in their first coordinate with the Heston-type system's.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 5, §2.1; p. 13, §3.2; p. 14, (6) and Theorem 3.1; pp. 26–28, §4.4; p. 30, Lemma 4.15

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-! ### Paths, jumps and pathwise sums over jumps -/

/-- The real-valued path `t ↦ N_t(ω)` of an `ℕ`-valued process. -/
def path {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℝ → ℝ :=
  fun t => (N t ω : ℝ)

/-- The jump `Δx(t) = x(t) − x(t−)` of a real path, with `x(t−)` Mathlib's `Function.leftLim`. -/
noncomputable def jump (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  x t - Function.leftLim x t

/-- `Σ_{s ∈ S, Δx(s) ≠ 0} Δx(s) g(s)`: the Stieltjes integral `∫_S g dx` of a pure-jump path `x`.
For a counting path and a bounded `S` the index set is finite. -/
noncomputable def jumpSumOn (x : ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) : ℝ :=
  ∑ᶠ (s : ℝ) (_ : s ∈ S ∧ jump x s ≠ 0), jump x s * g s

/-- The intensity of one component of the bidimensional Hawkes process (p. 13), cadlag version:
`μ + ∫_{(0,t]} φ_self(t − s) dN^{self}_s + ∫_{(0,t]} φ_cross(t − s) dN^{other}_s`. -/
noncomputable def intensity (μ : ℝ) (φself φcross : ℝ → ℝ) (nself nother : ℝ → ℝ) (t : ℝ) : ℝ :=
  μ + jumpSumOn nself (fun s => φself (t - s)) (Set.Ioc 0 t) +
    jumpSumOn nother (fun s => φcross (t - s)) (Set.Ioc 0 t)

/-- The predictable (left-limit) version of `intensity`: jumps at `s < t` only. Used inside
integrands against `dN` and `dM`. -/
noncomputable def intensityPred (μ : ℝ) (φself φcross : ℝ → ℝ) (nself nother : ℝ → ℝ) (t : ℝ) :
    ℝ :=
  μ + jumpSumOn nself (fun s => φself (t - s)) (Set.Ioo 0 t) +
    jumpSumOn nother (fun s => φcross (t - s)) (Set.Ioo 0 t)

/-! ### The bidimensional Hawkes process of §3.2 -/

/-- A simple counting process on `[0, ∞)`: measurable, `N_0 = 0`, nondecreasing, right-continuous,
with jumps of size at most one. -/
structure IsSimpleCounting {Ω : Type*} [MeasurableSpace Ω] (N : ℝ → Ω → ℕ) : Prop where
  meas : ∀ t, Measurable (N t)
  zero : ∀ ω, N 0 ω = 0
  mono : ∀ ω, MonotoneOn (fun t => N t ω) (Set.Ici 0)
  rcont : ∀ ω t, 0 ≤ t → ContinuousWithinAt (path N ω) (Set.Ici t) t
  unit_jumps : ∀ ω t, 0 < t → jump (path N ω) t ≤ 1

/-- The joint natural filtration `F_t = σ(N⁺_s, N⁻_s : 0 ≤ s ≤ t)`. -/
abbrev natFiltration2 {Ω : Type*} (Np Nm : ℝ → Ω → ℕ) (t : ℝ) : MeasurableSpace Ω :=
  ⨆ s ∈ Set.Icc (0 : ℝ) t,
    (MeasurableSpace.comap (Np s) inferInstance ⊔ MeasurableSpace.comap (Nm s) inferInstance)

/-- The **bidimensional Hawkes process** `(N^{T+}, N^{T−})` on `[0, T]` (§3.2, p. 13, following
the one-dimensional definition of p. 5): two simple counting processes without common jumps, with
intensities
`λ^{T+}_t = μ + ∫_0^t φ^T_1(t − s) dN^{T+}_s + ∫_0^t φ^T_2(t − s) dN^{T−}_s` and
`λ^{T−}_t = μ + ∫_0^t φ^T_2(t − s) dN^{T+}_s + ∫_0^t φ^T_1(t − s) dN^{T−}_s`
relative to the joint natural filtration: for `0 ≤ a < b ≤ T` and `A ∈ F_a`,
`E[(N^±_b − N^±_a) 1_A] = E[∫_a^b λ^±_s 1_A ds]` (in `[0, ∞]`). -/
structure IsHawkes2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℝ) (φ1T φ2T : ℝ → ℝ)
    (Tend : ℝ) (Np Nm : ℝ → Ω → ℕ) : Prop where
  countPlus : IsSimpleCounting Np
  countMinus : IsSimpleCounting Nm
  no_common_jumps : ∀ ω t, 0 < t → jump (path Np ω) t = 0 ∨ jump (path Nm ω) t = 0
  intensityPlus_id : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ Tend → ∀ A : Set Ω,
    MeasurableSet[natFiltration2 Np Nm a] A →
      ∫⁻ ω in A, ((Np b ω - Np a ω : ℕ) : ℝ≥0∞) ∂P =
        ∫⁻ ω in A, (∫⁻ s in Set.Ioc a b,
          ENNReal.ofReal (intensity μ φ1T φ2T (path Np ω) (path Nm ω) s)) ∂P
  intensityMinus_id : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ Tend → ∀ A : Set Ω,
    MeasurableSet[natFiltration2 Np Nm a] A →
      ∫⁻ ω in A, ((Nm b ω - Nm a ω : ℕ) : ℝ≥0∞) ∂P =
        ∫⁻ ω in A, (∫⁻ s in Set.Ioc a b,
          ENNReal.ofReal (intensity μ φ1T φ2T (path Nm ω) (path Np ω) s)) ∂P

section Processes

variable {Ω : Type*}

/-- `λ^{T+}_t` with `φ^T_i = a φ_i` (cadlag version). -/
noncomputable def lamPlus (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  intensity μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) (path Np ω) (path Nm ω) t

/-- `λ^{T−}_t` with `φ^T_i = a φ_i` (cadlag version). -/
noncomputable def lamMinus (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  intensity μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) (path Nm ω) (path Np ω) t

/-- `λ^{T+}_{t−}`, the predictable version of `λ^{T+}_t`. -/
noncomputable def lamPlusPred (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) :
    ℝ :=
  intensityPred μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) (path Np ω) (path Nm ω) t

/-- `λ^{T−}_{t−}`, the predictable version of `λ^{T−}_t`. -/
noncomputable def lamMinusPred (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) :
    ℝ :=
  intensityPred μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) (path Nm ω) (path Np ω) t

/-- The pathwise integral `∫_0^t f(u) dM_u` against `M = N − ∫_0^· λ_s ds`:
`Σ_{jumps u ∈ (0,t]} ΔN_u f(u) − ∫_0^t f(u) λ_u du`. -/
noncomputable def intDM (f : ℝ → ℝ) (n lam : ℝ → ℝ) (t : ℝ) : ℝ :=
  jumpSumOn n f (Set.Ioc 0 t) - ∫ u in (0 : ℝ)..t, f u * lam u

/-- `∫_0^t f(u) (dM^{T+}_u − dM^{T−}_u)`, pathwise. -/
noncomputable def intDiffM (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (f : ℝ → ℝ) (t : ℝ)
    (ω : Ω) : ℝ :=
  intDM f (path Np ω) (fun s => lamPlus μ a φ₁ φ₂ Np Nm s ω) t -
    intDM f (path Nm ω) (fun s => lamMinus μ a φ₁ φ₂ Np Nm s ω) t

/-- `M^{T+}_t = N^{T+}_t − ∫_0^t λ^{T+}_s ds` (p. 27). -/
noncomputable def MPlus (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  path Np ω t - ∫ s in (0 : ℝ)..t, lamPlus μ a φ₁ φ₂ Np Nm s ω

/-- `M^{T−}_t = N^{T−}_t − ∫_0^t λ^{T−}_s ds` (p. 27). -/
noncomputable def MMinus (μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  path Nm ω t - ∫ s in (0 : ℝ)..t, lamMinus μ a φ₁ φ₂ Np Nm s ω

/-- `M̄^{T+}_t − M̄^{T−}_t = (M^{T+}_{Tt} − M^{T−}_{Tt}) / T` (p. 27). -/
noncomputable def MbarDiff (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (MPlus μ a φ₁ φ₂ Np Nm (T * t) ω - MMinus μ a φ₁ φ₂ Np Nm (T * t) ω) / T

/-- `∫_0^t g(u) d(M̄^{T+}_u − M̄^{T−}_u) = (1/T) ∫_0^{Tt} g(s/T) (dM^{T+}_s − dM^{T−}_s)`. -/
noncomputable def intDiffMbar (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (g : ℝ → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  intDiffM μ a φ₁ φ₂ Np Nm (fun s => g (s / T)) (T * t) ω / T

/-- The renormalized price `P^T_t = (N^{T+}_{Tt} − N^{T−}_{Tt}) / T`, display (6), p. 14. -/
noncomputable def priceProc (T : ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (path Np ω (T * t) - path Nm ω (T * t)) / T

/-- `C^T_t = (λ^{T+}_{tT} + λ^{T−}_{tT}) / T` (p. 26). -/
noncomputable def volProc (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (lamPlus μ a φ₁ φ₂ Np Nm (t * T) ω + lamMinus μ a φ₁ φ₂ Np Nm (t * T) ω) / T

/-- `X^T_s = (λ^{T+}_{sT} − λ^{T−}_{sT}) / T` (p. 27). -/
noncomputable def imbalanceProc (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (s : ℝ) (ω : Ω) :
    ℝ :=
  (lamPlus μ a φ₁ φ₂ Np Nm (s * T) ω - lamMinus μ a φ₁ φ₂ Np Nm (s * T) ω) / T

/-- The sign of `dM^{T−}` in `(B^{i+1})^T`: `+1` for `i = 0` (`B¹`), `−1` for `i = 1` (`B²`). -/
def bSign (i : Fin 2) : ℝ :=
  if i = 0 then 1 else -1

/-- The integrand `1 / √(T(λ^{T+}_{s−} + λ^{T−}_{s−}))` of `(B¹)^T, (B²)^T`, with the predictable
intensities. -/
noncomputable def bIntegrand (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (s : ℝ) (ω : Ω) :
    ℝ :=
  1 / Real.sqrt (T * (lamPlusPred μ a φ₁ φ₂ Np Nm s ω + lamMinusPred μ a φ₁ φ₂ Np Nm s ω))

/-- `(B¹)^T_t = ∫_0^{tT} (dM^{T+}_s + dM^{T−}_s) / √(T(λ^{T+}_s + λ^{T−}_s))` (`i = 0`) and
`(B²)^T_t = ∫_0^{tT} (dM^{T+}_s − dM^{T−}_s) / √(T(λ^{T+}_s + λ^{T−}_s))` (`i = 1`), p. 27,
pathwise, with the predictable intensities in the integrand. -/
noncomputable def brownianT (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (i : Fin 2) (t : ℝ)
    (ω : Ω) : ℝ :=
  intDM (fun s => bIntegrand T μ a φ₁ φ₂ Np Nm s ω) (path Np ω)
      (fun s => lamPlus μ a φ₁ φ₂ Np Nm s ω) (t * T) +
    bSign i * intDM (fun s => bIntegrand T μ a φ₁ φ₂ Np Nm s ω) (path Nm ω)
      (fun s => lamMinus μ a φ₁ φ₂ Np Nm s ω) (t * T)

/-- The quadratic co-variation `[(B^{i+1})^T, (B^{j+1})^T]_t` of the pure-jump processes of
`brownianT`: the sum over the jump times `s ∈ (0, tT]` of `N^{T+}` or `N^{T−}` of the product of
the jumps,
`(ΔN⁺_s + ε_i ΔN⁻_s)(ΔN⁺_s + ε_j ΔN⁻_s) / (T(λ^{T+}_{s−} + λ^{T−}_{s−}))`, `ε_0 = 1`, `ε_1 = −1`. -/
noncomputable def bracketT (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (i j : Fin 2) (t : ℝ)
    (ω : Ω) : ℝ :=
  ∑ᶠ (s : ℝ) (_ : s ∈ Set.Ioc 0 (t * T) ∧ (jump (path Np ω) s ≠ 0 ∨ jump (path Nm ω) s ≠ 0)),
    (jump (path Np ω) s + bSign i * jump (path Nm ω) s) *
      (jump (path Np ω) s + bSign j * jump (path Nm ω) s) /
      (T * (lamPlusPred μ a φ₁ φ₂ Np Nm s ω + lamMinusPred μ a φ₁ φ₂ Np Nm s ω))

/-- `R^T_t = ∫_0^t ∫_{T(t−u)}^{+∞} ψ^T(s) ds d(M̄^{T+}_u − M̄^{T−}_u)` (Lemma 4.16, p. 30), with the
signed resolvent `ψ^T` of `φ^T = a φ₁ − a φ₂`. -/
noncomputable def remainderR (T μ a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (Np Nm : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) :
    ℝ :=
  intDiffMbar T μ a φ₁ φ₂ Np Nm
    (fun u => ∫ s in Set.Ioi (T * (t - u)), psiSigned a φ₁ φ₂ s) t ω

end Processes

/-! ### Convergence notions on `[0, 1]` -/

/-- A cadlag path on `[0, 1]`: right-continuous at every `t ∈ [0, 1)`, with a left limit at every
`t ∈ (0, 1]`. Values outside `[0, 1]` are irrelevant. -/
def IsCadlag01 {E : Type*} [TopologicalSpace E] (x : ℝ → E) : Prop :=
  (∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt x (Set.Ici t) t) ∧
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∃ y : E, Tendsto x (𝓝[<] t) (𝓝 y)

/-- **Skorohod (J₁) convergence on `D[0, 1]`**: all paths are cadlag on `[0, 1]` and there are time
changes `λ_n` of `[0, 1]` with `sup_{t ∈ [0,1]} ‖x_n(λ_n t) − x(t)‖ → 0` and
`sup_{t ∈ [0,1]} |λ_n t − t| → 0`. For a product-valued path this uses one time change for all
components. -/
def SkorohodTendsto01 {E : Type*} [MetricSpace E] (xs : ℕ → ℝ → E) (x : ℝ → E) : Prop :=
  (∀ n, IsCadlag01 (xs n)) ∧ IsCadlag01 x ∧
    ∃ l : ℕ → ℝ → ℝ, (∀ n, NearlyUnstableHawkes.CIR.IsTimeChange01 (l n)) ∧
      TendstoUniformlyOn (fun n t => xs n (l n t)) x atTop (Set.Icc 0 1) ∧
      TendstoUniformlyOn l id atTop (Set.Icc 0 1)

/-- Extend a path on `[0, 1]` to `ℝ` by clamping time to `[0, 1]`. -/
noncomputable def extend01 {E : Type*} (w : Set.Icc (0 : ℝ) 1 → E) : ℝ → E :=
  fun t => w (Set.projIcc 0 1 zero_le_one t)

/-- **Convergence in law for the Skorohod topology on `[0, 1]`**, in coupling
(Skorohod-representation) form: there is a probability space carrying path-valued random variables
`W_n`, `W'` with `W_n` distributed as the path `(V_n(t))_{t ∈ [0,1]}` under `P_n`, `W'` distributed
as the path `(V'(t))_{t ∈ [0,1]}` under `P'`, and `W_n(ω) → W'(ω)` in `D[0, 1]` for almost every
`ω`. Laws are taken on the product σ-algebra of `[0, 1] → E`. -/
def ConvInLawSkorohod01 {E : Type*} [MetricSpace E] [MeasurableSpace E]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (V : ∀ n, ℝ → Ω n → E) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (V' : ℝ → Ω' → E) : Prop :=
  ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
      (W : ℕ → Ω'' → Set.Icc (0 : ℝ) 1 → E) (W' : Ω'' → Set.Icc (0 : ℝ) 1 → E),
    IsProbabilityMeasure P'' ∧
    (∀ n, IdentDistrib (W n) (fun ω (t : Set.Icc (0 : ℝ) 1) => V n t ω) P'' (P n)) ∧
    IdentDistrib W' (fun ω (t : Set.Icc (0 : ℝ) 1) => V' t ω) P'' P' ∧
    ∀ᵐ ω ∂P'', SkorohodTendsto01 (fun n => extend01 (W n ω)) (extend01 (W' ω))

/-- **Uniform convergence in probability on `[0, 1]`** (u.c.p.) to `0`, for processes on varying
probability spaces: for every `ε > 0`, `P_n(sup_{t ∈ [0,1]} |Y_n(t)| > ε) → 0` (the probability of
the event `∃ t ∈ [0, 1], |Y_n(t)| > ε`, an outer measure if that event is not measurable). -/
def TendstoUCP01Zero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (Y : ∀ n, ℝ → Ω n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => P n {ω | ∃ t ∈ Set.Icc (0 : ℝ) 1, ε < |Y n t ω|}) atTop (𝓝 0)

/-! ### The limit equations -/

/-- The drift of the Heston-type system of Theorem 3.1 in the state `x = (C, P)`:
`b(t, x) = ((2μ/λ − C)(λ/m), 0)`. -/
noncomputable def hestonDrift (μ lam m : ℝ) :
    ℝ≥0 × EthierKurtz.SDEState 2 → EthierKurtz.SDEState 2 :=
  fun p => !₂[(2 * μ / lam - p.2 0) * (lam / m), 0]

/-- The diffusion matrix of the Heston-type system of Theorem 3.1 in the state `x = (C, P)`, driven
by `(B¹, B²)`: `σ(t, x) = diag((1/m) √C, (1/(1 − ‖φ‖₁)) √C)` with `‖φ‖₁ = phiMass φ₁ φ₂`. -/
noncomputable def hestonDiff (m : ℝ) (φ₁ φ₂ : ℝ → ℝ) :
    ℝ≥0 × EthierKurtz.SDEState 2 → EthierKurtz.SDEDiffusion 2 :=
  fun p => WithLp.toLp 2 (fun ij : Fin 2 × Fin 2 =>
    if ij = (0, 0) then (1 / m) * Real.sqrt (p.2 0)
    else if ij = (1, 1) then (1 / (1 - phiMass φ₁ φ₂)) * Real.sqrt (p.2 0)
    else 0)

/-- The drift of the pair `(C, B²)` of Lemma 4.15: `b(t, x) = ((2μ/λ − C)(λ/m), 0)`. -/
noncomputable def cirPairDrift (μ lam m : ℝ) :
    ℝ≥0 × EthierKurtz.SDEState 2 → EthierKurtz.SDEState 2 :=
  fun p => !₂[(2 * μ / lam - p.2 0) * (lam / m), 0]

/-- The diffusion matrix of the pair `(C, B²)` of Lemma 4.15, driven by `(W, B²)`:
`σ(t, x) = diag((1/m) √C, 1)`. -/
noncomputable def cirPairDiff (m : ℝ) :
    ℝ≥0 × EthierKurtz.SDEState 2 → EthierKurtz.SDEDiffusion 2 :=
  fun p => WithLp.toLp 2 (fun ij : Fin 2 × Fin 2 =>
    if ij = (0, 0) then (1 / m) * Real.sqrt (p.2 0)
    else if ij = (1, 1) then 1
    else 0)

end NearlyUnstableHawkes.Heston



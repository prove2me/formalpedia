-- Prove2me | Definitions.Def_UnifiedFBSDE_Main_Setting
-- name    : UnifiedFBSDE_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:29.5086+00:00
-- url     : https://prove2.me/theorems/ff225c6b-57ef-42c4-9b52-83dc28045f77
-- title:
--   Assumption 2.1, (2.2), (4.4), Definition 2.2, pp. 5–7, 12 — the FBSDE (1.1) with random Lipschitz coefficients, its 𝕃² solutions and decoupling fields
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space carrying a one-dimensional Brownian motion $B$, and let $\mathbb F=\{\mathcal F_t\}_{t\ge0}$ be the natural filtration of $B$ augmented by the $\mathbb P$-null sets. Fix a horizon $T>0$. This file sets up the forward–backward SDE
--
--   $$
--   X_t = x + \int_0^t b(s,\Theta_s)\,ds + \int_0^t \sigma(s,\Theta_s)\,dB_s,\qquad
--   Y_t = g(X_T) + \int_t^T f(s,\Theta_s)\,ds - \int_t^T Z_s\,dB_s,\qquad t\in[0,T],
--   $$
--
--   with $\Theta=(X,Y,Z)$, and the objects built on it.
--
--   1. **Coefficients.** Random functions $b,\sigma,f:[0,T]\times\Omega\times\mathbb R^3\to\mathbb R$ and $g:\mathbb R\times\Omega\to\mathbb R$.
--   2. **Assumption 2.1** with Lipschitz constant $K_0$: for fixed $(x,y,z)$ the coefficients $b,\sigma,f$ are $\mathbb F$-progressively measurable on $[0,T]$ and $g(x)$ is $\mathcal F_T$-measurable; the integrability condition
--   $$I_0^2=\mathbb E\Big\{\Big(\int_0^T[|b|+|f|](t,0,0,0)\,dt\Big)^2+\int_0^T|\sigma|^2(t,0,0,0)\,dt+|g(0)|^2\Big\}<\infty$$
--   holds; and $K_0>0$ with $|\varphi(t,\omega,x,y,z)-\varphi(t,\omega,x',y',z')|\le K_0(|x-x'|+|y-y'|+|z-z'|)$ for $\varphi=b,\sigma,f$ and $|g(x)-g(x')|\le K_0|x-x'|$, for every $\omega$ and $t\in[0,T]$.
--   3. **The space $\mathbb L^2$** on an interval $[t_1,t_2]$: progressively measurable $\Theta$ with $\|\Theta\|^2_{\mathbb L^2}=\mathbb E\{\sup_{t_1\le t\le t_2}[|X_t|^2+|Y_t|^2]+\int_{t_1}^{t_2}|Z_t|^2dt\}<\infty$.
--   4. **Solutions of (2.2)** on $[t_1,t_2]$ with initial value $\eta$ and terminal map $\varphi(x,\omega)$: $\Theta\in\mathbb L^2$ such that for every $t\in[t_1,t_2]$, almost surely, $X_t=\eta+\int_{t_1}^t b(s,\Theta_s)ds+\int_{t_1}^t\sigma(s,\Theta_s)dB_s$ and $Y_t=\varphi(X_{t_2})+\int_t^{t_2}f(s,\Theta_s)ds-\int_t^{t_2}Z_sdB_s$. A solution of (1.1) from $x$ is a solution on $[0,T]$ with $\eta\equiv x$ and $\varphi=g$. **Unique solvability** means a solution exists and any two agree: $X$ and $Y$ a.s. at every time, $Z$ $dt\otimes d\mathbb P$-a.e.
--   5. **Decoupling field (Definition 2.2).** A random field $u(t,x,\omega)$, progressively measurable in $(t,\omega)$ for each $x$, with $u(T,x)=g(x)$, such that for some $\delta>0$, for all $0\le t_1<t_2\le T$ with $t_2-t_1\le\delta$ and all $\eta\in L^2(\mathcal F_{t_1})$, the FBSDE (2.2) on $[t_1,t_2]$ with initial value $\eta$ and terminal map $u(t_2,\cdot)$ is uniquely solvable in $\mathbb L^2$ and its solution satisfies $Y_t=u(t,X_t)$, $t\in[t_1,t_2]$, a.s.
--
--   These are the objects of the well-posedness theory: a decoupling field reduces solvability over $[0,T]$ to solvability over short intervals.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$ (the convention of the referenced `Peng1990.SMP.Stochastic`), with time integrals taken over real intervals through `toNNReal`. Stochastic integrals are `IsItoIntegral` processes of the integrands $\mathbf 1_{(t_1,t_2]}(s)\sigma(s,\Theta_s)$ and $\mathbf 1_{(t_1,t_2]}(s)Z_s$, so $\int_{t_1}^t\sigma\,dB=J_t-J_{t_1}$. Progressive measurability on an interval is stated for the process stopped at $t_2$ and set to $0$ before $t_1$. Every time integral carries its integrability, and every moment is a lower Lebesgue integral in $[0,\infty]$. The Lipschitz condition uses the $\ell^1$ norm on $\mathbb R^3$ (the page names no norm). Definition 2.2 prints "$0=t_1<t_2\le T$"; it is read as $0\le t_1$, which is how the proof of Theorem 2.3 uses it. Uniqueness is uniqueness in $\mathbb L^2$, the class of Theorems 6.1 and 7.4.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 2, (1.1), (1.4); p. 5, §2 setting; pp. 5–6, Assumption 2.1, (2.1); p. 6, (2.2), Definition 2.2; p. 12, (4.4)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting

namespace UnifiedFBSDE.Main

open MeasureTheory ProbabilityTheory Set Peng1990.SMP
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The (random) coefficients of the one-dimensional FBSDE (1.1):
`b, σ, f : [0, T] × Ω × ℝ³ → ℝ`, written `b t ω x y z`, and `g : ℝ × Ω → ℝ`, written `g x ω`.
Time is `ℝ≥0`; only `t ∈ [0, T]` is ever used. -/
structure Coeffs (Ω : Type*) where
  b : ℝ≥0 → Ω → ℝ → ℝ → ℝ → ℝ
  σ : ℝ≥0 → Ω → ℝ → ℝ → ℝ → ℝ
  f : ℝ≥0 → Ω → ℝ → ℝ → ℝ → ℝ
  g : ℝ → Ω → ℝ

/-- `I₀²` of (2.1): `E{(∫₀ᵀ [|b| + |f|](t, 0, 0, 0) dt)² + ∫₀ᵀ |σ|²(t, 0, 0, 0) dt + |g(0)|²}`,
computed in `[0, ∞]` (all integrands are nonnegative, so lower Lebesgue integrals are used and no
junk value can occur). -/
noncomputable def I0sq (P : Measure Ω) (T : ℝ≥0) (c : Coeffs Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ((∫⁻ t in Icc (0 : ℝ) T, (‖c.b t.toNNReal ω 0 0 0‖ₑ + ‖c.f t.toNNReal ω 0 0 0‖ₑ)) ^ 2
      + (∫⁻ t in Icc (0 : ℝ) T, ‖c.σ t.toNNReal ω 0 0 0‖ₑ ^ 2) + ‖c.g 0 ω‖ₑ ^ 2) ∂P

/-- Assumption 2.1 with common Lipschitz constant `K₀` on the horizon `[0, T]`:
(i) for fixed `(x, y, z)`, `b, σ, f` are `𝔽`-progressively measurable on `[0, T]` (stated as
progressive measurability of the process stopped at `T`), `g(x)` is `𝓕_T`-measurable for fixed `x`,
and `I₀² < ∞`; (ii) `K₀ > 0` and, for every `ω` and `t ∈ [0, T]`,
`|φ(t, x, y, z) − φ(t, x', y', z')| ≤ K₀(|x − x'| + |y − y'| + |z − z'|)` for `φ = b, σ, f`, and
`|g(x) − g(x')| ≤ K₀|x − x'|`. -/
structure Assumption21 (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (K₀ : ℝ)
    (c : Coeffs Ω) : Prop where
  prog_b : ∀ x y z : ℝ, IsStronglyProgressive 𝓕 (fun t ω => c.b (min t T) ω x y z)
  prog_σ : ∀ x y z : ℝ, IsStronglyProgressive 𝓕 (fun t ω => c.σ (min t T) ω x y z)
  prog_f : ∀ x y z : ℝ, IsStronglyProgressive 𝓕 (fun t ω => c.f (min t T) ω x y z)
  meas_g : ∀ x : ℝ, StronglyMeasurable[𝓕 T] (c.g x)
  integrability : I0sq P T c < ⊤
  K₀_pos : 0 < K₀
  lip_b : ∀ t ≤ T, ∀ (ω : Ω) (x y z x' y' z' : ℝ),
    |c.b t ω x y z - c.b t ω x' y' z'| ≤ K₀ * (|x - x'| + |y - y'| + |z - z'|)
  lip_σ : ∀ t ≤ T, ∀ (ω : Ω) (x y z x' y' z' : ℝ),
    |c.σ t ω x y z - c.σ t ω x' y' z'| ≤ K₀ * (|x - x'| + |y - y'| + |z - z'|)
  lip_f : ∀ t ≤ T, ∀ (ω : Ω) (x y z x' y' z' : ℝ),
    |c.f t ω x y z - c.f t ω x' y' z'| ≤ K₀ * (|x - x'| + |y - y'| + |z - z'|)
  lip_g : ∀ (ω : Ω) (x x' : ℝ), |c.g x ω - c.g x' ω| ≤ K₀ * |x - x'|

/-- A process living on `[t₁, t₂]`, extended by `0` before `t₁` and frozen at its `t₂`-value after
`t₂`; used to state progressive measurability on `[t₁, t₂]` with Mathlib's predicate on `ℝ≥0`. -/
noncomputable def onInterval (t₁ t₂ : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => if t < t₁ then 0 else X (min t t₂) ω

/-- `‖Θ‖²_{𝕃²}` of (4.4) with `p = 2`, on the interval `[t₁, t₂]`:
`E{sup_{t₁≤t≤t₂} [|X_t|² + |Y_t|²] + ∫_{t₁}^{t₂} |Z_t|² dt}`, in `[0, ∞]`. -/
noncomputable def L2NormSq (P : Measure Ω) (t₁ t₂ : ℝ≥0) (X Y Z : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((⨆ t ∈ Icc t₁ t₂, (‖X t ω‖ₑ ^ 2 + ‖Y t ω‖ₑ ^ 2))
      + (∫⁻ s in Icc (t₁ : ℝ) t₂, ‖Z s.toNNReal ω‖ₑ ^ 2)) ∂P

/-- `Θ = (X, Y, Z) ∈ 𝕃²` on `[t₁, t₂]`: the three processes are `𝔽`-progressively measurable on
`[t₁, t₂]` and `‖Θ‖²_{𝕃²} < ∞` ((4.4), `p = 2`). -/
def MemL2On (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (t₁ t₂ : ℝ≥0)
    (X Y Z : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 (onInterval t₁ t₂ X) ∧ IsStronglyProgressive 𝓕 (onInterval t₁ t₂ Y) ∧
    IsStronglyProgressive 𝓕 (onInterval t₁ t₂ Z) ∧ L2NormSq P t₁ t₂ X Y Z < ⊤

/-- `Θ = (X, Y, Z)` solves the FBSDE (2.2) on `[t₁, t₂]` with initial value `η` and terminal map
`φ(x, ω)`, driven by the one-dimensional Brownian motion `B`:
`Θ ∈ 𝕃²` on `[t₁, t₂]`, and there are Itô integral processes `J`, `K` (on `[0, t₂]`, in the sense
of `IsItoIntegral`) of `1_{(t₁, t₂]}(s) σ(s, Θ_s)` and `1_{(t₁, t₂]}(s) Z_s` such that, for every
`t ∈ [t₁, t₂]`, almost surely, the drift integrands are integrable and
`X_t = η + ∫_{t₁}^t b(s, Θ_s) ds + (J_t − J_{t₁})`,
`Y_t = φ(X_{t₂}) + ∫_t^{t₂} f(s, Θ_s) ds − (K_{t₂} − K_t)`. -/
def SolvesFBSDEOn (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (B : ℝ≥0 → Ω → Fin 1 → ℝ)
    (c : Coeffs Ω) (t₁ t₂ : ℝ≥0) (η : Ω → ℝ) (φ : ℝ → Ω → ℝ)
    (X Y Z : ℝ≥0 → Ω → ℝ) : Prop :=
  MemL2On 𝓕 P t₁ t₂ X Y Z ∧
    ∃ J K : ℝ≥0 → Ω → ℝ,
      IsItoIntegral 𝓕 P t₂ (fun s ω => B s ω 0)
        (fun s ω => if t₁ < s ∧ s ≤ t₂ then c.σ s ω (X s ω) (Y s ω) (Z s ω) else 0) J ∧
      IsItoIntegral 𝓕 P t₂ (fun s ω => B s ω 0)
        (fun s ω => if t₁ < s ∧ s ≤ t₂ then Z s ω else 0) K ∧
      ∀ t ∈ Icc t₁ t₂, ∀ᵐ ω ∂P,
        IntegrableOn (fun s : ℝ => c.b s.toNNReal ω (X s.toNNReal ω) (Y s.toNNReal ω)
          (Z s.toNNReal ω)) (Icc (t₁ : ℝ) t) ∧
        IntegrableOn (fun s : ℝ => c.f s.toNNReal ω (X s.toNNReal ω) (Y s.toNNReal ω)
          (Z s.toNNReal ω)) (Icc (t : ℝ) t₂) ∧
        X t ω = η ω + (∫ s in Icc (t₁ : ℝ) t, c.b s.toNNReal ω (X s.toNNReal ω)
          (Y s.toNNReal ω) (Z s.toNNReal ω)) + (J t ω - J t₁ ω) ∧
        Y t ω = φ (X t₂ ω) ω + (∫ s in Icc (t : ℝ) t₂, c.f s.toNNReal ω (X s.toNNReal ω)
          (Y s.toNNReal ω) (Z s.toNNReal ω)) - (K t₂ ω - K t ω)

/-- The FBSDE (2.2) on `[t₁, t₂]` with data `(η, φ)` has a unique solution in `𝕃²`: a solution
exists, and any two solutions agree — `X_t = X'_t` and `Y_t = Y'_t` a.s. for each
`t ∈ [t₁, t₂]`, and `Z = Z'` `dt ⊗ dP`-a.e. on `[t₁, t₂] × Ω`. -/
def HasUniqueSolutionOn (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (B : ℝ≥0 → Ω → Fin 1 → ℝ)
    (c : Coeffs Ω) (t₁ t₂ : ℝ≥0) (η : Ω → ℝ) (φ : ℝ → Ω → ℝ) : Prop :=
  (∃ X Y Z : ℝ≥0 → Ω → ℝ, SolvesFBSDEOn 𝓕 P B c t₁ t₂ η φ X Y Z) ∧
    ∀ X Y Z X' Y' Z' : ℝ≥0 → Ω → ℝ,
      SolvesFBSDEOn 𝓕 P B c t₁ t₂ η φ X Y Z → SolvesFBSDEOn 𝓕 P B c t₁ t₂ η φ X' Y' Z' →
        (∀ t ∈ Icc t₁ t₂, X t =ᵐ[P] X' t ∧ Y t =ᵐ[P] Y' t) ∧
        ∫⁻ ω, (∫⁻ s in Icc (t₁ : ℝ) t₂, ‖Z s.toNNReal ω - Z' s.toNNReal ω‖ₑ ^ 2) ∂P = 0

/-- `Θ` solves the FBSDE (1.1) on `[0, T]` from the initial state `x`: (2.2) on `[0, T]` with
`η ≡ x` and terminal map `g`. -/
def SolvesFBSDE (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (B : ℝ≥0 → Ω → Fin 1 → ℝ)
    (c : Coeffs Ω) (T : ℝ≥0) (x : ℝ) (X Y Z : ℝ≥0 → Ω → ℝ) : Prop :=
  SolvesFBSDEOn 𝓕 P B c 0 T (fun _ => x) c.g X Y Z

/-- The FBSDE (1.1) on `[0, T]` from `x` has a unique solution `Θ ∈ 𝕃²`. -/
def HasUniqueSolution (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (B : ℝ≥0 → Ω → Fin 1 → ℝ)
    (c : Coeffs Ω) (T : ℝ≥0) (x : ℝ) : Prop :=
  HasUniqueSolutionOn 𝓕 P B c 0 T (fun _ => x) c.g

/-- Definition 2.2: `u : [0, T] × ℝ × Ω → ℝ` (written `u t x ω`) is a decoupling field of (1.1):
for each `x`, `u(·, x)` is `𝔽`-progressively measurable on `[0, T]`; `u(T, x) = g(x)`; and there
is `δ > 0` such that for all `0 ≤ t₁ < t₂ ≤ T` with `t₂ − t₁ ≤ δ` and every `η ∈ L²(𝓕_{t₁})`, the
FBSDE (2.2) on `[t₁, t₂]` with initial value `η` and terminal map `u(t₂, ·)` has a unique solution in
`𝕃²`, and every solution satisfies (1.4), `Y_t = u(t, X_t)` a.s., for each `t ∈ [t₁, t₂]`. -/
def IsDecouplingField (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (B : ℝ≥0 → Ω → Fin 1 → ℝ)
    (c : Coeffs Ω) (T : ℝ≥0) (u : ℝ≥0 → ℝ → Ω → ℝ) : Prop :=
  (∀ x : ℝ, IsStronglyProgressive 𝓕 (fun t ω => u (min t T) x ω)) ∧
    (∀ x : ℝ, u T x = c.g x) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₁ t₂ : ℝ≥0, t₁ < t₂ → t₂ ≤ T → (t₂ : ℝ) - t₁ ≤ δ →
      ∀ η : Ω → ℝ, StronglyMeasurable[𝓕 t₁] η → ∫⁻ ω, ‖η ω‖ₑ ^ 2 ∂P < ⊤ →
        HasUniqueSolutionOn 𝓕 P B c t₁ t₂ η (u t₂) ∧
        ∀ X Y Z : ℝ≥0 → Ω → ℝ, SolvesFBSDEOn 𝓕 P B c t₁ t₂ η (u t₂) X Y Z →
          ∀ t ∈ Icc t₁ t₂, ∀ᵐ ω ∂P, Y t ω = u t (X t ω) ω

end UnifiedFBSDE.Main



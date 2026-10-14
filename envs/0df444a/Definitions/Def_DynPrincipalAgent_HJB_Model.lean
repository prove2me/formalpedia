-- Prove2me | Definitions.Def_DynPrincipalAgent_HJB_Model
-- name    : DynPrincipalAgent_HJB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:54.189902+00:00
-- url     : https://prove2.me/theorems/d892d404-ab0a-46c5-a13d-314bcae00a65
-- title:
--   Assumptions 2.2, 2.7, 3.1 and (2.10)–(2.11), (2.17), (3.1) — the type-indexed model data, the barriers and the domain D_θ
-- statement:
--   This file fixes the deterministic data of the dynamic principal–agent model of Zhang and Zhu, together with the standing assumptions of the paper.
--
--   **Data.** A horizon $T>0$, a payment cap $C_0>0$, constants $\Lambda_0\ge 1$ and $\Lambda_1>0$, a modulus of continuity $\rho$, a set $\Theta$ of agent types, and for every type $\theta\in\Theta$:
--   1. the agent's running utility $f(\theta;s,\eta)$ from a payment rate $\eta$;
--   2. the agent's running cost $h(\theta;s,\alpha)$ of an effort $\alpha$;
--   3. the agent's individual rationality (market value) $R^\theta_s$ and his quitting cost $c^\theta_s$;
--
--   and the principal's cost $c^P_s$ of a quitting.
--
--   **Derived objects.** $I^h(\theta;s,\cdot)$ is the inverse of $\partial_\alpha h(\theta;s,\cdot)$ and $I^f(\theta;s,\cdot)$ the inverse of $f(\theta;s,\cdot)$ on payments $\eta\le C_0$ (2.10); the Hamiltonians are
--   $$H(\theta;s,z)=z\,I^h(\theta;s,z)-h\big(\theta;s,I^h(\theta;s,z)\big),\qquad \tilde H(\theta;s,z)=-h\big(\theta;s,I^h(\theta;s,z)\big).$$
--   The upper barrier, the lower barrier and the domain are
--   $$\overline L^\theta_t=\int_t^T f(\theta;s,C_0)\,ds,\qquad \underline L^\theta_t=R^\theta_t-c^\theta_t,\qquad D_\theta=\{(t,x):0\le t<T,\ \underline L^\theta_t<x\le\overline L^\theta_t\},$$
--   and $O_\theta=\{(t,x):0<t<T,\ \underline L^\theta_t<x<\overline L^\theta_t\}$ is its interior.
--
--   **Assumption 2.2.** For $s\in[0,T]$ and every type: $f$ is twice differentiable in $\eta$ with $f\le-1/\Lambda_0$, $\partial_\eta f\ge 1/\Lambda_0$, $\partial_{\eta\eta}f\le-1/\Lambda_0$ for all $\eta\le C_0$ and $f(\theta;s,C_0)\ge-\Lambda_0$; $h$ is twice differentiable in $\alpha$ with $h\ge0$, $h(\theta;s,0)=0$ and $1/\Lambda_0\le\partial_{\alpha\alpha}h\le\Lambda_0$; and $f$, $h$, $\partial_\alpha h$ are uniformly continuous in $s$ with the common modulus $\rho$.
--
--   **Assumption 2.7.** $-\Lambda_0\le R^\theta_s\le\overline L^\theta_s$ on $[0,T]$, $R^\theta_T=0$, and $|R^\theta_s-R^\theta_{s'}|\le\rho(|s-s'|)$.
--
--   **Assumption 3.1.** Assumption 2.7 holds; $c^\theta_t\ge 1/\Lambda_0$ and $c^P_t\ge0$; $c^\theta$, $c^P$ are uniformly continuous with modulus $\rho$ and bounded by $\Lambda_0$; and $|\underline L^\theta_t-\underline L^\theta_s|\le\Lambda_1|t-s|$.
--
--   The structure `Standing` bundles Assumptions 2.2 and 3.1, which are in force from §3 of the paper on.
--
--   **Formalization Note.** A modulus of continuity is a function $\rho$ that is nondecreasing on $[0,\infty)$, tends to $0$ at $0^+$, and satisfies $\rho(\delta)\ge\delta$. The continuity conditions are uniform in $\theta$, in $\eta\le C_0$ (for $f$) and in $\alpha$ (for $h$, $\partial_\alpha h$), as the paper's "common for all $\theta$" (p. 8) requires. Assumption 2.7 (ii) ("uniformly Lipschitz continuous … with modulus of continuity function $\rho$") is read as $|R^\theta_s-R^\theta_{s'}|\le\rho(|s-s'|)$. Two conditions the paper does not state are added because the random types of §5–§6 need them: $\Theta$ carries a σ-algebra, and $f$, $h$, $\partial_\alpha h$ are jointly measurable in $(\theta,s,\cdot)$. $H$ and $\tilde H$ are taken in the closed forms of (2.11)–(2.12) (the paper's argument order $h(s,\theta,\cdot)$ there is a typo for $h(\theta;s,\cdot)$). All conditions are imposed for times in $[0,T]$; deterministic data take real time arguments.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Assumptions 2.2, 2.7, 3.1, (2.10)–(2.12), (2.17), (3.1), pp. 8–12

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace DynPrincipalAgent.HJB

/-- The deterministic data of the model (Zhang–Zhu, §2–§3, pp. 7–12): the horizon `T`, the bound `C₀`
on payments, the constants `Λ₀`, `Λ₁`, the modulus of continuity `ρ`, and, for every agent type
`θ ∈ Θ`, the running utility `f(θ; s, η)`, the running cost `h(θ; s, α)`, the individual rationality
(market value) `R^θ_s` and the agent's quitting cost `c^θ_s`; finally the principal's hiring cost
`c^P_s`. Times of the deterministic data are real numbers. -/
structure Model (Θ : Type) where
  /-- the horizon `T` -/
  T : ℝ≥0
  /-- the uniform upper bound `C₀` on payments (Definition 2.1 (i)) -/
  C₀ : ℝ
  /-- the constant `Λ₀` of Assumptions 2.2, 2.7, 3.1 -/
  Λ₀ : ℝ
  /-- the Lipschitz constant `Λ₁` of the lower barrier (Assumption 3.1 (iii)) -/
  Λ₁ : ℝ
  /-- the common modulus of continuity `ρ` -/
  ρ : ℝ → ℝ
  /-- the agent's running utility `f(θ; s, η)` -/
  f : Θ → ℝ → ℝ → ℝ
  /-- the agent's running cost `h(θ; s, α)` -/
  h : Θ → ℝ → ℝ → ℝ
  /-- the agent's individual rationality `R^θ_s` -/
  R : Θ → ℝ → ℝ
  /-- the agent's quitting cost `c^θ_s` -/
  c : Θ → ℝ → ℝ
  /-- the principal's cost `c^P_s` of a quitting -/
  cP : ℝ → ℝ

namespace Model

variable {Θ : Type} (M : Model Θ)

/-- `I^h(θ; s, ·)`, the inverse function of `∂_α h(θ; s, ·)` ((2.10)). -/
noncomputable def Ih (θ : Θ) (s z : ℝ) : ℝ :=
  Function.invFun (deriv (M.h θ s)) z

/-- `I^f(θ; s, ·)`, the inverse of `f(θ; s, ·)` restricted to payments `η ≤ C₀` ((2.10)); it is
used for `y ≤ f(θ; s, C₀)`. -/
noncomputable def If (θ : Θ) (s y : ℝ) : ℝ :=
  ((@Function.invFun (Set.Iic M.C₀) ℝ ⟨⟨M.C₀, Set.mem_Iic.mpr le_rfl⟩⟩ (fun η => M.f θ s η) y :
    Set.Iic M.C₀) : ℝ)

/-- `H(θ; s, z) = z I^h(θ; s, z) − h(θ; s, I^h(θ; s, z))`, the closed form of
`sup_α [α z − h(θ; s, α)]` ((2.11)–(2.12)). -/
noncomputable def H (θ : Θ) (s z : ℝ) : ℝ :=
  z * M.Ih θ s z - M.h θ s (M.Ih θ s z)

/-- `H̃(θ; s, z) = −h(θ; s, I^h(θ; s, z))` ((2.11)). -/
noncomputable def Htil (θ : Θ) (s z : ℝ) : ℝ :=
  -M.h θ s (M.Ih θ s z)

/-- The upper barrier `L̄^θ_t = ∫_t^T f(θ; s, C₀) ds` ((2.17)). -/
noncomputable def Lbar (θ : Θ) (t : ℝ) : ℝ :=
  ∫ s in t..(M.T : ℝ), M.f θ s M.C₀

/-- The lower barrier `L̲^θ_t = R^θ_t − c^θ_t` ((3.1)). -/
def Lund (θ : Θ) (t : ℝ) : ℝ :=
  M.R θ t - M.c θ t

/-- The domain `D_θ = {(t, x) : 0 ≤ t < T, L̲^θ_t < x ≤ L̄^θ_t}` ((3.1)). -/
def D (θ : Θ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 < (M.T : ℝ) ∧ M.Lund θ p.1 < p.2 ∧ p.2 ≤ M.Lbar θ p.1}

/-- The interior `O_θ = {(t, x) : 0 < t < T, L̲^θ_t < x < L̄^θ_t}` of `D_θ`, where the HJB
equation (4.6) is tested in the viscosity sense. -/
def O (θ : Θ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < (M.T : ℝ) ∧ M.Lund θ p.1 < p.2 ∧ p.2 < M.Lbar θ p.1}

end Model

/-- A modulus of continuity function: nondecreasing on `[0, ∞)`, `ρ(δ) → 0` as `δ ↓ 0`, and
`ρ(δ) ≥ δ` (the normalisation of Assumption 2.2 (iii)). -/
structure IsModulus (ρ : ℝ → ℝ) : Prop where
  mono : MonotoneOn ρ (Ici 0)
  tendsto_zero : Tendsto ρ (𝓝[>] 0) (𝓝 0)
  ge_self : ∀ δ, 0 ≤ δ → δ ≤ ρ δ

namespace Model

variable {Θ : Type} (M : Model Θ)

/-- Assumption 2.2 (p. 8), with the standing constants: `T > 0`, `C₀ > 0`, `Λ₀ ≥ 1`, `ρ` a modulus of
continuity. (i) `f` is twice differentiable in `η` with `f ≤ −1/Λ₀`, `∂_η f ≥ 1/Λ₀`,
`∂_ηη f ≤ −1/Λ₀` for all `η ≤ C₀`, and `f(θ; s, C₀) ≥ −Λ₀`. (ii) `h` is twice differentiable in `α`
with `h ≥ 0`, `h(θ; s, 0) = 0`, `1/Λ₀ ≤ ∂_αα h ≤ Λ₀`. (iii) `f`, `h`, `∂_α h` are uniformly continuous in
`s` with the common modulus `ρ`, uniformly in `θ`, in `η ≤ C₀` (for `f`) and in `α` (for `h`, `∂_α h`).
All conditions are for `s ∈ [0, T]` and every type `θ`. In addition `f`, `h`, `∂_α h` are jointly
measurable in `(θ, s, ·)`. -/
structure A22 [MeasurableSpace Θ] : Prop where
  T_pos : 0 < (M.T : ℝ)
  C₀_pos : 0 < M.C₀
  Λ₀_ge_one : 1 ≤ M.Λ₀
  modulus : IsModulus M.ρ
  f_diff : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T,
    Differentiable ℝ (M.f θ s) ∧ Differentiable ℝ (deriv (M.f θ s))
  f_le : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ η ≤ M.C₀, M.f θ s η ≤ -1 / M.Λ₀
  f_deriv_ge : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ η ≤ M.C₀, 1 / M.Λ₀ ≤ deriv (M.f θ s) η
  f_deriv2_le : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ η ≤ M.C₀,
    deriv (deriv (M.f θ s)) η ≤ -1 / M.Λ₀
  f_C₀_ge : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, -M.Λ₀ ≤ M.f θ s M.C₀
  h_diff : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T,
    Differentiable ℝ (M.h θ s) ∧ Differentiable ℝ (deriv (M.h θ s))
  h_nonneg : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ α, 0 ≤ M.h θ s α
  h_zero : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, M.h θ s 0 = 0
  h_deriv2 : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ α,
    1 / M.Λ₀ ≤ deriv (deriv (M.h θ s)) α ∧ deriv (deriv (M.h θ s)) α ≤ M.Λ₀
  f_unif : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ s' ∈ Icc (0 : ℝ) M.T, ∀ η ≤ M.C₀,
    |M.f θ s η - M.f θ s' η| ≤ M.ρ |s - s'|
  h_unif : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ s' ∈ Icc (0 : ℝ) M.T, ∀ α,
    |M.h θ s α - M.h θ s' α| ≤ M.ρ |s - s'|
  dh_unif : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ s' ∈ Icc (0 : ℝ) M.T, ∀ α,
    |deriv (M.h θ s) α - deriv (M.h θ s') α| ≤ M.ρ |s - s'|
  f_meas : Measurable fun p : Θ × ℝ × ℝ => M.f p.1 p.2.1 p.2.2
  h_meas : Measurable fun p : Θ × ℝ × ℝ => M.h p.1 p.2.1 p.2.2
  dh_meas : Measurable fun p : Θ × ℝ × ℝ => deriv (M.h p.1 p.2.1) p.2.2

/-- Assumption 2.7 (p. 11): (i) `−Λ₀ ≤ R^θ_s ≤ L̄^θ_s` for `0 ≤ s ≤ T`, and `R^θ_T = 0`;
(ii) `R^θ` is uniformly continuous in `s` with the modulus `ρ`, uniformly in `θ`. -/
structure A27 : Prop where
  R_bounds : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, -M.Λ₀ ≤ M.R θ s ∧ M.R θ s ≤ M.Lbar θ s
  R_T : ∀ θ, M.R θ M.T = 0
  R_unif : ∀ θ, ∀ s ∈ Icc (0 : ℝ) M.T, ∀ s' ∈ Icc (0 : ℝ) M.T,
    |M.R θ s - M.R θ s'| ≤ M.ρ |s - s'|

/-- Assumption 3.1 (p. 12): `R^θ` satisfies Assumption 2.7, and, for the same `Λ₀`, `ρ`,
(i) `c^θ_t ≥ 1/Λ₀`, `c^P_t ≥ 0`; (ii) `c^θ`, `c^P` are uniformly continuous in `t` with modulus `ρ`;
(iii) `c^θ`, `c^P` are bounded by `Λ₀`, and `|L̲^θ_t − L̲^θ_s| ≤ Λ₁ |t − s|` for a constant `Λ₁ > 0`.
All conditions are for times in `[0, T]` and every type `θ`. -/
structure A31 : Prop where
  a27 : M.A27
  c_ge : ∀ θ, ∀ t ∈ Icc (0 : ℝ) M.T, 1 / M.Λ₀ ≤ M.c θ t
  cP_nonneg : ∀ t ∈ Icc (0 : ℝ) M.T, 0 ≤ M.cP t
  c_unif : ∀ θ, ∀ t ∈ Icc (0 : ℝ) M.T, ∀ s ∈ Icc (0 : ℝ) M.T,
    |M.c θ t - M.c θ s| ≤ M.ρ |t - s|
  cP_unif : ∀ t ∈ Icc (0 : ℝ) M.T, ∀ s ∈ Icc (0 : ℝ) M.T, |M.cP t - M.cP s| ≤ M.ρ |t - s|
  c_bdd : ∀ θ, ∀ t ∈ Icc (0 : ℝ) M.T, |M.c θ t| ≤ M.Λ₀
  cP_bdd : ∀ t ∈ Icc (0 : ℝ) M.T, |M.cP t| ≤ M.Λ₀
  Λ₁_pos : 0 < M.Λ₁
  Lund_lip : ∀ θ, ∀ t ∈ Icc (0 : ℝ) M.T, ∀ s ∈ Icc (0 : ℝ) M.T,
    |M.Lund θ t - M.Lund θ s| ≤ M.Λ₁ * |t - s|

/-- The standing assumptions of §3–§6: Assumptions 2.2 and 3.1 (which contains Assumption 2.7). -/
structure Standing [MeasurableSpace Θ] : Prop where
  a22 : M.A22
  a31 : M.A31

end Model

end DynPrincipalAgent.HJB



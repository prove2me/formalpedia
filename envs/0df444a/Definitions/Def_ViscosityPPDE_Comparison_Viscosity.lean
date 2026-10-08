-- Prove2me | Definitions.Def_ViscosityPPDE_Comparison_Viscosity
-- name    : ViscosityPPDE_Comparison_Viscosity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:31.347315+00:00
-- url     : https://prove2.me/theorems/93a19600-c660-4de5-9680-d325b64f4a0b
-- title:
--   (3.4)–(3.6), Definition 3.3 — nonlinear expectations, test sets $\underline{\mathcal A}^L$, $\overline{\mathcal A}^L$, viscosity sub- and supersolutions
-- statement:
--   Let $f : \Lambda \times \mathbb R \times \mathbb R^d \to \mathbb R$ be the coefficient of the semilinear PPDE
--   $$(\mathcal L u)(t,\omega) = -\partial_t u(t,\omega) - \tfrac12\operatorname{tr}\big(\partial^2_{\omega\omega}u(t,\omega)\big) - f\big(t,\omega,u(t,\omega),\partial_\omega u(t,\omega)\big) = 0,\quad 0\le t<T. \qquad (3.1)$$
--
--   1. For $L\ge0$ and $t<T$, $\mathcal U^L_t$ is the set of $\mathbb F^t$-progressively measurable $\mathbb R^d$-valued processes $\beta$ each of whose components is bounded by $L$. For $\beta \in \mathcal U^L_t$, $M^{t,\beta}_T = \exp\big(\int_t^T\beta_r\,dB^t_r - \frac12\int_t^T|\beta_r|^2dr\big)$ and $dP^{t,\beta} = M^{t,\beta}_T\,dP^t_0$ (3.4). The nonlinear expectations (3.5) are $\underline{\mathcal E}^L_t[\xi] = \inf_\beta E^{P^{t,\beta}}[\xi]$ and $\overline{\mathcal E}^L_t[\xi] = \sup_\beta E^{P^{t,\beta}}[\xi]$.
--   2. For $u \in C^0_b(\Lambda)$, $u^{t,\omega}(s,\omega') = u(s,\omega\otimes_t\omega')$. The test set $\underline{\mathcal A}^L u(t,\omega)$ (3.6) consists of the $\varphi \in C^{1,2}_b(\Lambda^t)$ for which some $\tau \in \mathcal T^t_+$ satisfies
--   $$0 = \varphi(t,\mathbf 0) - u(t,\omega) = \min_{\tilde\tau\in\mathcal T^t}\underline{\mathcal E}^L_t\big[(\varphi - u^{t,\omega})_{\tilde\tau\wedge\tau}\big],$$
--   and $\overline{\mathcal A}^L u(t,\omega)$ is defined with $\max$ and $\overline{\mathcal E}^L_t$.
--   3. The shifted operator is $(\mathcal L^{t,\omega}\varphi)(s,\tilde\omega) = -\partial_t\varphi - \frac12\operatorname{tr}[\partial^2_{\omega\omega}\varphi] - f^{t,\omega}(s,\tilde\omega,\varphi(s,\tilde\omega),\partial_\omega\varphi(s,\tilde\omega))$, with $f^{t,\omega}(s,\tilde\omega,y,z) = f(s,\omega\otimes_t\tilde\omega,y,z)$.
--   4. (Definition 3.3) $u \in C^0_b(\Lambda)$ is a **viscosity $L$-subsolution** (resp. $L$-supersolution) if for every $(t,\omega) \in [0,T)\times\Omega$ and every $\varphi \in \underline{\mathcal A}^L u(t,\omega)$ (resp. $\overline{\mathcal A}^L u(t,\omega)$), $(\mathcal L^{t,\omega}\varphi)(t,\mathbf 0) \le 0$ (resp. $\ge 0$). It is a **viscosity subsolution** (resp. supersolution) if it is a viscosity $L$-subsolution (resp. $L$-supersolution) for some $L \ge 0$, one $L$ for all $(t,\omega)$; a **viscosity solution** if it is both.
--
--   This is the paper's notion of viscosity solution of a path-dependent PDE, in which the pointwise tangency of the classical theory is replaced by an optimal stopping problem under the nonlinear expectation.
--
--   **Formalization Note** The minimum in (3.6) is attained at $\tilde\tau \equiv t$, where the argument is $0$, so the condition is written without $\min$ and $\inf$: $\varphi(t,\mathbf 0) = u(t,\omega)$ and, for every $\tilde\tau \in \mathcal T^t$ and every $\beta \in \mathcal U^L_t$, $M^{t,\beta}_T(\varphi-u^{t,\omega})_{\tilde\tau\wedge\tau}$ is $P^t_0$-integrable with nonnegative expectation (nonpositive for $\overline{\mathcal A}^L$). The integrability clause excludes Lean's junk value $0$ for non-integrable integrands; mathematically it always holds, since $M^{t,\beta}_T$ has moments of all orders. The stochastic integral is any Itô integral process of Peng's `IsItoIntegral` (platform definition `Peng1990.SMP.Stochastic`) for $\mathbb F^t$ and $P^t_0$; it vanishes on $[0,t]$ because $B^t$ does. The derivatives at $(t,\mathbf 0)$ are those of an arbitrary $C^{1,2}_b(\hat\Lambda^t)$ extension of $\varphi$, and the property is required for all of them.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, (3.1), p. 9; (3.4)–(3.6), Definition 3.3, p. 10; Remark 3.5(ii), p. 11

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ViscosityPPDE_Comparison_Calculus

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

variable {d : ℕ} {T : ℝ≥0}

/-- `β ∈ 𝒰^L_t`: an `𝔽^t`-progressively measurable `ℝ^d`-valued process each of whose components
is bounded by `L`. -/
def IsUL (T t : ℝ≥0) (L : ℝ) (β : ℝ≥0 → Omega d T t → Rd d) : Prop :=
  IsStronglyProgressive (filt d T t) β ∧ ∀ s ω i, |β s ω i| ≤ L

/-- `J = (J^1, …, J^d)` are Itô integral processes `J^i_s = ∫_0^s β^i_r dB^{t,i}_r` under `P^t_0`
for the filtration `𝔽^t` (Peng's `IsItoIntegral`). Since `B^t` vanishes on `[0,t]`, `J^i_s` is the
paper's `∫_t^s β^i_r dB^{t,i}_r`. -/
def IsItoOf (P0 : Measure (Omega d T 0)) (t : ℝ≥0) (β : ℝ≥0 → Omega d T t → Rd d)
    (J : Fin d → ℝ≥0 → Omega d T t → ℝ) : Prop :=
  ∀ i, Peng1990.SMP.IsItoIntegral (filt d T t) (Pt P0 t) T (fun s ω => ω.1 s i)
    (fun s ω => β s ω i) (J i)

/-- The Girsanov density (3.4) `M^{t,β}_T = exp(∫_t^T β_r dB^t_r − ½ ∫_t^T |β_r|² dr)`, so that
`dP^{t,β} = M^{t,β}_T dP^t_0`. -/
noncomputable def density (T t : ℝ≥0) (β : ℝ≥0 → Omega d T t → Rd d)
    (J : Fin d → ℝ≥0 → Omega d T t → ℝ) (ω : Omega d T t) : ℝ :=
  Real.exp (∑ i, J i T ω - (1 / 2) * ∫ r in Set.Icc (t : ℝ) T, ‖β r.toNNReal ω‖ ^ 2)

/-- `ℰ̲^L_t[ξ] ≥ 0`, written without the infimum (3.5): for every `β ∈ 𝒰^L_t`,
`E^{P^{t,β}}[ξ] = E^{P^t_0}[M^{t,β}_T ξ]` is well defined and `≥ 0`. -/
def LowerExpNonneg (P0 : Measure (Omega d T 0)) (t : ℝ≥0) (L : ℝ) (ξ : Omega d T t → ℝ) : Prop :=
  ∀ β, IsUL T t L β → ∀ J, IsItoOf P0 t β J →
    Integrable (fun ω => density T t β J ω * ξ ω) (Pt P0 t) ∧
      0 ≤ ∫ ω, density T t β J ω * ξ ω ∂(Pt P0 t)

/-- `ℰ̄^L_t[ξ] ≤ 0`, written without the supremum (3.5): for every `β ∈ 𝒰^L_t`,
`E^{P^{t,β}}[ξ]` is well defined and `≤ 0`. -/
def UpperExpNonpos (P0 : Measure (Omega d T 0)) (t : ℝ≥0) (L : ℝ) (ξ : Omega d T t → ℝ) : Prop :=
  ∀ β, IsUL T t L β → ∀ J, IsItoOf P0 t β J →
    Integrable (fun ω => density T t β J ω * ξ ω) (Pt P0 t) ∧
      ∫ ω, density T t β J ω * ξ ω ∂(Pt P0 t) ≤ 0

/-- `(φ − u^{t,ω})_{τ̃ ∧ τ}` as a random variable on `Ω^t`, where `u^{t,ω}(s, ω') = u(s, ω ⊗_t ω')`. -/
def stoppedDiff (u : ℝ≥0 → Omega d T 0 → ℝ) (t : ℝ≥0) (ω : Omega d T 0)
    (φ : ℝ≥0 → Omega d T t → ℝ) (τ' τ : Omega d T t → ℝ≥0) (ω' : Omega d T t) : ℝ :=
  φ (min (τ' ω') (τ ω')) ω' - u (min (τ' ω') (τ ω')) (concat ω t ω')

/-- The condition defining `φ ∈ 𝒜̲^L u(t, ω)` in (3.6), for `φ ∈ C^{1,2}_b(Λ^t)`:
`0 = φ(t,0) − u(t,ω) = min_{τ̃ ∈ 𝒯^t} ℰ̲^L_t[(φ − u^{t,ω})_{τ̃∧τ}]` for some `τ ∈ 𝒯^t_+`.
The minimum is attained at `τ̃ ≡ t`, where the argument is `0`; so the condition says
`φ(t,0) = u(t,ω)` and `ℰ̲^L_t[(φ − u^{t,ω})_{τ̃∧τ}] ≥ 0` for every `τ̃ ∈ 𝒯^t`. -/
def InTestSub (P0 : Measure (Omega d T 0)) (L : ℝ) (u : ℝ≥0 → Omega d T 0 → ℝ) (t : ℝ≥0)
    (ω : Omega d T 0) (φ : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  φ t (zeroPath d T t) = u t ω ∧ ∃ τ, IsStopTPlus T t τ ∧
    ∀ τ', IsStopT T t τ' → LowerExpNonneg P0 t L (stoppedDiff u t ω φ τ' τ)

/-- The condition defining `φ ∈ 𝒜̄^L u(t, ω)` in (3.6): `φ(t,0) = u(t,ω)` and
`ℰ̄^L_t[(φ − u^{t,ω})_{τ̃∧τ}] ≤ 0` for every `τ̃ ∈ 𝒯^t` (the maximum is attained at `τ̃ ≡ t`). -/
def InTestSuper (P0 : Measure (Omega d T 0)) (L : ℝ) (u : ℝ≥0 → Omega d T 0 → ℝ) (t : ℝ≥0)
    (ω : Omega d T 0) (φ : ℝ≥0 → Omega d T t → ℝ) : Prop :=
  φ t (zeroPath d T t) = u t ω ∧ ∃ τ, IsStopTPlus T t τ ∧
    ∀ τ', IsStopT T t τ' → UpperExpNonpos P0 t L (stoppedDiff u t ω φ τ' τ)

/-- The shifted operator of Definition 3.3,
`(ℒ^{t,ω}φ)(s, ω̃) = −∂_t φ − ½ tr ∂²_{ωω} φ − f^{t,ω}(s, ω̃, y, ∂_ω φ)` with `y = φ(s, ω̃)`, the
derivatives being those of the `C^{1,2}_b` data `X` at the time `s` and path `p`, and
`f^{t,ω}(s, ω̃, ·, ·) = f(s, ω ⊗_t ω̃, ·, ·)`. -/
noncomputable def shiftedOp (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (t : ℝ≥0) (ω : Omega d T 0)
    (X : C12Data d) (s : ℝ≥0) (p : ℝ≥0 → Rd d) (ω' : Omega d T t) (y : ℝ) : ℝ :=
  -X.dt s p - (1 / 2) * Matrix.trace (X.dww s p) - f s (concat ω t ω') y (X.dw s p)

/-- `u` is a viscosity `L`-subsolution of (3.1) (Definition 3.3(i)): `u ∈ C^0_b(Λ)` and for every
`(t, ω) ∈ [0,T) × Ω` and every `φ ∈ 𝒜̲^L u(t,ω)`, `(ℒ^{t,ω}φ)(t, 0) ≤ 0`, the derivatives at
`(t, 0)` being those of any `C^{1,2}_b(Λ̂^t)` extension of `φ`. -/
def IsViscSubL (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (L : ℝ)
    (u : ℝ≥0 → Omega d T 0 → ℝ) : Prop :=
  IsC0b T 0 u ∧ ∀ t ω, t < T → ∀ (φ : ℝ≥0 → Omega d T t → ℝ) (X : C12Data d),
    ExtC12b T t φ X → InTestSub P0 L u t ω φ →
      shiftedOp f t ω X t 0 (zeroPath d T t) (φ t (zeroPath d T t)) ≤ 0

/-- `u` is a viscosity `L`-supersolution of (3.1) (Definition 3.3(i)). -/
def IsViscSuperL (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (L : ℝ)
    (u : ℝ≥0 → Omega d T 0 → ℝ) : Prop :=
  IsC0b T 0 u ∧ ∀ t ω, t < T → ∀ (φ : ℝ≥0 → Omega d T t → ℝ) (X : C12Data d),
    ExtC12b T t φ X → InTestSuper P0 L u t ω φ →
      0 ≤ shiftedOp f t ω X t 0 (zeroPath d T t) (φ t (zeroPath d T t))

/-- Viscosity subsolution (Definition 3.3(ii)): a viscosity `L`-subsolution for some `L ≥ 0`,
the same `L` for all `(t, ω)`. -/
def IsViscSub (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (u : ℝ≥0 → Omega d T 0 → ℝ) : Prop :=
  ∃ L, 0 ≤ L ∧ IsViscSubL P0 f L u

/-- Viscosity supersolution (Definition 3.3(ii)). -/
def IsViscSuper (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (u : ℝ≥0 → Omega d T 0 → ℝ) : Prop :=
  ∃ L, 0 ≤ L ∧ IsViscSuperL P0 f L u

/-- Viscosity solution (Definition 3.3(iii)). -/
def IsViscSol (P0 : Measure (Omega d T 0)) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (u : ℝ≥0 → Omega d T 0 → ℝ) : Prop :=
  IsViscSub P0 f u ∧ IsViscSuper P0 f u

end ViscosityPPDE.Comparison



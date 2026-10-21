-- Prove2me | Definitions.Def_DCPenalty_Penalty_Stationarity
-- name    : DCPenalty_Penalty_Stationarity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:30.263992+00:00
-- url     : https://prove2.me/theorems/58ed9965-b89d-4482-94da-12417236a56b
-- title:
--   (1.17), (2.2), (2.3), Definition 2.1, pp. 6–7 — B-stationarity, Y_J(x̄), C_J(x̄) and the pointwise Slater constraint qualification
-- statement:
--   For the constrained DC program (1.1), with $\mathcal T$ the Bouligand tangent cone and $f'(x;d)=\lim_{\tau\downarrow 0}\big(f(x+\tau d)-f(x)\big)/\tau$ the one-sided directional derivative (p. 5), this file defines:
--
--   1. **B-stationarity** (1.17): $\bar x\in\Omega$ is a B-stationary point of (1.1) if
--   $$
--   F'(\bar x;d)\ge 0\qquad\forall d\in\mathcal T_\Omega(\bar x);
--   $$
--   2. for $\bar x\in\Omega$ and $\mathbb J=(j_1,\dots,j_I)$, the convex inner approximation (2.2)
--   $$
--   Y_{\mathbb J}(\bar x)=\{x\in X:\ \phi_i(x)+\zeta_i(x)-\ell_{\psi_{i,j_i}}(x;\bar x)\le 0\ \ \forall i\in\mathcal I\};
--   $$
--   3. the linearized cone (2.3)
--   $$
--   C_{\mathbb J}(\bar x)=\{d\in\mathcal T_X(\bar x):\ \nabla\phi_i(\bar x)^Td+\zeta_i'(\bar x;d)-\nabla\psi_{i,j_i}(\bar x)^Td\le 0\ \ \forall i\in\mathcal I_=(\bar x)\};
--   $$
--   4. the **pointwise Slater constraint qualification** (PSCQ, Definition 2.1): for every $\mathbb J\in\mathcal J(\bar x)$ there is some $d_{\mathbb J}\in\mathcal T_X(\bar x)$ with
--   $$
--   \nabla\phi_i(\bar x)^Td_{\mathbb J}+\zeta_i'(\bar x;d_{\mathbb J})-\nabla\psi_{i,j_i}(\bar x)^Td_{\mathbb J}<0\qquad\forall i\in\mathcal I_=(\bar x). \tag{2.5}
--   $$
--
--   The direction $d_{\mathbb J}$ may depend on $\mathbb J$. The PSCQ is the constraint qualification under which the paper's penalty method reaches B-stationary points.
--
--   **Formalization Note** The directional derivative is the published predicate `ClarkeGradients.MaxFunctions.HasOneSidedDirDeriv f x d c` (the limit along $\tau\to 0^+$ exists and equals $c$). B-stationarity therefore asserts that $F'(\bar x;d)$ *exists* and is $\ge 0$; $\zeta_i'(\bar x;d)$ enters (2.3) and (2.5) as "the limit exists and the inequality holds for it" (it always exists under the standing assumptions, since $\zeta_i$ is convex on the open set $\mathcal S\ni\bar x$). The page's preamble of Definition 2.1 ($\bar x\in\Omega$, $\mathcal I_=(\bar x)\neq\emptyset$) is kept as separate hypotheses of each theorem that uses the PSCQ.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 6, (1.17), (2.2), (2.3); p. 7, Definition 2.1, (2.5)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem

namespace DCPenalty.Penalty

open ClarkeGradients.MaxFunctions

namespace DCProblem

variable {n m : ℕ} (P : DCProblem n m)

/-- (1.17) for `f = F`, `Y = Ω`: `x` is a B-stationary point of problem (1.1) if `x ∈ Ω` and, for
every `d ∈ 𝒯_Ω(x)`, the one-sided directional derivative `F′(x; d)` exists and is `≥ 0`. -/
def IsBStationary (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ P.Ω ∧ ∀ d ∈ tangentConeB P.Ω x, ∃ c, HasOneSidedDirDeriv P.F x d c ∧ 0 ≤ c

/-- (2.2): `Y_𝕁(x̄) = {x ∈ X | φ_i(x) + ζ_i(x) − ℓ_{ψ_{i,j_i}}(x; x̄) ≤ 0, ∀ i ∈ 𝓘}`. -/
noncomputable def Y (jj : (i : Fin m) → Fin (P.J i.succ)) (xbar : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ P.X ∧ ∀ i, P.φ i.succ x + P.ζ i.succ x - lin (P.ψ i.succ (jj i)) xbar x ≤ 0}

/-- (2.3): `C_𝕁(x̄) = {d ∈ 𝒯_X(x̄) | ∇φ_i(x̄)ᵀd + ζ_i′(x̄; d) − ∇ψ_{i,j_i}(x̄)ᵀd ≤ 0, ∀ i ∈ 𝓘_=(x̄)}`,
with `ζ_i′(x̄; d)` the one-sided directional derivative. -/
def C (jj : (i : Fin m) → Fin (P.J i.succ)) (xbar : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {d | d ∈ tangentConeB P.X xbar ∧ ∀ i ∈ P.Ieq xbar, ∃ c, HasOneSidedDirDeriv (P.ζ i.succ) xbar d c ∧
    fderiv ℝ (P.φ i.succ) xbar d + c - fderiv ℝ (P.ψ i.succ (jj i)) xbar d ≤ 0}

/-- Definition 2.1, (2.5): the pointwise Slater constraint qualification at `x̄`: for every
`𝕁 ∈ 𝓙(x̄)` there is `d_𝕁 ∈ 𝒯_X(x̄)` with
`∇φ_i(x̄)ᵀd_𝕁 + ζ_i′(x̄; d_𝕁) − ∇ψ_{i,j_i}(x̄)ᵀd_𝕁 < 0` for all `i ∈ 𝓘_=(x̄)`.
(The page's standing hypotheses `x̄ ∈ Ω`, `𝓘_=(x̄) ≠ ∅` are kept separate in each theorem.) -/
def PSCQ (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ jj ∈ P.Jtup xbar, ∃ d ∈ tangentConeB P.X xbar, ∀ i ∈ P.Ieq xbar,
    ∃ c, HasOneSidedDirDeriv (P.ζ i.succ) xbar d c ∧
      fderiv ℝ (P.φ i.succ) xbar d + c - fderiv ℝ (P.ψ i.succ (jj i)) xbar d < 0

end DCProblem

end DCPenalty.Penalty



-- Prove2me | Definitions.Def_HoneycombCodes_R2MQC
-- name    : HoneycombCodes_R2MQC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:28:21.067305+00:00
-- url     : https://prove2.me/theorems/14b525b2-b5e8-4c05-8bce-1c9cd3b9ae1d
-- title:
--   Normalized 2MQC exponent $R_{2MQC}(\delta)$, $\lambda_\delta$, $A_\delta$, $\Psi_\delta$, $\mathcal E$, $F_\delta$ and $R_{EB}$
-- statement:
--   For $0\le v\le u\le 1$ define
--
--   $$
--   D(u,v)=u^2(1-v^2)+v^2(u+v^2),\qquad \lambda_\delta(u,v)=\frac{(u^2-v^2)^2+2\delta u^2(1+u)}{D(u,v)},\qquad \lambda_\delta(0,0)=2\delta,
--   $$
--
--   $$
--   A_\delta=\min\{1,\lambda_\delta\},\qquad \Psi_\delta(u,v)=1+g(u^2)-g(A_\delta(u,v))-g(v^2),\qquad
--   \mathcal E(u,v,A)=\frac{A\,D(u,v)-(u^2-v^2)^2}{2u^2(1+u)}.
--   $$
--
--   The **normalized 2MQC exponent** is
--
--   $$
--   R_{2MQC}(\delta)=\inf\bigl\{\Psi_\delta(u,v): 0\le v\le u\le 1,\ v^2(u^2-v^2)<2\delta u^2(1-v^2)\bigr\}.
--   $$
--
--   The module also names the closed feasible set $F_\delta=\{0\le v\le u\le 1,\ v^2(u^2-v^2)\le 2\delta u^2(1-v^2)\}$ of (126), a **minimizing 2MQC point** (a point of $F_\delta$ at which $\Psi_\delta$ attains its minimum over $F_\delta$), and $R_{EB}(\delta)=1-g(2\delta)$.
--
--   **Formalization Note** Defined by the paper's displays (122)–(124) in the normalized variables of [AG26]; the origin is assigned $\lambda_\delta(0,0)=2\delta$ explicitly (Lean's $0/0=0$ would give $0$). $F_\delta$ is named `Fset` to avoid a clash with $F_\delta(\tau)$ of (2).
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.2, eqs. (122)–(126), pp.60–61 (PDF 62–63); R_EB: eq. (129), p.61 (PDF 63)

import Mathlib
import Definitions.Def_HoneycombCodes_H2

set_option autoImplicit false

namespace HoneycombCodes

/-- `D(u, v) = u²(1 − v²) + v²(u + v²)`, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for
Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.2, eq. (122), p.60 (PDF 62). -/
def Dfun (u v : ℝ) : ℝ :=
  u ^ 2 * (1 - v ^ 2) + v ^ 2 * (u + v ^ 2)

/-- `λ_δ(u, v) = ((u² − v²)² + 2δu²(1 + u))/D(u, v)`, with the continuous extension
`λ_δ(0, 0) = 2δ`, arXiv:2608.20287v2, eq. (122), p.60 (PDF 62).

**Formalization Note.** The value at the origin is set explicitly to `2δ` (Lean's `0/0 = 0` would
give `0`). -/
noncomputable def lamDelta (δ u v : ℝ) : ℝ :=
  if u = 0 ∧ v = 0 then 2 * δ
  else ((u ^ 2 - v ^ 2) ^ 2 + 2 * δ * u ^ 2 * (1 + u)) / Dfun u v

/-- `A_δ(u, v) = min{1, λ_δ(u, v)}`, arXiv:2608.20287v2, eq. (123), p.60 (PDF 62). -/
noncomputable def Adelta (δ u v : ℝ) : ℝ :=
  min 1 (lamDelta δ u v)

/-- `Ψ_δ(u, v) = 1 + g(u²) − g(A_δ(u, v)) − g(v²)`, arXiv:2608.20287v2, p.60 (PDF 62). -/
noncomputable def PsiDelta (δ u v : ℝ) : ℝ :=
  1 + g (u ^ 2) - g (Adelta δ u v) - g (v ^ 2)

/-- The unoptimized error functional (125), `E(u, v, A) = (A D(u, v) − (u² − v²)²)/(2u²(1 + u))`
(for `u > 0`), arXiv:2608.20287v2, p.60 (PDF 62). -/
noncomputable def Efun (u v A : ℝ) : ℝ :=
  (A * Dfun u v - (u ^ 2 - v ^ 2) ^ 2) / (2 * u ^ 2 * (1 + u))

/-- Strict 2MQC pair feasibility, the constraint of (124): `0 ≤ v ≤ u ≤ 1` and
`v²(u² − v²) < 2δu²(1 − v²)`, arXiv:2608.20287v2, p.60 (PDF 62). -/
def StrictFeasible2MQC (δ u v : ℝ) : Prop :=
  0 ≤ v ∧ v ≤ u ∧ u ≤ 1 ∧ v ^ 2 * (u ^ 2 - v ^ 2) < 2 * δ * u ^ 2 * (1 - v ^ 2)

/-- The **normalized 2MQC exponent** of [AG26] as recalled in arXiv:2608.20287v2, eq. (124),
p.60 (PDF 62): `R_2MQC(δ) = inf { Ψ_δ(u, v) : 0 ≤ v ≤ u ≤ 1, v²(u² − v²) < 2δu²(1 − v²) }`.

**Formalization Note.** Defined by the paper's display (124) in the normalized variables of
[AG26, Eqs. (43)–(46), Corollary 24]; it is not re-derived from the channel. A real `sInf` of the
objective values over the strictly feasible pairs. -/
noncomputable def R2MQC (δ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ u v : ℝ, StrictFeasible2MQC δ u v ∧ r = PsiDelta δ u v}

/-- The closed feasible set (126),
`F_δ = {(u, v) : 0 ≤ v ≤ u ≤ 1, v²(u² − v²) ≤ 2δu²(1 − v²)}`, arXiv:2608.20287v2, Lemma D.2,
p.61 (PDF 63). Named `Fset` to avoid a clash with the MRRW objective `F_δ(τ)` of (2). -/
def Fset (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ^ 2 * (p.1 ^ 2 - p.2 ^ 2) ≤ 2 * δ * p.1 ^ 2 * (1 - p.2 ^ 2)}

/-- A **minimizing 2MQC point**: a point of `F_δ` at which `Ψ_δ` attains its minimum over `F_δ`
("Let (u, v) minimize (127)", Proposition D.4, arXiv:2608.20287v2, p.62 (PDF 64)). -/
def IsR2MQCMinimizer (δ u v : ℝ) : Prop :=
  (u, v) ∈ Fset δ ∧ ∀ p ∈ Fset δ, PsiDelta δ u v ≤ PsiDelta δ p.1 p.2

/-- `R_EB(δ) = 1 − g(2δ)`, arXiv:2608.20287v2, eq. (129), p.61 (PDF 63). -/
noncomputable def REB (δ : ℝ) : ℝ :=
  1 - g (2 * δ)

end HoneycombCodes



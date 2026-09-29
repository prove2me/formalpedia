-- Prove2me | Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
-- name    : PolyhedralSOC_Shared_IsPolyhedralApprox
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:44:59.866734+00:00
-- url     : https://prove2.me/theorems/cf6e1a75-a828-417f-a28e-00af1acbf385
-- title:
--   Polyhedral $\varepsilon$-approximation of the Lorentz cone
-- statement:
--   Let $\varepsilon$ be a real number and $k,p,q$ natural numbers. A **polyhedral $\varepsilon$-approximation** of the Lorentz cone $L^k$ is a *linear* mapping
--   $$\Pi(y,t,u):\mathbb R^k\times\mathbb R\times\mathbb R^{p}\to\mathbb R^{q}$$
--   such that
--   1. if $(y,t)\in L^k$, then there exists $u\in\mathbb R^{p}$ with $\Pi(y,t,u)\ge 0$;
--   2. if $(y,t)\in\mathbb R^k\times\mathbb R$ is such that $\Pi(y,t,u)\ge0$ for some $u$, then $\|y\|_2\le(1+\varepsilon)t$.
--
--   Here $\ge 0$ is componentwise. Geometrically, the homogeneous linear system $\Pi(y,t,u)\ge0$ defines a polyhedral cone whose projection onto the $(y,t)$-space contains $L^k$ and is contained in its "$(1+\varepsilon)$-extension". The number $p$ is the dimension of the auxiliary vector $u$ and $q$ the image dimension (the number of linear inequalities; an equation counts as two).
--
--   **Formalization Note** $\Pi$ is an $\mathbb R$-linear map `(Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)`; linearity is essential, since with an arbitrary map $\Pi(y,t)=t-\|y\|_2$ would be an exact approximation of size $p=0$, $q=1$. The paper fixes $\varepsilon>0$ before the definition; the definition itself does not need the sign (for $k\ge1$ clause 2 applied to $((1,0,\dots,0),1)\in L^k$ already forces $\varepsilon\ge0$).
--
--   This definition is shared by two missions of this series: I (upper bound: Theorem 1.1, p. 195, and the construction of §2, pp. 198–201) and II (lower bound: Proposition 3.1, p. 202, and its proof).
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 194, definition of a polyhedral ε-approximation, clauses (i)–(ii)

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone

namespace PolyhedralSOC.Shared

/-- A polyhedral `ε`-approximation of the Lorentz cone `L^k`
(Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), p. 194 (PDF p. 2)): a **linear** mapping
`Π(y, t, u) : ℝ^k × ℝ × ℝ^p → ℝ^q` such that
(i) if `(y, t) ∈ L^k`, then there exists `u ∈ ℝ^p` with `Π(y, t, u) ≥ 0`;
(ii) if `Π(y, t, u) ≥ 0` for some `u`, then `‖y‖₂ ≤ (1 + ε) t`.
Here `≥ 0` is componentwise (the pointwise order on `Fin q → ℝ`), and `p`, `q` are the
dimension of the auxiliary vector `u` and the image dimension. -/
def IsPolyhedralApprox (k p q : ℕ) (ε : ℝ)
    (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)) : Prop :=
  (∀ (y : Fin k → ℝ) (t : ℝ), (y, t) ∈ LorentzCone k → ∃ u : Fin p → ℝ, 0 ≤ P (y, t, u)) ∧
  (∀ (y : Fin k → ℝ) (t : ℝ) (u : Fin p → ℝ), 0 ≤ P (y, t, u) → eucNorm y ≤ (1 + ε) * t)

end PolyhedralSOC.Shared



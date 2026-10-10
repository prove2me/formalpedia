-- Prove2me | Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
-- name    : GraphLQGame_Equilibrium_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:25:45.867879+00:00
-- url     : https://prove2.me/theorems/76fa3056-fec1-4b9e-82a9-82205d54193a
-- title:
--   The function $Q_G$ (2.4), the ODE $f' = cQ_G'(f)$, the matrices $P_G(t)$ (2.5) and the feedback $\alpha_i^G$ of Theorem 2.5
-- statement:
--   Let $G$ be a finite graph on $n$ vertices with random-walk Laplacian $L_G$, and let $c,T>0$.
--
--   1. $Q_G(x) := \det(I-xL_G)^{1/n}$ (2.4).
--   2. A function $f$ **solves** $f'(t)=cQ'(f(t))$, $f(0)=0$ on $[0,T]$ if $f(0)=0$, $f$ is continuous and nonnegative on $[0,T]$, and at every $t\in[0,T]$ its (one-sided at the endpoints) derivative within $[0,T]$ equals $cQ'(f(t))$.
--   3. $P_G(t) := -f'_G(T-t)\,L_G\big(I-f_G(T-t)L_G\big)^{-1}$ (2.5), written with $f'_G(T-t)=cQ_G'(f_G(T-t))$.
--   4. The feedback $\alpha^G_i(t,x) := -e_i^\top P_G(t)x$ for $t\in[0,T]$.
--
--   These are the objects of the explicit Nash equilibrium of Theorem 2.5.
--
--   **Formalization Note** $Q_G$ uses `Real.rpow` with exponent $(n:\mathbb R)^{-1}$; $Q'$ is `deriv Q`. In $P_G$, $f'_G(T-t)$ is replaced by its value $cQ_G'(f_G(T-t))$ under the ODE, which avoids a two-sided derivative of $f$ at the endpoint. The feedback is set to $0$ for $t\notin[0,T]$ (values there are never used), so that its Borel measurability does not depend on the values of $f$ off $[0,T]$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Theorem 2.5, §2.2, p. 6, (2.4)–(2.5)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Graph

namespace GraphLQGame.Equilibrium

open EthierKurtz

/-- `Q_G(x) = det(I − x L_G)^{1/n}` (2.4), Theorem 2.5, p. 6.

Formalization Note: `Real.rpow` with exponent `(n : ℝ)⁻¹`. The formula is total; the paper uses it
for `x ∈ ℝ₊`, where the determinant is positive (stated in Theorem 2.5). -/
noncomputable def QG {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : ℝ) : ℝ :=
  (Matrix.det (1 - x • lap G)) ^ ((n : ℝ)⁻¹)

/-- `f : [0, T] → ℝ₊` solves `f'(t) = c Q'(f(t))`, `f(0) = 0` (Theorem 2.5, p. 6): `f(0) = 0`, `f`
is continuous and nonnegative on `[0, T]`, and at each `t ∈ [0, T]` it has derivative
`c Q'(f(t))` within `[0, T]` (one-sided at the endpoints). `Q'` is `deriv Q`.

Formalization Note: only the values of `f` on `[0, T]` are constrained. -/
def IsFSol (c T : ℝ) (Q : ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ ContinuousOn f (Set.Icc 0 T) ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ f t) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt f (c * deriv Q (f t)) (Set.Icc 0 T) t

/-- `P_G(t) = −f'_G(T − t) L_G (I − f_G(T − t) L_G)⁻¹` (2.5), Theorem 2.5, p. 6.

Formalization Note: `f'_G(T − t)` is written as its value `c Q'_G(f_G(T − t))` under the ODE,
which avoids a two-sided derivative of `f` at the endpoint `T − t = 0`. -/
noncomputable def PG {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c T : ℝ)
    (f : ℝ → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  -(c * deriv (QG G) (f (T - t))) • lap G * (1 - f (T - t) • lap G)⁻¹

/-- The equilibrium feedback `α_i^G(t, x) = −e_iᵀ P_G(t) x` (Theorem 2.5, p. 6).

Formalization Note: controls are only used on `[0, T]`; outside `[0, T]` this control is set to
`0`, so that its Borel measurability does not depend on the values of `f` off `[0, T]`, which the
ODE does not constrain. -/
noncomputable def alphaG {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c T : ℝ)
    (f : ℝ → ℝ) (i : Fin n) (t : ℝ) (x : SDEState n) : ℝ :=
  if t ∈ Set.Icc (0 : ℝ) T then -((PG G c T f t).mulVec (fun j => x j)) i else 0

end GraphLQGame.Equilibrium



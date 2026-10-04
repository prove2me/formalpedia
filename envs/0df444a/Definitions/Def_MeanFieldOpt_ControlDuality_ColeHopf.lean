-- Prove2me | Definitions.Def_MeanFieldOpt_ControlDuality_ColeHopf
-- name    : MeanFieldOpt_ControlDuality_ColeHopf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:42:56.888548+00:00
-- url     : https://prove2.me/theorems/69dc9182-56f4-4491-bfa9-b77e0d7641a2
-- title:
--   Step functions $\mathsf{SF}_+$ and the Cole–Hopf solution $\Phi_\gamma$ of the Parisi PDE
-- statement:
--   **Step functions.** The class $\mathsf{SF}_+$ (Eq. (4.3)) consists of the functions
--   $$\gamma=\sum_{i=1}^m \gamma_i\,\mathbb I_{[t_{i-1},t_i)},\qquad 0=t_0<t_1<\dots<t_m=1,\quad \gamma_i\ge 0,$$
--   on $[0,1)$. A function of $\mathsf{SF}_+$ is given here by its data $(m,(t_i),(\gamma_i))$.
--
--   **Cole–Hopf solution.** Let $r(t)=\xi'(1)-\xi'(t)$ and let $G\sim\mathsf N(0,1)$. The solution $\Phi_\gamma:[0,1]\times\mathbb R\to\mathbb R$ of the Parisi PDE
--   $$\partial_t\Phi_\gamma+\tfrac12\xi''(t)\big(\partial_x^2\Phi_\gamma+\gamma(t)(\partial_x\Phi_\gamma)^2\big)=0,\qquad \Phi_\gamma(1,x)=|x|,$$
--   is constructed backwards in time (Eq. (7.3)): $\Phi_\gamma(1,x)=|x|$, and for $i=m,m-1,\dots,1$ and $t\in[t_{i-1},t_i)$,
--   $$\Phi_\gamma(t,x)=\frac1{\gamma_i}\log\mathbb E\exp\Big\{\gamma_i\,\Phi_\gamma\big(t_i,\,x+\sqrt{r(t)-r(t_i)}\,G\big)\Big\}.$$
--   When $\gamma_i=0$ the formula is replaced by its limit as $\gamma_i\to0$, the heat semigroup $\Phi_\gamma(t,x)=\mathbb E\,\Phi_\gamma\big(t_i,x+\sqrt{r(t)-r(t_i)}\,G\big)$.
--
--   $\Phi_\gamma$ enters the Parisi functional through $\Phi_\gamma(0,0)$ and the candidate value function through its Legendre transform.
--
--   **Formalization Note** $\gamma$ is a function on $\mathbb R$ that vanishes outside $[0,1)$; its value at the single point $t=1$ (the paper extends $\gamma$ by continuity there) never matters, since $\gamma$ enters only through integrals. The expectation over $G$ is the integral against `gaussianReal 0 1`. The case $\gamma_i=0$ (allowed in $\mathsf{SF}_+$) is the heat-semigroup branch; without it the formula would divide by zero. $\Phi_\gamma(t,\cdot)$ is defined as $|x|$ for $t\ge1$; negative times are never used. $\Phi_\gamma$ is computed from the given breakpoints; it does not depend on the representation of $\gamma$, but no statement needs this.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 11, Eq. (4.3) (SF_+); p. 34, Eq. (7.1) (Parisi PDE with Φ_γ(1,x) = |x|); p. 35, Eq. (7.3) (Cole–Hopf recursion)

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_Mixture

open MeasureTheory ProbabilityTheory

namespace MeanFieldOpt.ControlDuality

/-- A representation of a nonnegative step function `γ ∈ SF₊` (arXiv:2001.00904v1, Eq. (4.3),
p. 11): breakpoints `0 = t_0 < t_1 < ⋯ < t_m = 1` and values `a_i ≥ 0`. With 0-based indices,
piece `i : Fin m` is `[t i.castSucc, t i.succ)` and carries the value `a i`. -/
structure SFData where
  m : ℕ
  t : Fin (m + 1) → ℝ
  a : Fin m → ℝ
  t_zero : t 0 = 0
  t_last : t (Fin.last m) = 1
  t_strictMono : StrictMono t
  a_nonneg : ∀ i, 0 ≤ a i

namespace SFData

/-- The step function `γ = ∑_i a_i 𝕀_{[t_{i-1}, t_i)}` on the real line (zero outside `[0, 1)`). -/
noncomputable def toFun (d : SFData) (s : ℝ) : ℝ :=
  ∑ i : Fin d.m, if d.t i.castSucc ≤ s ∧ s < d.t i.succ then d.a i else 0

/-- Breakpoint `t_k` for `k ≤ m` (natural-number index; `1` beyond `m`). -/
noncomputable def tt (d : SFData) (k : ℕ) : ℝ :=
  if h : k ≤ d.m then d.t ⟨k, Nat.lt_succ_of_le h⟩ else 1

/-- Value of the piece with 0-based index `k < m` (natural-number index; `0` beyond). -/
noncomputable def aa (d : SFData) (k : ℕ) : ℝ :=
  if h : k < d.m then d.a ⟨k, h⟩ else 0

end SFData

/-- One Cole–Hopf step (Eq. (7.3), p. 35). Given the value `h = Φ(t_i, ·)` at the right end of a
piece on which `γ ≡ g`, and the variance `Δ = r(t) − r(t_i) = ξ'(t_i) − ξ'(t)`,
`Φ(t, x) = (1/g) log E exp{g h(x + √Δ G)}`, `G ∼ N(0,1)`. For `g = 0` the formula divides by
zero; its limit, the heat semigroup `Φ(t, x) = E h(x + √Δ G)`, is used instead. -/
noncomputable def coleHopfStep (g Δ : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  if g = 0 then ∫ y, h (x + Real.sqrt Δ * y) ∂(gaussianReal 0 1)
  else (1 / g) * Real.log (∫ y, Real.exp (g * h (x + Real.sqrt Δ * y)) ∂(gaussianReal 0 1))

/-- `PhiNode ξ d n = Φ_γ(t_{m-n}, ·)`: the Cole–Hopf solution at the breakpoint `t_{m-n}`,
obtained from the terminal condition `Φ_γ(1, x) = |x|` (Eq. (7.1)) by `n` backward steps. -/
noncomputable def PhiNode (ξ : Mixture) (d : SFData) : ℕ → ℝ → ℝ
  | 0 => fun x => |x|
  | n + 1 => coleHopfStep (d.aa (d.m - (n + 1)))
      (ξ.xi' (d.tt (d.m - n)) - ξ.xi' (d.tt (d.m - (n + 1)))) (PhiNode ξ d n)

/-- The solution `Φ_γ(t, x)` of the Parisi PDE (7.1) with `Φ_γ(1, x) = |x|`, for `γ ∈ SF₊` given
by `d`, built by the Cole–Hopf recursion (7.3), p. 35: for `t` in the piece
`[t_i, t_{i+1})` (0-based), `Φ_γ(t, ·)` is one Cole–Hopf step with value `a_i` and variance
`ξ'(t_{i+1}) − ξ'(t)` applied to `Φ_γ(t_{i+1}, ·)`. For `t ≥ 1` it is `|x|`; times `t < 0` are
never used (the value there is `0`). -/
noncomputable def PhiSF (ξ : Mixture) (d : SFData) (t x : ℝ) : ℝ :=
  if 1 ≤ t then |x|
  else ∑ i : Fin d.m,
    if d.t i.castSucc ≤ t ∧ t < d.t i.succ then
      coleHopfStep (d.a i) (ξ.xi' (d.t i.succ) - ξ.xi' t) (PhiNode ξ d (d.m - (i.val + 1))) x
    else 0

end MeanFieldOpt.ControlDuality



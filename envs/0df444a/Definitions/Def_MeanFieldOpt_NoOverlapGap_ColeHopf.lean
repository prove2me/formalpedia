-- Prove2me | Definitions.Def_MeanFieldOpt_NoOverlapGap_ColeHopf
-- name    : MeanFieldOpt_NoOverlapGap_ColeHopf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:06:25.523012+00:00
-- url     : https://prove2.me/theorems/01e45919-9a8d-4139-bc41-63d117d8ee18
-- title:
--   Step functions $\mathrm{SF}_+$ (6.1) and the Cole–Hopf solution $\Phi^\gamma$ of the Parisi PDE (7.3)
-- statement:
--   **Step functions.** The space of non-negative step functions is (Eq. (6.1))
--
--   $$\mathrm{SF}_+ = \Big\{ g = \sum_{i=1}^m a_i\, \mathbb I_{[t_{i-1}, t_i)} \;:\; 0 = t_0 < t_1 < \dots < t_m = 1,\ a_i \in \mathbb R_{\ge 0},\ m \in \mathbb N \Big\}.$$
--
--   **The Parisi PDE.** For $\gamma \in \mathrm{SF}_+$ and a mixture $\xi$, the Parisi PDE (1.5) is
--
--   $$\partial_t \Phi(t,x) + \tfrac12 \xi''(t)\big(\partial_x^2 \Phi(t,x) + \gamma(t)(\partial_x \Phi(t,x))^2\big) = 0, \qquad \Phi(1,x) = |x| .$$
--
--   Its solution is given by the **Cole–Hopf recursion** (7.3). Let $r(t) = \xi'(1) - \xi'(t)$ and $G \sim \mathsf N(0,1)$. Starting from $\Phi(1,x) = |x|$, for $i = m, m-1, \dots, 1$ and $t \in [t_{i-1}, t_i)$,
--
--   $$\Phi(t,x) = \frac{1}{\gamma_i} \log \mathbb E \exp\Big\{ \gamma_i\, \Phi\big(t_i,\, x + \sqrt{r(t) - r(t_i)}\, G\big) \Big\}, \qquad \gamma_i := a_i,$$
--
--   where $r(t) - r(t_i) = \xi'(t_i) - \xi'(t) \ge 0$. When $\gamma_i = 0$ the formula is read as its limit $\gamma_i \to 0$, the heat semigroup
--
--   $$\Phi(t,x) = \mathbb E\, \Phi\big(t_i,\, x + \sqrt{r(t) - r(t_i)}\, G\big).$$
--
--   This object is the explicit solution from which $\Phi^\gamma$ for general $\gamma \in \mathscr L$ and the Parisi functional are built.
--
--   **Formalization Note** A step function is given by its data $(m, t, a)$ with $m \ge 1$; `toFun` is the step function on $[0,1)$. The recursion is computed from the data. The case $\gamma_i = 0$ is a separate branch (the heat semigroup), since Lean's $1/0 = 0$ would otherwise make $\Phi$ vanish on that piece. Gaussian expectations are integrals against `gaussianReal 0 1`. At $t = 1$, and as an irrelevant junk value outside $[0,1]$, $\Phi(t,x) = |x|$. The paper prints "(with $\Phi(t,x) = |x|$.)" for the terminal condition $\Phi(1,x) = |x|$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 23, Eq. (6.1); p. 3, Eq. (1.5); p. 35, Eq. (7.3)

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldOpt.NoOverlapGap

/-- Data of a function in `SF₊` (6.1), p. 23: `g = Σ_{i=1}^m a_i 𝕀_{[t_{i-1}, t_i)}` with
`0 = t_0 < t_1 < ⋯ < t_m = 1` and `a_i ≥ 0`. Index `i : Fin m` is the paper's piece `i + 1`. -/
structure SFData where
  m : ℕ
  one_le_m : 1 ≤ m
  t : Fin (m + 1) → ℝ
  t_strictMono : StrictMono t
  t_zero : t 0 = 0
  t_last : t (Fin.last m) = 1
  a : Fin m → ℝ
  a_nonneg : ∀ i, 0 ≤ a i

namespace SFData

/-- The step function `Σ_i a_i 𝕀_{[t_{i-1}, t_i)}`. -/
noncomputable def toFun (d : SFData) (s : ℝ) : ℝ :=
  ∑ i : Fin d.m, if d.t i.castSucc ≤ s ∧ s < d.t i.succ then d.a i else 0

/-- Breakpoint `t_j` for `j ≤ m` (and `1` beyond). -/
noncomputable def tN (d : SFData) (j : ℕ) : ℝ :=
  if h : j ≤ d.m then d.t ⟨j, Nat.lt_succ_of_le h⟩ else 1

/-- Value `γ_j` on the paper's piece `[t_{j-1}, t_j)`, `1 ≤ j ≤ m` (and `0` otherwise). -/
noncomputable def aN (d : SFData) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ d.m then d.a ⟨j - 1, by omega⟩ else 0

end SFData

/-- One Cole–Hopf step (7.3), p. 35: given `f = Φ(u, ·)` and the constant value `g` of `γ` on
`[s, u)`, returns `Φ(s, ·)`:
`Φ(s,x) = (1/g) log E exp{ g f(x + √(r(s) − r(u)) G) }`, `G ∼ N(0,1)`, `r(t) = ξ'(1) − ξ'(t)`,
so `r(s) − r(u) = ξ'(u) − ξ'(s)`. For `g = 0` (allowed in `SF₊`) the formula is read as its
limit, the heat semigroup `Φ(s,x) = E f(x + √(r(s) − r(u)) G)`. -/
noncomputable def coleHopfStep (ξ : Mixture) (g s u : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if g = 0 then
    ∫ z, f (x + Real.sqrt (ξ.xi' u - ξ.xi' s) * z) ∂(gaussianReal 0 1)
  else
    (1 / g) * Real.log
      (∫ z, Real.exp (g * f (x + Real.sqrt (ξ.xi' u - ξ.xi' s) * z)) ∂(gaussianReal 0 1))

/-- `phiNode ξ d k = Φ(t_{m-k}, ·)`: the Cole–Hopf recursion run downward from
`Φ(t_m, x) = Φ(1, x) = |x|` (terminal condition of (1.5)). -/
noncomputable def phiNode (ξ : Mixture) (d : SFData) : ℕ → ℝ → ℝ
  | 0 => fun x => |x|
  | k + 1 => coleHopfStep ξ (d.aN (d.m - k)) (d.tN (d.m - k - 1)) (d.tN (d.m - k))
      (phiNode ξ d k)

open Classical in
/-- The Cole–Hopf solution `Φ^γ(t, x)` of the Parisi PDE (1.5) for `γ ∈ SF₊` given by the data
`d` (Eq. (7.3), p. 35): for `t ∈ [t_{j-1}, t_j)` it is one Cole–Hopf step from `Φ(t_j, ·)` with
`γ_j`; at `t = 1` (and, as a junk value, outside `[0,1]`) it is `|x|`. -/
noncomputable def PhiSF (ξ : Mixture) (d : SFData) (t x : ℝ) : ℝ :=
  if h : ∃ j : ℕ, 1 ≤ j ∧ j ≤ d.m ∧ d.tN (j - 1) ≤ t ∧ t < d.tN j then
    coleHopfStep ξ (d.aN (Nat.find h)) t (d.tN (Nat.find h))
      (phiNode ξ d (d.m - Nat.find h)) x
  else |x|

end MeanFieldOpt.NoOverlapGap



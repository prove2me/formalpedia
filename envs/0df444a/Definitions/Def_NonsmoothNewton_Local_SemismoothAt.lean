-- Prove2me | Definitions.Def_NonsmoothNewton_Local_SemismoothAt
-- name    : NonsmoothNewton_Local_SemismoothAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:00:03.953821+00:00
-- url     : https://prove2.me/theorems/62b45fb6-ce3e-4add-9548-4f706d5af998
-- title:
--   Semismooth and $p$-order semismooth maps at a point
-- statement:
--   Let $E$, $G$ be real normed spaces, $F : E \to G$, $x \in E$, and let $\partial F$ be Clarke's generalized Jacobian and $F'(x;h)$ the one-sided directional derivative.
--
--   1. $F$ is **semismooth at $x$** if $F$ is Lipschitz on some neighbourhood of $x$ and, for every direction $h \in E$, the limit
--   $$
--   \lim_{\substack{V \in \partial F(x+th') \\ h' \to h,\ t \downarrow 0}} \{V h'\}
--   $$
--   exists; that is, there is $L \in G$ such that for every $\varepsilon > 0$ there is $\delta > 0$ with $\|V h' - L\| < \varepsilon$ whenever $0 < t < \delta$, $\|h' - h\| < \delta$ and $V \in \partial F(x + th')$.
--
--   2. For a real $p$, $F$ is **$p$-order semismooth at $x$** if it is semismooth at $x$ and
--   $$
--   V h - F'(x;h) = O(\|h\|^{1+p}) \qquad (V \in \partial F(x+h),\ h \to 0),
--   $$
--   that is, there are constants $C$ and $\delta > 0$ such that $\|Vh - F'(x;h)\| \le C \|h\|^{1+p}$ whenever $\|h\| < \delta$ and $V \in \partial F(x+h)$.
--
--   Semismoothness, introduced by Mifflin for functionals and extended here to vector-valued maps, is the regularity under which the generalized-Jacobian Newton method converges superlinearly; $p$-order semismoothness gives convergence of order $1+p$.
--
--   **Formalization Note** The paper's $O(\cdot)$ is pinned to an explicit constant $C$ and radius $\delta$. The paper remarks that $p$-order semismoothness "implies semismoothness" and uses it "in addition" to semismoothness; the definition therefore includes semismoothness, which also guarantees that $F'(x;h)$ exists. The paper's range $0 < p \le 1$ is a hypothesis of every statement that uses the notion, and $\|h\|^{1+p}$ is the real power.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 355 (definition of semismooth) and p. 358 (definition of p-order semismooth)

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology

namespace NonsmoothNewton.Local

/-- Semismoothness, Qi–Sun (1993), p. 355: `F` is locally Lipschitz at `x` and, for every
direction `h`, the limit `lim_{V ∈ ∂F(x + t h'), h' → h, t ↓ 0} V h'` exists (called `L`). -/
def SemismoothAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  (∃ K : NNReal, ∃ U ∈ 𝓝 x, LipschitzOnWith K F U) ∧
  ∀ h : E, ∃ L : G, ∀ ε > 0, ∃ δ > 0, ∀ (t : ℝ) (h' : E), 0 < t → t < δ → ‖h' - h‖ < δ →
    ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + t • h'), ‖V h' - L‖ < ε

/-- `p`-order semismoothness, Qi–Sun (1993), p. 358: `F` is semismooth at `x` and
`V h - F'(x; h) = O(‖h‖^{1+p})` for `V ∈ ∂F(x + h)`, `h → 0`, pinned as: there are `C` and
`δ > 0` with `‖V h - F'(x; h)‖ ≤ C ‖h‖^{1+p}` whenever `‖h‖ < δ` and `V ∈ ∂F(x + h)`.
The paper's range `0 < p ≤ 1` is a hypothesis of every statement that uses it. -/
def POrderSemismoothAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (p : ℝ) (F : E → G) (x : E) : Prop :=
  SemismoothAt F x ∧ ∃ C δ : ℝ, 0 < δ ∧ ∀ h : E, ‖h‖ < δ → ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + h),
    ∀ d : G, HasDirDerivAt F x h d → ‖V h - d‖ ≤ C * ‖h‖ ^ (1 + p)

end NonsmoothNewton.Local



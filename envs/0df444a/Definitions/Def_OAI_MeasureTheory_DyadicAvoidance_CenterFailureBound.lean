-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
-- name    : OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:06:30.485585+00:00
-- url     : https://prove2.me/theorems/a0a64b51-8228-4534-a790-5604ae1c6bec
-- title:
--   Centre atoms and the no-default event of the finite table model
-- statement:
--   Fix $M, d \in \mathbb{N}$. Children are $0,1,\dots,M$, with default child $M$; nodes are words $P$ over $\{0,\dots,M\}$ with $|P| < d$ (finite set $\mathcal{N}_{M,d}$), leaves are words of length exactly $d$ (finite set $\mathcal{L}_{M,d}$), and $\varnothing$ is the root. For $n \in \mathbb{N}$ and $x \in \mathbb{R}$, $\kappa_n(x) = \lfloor 2^{n+2}\{x\} \rfloor \in \{0,\dots,2^{n+2}-1\}$ is the dyadic key of $x$, where $\{x\} = x - \lfloor x \rfloor$. Boolean values are written $0$ (false) and $1$ (true). Let $b_S : \mathcal{N}_{M,d} \times \{0,\dots,M-1\} \to \mathbb{N}$ and $b_T : \mathcal{L}_{M,d} \to \mathbb{N}$ be selector and terminal resolutions. An outcome is a pair $(\omega_S, \omega_T)$ of a selector table $\omega_S$ (a $\{0,1\}$-valued function on the coordinates $((P,i),j)$ with $0 \le j < 2^{b_S(P,i)+2}$) and a terminal table $\omega_T$ (a $\{0,1\}$-valued function on the coordinates $(L,j)$ with $0 \le j < 2^{b_T(L)+2}$). At a centre $x \in \mathbb{R}$, the exposure of $\omega_S$ is the array $E_x(\omega_S)(P,i) = \omega_S((P,i), \kappa_{b_S(P,i)}(x))$ indexed by $\mathcal{N}_{M,d} \times \{0,\dots,M-1\}$; the centre choice $c_x(P,\omega_S)$ is the least $i < M$ whose selector value at $(P,i)$, read at $x$, equals $1$ (or $M$ if there is none), where selector values at words of length at least $d$ are $0$; and $R_k(\varnothing,\omega_S)$ is the word obtained from the root by $k$ successive centre choices of the table $\omega_S$.
--
--   1. **Centre atom.** For an array $\xi : \mathcal{N}_{M,d} \times \{0,\dots,M-1\} \to \{0,1\}$, the centre atom of $\xi$ at $x$ is the set of all outcomes whose selector table exposes $\xi$ at $x$:
--   $$
--   \mathcal{A}_x(\xi) = \big\{ (\omega_S, \omega_T) : E_x(\omega_S) = \xi \big\}.
--   $$
--
--   2. **No-default event.** The event that the centre route never takes the default child before depth $d$ is
--   $$
--   \mathcal{D}_x = \big\{ (\omega_S, \omega_T) : c_x\big(R_k(\varnothing,\omega_S),\, \omega_S\big) \ne M \ \text{ for every } k < d \big\}.
--   $$
--   Neither event constrains the terminal table, which is nevertheless kept as part of the outcome so that both are events of the full outcome space.
--
--   The centre atoms partition the outcome space, and an outcome lies in $\mathcal{D}_x$ exactly when its exposure at $x$ is not good, i.e. when its centre route avoids the default child at all depths below $d$. The failure estimate at a fixed centre bounds the probability that $x$ is an exceptional centre of the random routed set by the probability of $\mathcal{D}_x$ plus the failure probabilities within the good centre atoms.
--
--   **Formalization Note** Outcomes are elements of `SelectorTable bS × TerminalTable bT`, both events are subsets of this product, and the default child is `Fin.last M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/CenterFailureBound.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/CenterFailureBound.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310.CenterFailureBound

open FiniteTableModel CenterRouteExposure

/-- The actual full-outcome fiber of the center selector exposure. -/
def centerAtom {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (x : ℝ) (ξ : Node M d × Fin M → Bool) :
    Set (SelectorTable bS × TerminalTable bT) :=
  {ω | centerExposure bS x ω.1 = ξ}

/-- No default occurs on the actual center path. Terminal coordinates do not
enter this event, but are retained in the probability space. -/
def noDefaultEvent {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (x : ℝ) : Set (SelectorTable bS × TerminalTable bT) :=
  {ω | ∀ k < d, centerChoice bS x
    (RoutingPath.routeFrom (centerChoice bS x) k [] ω.1) ω.1 ≠ Fin.last M}

end Problem310.CenterFailureBound

end

end OAI



-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
-- name    : OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:13:26.776998+00:00
-- url     : https://prove2.me/theorems/0b383333-974b-4d3d-ad8c-48c4c8c227a4
-- title:
--   The routed random one-periodic set defined by selector and terminal tables
-- statement:
--   Fix $M, d \in \mathbb{N}$. Children are $0,1,\dots,M$, with default child $M$; nodes are words $P$ over $\{0,\dots,M\}$ with $|P| < d$ (finite set $\mathcal{N}_{M,d}$), leaves are words of length exactly $d$ (finite set $\mathcal{L}_{M,d}$), and $\varnothing$ is the root. For $n \in \mathbb{N}$ and $x \in \mathbb{R}$, $\kappa_n(x) = \lfloor 2^{n+2}\{x\} \rfloor \in \{0,\dots,2^{n+2}-1\}$ is the dyadic key of $x$, where $\{x\} = x - \lfloor x \rfloor$. Boolean values are written $0$ (false) and $1$ (true). Let $b_S : \mathcal{N}_{M,d} \times \{0,\dots,M-1\} \to \mathbb{N}$ and $b_T : \mathcal{L}_{M,d} \to \mathbb{N}$ be selector and terminal resolutions. A selector table $\omega_S$ is a $\{0,1\}$-valued function on the coordinates $((P,i),j)$ with $0 \le j < 2^{b_S(P,i)+2}$, and a terminal table $\omega_T$ is a $\{0,1\}$-valued function on the coordinates $(L,j)$ with $L$ a leaf and $0 \le j < 2^{b_T(L)+2}$. The selector value is $s_{\omega_S}(P,i,x) = \omega_S((P,i), \kappa_{b_S(P,i)}(x))$ if $|P| < d$ and $0$ for longer words.
--
--   1. **Selector choice.** For a word $P$ and $x \in \mathbb{R}$, $\operatorname{sc}_{\omega_S}(P,x)$ is the first-success choice: the least $i < M$ with $s_{\omega_S}(P,i,x) = 1$, or the default child $M$ if there is none.
--
--   2. **Routed leaf.** $L_{\omega_S}(x)$ is the leaf reached from the root by $d$ successive selector choices: with $R_0 = \varnothing$ and $R_{k+1} = R_k\,\operatorname{sc}_{\omega_S}(R_k, x)$ (append the chosen child), $L_{\omega_S}(x) = R_d$, a word of length $d$.
--
--   3. **Routed address.** The terminal coordinate consulted at $x$ is $\big(L_{\omega_S}(x),\ \kappa_{b_T(L_{\omega_S}(x))}(x)\big)$.
--
--   4. **Routed set.** For an outcome $\omega = (\omega_S, \omega_T)$,
--   $$
--   B(\omega) = \Big\{ x \in \mathbb{R} : \omega_T\big(L_{\omega_S}(x),\ \kappa_{b_T(L_{\omega_S}(x))}(x)\big) = 1 \Big\}.
--   $$
--
--   The file also proves that the selector choice, the routed leaf and the routed address are one-periodic in $x$: their values at $x+1$ and at $x$ coincide for every table.
--
--   The routed set is the raw random set of the dyadic avoidance construction. A point is routed down a tree of depth $d$ by fair selector coins read at dyadic resolutions, and the terminal label of the leaf it reaches, read at that leaf's resolution, decides membership. Since terminal labels are independent of the selectors, the expected density of $B(\omega)$ over $[0,1]$ equals the probability that a single terminal label is $1$; this is how the density budget $p$ of the construction arises.
--
--   **Formalization Note** The routed leaf is `RoutingPath.routeFrom (selectorChoice b ω) d [] x`, packaged as an element of `List.Vector (Fin (M + 1)) d`, and the routed set is `RandomSetDensity.selectedSet` applied to the routed address map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutedSetDensity.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutedSetDensity.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.RoutedSetDensity

open FiniteTableModel

/-- The actual first-success/default child choice made by the finite selector tables. -/
def selectorChoice {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (x : ℝ) : Child M :=
  OrderedRouting.chooseChild (fun i => selectorValue b ω P i x)

/-- The leaf reached by the root router, as an element of the finite leaf type. -/
def routedLeaf {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (x : ℝ) : Leaf M d :=
  ⟨RoutingPath.routeFrom (selectorChoice b ω) d [] x, by simp⟩

/-- The terminal table coordinate consulted by the complete finite router. -/
def routedAddress {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ω : SelectorTable bS) (x : ℝ) : TerminalAddress bT :=
  terminalAddress bT (routedLeaf bS ω x) x

/-- The raw random periodic set, with both selector and terminal tables explicit. -/
def routedSet {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ω : SelectorTable bS × TerminalTable bT) : Set ℝ :=
  RandomSetDensity.selectedSet (routedAddress bS bT) ω

@[simp] lemma selectorChoice_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (x : ℝ) :
    selectorChoice b ω P (x + 1) = selectorChoice b ω P x := by
  apply OrderedRouting.chooseChild_congr
  intro i
  exact selectorValue_add_one b ω P i x

@[simp] lemma routedLeaf_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (x : ℝ) : routedLeaf b ω (x + 1) = routedLeaf b ω x := by
  apply Subtype.ext
  exact RoutingPath.routeFrom_periodic (selectorChoice b ω) (selectorChoice_add_one b ω) d [] x

@[simp] lemma routedAddress_add_one {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS) (x : ℝ) :
    routedAddress bS bT ω (x + 1) = routedAddress bS bT ω x := by
  simp [routedAddress]

end Problem310.RoutedSetDensity

end

end OAI



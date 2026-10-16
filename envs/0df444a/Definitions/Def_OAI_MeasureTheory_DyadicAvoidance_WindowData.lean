-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:22:16.851156+00:00
-- url     : https://prove2.me/theorems/9554e91f-d1ad-4f7f-bf6d-46fc745dc43a
-- title:
--   Window data: windows of dyadic scales on the edges of a finite tree, with gap conditions
-- statement:
--   This file defines the deterministic window structure that assigns to every edge of a finite tree a window of consecutive scale exponents. Fix natural numbers $q$ (the total number of children of each node), $d$ (the depth), $g$ (the gap) and $r_0$ (a length threshold). Nodes are words over the alphabet $\{0,\dots,q-1\}$, $|P|$ is the length of $P$, and $P\,c$ denotes $P$ followed by the letter $c$.
--
--   1. **Valid window edges.** A word $P$ is a valid window edge if $P \ne \varnothing$ and $|P| \le d$. It stands for the edge of the tree that ends at the node $P$.
--
--   2. **Window data.** Window data with parameters $(q,d,g,r_0)$ consist of functions $r : \mathbb{N} \to \mathbb{N}$ and $a, b, b^{*}$ from words to $\mathbb{N}$. The window length of an edge is $\ell(P) = r(d + 1 - |P|)$, which depends only on the depth of $P$, and the window of $P$ is the integer interval $\{a(P), \dots, b(P)\}$. For all valid window edges $P$ and $Q$ the following are required:
--      - *length:* $\ell(P) \ge 1$ and $\ell(P) \ge r_0$;
--      - *start:* $a(P) \ge 3$;
--      - *endpoint:* $b(P) + 1 = a(P) + \ell(P)$, so the window consists of exactly $\ell(P)$ consecutive integers;
--      - *prefix gap:* if $P$ is a proper prefix of $Q$, then $b(P) + g < a(Q)$;
--      - *sibling gap:* for every word $P$, all children $i < j$ and every word $T$, if $P\,i$ and $P\,j\,T$ are valid window edges then $b(P\,i) + g < a(P\,j\,T)$;
--      - *descendant bounds:* if $P$ is a prefix of $Q$ (possibly $Q = P$), then $b(P) \le b(Q) \le b^{*}(P)$;
--      - *padding:* $b^{*}(P) + 1 \le a(P) + 2\,\ell(P)$.
--
--   3. **Length.** The abbreviation $\ell_W(P) = r(d + 1 - |P|)$ is introduced for every word $P$.
--
--   In particular, the two separation conditions read
--   $$
--   b(P) + g < a(Q) \ \ (P \text{ a proper prefix of } Q), \qquad b(P\,i) + g < a(P\,j\,T) \ \ (i < j).
--   $$
--
--   The integers in a window are exponents $n$ of dyadic scales $2^{-n}$. The separation conditions place the windows of all deeper edges, and of all edges in the subtrees of later siblings, at strictly finer scales, more than $g$ exponents beyond the end of the earlier window; the value $b^{*}(P)$ bounds the window ends of all descendants of $P$. In the construction the window ends serve as the resolutions at which the random tables are read. Windows of different edges are compared only along ancestor-descendant pairs and from an edge $P\,i$ to the subtrees of its later siblings $P\,j$, $j > i$; these are exactly the comparisons used by the routing argument.
--
--   **Formalization Note** Words are `List (Fin q)` and prefixes are `List.IsPrefix`; the conditions are the fields of the structure `WindowData q d g r₀`. The expression `d + 1 - P.length` uses truncated natural subtraction, but for a valid edge $|P| \le d$, so it equals $d + 1 - |P| \ge 1$. In applications $q = M + 1$, the last child being the default.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowData.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowData.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate

namespace OAI

noncomputable section

namespace Problem310

/-- An edge is identified with the nonempty path to its child. -/
def ValidWindowEdge {q : ℕ} (d : ℕ) (P : List (Fin q)) : Prop :=
  P ≠ [] ∧ P.length ≤ d

/-- Deterministic window interface shared by the finite router and its
geometric/probabilistic estimates. `q` is the TOTAL number of children.
Only the two ordering comparisons actually used by routing are required;
a preorder construction can supply them from its general rank gap bound. -/
structure WindowData (q d g r₀ : ℕ) where
  r : ℕ → ℕ
  a : List (Fin q) → ℕ
  b : List (Fin q) → ℕ
  bstar : List (Fin q) → ℕ
  length_pos : ∀ P : List (Fin q), ValidWindowEdge d P → 1 ≤ r (d + 1 - P.length)
  length_threshold : ∀ P : List (Fin q), ValidWindowEdge d P → r₀ ≤ r (d + 1 - P.length)
  start_three : ∀ P, ValidWindowEdge d P → 3 ≤ a P
  endpoint : ∀ P, ValidWindowEdge d P →
    b P + 1 = a P + r (d + 1 - P.length)
  gap_prefix : ∀ P Q, ValidWindowEdge d P → ValidWindowEdge d Q →
    P.IsPrefix Q → P ≠ Q → b P + g < a Q
  gap_sibling : ∀ (P : List (Fin q)) (i j : Fin q) (tail : List (Fin q)),
    i < j → ValidWindowEdge d (P ++ [i]) → ValidWindowEdge d (P ++ j :: tail) →
      b (P ++ [i]) + g < a (P ++ j :: tail)
  descendant_bounds : ∀ P Q, ValidWindowEdge d P → ValidWindowEdge d Q →
    P.IsPrefix Q → b P ≤ b Q ∧ b Q ≤ bstar P
  padding : ∀ P, ValidWindowEdge d P →
    bstar P + 1 ≤ a P + 2 * r (d + 1 - P.length)

namespace WindowData

variable {q d g r₀ : ℕ} (W : WindowData q d g r₀)

abbrev length (P : List (Fin q)) : ℕ := W.r (d + 1 - P.length)

end WindowData
end Problem310

end

end OAI



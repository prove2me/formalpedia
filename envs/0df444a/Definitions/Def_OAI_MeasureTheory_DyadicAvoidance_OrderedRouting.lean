-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
-- name    : OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:00:52.038565+00:00
-- url     : https://prove2.me/theorems/0f2ab3cd-3a6a-4f8d-9390-1a25cc6f989c
-- title:
--   First-success choice of a child, with a default child
-- statement:
--   This file defines the *first-success rule* by which a node of a routing tree chooses one of its $M+1$ children $0,1,\dots,M$, the last child $M$ serving as the default.
--
--   1. **First-success choice.** Let $M \in \mathbb{N}$ and let $S : \{0,1,\dots,M-1\} \to \{0,1\}$ be a vector of Boolean selector values, where $1$ means success. The chosen child is
--   $$
--   \operatorname{choose}(S) = \min\Big( \big\{\, i \in \{0,\dots,M-1\} : S(i) = 1 \,\big\} \cup \{M\} \Big) \in \{0,1,\dots,M\}.
--   $$
--   In words, the selectors are inspected in the order $0, 1, \dots, M-1$; the first successful one is chosen, and if none succeeds the default child $M$ is chosen. (For $M = 0$ the default child $0$ is always chosen.)
--
--   2. **Congruence.** If $S(i) = T(i)$ for every $i \in \{0,\dots,M-1\}$, then $\operatorname{choose}(S) = \operatorname{choose}(T)$.
--
--   This is the local decision rule of the random router in the dyadic avoidance construction. Its ordered form keeps the routing probabilities explicit: if the selector values are independent fair bits, child $i < M$ is chosen with probability $2^{-(i+1)}$ and the default child with probability $2^{-M}$.
--
--   **Formalization Note** Children are elements of `Fin (M + 1)`. The choice is `Fin.find` applied to the predicate `Fin.lastCases true S i = true`, which holds at `Fin.last M` and agrees with `S j` at `j.castSucc`; `Fin.last M` is supplied as the witness that the predicate is satisfiable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/OrderedRouting.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/OrderedRouting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel

namespace OAI

namespace Problem310.OrderedRouting

/-- The first successful nondefault selector, or the final (default) child. -/
def chooseChild {M : ℕ} (S : Fin M → Bool) : Fin (M + 1) :=
  Fin.find (fun i => Fin.lastCases true S i = true) ⟨Fin.last M, by simp⟩

variable {M : ℕ}

/-- Pointwise equality of selectors preserves the complete child choice. -/
theorem chooseChild_congr (S T : Fin M → Bool) (h : ∀ i, S i = T i) :
    chooseChild S = chooseChild T := by
  congr 1
  exact funext h

end Problem310.OrderedRouting

end OAI



-- Prove2me | Definitions.Def_PrecDTree_Main_Sepcover
-- name    : PrecDTree_Main_Sepcover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:51:46.61393+00:00
-- url     : https://prove2.me/theorems/90a0f9e4-d07c-47af-8930-fbaa65764327
-- title:
--   Sepcover sepc(D) of a decision tree (Definition 3.3)
-- statement:
--   Let $D$ be a decision tree for $I=(H,T,\preceq)$. Starting at the root, follow a reply whose subtree has the largest number of leaves, until reaching a test node $v$ at which every reply subtree has at most $|H|/2$ leaves. The sequence $\mathrm{tests}(D,v)$ of tests on the path from the root to $v$, $v$ included, is a **sepcover** $\mathrm{sepc}(D)$. Ties are broken arbitrarily; for an optimal $D$ one writes $\mathrm{sepc}(I)=\mathrm{sepc}(D)$.
--
--   **Formalization Note.** The number of leaves of a reply subtree is the number of hypotheses of its reply block. `SepWalk` is the walk as an inductive relation (stop when every block has `2·|block| ≤ |H|`, otherwise step into a block of maximum size, which then has more than `|H|/2` hypotheses); `IsSepcover T Hs D S` says `S` is a sepcover of `D` for some admissible tie-breaking.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 6, Definition 3.3

import Mathlib
import Definitions.Def_PrecDTree_Main_DecisionTree

set_option autoImplicit false

/-!
# Sepcover (Definition 3.3, p. 6)

"Starting at the root of D, follow a reply whose subtree has the largest number of leaves until
reaching a test v at which every reply subtree has at most |H|/2 leaves. Then the sequence
tests(D, v) is called a sepcover for D." The leaves of a reply subtree of a decision tree are the
hypotheses of that reply block, so a subtree's number of leaves is the size of its block. Ties are
broken arbitrarily: `IsSepcover` holds for every admissible choice.
-/

namespace PrecDTree.Main

variable {m : ℕ} {H : Type}

/-- `SepWalk T n pre Hc D S`: walking down from a node with root path `pre`, hypothesis set `Hc`
and subtree `D`, the walk of Definition 3.3 (with `n = |H|`) stops at a test node and the root path
of that node, the node included, is `S`. -/
inductive SepWalk [DecidableEq H] (T : Fin m → H → ℕ) (n : ℕ) :
    List (Fin m) → Finset H → DTree m H → List (Fin m) → Prop
  | stop (pre : List (Fin m)) (Hc : Finset H) (t : Fin m) (c : ℕ → DTree m H) :
      (∀ v : ℕ, 2 * (block T Hc t v).card ≤ n) →
      SepWalk T n pre Hc (.node t c) (pre ++ [t])
  | step (pre : List (Fin m)) (Hc : Finset H) (t : Fin m) (c : ℕ → DTree m H) (v : ℕ)
      (S : List (Fin m)) :
      (∀ w : ℕ, (block T Hc t w).card ≤ (block T Hc t v).card) →
      n < 2 * (block T Hc t v).card →
      SepWalk T n (pre ++ [t]) (block T Hc t v) (c v) S →
      SepWalk T n pre Hc (.node t c) S

/-- `S` is a sepcover `sepc(D)` of the decision tree `D` for the hypothesis set `Hs`
(Definition 3.3), for some admissible tie-breaking. -/
def IsSepcover [DecidableEq H] (T : Fin m → H → ℕ) (Hs : Finset H) (D : DTree m H)
    (S : List (Fin m)) : Prop :=
  SepWalk T Hs.card [] Hs D S

end PrecDTree.Main



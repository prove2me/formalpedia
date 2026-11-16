-- Prove2me | Definitions.Def_ImplicitParityWL_Supplement_ContradictionTree
-- name    : ImplicitParityWL_Supplement_ContradictionTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:26:12.882089+00:00
-- url     : https://prove2.me/theorems/74ba4892-713f-4995-984b-d2355e585ae3
-- title:
--   Derivation and contradiction trees of a parity system
-- statement:
--   Fix a parity system $P=(V,H,K_0)$. A **derivation tree** of a fact $(X,b)\in V\times\mathbb F_2$ is a finite rooted tree whose nodes are labeled by facts and whose root is labeled $(X,b)$. It is either a single node with $(X,b)\in K_0$, or its root uses an equation $h\in H$ with $X\in h$ and has one child for every $Y\in h\setminus\{X\}$, rooting a derivation tree of some fact $(Y,b_Y)$, such that
--   $$b=\sum_{Y\in h\setminus\{X\}}b_Y.$$
--   A **contradiction tree** has a new root with two children rooting derivation trees of $(X,0)$ and $(X,1)$ for some $X\in V$. The size of either kind of tree is its number of nodes, including the new root in the contradiction case.
--
--   Distinct children root disjoint subtrees, so a fact used twice is derived twice; this is what makes contradiction trees exponentially larger than the conflict round $\tau$ (Theorem 10.6 and Theorem 1.4).
--
--   **Formalization Note** Derivation trees are an inductive family indexed by the fact; the children of a node are a function of $Y\in h\setminus\{X\}$. The parity system is the published `ParitySystem`.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Definition 4.1, p.16

import Mathlib
import Definitions.Def_ImplicitParityWL_ParitySystem

universe u

namespace ImplicitParityWL

namespace Supplement

open scoped Classical in
/-- A **derivation tree** of a fact `(X, b)` in a parity system `P = (V, H, K₀)` (Curticapean, Liu,
Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*,
manuscript of November 3, 2026, Definition 4.1, p.16): a single node with `(X, b) ∈ K₀`, or a root using
an equation `h ∈ H` with `X ∈ h` that has one child for every `Y ∈ h ∖ {X}`, rooting a derivation tree
of a fact `(Y, b_Y)`, with `b = ∑_{Y ∈ h ∖ {X}} b_Y`.

**Formalization Note** The children are a function of `Y`, so distinct children root disjoint subtrees,
as on the page: a fact used twice has two copies of its derivation. `h ∖ {X}` is `h.erase X`
(classical equality on the variables, as in `ParitySystem.K`). -/
inductive DerivTree {V : Type u} (P : ParitySystem V) : V × ZMod 2 → Type u
  | leaf (f : V × ZMod 2) (hf : f ∈ P.init) : DerivTree P f
  | node (X : V) (h : Finset V) (hh : h ∈ P.eqs) (hX : X ∈ h) (b : V → ZMod 2)
      (child : (Y : h.erase X) → DerivTree P (Y.1, b Y.1)) :
      DerivTree P (X, ∑ Y ∈ h.erase X, b Y)

open scoped Classical in
/-- The size of a derivation tree: its number of nodes (Definition 4.1, p.16). -/
noncomputable def DerivTree.size {V : Type u} {P : ParitySystem V} : {f : V × ZMod 2} → DerivTree P f → ℕ
  | _, .leaf _ _ => 1
  | _, .node _ h _ _ _ child => 1 + ∑ Y : (h.erase _), (child Y).size

/-- A **contradiction tree** (Definition 4.1, p.16): a new root with two children rooting derivation
trees of `(X, 0)` and `(X, 1)` for some variable `X`. -/
structure ContraTree {V : Type u} (P : ParitySystem V) where
  /-- The variable with both values derived. -/
  X : V
  /-- A derivation tree of `(X, 0)`. -/
  d₀ : DerivTree P (X, 0)
  /-- A derivation tree of `(X, 1)`. -/
  d₁ : DerivTree P (X, 1)

/-- The size of a contradiction tree: its number of nodes, including the new root (Definition 4.1). -/
noncomputable def ContraTree.size {V : Type u} {P : ParitySystem V} (D : ContraTree P) : ℕ :=
  1 + D.d₀.size + D.d₁.size

end Supplement

end ImplicitParityWL



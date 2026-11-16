-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_TerminalTrees
-- name    : LeeCutCertificates_Certificate_Supplement_TerminalTrees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:00.93318+00:00
-- url     : https://prove2.me/theorems/c6dc1af7-7834-4319-aee5-c81895625b66
-- title:
--   Trees with terminals and minimum extension costs
-- statement:
--   A finite tree $T$ has distinct designated terminals indexed by the vertices of a graph and may contain Steiner vertices. Capacities are arbitrary nonnegative real numbers. The root is auxiliary; each nonroot node carries the capacity of its parent edge. The minimum terminal-extension cost is
--
--   $$R_T(S)=\min_{X:\,X\cap V=S}\sum_{uv\in\partial_T(X)}c_{uv}.$$
--
--   An $\alpha$-tree cut sparsifier requires $\alpha\ge1$ and $c_G(S)\le R_T(S)\le\alpha c_G(S)$ for every terminal shore, including the empty and full shores. Terminals need not be leaves in this general interface. This is the arbitrary-tree input used by conversion.
--
--   **Formalization Note** The finite nonempty extension family is encoded by a real `sInf`. Injectivity of the terminal map guarantees an extension for every labeling. There is no boundedness or attainment hypothesis on the input, since finiteness supplies both.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Definition 5, printed p.7 (PDF p.8); §4, printed p.9 (PDF p.10)

import Definitions.Def_LeeCutCertificates_Certificate_CutQueries
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_RootedTrees

set_option autoImplicit false
open scoped BigOperators
open Classical
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

/-- Public topology with distinct terminals, which need not be leaves. -/
structure TerminalTree (n : ℕ) where
  nodes : ℕ
  tree : RootedTree nodes
  terminal : Fin n → Fin nodes
  terminal_injective : Function.Injective terminal

/-- Cost of a binary labeling; the root's dummy capacity is never charged. -/
noncomputable def TerminalTree.labelCost {n : ℕ} (T : TerminalTree n)
    (capacity : Fin T.nodes → ℝ) (X : Finset (Fin T.nodes)) : ℝ :=
  ∑ u, if u ≠ T.tree.root ∧ ¬ (u ∈ X ↔ T.tree.parent u ∈ X) then capacity u else 0

/-- A minimum of a finite nonempty set: injectivity always permits a label extension. -/
noncomputable def TerminalTree.rep {n : ℕ} (T : TerminalTree n)
    (capacity : Fin T.nodes → ℝ) (S : Finset (Fin n)) : ℝ :=
  sInf {r : ℝ | ∃ X : Finset (Fin T.nodes),
    (∀ v, T.terminal v ∈ X ↔ v ∈ S) ∧ r = T.labelCost capacity X}

structure CapacitatedTree (n : ℕ) extends TerminalTree n where
  capacity : Fin nodes → ℝ
  nonnegative : ∀ u, 0 ≤ capacity u

def Approximates {n m : ℕ} (G : Graph n m) (T : CapacitatedTree n) (α : ℝ) : Prop :=
  1 ≤ α ∧ ∀ S, cutw G S ≤ T.toTerminalTree.rep T.capacity S ∧
    T.toTerminalTree.rep T.capacity S ≤ α * cutw G S

end LeeCutCertificates.Certificate.Supplement



-- Prove2me | Definitions.Def_ShallowSym_Layer
-- name    : ShallowSym_Layer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:10.121265+00:00
-- url     : https://prove2.me/theorems/61557005-d406-43f9-b886-97ec8ae88371
-- title:
--   Depth-$d$ alternating AND/OR formulas, $\Sigma_d$ and $\Pi_d$, and their size
-- statement:
--   A **depth-$d$ formula** over the variables $x_0,\dots,x_{n-1}$ is built in levels:
--
--   1. a level-$0$ node is a **literal** $x_i$ or $\neg x_i$;
--   2. a level-$(m+1)$ node is a **gate** reading a finite list (of any length, possibly empty) of level-$m$ nodes.
--
--   Gate kinds alternate between AND and OR from level to level. A depth-$d$ formula is a **$\Sigma_d$ formula** when its output gate (level $d$) is an OR, and a **$\Pi_d$ formula** when it is an AND. An OR of an empty list is false and an AND of an empty list is true. The **size** of a formula is the number of its AND and OR gates; literals are not counted.
--
--   This is the layered circuit model of the paper ("alternating layers of AND and OR gates, with a single output gate at the top"; the depth is the number of gate layers and the size the number of AND and OR gates), restricted to trees: no gate output is shared. A formula is a circuit with the same number of gates, so size upper bounds for formulas give the same bounds for circuits.
--
--   **Formalization Note** `Layer n m` is defined by recursion on the level: `Layer n 0 = Fin n × Bool` (the literal $(i,b)$ is true at $x$ iff $x_i=b$) and `Layer n (m+1) = List (Layer n m)`. The gate kind is not stored: `eval m orGate` evaluates a node whose gate is an OR when `orGate` is true and flips the kind at each level below. `evalSigma d` and `evalPi d` read a depth-$d$ formula as $\Sigma_d$ and $\Pi_d$, and `size` counts the gate nodes. There are no constant leaves and no gates other than AND and OR.
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §2 'Circuits', p.5

import Mathlib
import Definitions.Def_ShallowSym_weight

namespace ShallowSym

/-- Strictly layered alternating AND/OR formulas over literals.

`Layer n m` is the type of level-`m` nodes over the variables `x₀, …, x_{n-1}`:
* a level-0 node is a literal `(i, b) : Fin n × Bool`, true at `x` iff `x i = b`
  (so `(i, true)` is `xᵢ` and `(i, false)` is `¬xᵢ`);
* a level-`(m+1)` node is a gate reading a finite list (any length, possibly empty) of
  level-`m` nodes.

The kind of each gate (AND or OR) is not stored: it is fixed by the kind of the output gate and
alternates from level to level (see `eval`). A depth-`d` formula is an element of
`Layer n d`; it is a **Σ_d formula** when its output gate is an OR (`evalSigma`) and a
**Π_d formula** when its output gate is an AND (`evalPi`).

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §2 "Circuits", p.5: "A circuit is a directed acyclic graph with input nodes labeled by
literals xi or ¬xi, along with AND (∧) and OR (∨) gates of arbitrary fan-in. We view circuits as
alternating layers of AND and OR gates, with a single output gate at the top. The depth is the
number of gate layers, and the size is the number of AND and OR gates. A depth-d circuit whose
output gate is an OR (resp. AND) is called a Σd (resp. Πd) circuit".

**Formalization Note.**
* These are formulas (trees: no gate output is shared), with strictly alternating layers: every
  literal sits at depth exactly `d`, and a gate at level `ℓ` reads only level-`(ℓ-1)` nodes.
  A formula is a circuit with the same number of gates, so an upper bound for formulas implies
  the paper's bound for circuits.
* Only AND and OR gates exist; there are no constant leaves.
* Empty fan-in is allowed: an empty AND is true and an empty OR is false.
* The size (`size`) is the number of gate nodes (levels ≥ 1); literals are not counted. -/
def Layer (n : ℕ) : ℕ → Type
  | 0 => Fin n × Bool
  | m + 1 => List (Layer n m)

/-- Evaluation of a level-`m` node at `x`. The flag `orGate` says whether the node, if it is
a gate, is an OR (`true`) or an AND (`false`); its children have the other kind. A literal
`(i, b)` evaluates to `x i == b`. An OR of an empty list is `false`, an AND of an empty list
is `true`. -/
def eval {n : ℕ} : (m : ℕ) → Bool → Layer n m → Cube n → Bool
  | 0, _, ℓ, x => x (show Fin n × Bool from ℓ).1 == (show Fin n × Bool from ℓ).2
  | m + 1, true, cs, x => (show List (Layer n m) from cs).any (fun c => eval m false c x)
  | m + 1, false, cs, x => (show List (Layer n m) from cs).all (fun c => eval m true c x)

/-- The number of AND/OR gates of a level-`m` node: `0` for a literal, and one plus the sizes
of the children for a gate. -/
def size {n : ℕ} : (m : ℕ) → Layer n m → ℕ
  | 0, _ => 0
  | m + 1, cs => 1 + ((show List (Layer n m) from cs).map (fun c => size m c)).sum

/-- The function computed by `φ : Layer n d` read as a **Σ_d formula** (output gate OR). -/
def evalSigma {n : ℕ} (d : ℕ) (φ : Layer n d) (x : Cube n) : Bool := eval d true φ x

/-- The function computed by `φ : Layer n d` read as a **Π_d formula** (output gate AND). -/
def evalPi {n : ℕ} (d : ℕ) (φ : Layer n d) (x : Cube n) : Bool := eval d false φ x

end ShallowSym



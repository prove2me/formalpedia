-- Prove2me | Definitions.Def_SamplingAC0_Forest
-- name    : SamplingAC0_Forest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:50.702427+00:00
-- url     : https://prove2.me/theorems/951aee8e-ec84-4ec4-b235-5fec17276be1
-- title:
--   Decision forest of depth $d$
-- statement:
--   A **decision forest** with input length $s$ and output positions $\iota$ is a family $f=(f_i)_{i\in\iota}$ of decision trees, one per output position. Each tree $f_i$ adaptively queries bits of an input $x\in\{0,1\}^s$ and ends in a leaf labelled by a bit; the forest's output on $x$ is the vector $f(x)=(f_i(x))_{i\in\iota}\in\{0,1\}^\iota$.
--
--   The forest has **depth at most $D$** if every tree makes at most $D$ queries on every input. The set of input positions queried by a tree $T$ on the path followed by $x$ is written $Q_T(x)$.
--
--   This is the sampling model of the paper: a forest applied to a uniform input $U$ samples the distribution $f(U)$.
--
--   **Formalization Note** The trees are the published `QAlgorithms.DecisionTree (Fin s) Bool Bool`. Trees are adaptive (the paper's "local" forests are a special case). Depth counts every query on the path, repeated ones included; the bound $D$ is a real number so that bounds such as $q^{1/10}$ need no rounding.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Notation, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
set_option autoImplicit false

namespace SamplingAC0

/-- **Decision forest (depth-`d` forest).** Riazanov–Viola, *Sampling Tools and the Power of AC0*,
STOC 2027 submission (manuscript sha256 99c33d30…), Notation, p.2: "The main sampling model
considered here is that of a depth-d forest {0, 1}^m → Σ^n. This is a collection of n decision trees
on m bits with output nodes labeled with Σ."

A forest with input length `s` and output index type `ι` is one (adaptive) decision tree per output
position, each querying the input bits `Fin s` and outputting a bit (Σ = {0,1}).

**Formalization Note.** The trees are the published `QAlgorithms.DecisionTree (Fin s) Bool Bool`.
Trees are adaptive (the paper's general forests, not its "local" ones). -/
abbrev Forest (s : ℕ) (ι : Type) : Type := ι → QAlgorithms.DecisionTree (Fin s) Bool Bool

/-- The output of the forest on input `x`: output position `i` is the value of tree `i` on `x`. -/
def Forest.eval {s : ℕ} {ι : Type} (f : Forest s ι) (x : Fin s → Bool) : ι → Bool :=
  fun i => (f i).eval x

/-- **Depth at most `D`.** Every tree makes at most `D` queries on every input (the length of every
root-to-leaf path that an input follows).

**Formalization Note.** Depth = worst-case number of queries `QAlgorithms.DecisionTree.queries`
(repeated queries on a path count, which only enlarges the class); the bound `D` is a real number,
so that bounds such as `q^{1/10}` or `n^c` need no rounding. -/
def Forest.DepthLE {s : ℕ} {ι : Type} (f : Forest s ι) (D : ℝ) : Prop :=
  ∀ i x, ((f i).queries x : ℝ) ≤ D

/-- The set of input positions queried by the tree `T` on the path followed by input `x`. -/
def queriedSet {ι κ α : Type} [DecidableEq ι] :
    QAlgorithms.DecisionTree ι κ α → (ι → κ) → Finset ι
  | .leaf _, _ => ∅
  | .node i next, x => insert i (queriedSet (next (x i)) x)

end SamplingAC0



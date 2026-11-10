-- Prove2me | Definitions.Def_PrecDTree_Main_DecisionTree
-- name    : PrecDTree_Main_DecisionTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:50:51.435676+00:00
-- url     : https://prove2.me/theorems/062b6e17-24f9-4f82-a114-54ecce11b873
-- title:
--   Decision trees, precedence-closed trees, cost_W, cost_A and OPT for PCWCDT and PCACDT (§2, Problems 2.1–2.2)
-- statement:
--   An instance $I=(H,T,\preceq)$ has a finite set $H$ of **hypotheses**, an indexed family $T$ of $m$ **tests**, each a partition of $H$ into **replies**, and a partial order $\preceq$ on the tests. For $H'\subseteq H$ the restricted test $t(H')$ has the nonempty replies $X\cap H'$, $X\in t$. A **decision tree** for $H'$ is either a leaf labelled by $h$, valid iff $H'=\{h\}$, or a node labelled by a test $t$ with one child per nonempty reply $X$ of $t(H')$, each child a decision tree for $X$. Tests may repeat, also on one path, and a test need not split $H'$. With $\mathrm{tests}(D,h)$ the sequence of tests on the root-to-leaf path of $h$,
--   $$\mathrm{cost}(D,h)=|\mathrm{tests}(D,h)|,\qquad \mathrm{cost}_W(D)=\max_{h\in H}\mathrm{cost}(D,h),\qquad \mathrm{cost}_A(D)=\sum_{h\in H}\mathrm{cost}(D,h).$$
--   $D$ is **precedence-closed** if for every node $v$ the sequence of tests on the path from the root to $v$ ($v$ included) is precedence-closed. **PCWCDT** (Problem 2.1) and **PCACDT** (Problem 2.2) ask for a precedence-closed tree minimizing $\mathrm{cost}_W$, resp. $\mathrm{cost}_A$; $\mathrm{OPT}(I)$ is the optimum over all precedence-closed decision trees. The instance is **identifiable** if every two distinct hypotheses are separated by some test.
--
--   **Formalization Note.** Hypotheses live in a type `H`, the hypothesis set is `Hs : Finset H`; test `t` is a labelling `T t : H → ℕ` whose fibres are its replies, and `block T Hs t v` is the reply `v` of $t(H_s)$. `DTree m H` has `leaf h` and `node t child` with `child : ℕ → DTree m H` (the child on reply label `v`); only children of nonempty blocks belong to the tree. `Valid`, `PrecClosedFrom` (with the root path accumulated) and `IsPCTree` are the validity and precedence-closedness above; `optW`/`optA` are `sInf` over $\mathbb N$ of the costs of precedence-closed trees, a genuine minimum when the instance is identifiable and $\preceq$ a partial order (otherwise the set may be empty and the value is a junk $0$, which is why every statement assumes these). `IsOptimalW` is an optimal tree for PCWCDT.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), pp. 4–5, §2, Problems 2.1 and 2.2; p. 5, restricted tests t(H')

import Mathlib
import Definitions.Def_PrecDTree_Main_Order

set_option autoImplicit false

/-!
# Decision trees, precedence-closed trees, worst-case and average-case cost, OPT (§2)

Szyfelbein, Dereniowski, *Precedence-Constrained Decision Trees and Coverings*, arXiv:2602.21312
(STOC 2027 submission version), pp. 4–5, §2, Problems 2.1 and 2.2; p. 5 (restricted tests `t(H')`).

Conventions.
* Hypotheses live in a type `H`; the hypothesis set of an instance is a finite set `Hs : Finset H`.
* The `m` tests are an indexed family `T : Fin m → H → ℕ`: test `t` partitions the hypotheses
  into the fibres of `T t` (the reply of `h` is the label `T t h`). The restriction `t(H')` of a
  test to `H' ⊆ H` has the nonempty blocks `block T H' t v`.
* A decision tree is a leaf labelled by a hypothesis, or a node labelled by a test with one child
  per reply label. Only the children of nonempty replies (relative to the current hypothesis set)
  are part of the tree; the others are never inspected.
-/

namespace PrecDTree.Main

/-- Decision trees over `m` tests and hypotheses in `H`: a leaf names a hypothesis; a node
performs test `t` and continues with `child v` on reply `v`. -/
inductive DTree (m : ℕ) (H : Type) : Type
  | leaf (h : H) : DTree m H
  | node (t : Fin m) (child : ℕ → DTree m H) : DTree m H

variable {m : ℕ} {H : Type}

/-- The reply block `{h ∈ Hs | T t h = v}`: the reply `v` of test `t` restricted to `Hs`. -/
def block [DecidableEq H] (T : Fin m → H → ℕ) (Hs : Finset H) (t : Fin m) (v : ℕ) : Finset H :=
  Hs.filter (fun h => T t h = v)

/-- `tests(D, h)`: the sequence of tests on the root-to-leaf path followed by hypothesis `h`. -/
def tests (T : Fin m → H → ℕ) : DTree m H → H → List (Fin m)
  | .leaf _, _ => []
  | .node t c, h => t :: tests T (c (T t h)) h

/-- `cost(D, h) = |tests(D, h)|`. -/
def cost (T : Fin m → H → ℕ) (D : DTree m H) (h : H) : ℕ := (tests T D h).length

/-- Worst-case cost `cost_W(D) = max_{h ∈ H} cost(D, h)`. -/
def costW (T : Fin m → H → ℕ) (Hs : Finset H) (D : DTree m H) : ℕ := Hs.sup (cost T D)

/-- Average-case cost `cost_A(D) = Σ_{h ∈ H} cost(D, h)` (a sum, as on p. 4). -/
def costA (T : Fin m → H → ℕ) (Hs : Finset H) (D : DTree m H) : ℕ := ∑ h ∈ Hs, cost T D h

/-- `D` is a decision tree for the hypothesis set `Hs`: a leaf `h` is valid iff `Hs = {h}`; a node
with test `t` is valid iff for every nonempty reply block `X` of `t` on `Hs` the child on that
reply is valid for `X`. A test may repeat, also on one path, and may fail to split `Hs`. -/
def Valid [DecidableEq H] (T : Fin m → H → ℕ) : Finset H → DTree m H → Prop
  | Hs, .leaf h => Hs = {h}
  | Hs, .node t c => ∀ v : ℕ, (block T Hs t v).Nonempty → Valid T (block T Hs t v) (c v)

/-- Precedence-closedness from a node whose root path so far is `pre`: for every node `v` (of the
part of the tree reached by the hypotheses of `Hs`) the sequence of tests on the path from the
root to `v`, `v` included, is precedence-closed. -/
def PrecClosedFrom [DecidableEq H] (le : Fin m → Fin m → Prop) (T : Fin m → H → ℕ) :
    List (Fin m) → Finset H → DTree m H → Prop
  | _, _, .leaf _ => True
  | pre, Hs, .node t c =>
      PrecClosedSeq le (pre ++ [t]) ∧
        ∀ v : ℕ, (block T Hs t v).Nonempty → PrecClosedFrom le T (pre ++ [t]) (block T Hs t v) (c v)

/-- `D` is a precedence-closed decision tree for the instance `(Hs, T, ⪯)`. -/
def IsPCTree [DecidableEq H] (le : Fin m → Fin m → Prop) (T : Fin m → H → ℕ) (Hs : Finset H)
    (D : DTree m H) : Prop :=
  Valid T Hs D ∧ PrecClosedFrom le T [] Hs D

/-- Every two distinct hypotheses of `Hs` are separated by some test (the domain of the problem:
otherwise no decision tree exists). -/
def Identifiable (T : Fin m → H → ℕ) (Hs : Finset H) : Prop :=
  ∀ h₁ ∈ Hs, ∀ h₂ ∈ Hs, h₁ ≠ h₂ → ∃ t : Fin m, T t h₁ ≠ T t h₂

/-- `OPT(I)` for PCWCDT (Problem 2.1): the least worst-case cost of a precedence-closed decision
tree for `(Hs, T, ⪯)`, over all such trees. -/
noncomputable def optW [DecidableEq H] (le : Fin m → Fin m → Prop) (T : Fin m → H → ℕ)
    (Hs : Finset H) : ℕ :=
  sInf {c | ∃ D : DTree m H, IsPCTree le T Hs D ∧ costW T Hs D = c}

/-- `OPT(I)` for PCACDT (Problem 2.2): the least average-case cost (sum over hypotheses). -/
noncomputable def optA [DecidableEq H] (le : Fin m → Fin m → Prop) (T : Fin m → H → ℕ)
    (Hs : Finset H) : ℕ :=
  sInf {c | ∃ D : DTree m H, IsPCTree le T Hs D ∧ costA T Hs D = c}

/-- `D` is an optimal precedence-closed decision tree for PCWCDT on `(Hs, T, ⪯)`. -/
def IsOptimalW [DecidableEq H] (le : Fin m → Fin m → Prop) (T : Fin m → H → ℕ) (Hs : Finset H)
    (D : DTree m H) : Prop :=
  IsPCTree le T Hs D ∧ ∀ D' : DTree m H, IsPCTree le T Hs D' → costW T Hs D ≤ costW T Hs D'

end PrecDTree.Main



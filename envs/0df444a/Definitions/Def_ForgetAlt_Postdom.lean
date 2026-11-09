-- Prove2me | Definitions.Def_ForgetAlt_Postdom
-- name    : ForgetAlt_Postdom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:45.158745+00:00
-- url     : https://prove2.me/theorems/ed912717-bbfb-435d-937c-13976bdc38e7
-- title:
--   Postdominators and the last postdominator $\mathrm{cl}_K$ in a DAG
-- statement:
--   Let $K$ be a DAG. A vertex $b$ **postdominates** $x$ if every path from $x$ to a sink of $K$ contains $b$. The **last postdominator** $\mathrm{cl}_K(x)$ is the postdominator of $x$ that is postdominated by no vertex other than itself, and
--
--   $$C_K(r)=\{x \mid \mathrm{cl}_K(x)=r\}$$
--
--   is the **postdominator class** with root $r$ (for $r$ with $\mathrm{cl}_K(r)=r$).
--
--   These classes capture the structure of vertex-disjoint paths to the sinks (Lemma 3.1) and drive the maximality transfer of Theorem 3.18.
--
--   **Formalization Note** $K$ is an arc relation on a type; paths are nonempty duplicate-free vertex lists whose consecutive vertices are joined by arcs. In a finite DAG the last postdominator exists and is unique, so `cl` (defined by `Classical.choose`) makes no choice there; elsewhere it is the junk value $x$.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.1.2, printed p.16 (PDF p.17)

import Mathlib

namespace ForgetAlt

/-!
# Directed paths, sinks, postdominators and postdominator classes of a DAG

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 3.1.2, printed p.16 (PDF p.17).

**Formalization Notes.**
* A directed graph is an arc relation `adj : W → W → Prop` on a vertex type `W`; `adj a b` is
  the arc `(a, b)`. Acyclicity and finiteness are hypotheses of the theorems, never bundled.
* A path is a vertex list: nonempty, without repeated vertices, consecutive vertices joined by
  arcs (`List.IsChain adj`). The paper's paths are simple ("path" means simple path, p.15).
* `cl adj x` is the last postdominator of `x`. In a finite DAG every vertex reaches a sink and
  its postdominators are totally ordered (p.16, [40]), so the last postdominator exists and is
  unique; `cl` picks it with `Classical.choose`, which is therefore no choice at all on a finite
  DAG. Outside that setting (no last postdominator) `cl adj x = x` is a junk value.
-/

variable {W : Type}

/-- A directed path of the arc relation `adj`, as its vertex list. -/
def IsDPath (adj : W → W → Prop) (l : List W) : Prop :=
  l ≠ [] ∧ l.Nodup ∧ l.IsChain adj

/-- A sink: a vertex with no out-arc. -/
def IsSink (adj : W → W → Prop) (x : W) : Prop :=
  ∀ y, ¬ adj x y

/-- A directed path from `x` to a sink. -/
def IsPathToSink (adj : W → W → Prop) (x : W) (l : List W) : Prop :=
  IsDPath adj l ∧ l.head? = some x ∧ ∃ s, l.getLast? = some s ∧ IsSink adj s

/-- `b` postdominates `x` (p.16): every path from `x` to a sink contains `b`. -/
def Postdominates (adj : W → W → Prop) (b x : W) : Prop :=
  ∀ l, IsPathToSink adj x l → b ∈ l

/-- `r` is the last postdominator `cl_K(x)` of `x` (p.16): a postdominator of `x` that is
postdominated by no vertex other than itself. -/
def IsLastPostdom (adj : W → W → Prop) (x r : W) : Prop :=
  Postdominates adj r x ∧ ∀ b, Postdominates adj b r → b = r

/-- `cl_K(x)`, the last postdominator of `x` (p.16). -/
noncomputable def cl (adj : W → W → Prop) (x : W) : W :=
  open Classical in if h : ∃ r, IsLastPostdom adj x r then h.choose else x

/-- The postdominator class `C_K(r) = {x | cl_K(x) = r}` (p.16); `r` is a class root when
`cl_K(r) = r`. -/
def postdomClass (adj : W → W → Prop) (r : W) : Set W :=
  {x | cl adj x = r}

end ForgetAlt



-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_Splicing
-- name    : ConstrainedDirSep_STSep_Splicing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:07:27.894162+00:00
-- url     : https://prove2.me/theorems/d3ff35c9-e52b-494b-ad10-a63d12457911
-- title:
--   Flow paths, split-arc ranks b(i, h), off-flow connectors and splicing constraints
-- statement:
--   Fix a capacity-one multigraph $H$ with terminals $s,t$, flow paths $P_1,\dots,P_\lambda$ (each a directed $s$–$t$ path $z_{i,0}=s\xrightarrow{f_{i,1}}z_{i,1}\to\cdots\xrightarrow{f_{i,\ell_i}}z_{i,\ell_i}=t$ with no repeated vertex, given by its arc list) and a set of **split arcs**. Let $C_i$ be the split arcs of $P_i$ in path order, $d_i=|C_i|$, and $c_i(x)$ the $x$-th of them ($x\in[d_i]$). The paths are **arc-disjoint** if no arc lies on two of them; $A(P)$ is the set of arcs on the paths.
--
--   A **flow occurrence** is a pair $(i,h)$ with $0\le h\le\ell_i$, representing $z_{i,h}$; $b(i,h)$ is the number of split arcs among the first $h$ arcs of $P_i$ and $a(i,h)=b(i,h)+1$. An **off-flow connector** from $(i,h)$ to $(j,h')$ is (i) a directed path of positive length from $z_{i,h}$ to $z_{j,h'}$ using no arc of $A(P)$ with all internal vertices off the flow paths, or (ii) a path of length zero when $z_{i,h}=z_{j,h'}$ but $(i,h)\ne(j,h')$. An assignment $x$ **satisfies the splicing constraint** (10) of such a connector if
--   $$\neg\big(x_i\ge a(i,h)\ \wedge\ x_j\le b(j,h')\big),$$
--   and it selects $Z(x)=\{c_i(x_i): i\in[\lambda]\}$.
--
--   **Formalization Note.** A type-(i) connector is a first arc outside $A(P)$ leaving $z_{i,h}$ followed by a walk whose intermediate vertices are off the flow paths; a walk with these properties shortens to such a path, so existence is unchanged.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), pp. 20–21 (PDF 23–24), §5.1.2, (10)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Multigraph

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **The `h`-th vertex of a walk** given by its arc list `p = (f_1, …, f_ℓ)` and start `s`:
`z_0 = s` and `z_h = head(f_h)` for `1 ≤ h ≤ ℓ`. Olkowski, Ramanujan, *Constrained Directed
Separation*, STOC 2027 submission (manuscript sha256 4dd06c29…), §5.1.2, p. 20 (PDF 23):
`P_i : z_{i,0} = s → z_{i,1} → ⋯ → z_{i,ℓ_i} = t` with arcs `f_{i,1}, …, f_{i,ℓ_i}`.

**Formalization Note.** For `h > ℓ` the value is the junk `s`; it is only used for `h ≤ ℓ`. -/
def Multigraph.walkVert {V A : Type*} (H : Multigraph V A) (s : V) (p : List A) (h : ℕ) : V :=
  if h = 0 then s else ((p[h - 1]?).map H.head).getD s

/-- **Directed s–t path** given by its arc list: consecutive arcs are joined
(`tail(f_{h+1}) = z_h`), the last vertex is `t`, and no vertex repeats (§3, p. 13, PDF 16: "A
directed path has no repeated vertex"). -/
def Multigraph.IsSTPath {V A : Type*} (H : Multigraph V A) (s t : V) (p : List A) : Prop :=
  (∀ (h : ℕ) (hh : h < p.length), H.tail p[h] = H.walkVert s p h) ∧
    H.walkVert s p p.length = t ∧
    ((List.range (p.length + 1)).map (H.walkVert s p)).Nodup

/-- **A branch's flow paths with designated split arcs.** §5.1.1–5.1.2, pp. 20–21 (PDF 23–24): a
capacity-one multigraph `H` with terminals `s`, `t`, flow paths `P_1, …, P_λ` (indexed by `Fin lam`,
each an arc list), and the set `Spl` of split arcs. -/
structure FlowFrame (V A : Type*) where
  /-- the capacity-one multigraph `H` -/
  H : Multigraph V A
  /-- the source `s` -/
  s : V
  /-- the sink `t` -/
  t : V
  /-- the number `λ` of flow paths -/
  lam : ℕ
  /-- the flow paths `P_i`, as arc lists `f_{i,1}, …, f_{i,ℓ_i}` -/
  P : Fin lam → List A
  /-- the split arcs -/
  Spl : Set A

/-- **The flow paths are pairwise arc-disjoint directed s–t paths** (§5.1.1, p. 20, PDF 23: "Fix λ
pairwise arc-disjoint s–t paths"). -/
def FlowFrame.IsArcDisjointPaths {V A : Type*} (Φ : FlowFrame V A) : Prop :=
  (∀ i, Φ.H.IsSTPath Φ.s Φ.t (Φ.P i)) ∧
    ∀ i j, i ≠ j → ∀ a, a ∈ Φ.P i → a ∉ Φ.P j

open Classical in
/-- **`C_i`, the split arcs of `P_i` in their order along `P_i`** (§5.1.2, p. 20, PDF 23); the
`x`-th of them (`x ∈ [d_i]`, 1-based) is `c_i(x) = (splitList i)[x - 1]`. -/
noncomputable def FlowFrame.splitList {V A : Type*} (Φ : FlowFrame V A) (i : Fin Φ.lam) : List A :=
  (Φ.P i).filter fun a => decide (a ∈ Φ.Spl)

/-- **`d_i = |C_i|`** (§5.1.2, p. 20, PDF 23). -/
noncomputable def FlowFrame.dom {V A : Type*} (Φ : FlowFrame V A) (i : Fin Φ.lam) : ℕ :=
  (Φ.splitList i).length

open Classical in
/-- **`b(i, h)`**, the number of split arcs among the first `h` arcs of `P_i` (§5.1.2, p. 21,
PDF 24: `b(i, h) = |{x ∈ [d_i] : pos_i(x) ≤ h}|`); `a(i, h) = b(i, h) + 1`. -/
noncomputable def FlowFrame.bcount {V A : Type*} (Φ : FlowFrame V A) (i : Fin Φ.lam) (h : ℕ) : ℕ :=
  ((Φ.P i).take h).countP fun a => decide (a ∈ Φ.Spl)

/-- **The vertex `z_{i,h}` of the flow occurrence `(i, h)`** (§5.1.2, p. 21, PDF 24). -/
def FlowFrame.occVert {V A : Type*} (Φ : FlowFrame V A) (i : Fin Φ.lam) (h : ℕ) : V :=
  Φ.H.walkVert Φ.s (Φ.P i) h

/-- **Vertices on the flow paths**: the vertices `z_{i,h}`, `0 ≤ h ≤ ℓ_i`. -/
def FlowFrame.flowVerts {V A : Type*} (Φ : FlowFrame V A) : Set V :=
  {v | ∃ i, ∃ h ≤ (Φ.P i).length, Φ.occVert i h = v}

/-- **`A(P)`, the arcs on the flow paths** (§5.1.1, p. 20, PDF 23). -/
def FlowFrame.flowArcs {V A : Type*} (Φ : FlowFrame V A) : Set A :=
  {a | ∃ i, a ∈ Φ.P i}

/-- **An off-flow arc leaving an off-flow vertex**: `u` is not on any flow path and some arc
`a ∉ A(P)` goes from `u` to `v`. -/
def FlowFrame.offStep {V A : Type*} (Φ : FlowFrame V A) (u v : V) : Prop :=
  u ∉ Φ.flowVerts ∧ ∃ a, a ∉ Φ.flowArcs ∧ Φ.H.tail a = u ∧ Φ.H.head a = v

/-- **Off-flow connector from `(i, h)` to `(j, h′)`.** §5.1.2, p. 21 (PDF 24): "(i) a directed
path of positive length from `z_{i,h}` to `z_{j,h′}` using no arc of `A(P)` and with all internal
vertices off the flow paths, or (ii) a path of length zero, when `z_{i,h} = z_{j,h′}` but
`(i, h) ≠ (j, h′)`."

**Formalization Note.** Type (i) is a first arc `a ∉ A(P)` leaving `z_{i,h}`, followed by a walk of
off-flow arcs from `head a` to `z_{j,h′}` whose every intermediate vertex is off the flow paths; a
walk with these properties shortens to a path with them, so existence is the same. -/
def FlowFrame.IsConnector {V A : Type*} (Φ : FlowFrame V A) (i : Fin Φ.lam) (h : ℕ)
    (j : Fin Φ.lam) (h' : ℕ) : Prop :=
  h ≤ (Φ.P i).length ∧ h' ≤ (Φ.P j).length ∧
    ((∃ a, a ∉ Φ.flowArcs ∧ Φ.H.tail a = Φ.occVert i h ∧
        Relation.ReflTransGen Φ.offStep (Φ.H.head a) (Φ.occVert j h')) ∨
      (Φ.occVert i h = Φ.occVert j h' ∧ (i, h) ≠ (j, h')))

/-- **The assignment `x` satisfies every splicing constraint (10).** §5.1.2, p. 21 (PDF 24): for
every connector from `(i, h)` to `(j, h′)`, `¬(X_i ≥ a(i, h) ∧ X_j ≤ b(j, h′))`. -/
def FlowFrame.SatisfiesSplicing {V A : Type*} (Φ : FlowFrame V A) (x : Fin Φ.lam → ℕ) : Prop :=
  ∀ (i : Fin Φ.lam) (h : ℕ) (j : Fin Φ.lam) (h' : ℕ), Φ.IsConnector i h j h' →
    ¬ (Φ.bcount i h + 1 ≤ x i ∧ x j ≤ Φ.bcount j h')

/-- **`Z(x) = {c_i(x_i) : i ∈ [λ]}`** (Lemma 5.9, p. 22, PDF 25): the `x_i`-th split arc of every
flow path. -/
noncomputable def FlowFrame.selectedArcs {V A : Type*} (Φ : FlowFrame V A) (x : Fin Φ.lam → ℕ) :
    Set A :=
  {a | ∃ i, (Φ.splitList i)[x i - 1]? = some a}

end ConstrainedDirSep.STSep



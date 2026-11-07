-- Prove2me | Definitions.Def_LocalBreadth_genOf
-- name    : LocalBreadth_genOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:17.433141+00:00
-- url     : https://prove2.me/theorems/9fe38d86-211b-48fe-8fe1-8f0531d2a7e3
-- title:
--   The online algorithm on a forest, and exceptional boards
-- statement:
--   Given labels $L_v$, parents and boards $I_v(x)$, the **online algorithm** works as follows. With $S_t=\{x_1,\dots,x_t\}$, a vertex $v$ is **consistent** if $S_t\subseteq L_v$, and **critical** if in addition $L_v\subseteq L_u$ for every earlier consistent $u<v$. The **guess** $Q_t$ is the largest-index critical vertex among the first $t$ vertices. If there is none, the algorithm outputs an available integer and leaves all records unchanged. Otherwise, for every $v$ on the active path from the root to $Q_t$, the record on $I=I_v(x_t)$ becomes
--   $$Z_{v,I}\leftarrow\begin{cases}Q_t&\text{if the record is new,}\\ \mathrm{LCA}(Z_{v,I},Q_t)&\text{otherwise,}\end{cases}$$
--   and no other record changes. It then scans the active path from root to leaf and outputs an available point of the first pod $I_v(x_t)\cap L_{Z_{v,I_v(x_t)}}$ containing one; if every pod is exhausted, it outputs an available point of $L_{Q_t}$.
--
--   A $z$-board is **exceptional** before $t_0$ if its $L_z$-trace contains an input or output from before $t_0$, or if it contains a board at an ancestor of $z$, including $z$, whose record was initialized before $t_0$. All other $z$-boards are **regular**.
--
--   **Formalization Note** The argument `pick` is the page's "fix tie-breaking rules for all choices"; the theorems quantify over every `pick` choosing inside nonempty sets. Vertices are 0-indexed, so the first $t$ vertices are the indices below $t$, with $t$ the number of inputs so far.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), §5.5, p.34; p.35; §5.8.4, p.39; §5.8.9, p.41

import Mathlib
import Definitions.Def_LocalBreadth_Generator
import Definitions.Def_LocalBreadth_scanParent

namespace LocalBreadth

open scoped Classical

/-- The state of the online algorithm after some rounds: the records `Z_{v,I}`, the inputs and the
outputs, oldest first. -/
structure RunState where
  /-- The record of the vertex–board pair `(v, I)`; `none` if it has not been initialized. -/
  record : ℕ → Set ℤ → Option ℕ
  /-- The inputs so far. -/
  inputs : List ℤ
  /-- The outputs so far. -/
  outs : List ℤ

/-- The state before any round. -/
def RunState.init : RunState := ⟨fun _ _ => none, [], []⟩

section Online

variable (L : ℕ → Set ℤ) (parent : ℕ → Option ℕ) (board : ℕ → ℤ → Set ℤ)
  (pick : Set ℤ → ℤ)

/-- `v` is **critical** for the input set `S` (§5.5, p.34; §5.8.4, p.39): it is consistent, `S ⊆ L v`,
and `L v ⊆ L u` for every earlier consistent `u < v`. -/
def IsCritical (S : Set ℤ) (v : ℕ) : Prop := S ⊆ L v ∧ ∀ u < v, S ⊆ L u → L v ⊆ L u

/-- The **current guess** `Q_t`: the largest-index critical vertex among the first `t` vertices, where
`t` is the number of inputs so far.

**Formalization Note.** Vertices are 0-indexed, so "the first `t` vertices" are the indices `< t`. -/
noncomputable def guess (xs : List ℤ) : Option ℕ :=
  if ∃ v < xs.length, IsCritical L {y | y ∈ xs} v then
    some (Nat.findGreatest (IsCritical L {y | y ∈ xs}) (xs.length - 1))
  else none

/-- Update (23), p.34, on the input `x` with guess `Q`: for every active `v` (an ancestor of `Q`), the
record on `I = I_v(x)` becomes `Q` if it is new, and `LCA(Z_{v,I}, Q)` otherwise. No other record
changes. -/
noncomputable def updateRecords (rec : ℕ → Set ℤ → Option ℕ) (x : ℤ) (Q : ℕ) :
    ℕ → Set ℤ → Option ℕ := fun v I =>
  if IsAnc parent v Q ∧ I = board v x then
    match rec v I with
    | none => some Q
    | some Z => some (lca parent Z Q)
  else rec v I

/-- The pod `I_v(x) ∩ L_{Z_{v, I_v(x)}}` of the vertex `v` on the input `x`. -/
def pod (rec : ℕ → Set ℤ → Option ℕ) (x : ℤ) (v : ℕ) : Set ℤ :=
  match rec v (board v x) with
  | some Z => board v x ∩ L Z
  | none => ∅

/-- One round of the **online algorithm** (§5.5, p.34; §5.8.4, p.39). With available points `av`
(neither an input so far, including `x`, nor an earlier output): if there is no guess, output any
available integer and leave the records unchanged. Otherwise update the records by (23), scan the active
path from root to leaf, and output an available point of the first pod containing one; if every pod is
exhausted, output an available point of `L_Q`.

**Formalization Note.** `pick` is the tie-breaking rule the page fixes for all choices; the milestones
quantify over every `pick` choosing inside nonempty sets. -/
noncomputable def step (σ : RunState) (x : ℤ) : RunState :=
  let inputs' := σ.inputs ++ [x]
  let av : Set ℤ := {y | y ∉ inputs' ∧ y ∉ σ.outs}
  match guess L inputs' with
  | none => ⟨σ.record, inputs', σ.outs ++ [pick av]⟩
  | some Q =>
    let rec' := updateRecords parent board σ.record x Q
    let o :=
      match (rootPath parent Q).find? (fun v => decide (pod L board rec' x v ∩ av).Nonempty) with
      | some v => pick (pod L board rec' x v ∩ av)
      | none => pick (L Q ∩ av)
    ⟨rec', inputs', σ.outs ++ [o]⟩

/-- The state after the rounds on the inputs `xs`. -/
noncomputable def run (xs : List ℤ) : RunState := xs.foldl (step L parent board pick) RunState.init

/-- The generator of the online algorithm: its answer to `xs` is the last output of the run on `xs`. -/
noncomputable def genOf : Generator := fun xs => (run L parent board pick xs).outs.getLastD 0

/-- The state after the first `t` rounds of the enumeration `x`. -/
noncomputable def stateAfter (x : ℕ → ℤ) (t : ℕ) : RunState :=
  run L parent board pick ((List.range t).map x)

/-- A `z`-board `I` is **exceptional** before time `t₀` (p.35; §5.8.9, p.41): its `L z`-trace contains an
input or an output from before `t₀`, or it contains a board at an ancestor of `z`, including `z`, whose
record was initialized before `t₀`. All other `z`-boards are **regular**. -/
def IsExceptional (x : ℕ → ℤ) (z t₀ : ℕ) (I : Set ℤ) : Prop :=
  (∃ t < t₀, x t ∈ L z ∩ I) ∨
  (∃ t < t₀, output (genOf L parent board pick) x t ∈ L z ∩ I) ∨
  ∃ u w, IsAnc parent u z ∧ board u w ⊆ I ∧
    (stateAfter L parent board pick x t₀).record u (board u w) ≠ none

end Online

end LocalBreadth



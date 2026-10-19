-- Prove2me | Definitions.Def_SandsSauerWoodrow_OrderOnSets
-- name    : SandsSauerWoodrow_OrderOnSets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-17T06:02:10.373952+00:00
-- url     : https://prove2.me/theorems/80934bd5-025e-4bf6-8178-cb2252e92f03
-- title:
--   Reachability along one colour, its asymmetric part, and the order it induces on sets
-- statement:
--   This definition module supplies the apparatus that the proof of Theorem 1 of Sands, Sauer and Woodrow (*On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, pp. 271–273) runs on, in the form used by the mechanized development of Chancelier (arXiv:2604.21376, Definitions 2 and 8).
--
--   Fix a digraph $D$ on a set $V$ of vertices whose arcs are coloured. For a colour $k$, write $x \to_k y$ for reachability from $x$ to $y$ along a directed path all of whose arcs have colour $k$. The **asymmetric part** of this relation is the relation $R_k$ with $x R_k y$ when $x \to_k y$ and not $y \to_k x$.
--
--   A set $S$ is **$R$-independent** when no two of its distinct members are connected by $R$ in either direction: for distinct $x, y \in S$, neither $x R y$ nor $y R x$. Specialized to the relation obtained from the monochromatic reachability of the source, this is the paper's notion of an independent set.
--
--   Finally, a relation $R$ **induces an order on sets** by
--
--   $$S \preceq_R T \iff \forall x \in S,\ \exists y \in T,\ x = y \ \vee\ x R y,$$
--
--   and the **family** of the maximality argument consists of the nonempty sets that are independent for the monochromatic relation and whose red afterset is contained in their monochromatic foreset: every vertex reached from the set along red arcs is reached from the set by a monochromatic path in the reverse direction.
--
--   **Formalization Note.** The colouring takes values in a three-element type, matching the platform module `opg1808_colored_tournaments`, and the hypotheses of the theorems that use these definitions restrict colours on arcs. The order on sets is equation (4) of the reference above.
-- source:
--   Proof step of B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275, Theorem 1 (pp. 271-273). Order formulation and isolation of the step: J.-P. Chancelier, A formal proof of the Sands-Sauer-Woodrow theorem using the Rocq prover and mathcomp/ssreflect, arXiv:2604.21376, Definition 8 (eq. 4) and Lemma 9.

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_MonoIndependent

/-! The apparatus of the proof of Sands-Sauer-Woodrow Theorem 1 (pp. 271-273): one colour
used as a reachability relation, its asymmetric part, independence for a relation, the order
that a relation induces on sets of vertices, and the family of sets the maximality argument
runs on. The order on sets is equation (4) of Chancelier, arXiv:2604.21376, Definition 8. -/

universe u

namespace SandsSauerWoodrow

open OPG1808

/-- Reachability from `x` to `y` along arcs of the fixed colour `k`. -/
def ReachC {V : Type u} (D : Digraph V) (color : ArcColoring V) (k : Fin 3) :
    V → V → Prop :=
  fun x y => Relation.ReflTransGen (fun a b => D a b ∧ color a b = k) x y

/-- The asymmetric part of reachability along one fixed colour: `x` reaches `y` and `y` does
not reach `x` through arcs of that colour. -/
def asymPart {V : Type u} (D : Digraph V) (color : ArcColoring V) (k : Fin 3) :
    V → V → Prop :=
  fun x y => ReachC D color k x y ∧ ¬ ReachC D color k y x

/-- `R`-independence: no two distinct members of the set are connected by the relation `R` in
either direction. For the monochromatic relation this is the paper's notion of independence. -/
def RelIndep {V : Type u} (R : V → V → Prop) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y ∧ ¬ R y x

/-- The order that a relation induces on sets of vertices: every member of `S` is either a
member of `T` or reaches a member of `T` through the relation. -/
def leSet {V : Type u} (R : V → V → Prop) (S T : Set V) : Prop :=
  ∀ x ∈ S, ∃ y ∈ T, x = y ∨ R x y

/-- The family of the maximality argument: nonempty sets that are independent for the
monochromatic relation and whose red afterset is contained in their monochromatic foreset. -/
def InFam {V : Type u} (D : Digraph V) (color : ArcColoring V) (S : Set V) : Prop :=
  S.Nonempty ∧ MonoIndependent D color S ∧
    ∀ y : V, (∃ s ∈ S, ReachC D color 0 s y) → ∃ s ∈ S, MonochromaticallyReaches D color y s

end SandsSauerWoodrow



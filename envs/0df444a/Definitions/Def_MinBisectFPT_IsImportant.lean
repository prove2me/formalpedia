-- Prove2me | Definitions.Def_MinBisectFPT_IsImportant
-- name    : MinBisectFPT_IsImportant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:42.407544+00:00
-- url     : https://prove2.me/theorems/1911d53d-e4b3-40c1-8a82-c45d0f778e71
-- title:
--   $(A_0,B_0)$-cuts, reachable sets $R_H(F)$, important cuts
-- statement:
--   Let $A_0,B_0\subseteq V(H)$. An **$(A_0,B_0)$-cut** is a set $F$ of edges of $H$ such that $H-F$ has no path from $A_0$ to $B_0$, and $R_H(F)$ is the set of vertices reachable from $A_0$ in $H-F$.
--
--   An $(A_0,B_0)$-cut is **minimal** if no proper subset of it is an $(A_0,B_0)$-cut. A minimal $(A_0,B_0)$-cut $F$ is **important** if no $(A_0,B_0)$-cut $F'$ satisfies $|F'|\le|F|$ and $R_H(F)\subsetneq R_H(F')$. Here $F'$ ranges over all cuts, not only minimal ones.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), §3, p.9

import Mathlib

open scoped Classical

namespace MinBisectFPT

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **An `(A0, B0)`-cut.** Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*,
STOC 2027 submission (manuscript sha256 8db80a52…), §3, p.9: "An (A0, B0)-cut is a set F of edges such
that H − F has no path from A0 to B0". `F` is a set of edges of `H`. -/
def IsCut (H : SimpleGraph V) (A0 B0 : Finset V) (F : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ F, e ∈ H.edgeSet) ∧
    ∀ a ∈ A0, ∀ b ∈ B0, ¬(H.deleteEdges (F : Set (Sym2 V))).Reachable a b

/-- `R_H(F)`, "the set of vertices reachable from A0 in H − F" (p.9). -/
noncomputable def reach (H : SimpleGraph V) (A0 : Finset V) (F : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v => ∃ a ∈ A0, (H.deleteEdges (F : Set (Sym2 V))).Reachable a v

/-- **Important cuts** (p.9): "An (A0, B0)-cut is minimal if no proper subset of it is an (A0, B0)-cut,
and a minimal (A0, B0)-cut F is important if no (A0, B0)-cut F′ satisfies |F′| ≤ |F| and
R_H(F) ⊊ R_H(F′)." `F′` ranges over all cuts, not only the minimal ones. -/
def IsImportant (H : SimpleGraph V) (A0 B0 : Finset V) (F : Finset (Sym2 V)) : Prop :=
  IsCut H A0 B0 F ∧ (∀ F', F' ⊂ F → ¬IsCut H A0 B0 F') ∧
    ∀ F', IsCut H A0 B0 F' → F'.card ≤ F.card → ¬(reach H A0 F ⊂ reach H A0 F')

end MinBisectFPT



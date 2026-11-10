-- Prove2me | Definitions.Def_NetworkSumSecure_Solvability_algebra
-- name    : NetworkSumSecure_Solvability_algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:03:31.885255+00:00
-- url     : https://prove2.me/theorems/bc74a0f7-33e6-4b8a-9122-15acd33e841f
-- title:
--   Target column, column and key-row spans, and appendix coordinate order
-- statement:
--   For key counts $z_i$, coordinates are indexed by a user $i$ and either its message slot or one of its $z_i$ key slots. The target column $\lambda$ has a one in every message slot and zero in every key slot. An explicit coordinate equivalence sends these user blocks to the appendix order with all messages first and all keys second.
--
--   Given global columns $G=(g_e)_{e\in E}$ and an edge subset $W$, let $\langle G_W\rangle$ be their column span. Column rank is the dimension of this span; user-block rank is the dimension after restricting to that user's coordinates. Rank validity means server column rank at least $r+1$ and every user-block rank at least one.
--
--   For a value $a\in F$, let $M_a$ be all row vectors $mG_W^{(m)}$ with $\sum_i m_i=a$, and let $V_k$ be the row span of the key rows $G_W^{(k)}$. The appendix intersection is
--
--   $$M_a\cap(y+V_k).$$
--
--   The affine coset is represented as the set of $v$ such that $v-y\in V_k$. Row span and column span are distinct objects. These constructions connect the operational security predicate to finite linear algebra without assuming any of the desired equivalences.
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), pp. 7–8 (PDF pp. 9–10); p. 13 (PDF p. 15); pp. 27–28 (PDF pp. 29–30), equations (4), (5), (20), (24), (65)–(74)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_encoding

open scoped BigOperators

namespace NetworkSumSecure.Solvability

/-! Equations (4), (5), (20), and Appendix A (65)–(74), printed pp.7–8,13,27–28.
The appendix permutation is explicit and introduces no new encoding data. -/

variable {V E U F : Type}

/-- User-block order is equivalent to all messages followed by all keys. -/
def appendixEquiv (z : U → ℕ) : Coord z ≃ U ⊕ ((i : U) × Fin (z i)) where
  toFun c := match c with
    | ⟨i, none⟩ => Sum.inl i
    | ⟨i, some j⟩ => Sum.inr ⟨i, j⟩
  invFun c := match c with
    | Sum.inl i => ⟨i, none⟩
    | Sum.inr ⟨i, j⟩ => ⟨i, some j⟩
  left_inv := by intro ⟨i, c⟩; cases c <;> rfl
  right_inv := by intro c; cases c <;> rfl

def appendixColumn {z : U → ℕ} (g : Coord z → F) :
    (U ⊕ ((i : U) × Fin (z i))) → F := fun c => g ((appendixEquiv z).symm c)

/-- The target column has a one in every user's message coordinate. -/
def target [Field F] (z : U → ℕ) : Coord z → F :=
  fun c => match c.2 with | none => 1 | some _ => 0

/-- Column span over actual edge identities in W. -/
def columnSpan [Field F] {z : U → ℕ} (G : E → Coord z → F) (W : Finset E) :
    Submodule F (Coord z → F) :=
  Submodule.span F (Set.range (fun e : W => G e.val))

noncomputable def columnRank [Field F] [Fintype U] {z : U → ℕ}
    (G : E → Coord z → F) (W : Finset E) : ℕ := by
  classical
  exact Module.finrank F (columnSpan G W)

noncomputable def userRank [Field F] {z : U → ℕ}
    (G : E → Coord z → F) (W : Finset E) (i : U) : ℕ :=
  Module.finrank F (Submodule.span F (Set.range
    (fun e : W => fun c : Option (Fin (z i)) => G e.val ⟨i, c⟩)))

def RankValid [Field F] [Fintype E] [Fintype U]
    {N : Network V E U} {z : U → ℕ} (C : LocalCode N F z) (r : ℕ) : Prop :=
  r + 1 ≤ columnRank (globalColumn C) (incoming N N.server) ∧
  ∀ i, 1 ≤ userRank (globalColumn C) (incoming N N.server) i

/-- M_a: message-row images of all deterministic inputs having sum a. -/
def messageImage [Field F] [Fintype U] {z : U → ℕ}
    (G : E → Coord z → F) (W : Finset E) (a : F) : Set (W → F) :=
  {v | ∃ m : U → F, (∑ i, m i) = a ∧
    ∀ e : W, v e = ∑ i, m i * appendixColumn (G e.val) (Sum.inl i)}

/-- Row span of the key rows, not the edge-column span. -/
def keyRowSpan [Field F] {z : U → ℕ} (G : E → Coord z → F) (W : Finset E) :
    Submodule F (W → F) :=
  Submodule.span F (Set.range (fun c : (i : U) × Fin (z i) =>
    fun e : W => appendixColumn (G e.val) (Sum.inr c)))

def affineIntersection [Field F] [Fintype U] {z : U → ℕ}
    (G : E → Coord z → F) (W : Finset E) (a : F) (y : W → F) : Set (W → F) :=
  messageImage G W a ∩ {v | v - y ∈ keyRowSpan G W}

end NetworkSumSecure.Solvability



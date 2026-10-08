-- Prove2me | Definitions.Def_StrongPerfectGraph_DoubleSplit_IsStriation
-- name    : StrongPerfectGraph_DoubleSplit_IsStriation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:05:41.530221+00:00
-- url     : https://prove2.me/theorems/9ae9e623-17aa-487f-9052-c991cee19e28
-- title:
--   Strips, antistrips, striations, local and resolving sets of a striation
-- statement:
--   Let $A, B, C$ be disjoint subsets of $V(G)$. The triple $S = (A, C, B)$ is a **strip** if $A, B$ are nonempty and every vertex of $A \cup B \cup C$ lies on a path between $A$ and $B$ with only its first vertex in $A$, only its last vertex in $B$, and interior in $C$; such a path is an **$S$-rung**. An **antistrip** is a strip of $\overline{G}$, its rungs being **antirungs**. A strip $S = (A, C, B)$ and an antistrip $T = (X, Z, Y)$ are **parallel** if $A$ is complete to $X \cup Z$, $B$ is complete to $Y \cup Z$, $X$ is anticomplete to $B \cup C$ and $Y$ is anticomplete to $A \cup C$; they are **co-parallel** if $S$ is parallel to $(Y, Z, X)$. Two strips **agree** on $T$ if both are parallel or both co-parallel to $T$, and **disagree** if one is parallel and the other co-parallel. $(S_1, S_2, T_1, T_2)$ is a **twist** if $S_1, S_2$ agree on one of $T_1, T_2$ and disagree on the other.
--
--   A **striation** $L$ is a family of strips $S_i = (A_i, C_i, B_i)$, $1 \le i \le m$, and antistrips $T_j = (X_j, Z_j, Y_j)$, $1 \le j \le n$, such that
--
--   1. all strips and antistrips are pairwise disjoint, and all rungs and antirungs have odd length;
--   2. $m, n \ge 2$;
--   3. distinct strips are anticomplete, distinct antistrips are complete to each other;
--   4. each $S_i, T_j$ are parallel or co-parallel;
--   5. for $i < i'$ there are distinct $j, j'$ with $(S_i, S_{i'}, T_j, T_{j'})$ a twist, and for $j < j'$ there are distinct $i, i'$ with $(S_i, S_{i'}, T_j, T_{j'})$ a twist.
--
--   $V(L)$ is the union of the vertex sets of all strips and antistrips. A set $X \subseteq V(L)$ is **local** with respect to $L$ if at most one of $X \cap V(S_1), \dots, X \cap V(S_m)$ is nonempty, every $T_j$-antirung has a vertex outside $X$, and $X \cap \bigcup_i V(S_i)$ is complete to $X \cap \bigcup_j V(T_j)$. $X$ **resolves** $L$ if $V(L) \setminus X$ is local with respect to the striation of $\overline{G}$ obtained by exchanging the strips and antistrips. $L$ is **maximal** if there is no striation $L'$ in $G$ with $V(L) \subsetneq V(L')$.
--
--   Striations organise a degenerate appearance of $K_4$ into maximal blocks; 9.4 and 9.5 describe how the rest of the graph attaches to a maximal one.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 111–112, §9, definitions of strip, rung, antistrip, parallel, co-parallel, agree, twist, striation, V(L), local, resolves and maximal

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace StrongPerfectGraph.DoubleSplit

/-- A **rung** of the triple `(A, C, B)` (p. 111): a path (induced, as everywhere in the paper)
between `A` and `B` with only its first vertex in `A`, only its last vertex in `B`, and interior
in `C`. Applied to `Gᶜ` it gives the antirungs of an antistrip. -/
def IsRung {V : Type*} (G : SimpleGraph V) (A C B : Set V) (p : List V) : Prop :=
  StrongPerfectGraph.Main.IsInducedPath G p ∧
  ∃ a b : V, p.head? = some a ∧ p.getLast? = some b ∧
    (∀ v ∈ p, v ∈ A ↔ v = a) ∧ (∀ v ∈ p, v ∈ B ↔ v = b) ∧
    ∀ v ∈ p, v ≠ a → v ≠ b → v ∈ C

/-- `(A, C, B)` is a **strip** (p. 111): `A, B, C` are disjoint, `A, B` are nonempty, and every
vertex of `A ∪ B ∪ C` lies on a rung. An **antistrip** is a strip in `Gᶜ`. -/
def IsStrip {V : Type*} (G : SimpleGraph V) (A C B : Set V) : Prop :=
  Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A.Nonempty ∧ B.Nonempty ∧
  ∀ v ∈ A ∪ B ∪ C, ∃ p : List V, IsRung G A C B p ∧ v ∈ p

/-- `X` is complete to `Y`: every vertex of `X` is adjacent to every vertex of `Y`. -/
def IsCompleteTo {V : Type*} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ Y, G.Adj u v

/-- `X` is anticomplete to `Y`: there is no edge between `X` and `Y`. -/
def IsAnticompleteTo {V : Type*} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ Y, ¬ G.Adj u v

/-- The strip `S = (A, C, B)` and the antistrip `T = (X, Z, Y)` are **parallel** (p. 111):
`A` is complete to `X ∪ Z`, `B` is complete to `Y ∪ Z`, `X` is anticomplete to `B ∪ C`, and `Y`
is anticomplete to `A ∪ C`. They are **co-parallel** if `S` and the reverse `(Y, Z, X)` of `T`
are parallel. -/
def IsParallel {V : Type*} (G : SimpleGraph V) (A C B X Z Y : Set V) : Prop :=
  IsCompleteTo G A (X ∪ Z) ∧ IsCompleteTo G B (Y ∪ Z) ∧
  IsAnticompleteTo G X (B ∪ C) ∧ IsAnticompleteTo G Y (A ∪ C)

/-- A **striation** candidate: strips `Sᵢ = (Aᵢ, Cᵢ, Bᵢ)` for `i < m` and antistrips
`Tⱼ = (Xⱼ, Zⱼ, Yⱼ)` for `j < n` (p. 112). The conditions are in `IsStriation`. -/
structure Striation (V : Type*) where
  m : ℕ
  n : ℕ
  A : Fin m → Set V
  C : Fin m → Set V
  B : Fin m → Set V
  X : Fin n → Set V
  Z : Fin n → Set V
  Y : Fin n → Set V

namespace Striation

variable {V : Type*}

/-- `V(Sᵢ) = Aᵢ ∪ Cᵢ ∪ Bᵢ`. -/
def stripVerts (L : Striation V) (i : Fin L.m) : Set V := L.A i ∪ L.C i ∪ L.B i

/-- `V(Tⱼ) = Xⱼ ∪ Zⱼ ∪ Yⱼ`. -/
def antistripVerts (L : Striation V) (j : Fin L.n) : Set V := L.X j ∪ L.Z j ∪ L.Y j

/-- `V(S₁) ∪ ⋯ ∪ V(Sₘ)`. -/
def allStripVerts (L : Striation V) : Set V := ⋃ i, L.stripVerts i

/-- `V(T₁) ∪ ⋯ ∪ V(Tₙ)`. -/
def allAntistripVerts (L : Striation V) : Set V := ⋃ j, L.antistripVerts j

/-- `V(L)`: the union of the vertex sets of all strips and antistrips. -/
def verts (L : Striation V) : Set V := L.allStripVerts ∪ L.allAntistripVerts

/-- The family obtained by exchanging the strips and the antistrips. -/
def swap (L : Striation V) : Striation V :=
  ⟨L.n, L.m, L.X, L.Z, L.Y, L.A, L.C, L.B⟩

/-- `Sᵢ` and `Tⱼ` are parallel. -/
def Par (G : SimpleGraph V) (L : Striation V) (i : Fin L.m) (j : Fin L.n) : Prop :=
  IsParallel G (L.A i) (L.C i) (L.B i) (L.X j) (L.Z j) (L.Y j)

/-- `Sᵢ` and `Tⱼ` are co-parallel: `Sᵢ` is parallel to the reverse `(Yⱼ, Zⱼ, Xⱼ)` of `Tⱼ`. -/
def CoPar (G : SimpleGraph V) (L : Striation V) (i : Fin L.m) (j : Fin L.n) : Prop :=
  IsParallel G (L.A i) (L.C i) (L.B i) (L.Y j) (L.Z j) (L.X j)

/-- `Sᵢ, Sᵢ'` **agree** on `Tⱼ` (p. 111): both are parallel to `Tⱼ` or both are co-parallel. -/
def Agree (G : SimpleGraph V) (L : Striation V) (i i' : Fin L.m) (j : Fin L.n) : Prop :=
  (L.Par G i j ∧ L.Par G i' j) ∨ (L.CoPar G i j ∧ L.CoPar G i' j)

/-- `Sᵢ, Sᵢ'` **disagree** on `Tⱼ` (p. 111): one pair is parallel and the other co-parallel. -/
def Disagree (G : SimpleGraph V) (L : Striation V) (i i' : Fin L.m) (j : Fin L.n) : Prop :=
  (L.Par G i j ∧ L.CoPar G i' j) ∨ (L.CoPar G i j ∧ L.Par G i' j)

/-- `(Sᵢ, Sᵢ', Tⱼ, Tⱼ')` is a **twist** (p. 111): `Sᵢ, Sᵢ'` agree on one of `Tⱼ, Tⱼ'` and
disagree on the other. -/
def IsTwist (G : SimpleGraph V) (L : Striation V) (i i' : Fin L.m) (j j' : Fin L.n) : Prop :=
  (L.Agree G i i' j ∧ L.Disagree G i i' j') ∨ (L.Disagree G i i' j ∧ L.Agree G i i' j')

end Striation

open Striation

/-- `L` is a **striation** in `G` (p. 112):
1. every `Sᵢ` is a strip and every `Tⱼ` an antistrip (a strip in `Gᶜ`), all of them pairwise
   disjoint, and every rung and every antirung has odd length;
2. `m, n ≥ 2`;
3. distinct strips are anticomplete to each other and distinct antistrips complete to each other;
4. every `Sᵢ, Tⱼ` are parallel or co-parallel;
5. for `i < i'` there are distinct `j, j'` with `(Sᵢ, Sᵢ', Tⱼ, Tⱼ')` a twist;
6. for `j < j'` there are distinct `i, i'` with `(Sᵢ, Sᵢ', Tⱼ, Tⱼ')` a twist. -/
def IsStriation {V : Type*} (G : SimpleGraph V) (L : Striation V) : Prop :=
  (∀ i, IsStrip G (L.A i) (L.C i) (L.B i)) ∧
  (∀ j, IsStrip Gᶜ (L.X j) (L.Z j) (L.Y j)) ∧
  (∀ i i', i ≠ i' → Disjoint (L.stripVerts i) (L.stripVerts i')) ∧
  (∀ j j', j ≠ j' → Disjoint (L.antistripVerts j) (L.antistripVerts j')) ∧
  (∀ i j, Disjoint (L.stripVerts i) (L.antistripVerts j)) ∧
  (∀ i (p : List V), IsRung G (L.A i) (L.C i) (L.B i) p → Odd (p.length - 1)) ∧
  (∀ j (q : List V), IsRung Gᶜ (L.X j) (L.Z j) (L.Y j) q → Odd (q.length - 1)) ∧
  2 ≤ L.m ∧ 2 ≤ L.n ∧
  (∀ i i', i ≠ i' → IsAnticompleteTo G (L.stripVerts i) (L.stripVerts i')) ∧
  (∀ j j', j ≠ j' → IsCompleteTo G (L.antistripVerts j) (L.antistripVerts j')) ∧
  (∀ i j, L.Par G i j ∨ L.CoPar G i j) ∧
  (∀ i i', i < i' → ∃ j j', j ≠ j' ∧ L.IsTwist G i i' j j') ∧
  (∀ j j', j < j' → ∃ i i', i ≠ i' ∧ L.IsTwist G i i' j j')

/-- `X ⊆ V(L)` is **local** with respect to `L` (p. 112): at most one of `X ∩ V(S₁), …, X ∩ V(Sₘ)`
is nonempty; for every `j`, every `Tⱼ`-antirung has a vertex not in `X`; and
`X ∩ (V(S₁) ∪ ⋯ ∪ V(Sₘ))` is complete to `X ∩ (V(T₁) ∪ ⋯ ∪ V(Tₙ))`. -/
def IsLocalForStriation {V : Type*} (G : SimpleGraph V) (L : Striation V) (X : Set V) : Prop :=
  X ⊆ L.verts ∧
  (∀ i i', (X ∩ L.stripVerts i).Nonempty → (X ∩ L.stripVerts i').Nonempty → i = i') ∧
  (∀ j (q : List V), IsRung Gᶜ (L.X j) (L.Z j) (L.Y j) q → ∃ v ∈ q, v ∉ X) ∧
  IsCompleteTo G (X ∩ L.allStripVerts) (X ∩ L.allAntistripVerts)

/-- `X` **resolves** `L` (p. 112): `V(L) \ X` is local with respect to the striation in `Gᶜ`
obtained from `L` by exchanging the strips and the antistrips. -/
def ResolvesStriation {V : Type*} (G : SimpleGraph V) (L : Striation V) (X : Set V) : Prop :=
  IsLocalForStriation Gᶜ L.swap (L.verts \ X)

/-- A striation `L` in `G` is **maximal** (p. 112): there is no striation `L'` in `G` with
`V(L) ⊊ V(L')`. -/
def IsMaximalStriation {V : Type*} (G : SimpleGraph V) (L : Striation V) : Prop :=
  IsStriation G L ∧ ∀ L' : Striation V, IsStriation G L' → ¬ (L.verts ⊂ L'.verts)

end StrongPerfectGraph.DoubleSplit



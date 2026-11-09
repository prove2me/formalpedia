-- Prove2me | Definitions.Def_ThreshRankBIS_closure
-- name    : ThreshRankBIS_closure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:57:15.712276+00:00
-- url     : https://prove2.me/theorems/036a07f8-1908-47a1-8217-44b01ea409bb
-- title:
--   Closure $[A]$, deficit $t(A)$, cut $S_A$, maximal set $M_A$, edge boundary
-- statement:
--   Let $G=(X\cup Y,E)$ be a bipartite graph and $A\subseteq X$. Write $N(A)\subseteq Y$ for its neighbourhood. The **closure** and the **deficit** of $A$ are
--
--   $$
--   [A]=\{x\in X: N(x)\subseteq N(A)\},\qquad t(A)=|N(A)|-|[A]|.
--   $$
--
--   $A$ is **closed** if $A=[A]$. The module also defines the cut $S_A=[A]\cup N(A)$, the set $M_A=[A]\cup(Y\setminus N(A))$ of Lemma 5, and the **edge boundary** $\nabla(S)$ of a vertex set $S$, the set of edges with exactly one endpoint in $S$.
--
--   The closure–deficit layer is how the paper relates independent sets, neighbourhoods and cuts: every maximal independent set is $M_A$ for a closed $A$, of size $n-t(A)$, and $|\nabla(S_A)|=d\,t(A)$.
--
--   **Formalization Note** The deficit is an integer, not a truncated natural-number difference. A boundary edge is recorded once, as the ordered pair (endpoint in $S$, endpoint outside $S$), which is a bijection with the paper's set of boundary edges.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), §2.1, p.8; Lemma 5, p.9

import Mathlib
import Definitions.Def_ThreshRankBIS_IsRegular
set_option autoImplicit false

namespace ThreshRankBIS

open Finset

/-- The neighbourhood `N(A) ⊆ Y` of a left set `A ⊆ X` (§2.1, p.7). -/
def nbhd {n : ℕ} (E : Fin n → Fin n → Bool) (A : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun y => ∃ x ∈ A, E x y = true)

/-- **The closure `[A] = {x ∈ X : N(x) ⊆ N(A)}`** of a left set `A ⊆ X` (§2.1, p.8).

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), §2.1, p.8; also
"The covered family", p.5.

The module also defines the deficit `t(A) = |N(A)| − |[A]|`, closedness, the cut
`S_A = [A] ∪ N(A)`, the maximal independent set `M_A = [A] ∪ (Y ∖ N(A))` (Lemma 5, p.9) and the
edge boundary `∇(S)`.

**Formalization Note.** The deficit is an integer (`ℤ`), never a truncated natural-number
difference; regularity makes it nonnegative (p.8), but no statement relies on a junk value. -/
def closure {n : ℕ} (E : Fin n → Fin n → Bool) (A : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun x => nbhd E {x} ⊆ nbhd E A)

/-- The deficit `t(A) = |N(A)| − |[A]|` (§2.1, p.8), as an integer. -/
def deficit {n : ℕ} (E : Fin n → Fin n → Bool) (A : Finset (Fin n)) : ℤ :=
  (#(nbhd E A) : ℤ) - #(closure E A)

/-- `A ⊆ X` is **closed** if `A = [A]` (§2.1, p.8). -/
def IsClosedLeft {n : ℕ} (E : Fin n → Fin n → Bool) (A : Finset (Fin n)) : Prop :=
  closure E A = A

/-- The cut `S_A = [A] ∪ N(A) ⊆ V(G)` (Lemma 5, p.9). -/
def SA {n : ℕ} (E : Fin n → Fin n → Bool) (A : Finset (Fin n)) : Finset (V n) :=
  (closure E A).map Function.Embedding.inl ∪ (nbhd E A).map Function.Embedding.inr

/-- The set `M_A = [A] ∪ (Y ∖ N(A)) ⊆ V(G)` (Lemma 5, p.9; p.5). -/
def MA {n : ℕ} (E : Fin n → Fin n → Bool) (A : Finset (Fin n)) : Finset (V n) :=
  (closure E A).map Function.Embedding.inl ∪ (univ \ nbhd E A).map Function.Embedding.inr

/-- The edge boundary `∇(S)`: the edges with exactly one endpoint in `S` (§2.1, p.8), each
recorded once as the ordered pair `(u, v)` with `u ∈ S`, `v ∉ S`.

**Formalization Note.** Since exactly one endpoint of a boundary edge lies in `S`, orienting it
from inside to outside is a bijection with the paper's set of edges, so `#(boundary E S) = |∇(S)|`. -/
noncomputable def boundary {n : ℕ} (E : Fin n → Fin n → Bool) (S : Finset (V n)) : Finset (V n × V n) := by
  classical
  exact univ.filter (fun p => p.1 ∈ S ∧ p.2 ∉ S ∧ (HiddenPartition.bip E).Adj p.1 p.2)

end ThreshRankBIS



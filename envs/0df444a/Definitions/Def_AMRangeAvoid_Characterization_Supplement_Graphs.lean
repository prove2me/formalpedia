-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Supplement_Graphs
-- name    : AMRangeAvoid_Characterization_Supplement_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:22:35.181946+00:00
-- url     : https://prove2.me/theorems/ed9327e7-4999-4b24-8eb3-c5b8e49da4ec
-- title:
--   Labeled graph encodings and complementary GI/GNI languages
-- statement:
--   Two simple undirected graphs share the vertex set $\{0,\ldots,n-1\}$. Each graph is represented by its full binary adjacency matrix; validity requires symmetry and a zero diagonal. Isomorphism is a permutation of this common vertex set preserving every adjacency entry.
--
--   $$G_0\cong G_1\quad\Longleftrightarrow\quad\exists\pi\in S_n\ \forall i,j,\ A_0(i,j)=A_1(\pi(i),\pi(j)).$$
--
--   Graph Non-Isomorphism accepts valid nonisomorphic pairs and rejects valid isomorphic pairs. Invalid string codes are placed on the Graph Isomorphism side, giving two complementary total languages for the NP and coNP assertions. Empty graphs and one-vertex graphs are included. The ordinary graph carrier is Mathlib's SimpleGraph; the new layer supplies the binary input representation and the source problem.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), §2.3 and Definition 2.9, printed p.11 (PDF p.13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Complexity

namespace AMRangeAvoid.Characterization.Supplement

/-- Raw adjacency matrices have all n² entries, including the diagonal.
The validity check enforces exactly simple undirected graphs. -/
structure GraphPair where
  n : ℕ
  left : Fin n → Fin n → Bool
  right : Fin n → Fin n → Bool

def GraphPair.valid (I : GraphPair) : Prop :=
  (∀ i, I.left i i = false ∧ I.right i i = false) ∧
    (∀ i j, I.left i j = I.left j i ∧ I.right i j = I.right j i)

instance graphPairValidDecidable (I : GraphPair) : Decidable I.valid := inferInstanceAs (Decidable
  ((∀ i, I.left i i = false ∧ I.right i i = false) ∧
    (∀ i j, I.left i j = I.left j i ∧ I.right i j = I.right j i)))

def GraphPair.code (I : GraphPair) : Bits :=
  natCode I.n ++ (List.ofFn (fun i => List.ofFn (I.left i))).flatten ++
    (List.ofFn (fun i => List.ofFn (I.right i))).flatten

def decodeGraphPair (b : Bits) : Option GraphPair := do
  let (n, rest) ← readNat b
  if rest.length = 2 * n * n then
    let I : GraphPair := ⟨n,
      fun i j => rest.getD (i.val * n + j.val) false,
      fun i j => rest.getD (n * n + i.val * n + j.val) false⟩
    if I.valid then pure I else none
  else none

/-- Vertex permutations preserve every adjacency entry, including for n=0,1. -/
def GraphPair.isomorphic (I : GraphPair) : Prop :=
  ∃ p : Equiv.Perm (Fin I.n), ∀ i j, I.left i j = I.right (p i) (p j)

/-- Invalid codes are assigned to the GI side, giving complementary TOTAL
languages for the NP ∩ coNP conclusions. This is a decidable syntax convention. -/
def GNIYes : Set Bits := {b | ∃ I, decodeGraphPair b = some I ∧ ¬ I.isomorphic}

def GNI : PromiseProblem where
  yes := GNIYes
  no := GNIYesᶜ
  disjoint := by
    rw [Set.disjoint_left]
    intro x hx hn
    exact hn hx

def GI : PromiseProblem := complement GNI

/-- Ordinary Mathlib simple graph associated to either valid adjacency matrix. -/
def simpleGraphOf (n : ℕ) (a : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (a i j = true ∨ a j i = true)
  symm := ⟨by intro i j h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

end AMRangeAvoid.Characterization.Supplement



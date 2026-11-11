-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_Nodes
-- name    : BuchiRabinIndex_LowerBound_Nodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:14.818103+00:00
-- url     : https://prove2.me/theorems/7ae49414-26ea-4dc6-96bc-01506e4f9582
-- title:
--   Positive ordered trees, chains, and the coexistence graph
-- statement:
--   A node is a finite word of positive integers, with the empty word $\epsilon$ as root and $\tau i$ the $i$th child, starting at $i=1$. An ordered tree is finite, prefix closed and left closed. Its node weight is the sum of the entries. The order $\prec$ and the tree-independent chain $C(\tau)$ contain the proper prefixes and the older siblings of prefixes, together with $\tau$ itself.
--
--   The unique $n$-full ordered tree is represented explicitly by all positive words of weight at most $n-1$. Its coexistence graph has distinct vertices adjacent precisely when
--   $$|C(x)\cup C(y)|\le n.$$
--   Here $\omega(G_n)$ uses Mathlib’s clique number, while $g(n,c)$ is a finite maximum over cliques whose vertices have weight at most $c$. The two decomposition parts and their explicit maps, the preorder order and the preorder rank are also defined.
--
--   These definitions supply the shared combinatorial objects, independent of any automaton. The ambient list type permits zeros, but every theorem and every valid tree enforces positivity. The extension at $n=0$ is empty and is outside the paper’s domain.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Definitions 2–4, pp. 5–6; §§3.1–3.3, pp. 10–11; Lemma 16, p. 14; §6.1, p. 25; Definition 34, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Mathlib

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound
noncomputable section
open scoped Classical

/-- Positive-index words; predicates below restrict the ambient list type. -/
abbrev Node := List ℕ

def Positive (x : Node) : Prop := ∀ i ∈ x, 0 < i

def Ordered (T : Finset Node) : Prop :=
  (∀ x ∈ T, Positive x) ∧
  (∀ x ∈ T, ∀ p, p.IsPrefix x → p ∈ T) ∧
  (∀ p i, p ++ [i] ∈ T → ∀ j, 0 < j → j ≤ i → p ++ [j] ∈ T)

def children (T : Finset Node) (x : Node) : Finset Node :=
  T.filter fun y => ∃ i, y = x ++ [i]

def degree (T : Finset Node) (x : Node) : ℕ :=
  ((children T x).image fun y => y.getLast!).sup id

def Leaf (T : Finset Node) (x : Node) : Prop := x ∈ T ∧ children T x = ∅

def Youngest (T : Finset Node) (x : Node) : Prop :=
  ∃ p i, x = p ++ [i] ∧ 0 < i ∧ i = degree T p

def weight (x : Node) : ℕ := x.sum

/-- The tree-independent strict order of §3.2. -/
def Prec (x y : Node) : Prop := ∃ p i v,
  y = p ++ i :: v ∧ (x = p ∨ ∃ j, 0 < j ∧ j < i ∧ x = p ++ [j])

/-- The finite set C(x), computed directly from the positive-index word. -/
def chain : Node → Finset Node
  | [] => {[]}
  | i :: v => insert []
      (((Finset.Icc 1 (i - 1)).image fun j => [j]) ∪ (chain v).image (i :: ·))

def PreLt (x y : Node) : Prop :=
  (x.IsPrefix y ∧ x ≠ y) ∨
  ∃ p i j u v, x = p ++ i :: u ∧ y = p ++ j :: v ∧ i < j

def Last (T : Finset Node) (x : Node) : Prop :=
  x ∈ T ∧ ∀ y ∈ T, y = x ∨ PreLt y x

/-- All positive words of length at most d over {1,...,b}. -/
def boundedWords (b : ℕ) : ℕ → Finset Node
  | 0 => {[]}
  | d + 1 => insert [] ((Finset.Icc 1 b).biUnion fun i =>
      (boundedWords b d).image (i :: ·))

/-- Explicit unique n-full ordered tree, for n≥1. -/
def fullTree (n : ℕ) : Finset Node :=
  if n = 0 then ∅ else (boundedWords (n - 1) (n - 1)).filter (weight · ≤ n - 1)

abbrev Vertex (n : ℕ) := ↥(fullTree n)

def Adj (n : ℕ) (x y : Node) : Prop :=
  x ≠ y ∧ (chain x ∪ chain y).card ≤ n

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := Adj n x.val y.val
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa [Finset.union_comm] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def omega (n : ℕ) : ℕ := (graph n).cliqueNum

/-- Bounded finite maximum, including the empty clique. -/
def g (n c : ℕ) : ℕ :=
  ((fullTree n).powerset.filter fun (S : Finset Node) =>
    (∀ x ∈ S, weight x ≤ c) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y).sup Finset.card

def part1 (n : ℕ) : Finset Node := (fullTree (n - 1)).image (1 :: ·)

def increment : Node → Node
  | [] => []
  | i :: v => (i + 1) :: v

def part2 (n : ℕ) : Finset Node := ((fullTree (n - 1)).erase []).image increment

def phi1 (x : Node) : Node := x.tail

def phi2 : Node → Node
  | [] => []
  | i :: v => (i - 1) :: v

/-- Zero-based preorder rank, so node τ_i owns Fin n value i-1. -/
def rank (T : Finset Node) (x : Node) : ℕ := (T.filter (PreLt · x)).card

end
end BuchiRabinIndex.LowerBound



-- Prove2me | Definitions.Def_EvenCycleListing723_Main_Procedure
-- name    : EvenCycleListing723_Main_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:14.705351+00:00
-- url     : https://prove2.me/theorems/f775a661-63b5-47f9-b40c-005d2507dc6b
-- title:
--   Maximum-degree BFS and color-coded listing procedure
-- statement:
--   Fix an order on the vertices of a finite simple undirected graph $G$. Repeatedly choose a vertex $u$ of maximum degree in the current induced graph $G_u$, breaking ties by the fixed order, and stop when that degree is at most one. The explored subgraph contains the radius-$k$ ball and exactly those edges with an endpoint in the radius-$(k-1)$ ball. Its derived exploration quantity is
--
--   $$W_k(G)=\sum_{u\text{ processed}}\ \sum_{v:\,\operatorname{dist}_{G_u}(u,v)\le k-1}\deg_{G_u}(v).$$
--
--   For each coloring, exclude $u$, retain endpoint-colored vertices only when adjacent to $u$, and retain edges between successive colors. Backward reachability prunes vertices unable to reach the final layer. A recursive depth-first traversal then lists the surviving paths, which close through $u$. After each round delete $u$; finally canonicalize, sort, and remove adjacent duplicates.
--
--   The deterministic color schedule enumerates a constructed $(2k-1)$-perfect family and every permutation of its palette. Perfection means every $(2k-1)$-vertex subset receives distinct colors under some family member. Random schedules instead use independent uniform palette values, with
--
--   $$R_{k,c}(n)=\left\lceil(2k+c+1)(2k-1)^{2k-1}\log n\right\rceil.$$
--
--   The success probability is the exact fraction of finite palette tapes whose computed listing is complete. This definition specifies finite operations, not their cost: the RAM implementation and its measured runtime remain theorem conclusions. Colors are encoded from zero, and label order supplies the tie order. A global perfect family restricts to each explored neighborhood.
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723 (October 2026), pp.4–5, Section 3 and proof of Lemma 3.1; canonical PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf (SHA256 653ba349d1e9c1a87fe327137dddf959c6871a48cf5a052e91a47e341e9e9d8f)

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_GraphModel

set_option autoImplicit false

namespace EvenCycleListing723.Main

noncomputable section

/-- Maximum current degree, ties by the fixed label order (Section 3, p.4). -/
def chooseRoot {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Option (Fin n) :=
  (A.toList.mergeSort fun u v =>
    if (neighbors G A u).card = (neighbors G A v).card then decide (u ≤ v)
    else decide ((neighbors G A v).card ≤ (neighbors G A u).card)).head?

/-- Delete the maximum-degree root, stopping at maximum degree at most one. -/
def roundsAux {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ → Finset (Fin n) → List (Finset (Fin n) × Fin n)
  | 0, _ => []
  | fuel + 1, A =>
    match chooseRoot G A with
    | none => []
    | some u => if (neighbors G A u).card ≤ 1 then []
                else (A, u) :: roundsAux G fuel (A.erase u)

def rounds {n : ℕ} (G : SimpleGraph (Fin n)) : List (Finset (Fin n) × Fin n) :=
  roundsAux G n Finset.univ

/-- Derived exploration sum, never a definition of machine time. -/
def exploration {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  ((rounds G).map fun au =>
    ∑ v ∈ ball G au.1 au.2 (k - 1), (neighbors G au.1 v).card).sum

/-- The BFS subgraph retains exactly edges having an endpoint in the inner ball. -/
def bfsEdge {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n)
    (k : ℕ) (v w : Fin n) : Prop :=
  v ∈ ball G A u k ∧ w ∈ ball G A u k ∧ G.Adj v w ∧
    (v ∈ ball G A u (k - 1) ∨ w ∈ ball G A u (k - 1))

/-- Palette is zero-based: color 0 is the paper's color 1. -/
def rawLayer {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n)
    (k : ℕ) (χ : Fin n → Fin (2 * k - 1)) (i : ℕ) : Finset (Fin n) := by
  classical
  exact (ball G A u k).filter fun v => v ≠ u ∧ (χ v).val = i ∧
    ((i = 0 ∨ i = 2 * k - 2) → G.Adj u v)

/-- Backwards reachability, retaining only vertices with an edge to the next surviving layer. -/
def prunedLayers {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n)
    (k : ℕ) (χ : Fin n → Fin (2 * k - 1)) : ℕ → List (Finset (Fin n))
  | 0 => []
  | s + 1 => by
    classical
    let rest := prunedLayers G A u k χ s
    let L := rawLayer G A u k χ (2 * k - 1 - (s + 1))
    exact match rest with
      | [] => [L]
      | next :: _ => (L.filter fun v => ∃ w ∈ next, bfsEdge G A u k v w) :: rest

/-- DFS of the surviving layered graph. Every recursive edge extension is explicit. -/
def layeredDFS {n : ℕ} (edge : Fin n → Fin n → Prop) :
    List (Finset (Fin n)) → Option (Fin n) → List (List (Fin n))
  | [], _ => [[]]
  | L :: rest, prev => by
    classical
    let candidates := L.toList.filter fun v =>
      match prev with
      | none => true
      | some w => decide (edge w v)
    exact candidates.flatMap fun v => (layeredDFS edge rest (some v)).map (v :: ·)

/-- Close the colorful paths through u. Distinct colors enforce distinct vertices. -/
def coloredRound {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n)
    (k : ℕ) (χ : Fin n → Fin (2 * k - 1)) : List (List (Fin n)) :=
  (layeredDFS (bfsEdge G A u k) (prunedLayers G A u k χ (2 * k - 1)) none).map (u :: ·)

/-- Sort canonical lists and remove adjacent repetitions, including across roots and colorings. -/
def normalizeOutput {n : ℕ} (L : List (List (Fin n))) : List (List (Fin n)) :=
  ((L.map canonical).mergeSort (fun a b => compare a b != Ordering.gt)).foldr
    (fun xs acc => if acc.head? = some xs then acc else xs :: acc) []

/-- The actual Section 3 listing procedure as finite recursive operations. A later RAM
implementation must compute this function; none of these operations is an atomic RAM instruction. -/
def listingProcedure {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (colors : Fin n → List (Fin n → Fin (2 * k - 1))) : List (List (Fin n)) :=
  normalizeOutput ((rounds G).flatMap fun au =>
    (colors au.2).flatMap (coloredRound G au.1 au.2 k))

/-- A perfect family is a specification for a *constructed output*, never an input promise. -/
def isPerfectFamily {n : ℕ} (k : ℕ) (F : List (Fin n → Fin (2 * k - 1))) : Prop :=
  ∀ S : Finset (Fin n), S.card = 2 * k - 1 →
    ∃ f ∈ F, Set.InjOn f (S : Set (Fin n))

def familyColorings {n : ℕ} (k : ℕ) (F : List (Fin n → Fin (2 * k - 1))) :
    List (Fin n → Fin (2 * k - 1)) := by
  classical
  exact F.flatMap fun f =>
    (Finset.univ : Finset (Equiv.Perm (Fin (2 * k - 1)))).toList.map fun (σ : Equiv.Perm (Fin (2 * k - 1))) => fun v => σ (f v)

/-- A finite product of independent uniform palette values, padded to every root and vertex. -/
abbrev RandomTape (n k R : ℕ) := Fin n → Fin R → Fin n → Fin (2 * k - 1)

def randomColorings {n k R : ℕ} (ω : RandomTape n k R) (u : Fin n) :
    List (Fin n → Fin (2 * k - 1)) := List.ofFn (ω u)

/-- The explicit repetition count derived on p.5; c is an arbitrary positive integer.
Integer confidence exponents are cofinal in the positive reals. -/
def repetitions (k c n : ℕ) : ℕ :=
  ⌈((2 * k + c + 1 : ℕ) : ℝ) * ((2 * k - 1 : ℕ) : ℝ) ^ (2 * k - 1) *
    Real.log n⌉₊

/-- Uniform finite counting probability, with no measurability or integrability convention. -/
def successProbability {n : ℕ} (G : SimpleGraph (Fin n)) (k R : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun ω : RandomTape n k R =>
    correctListing G k (listingProcedure G k (randomColorings ω))).card : ℝ) /
      Fintype.card (RandomTape n k R)

end
end EvenCycleListing723.Main



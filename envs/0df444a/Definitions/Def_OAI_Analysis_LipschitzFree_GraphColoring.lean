-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
-- name    : OAI_Analysis_LipschitzFree_GraphColoring
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:32:09.098803+00:00
-- url     : https://prove2.me/theorems/5c7810ea-d04c-4912-a31d-5cb83a959546
-- title:
--   One countable colored port graph containing every coloring of the finite Cayley graphs
-- statement:
--   Throughout, a *port graph* on a vertex set $X$ with port set $D$ consists of an involution $e\mapsto\bar e$ of $D$ and a move map $X\times D\to X$, $(x,e)\mapsto x\cdot e$, such that $(x\cdot e)\cdot\bar e=x$ for all $x\in X$ and $e\in D$. A word $w=e_1e_2\cdots e_k$ of ports (an arbitrary finite list, not necessarily reduced) moves $x$ along a walk to $x\cdot w=(\cdots((x\cdot e_1)\cdot e_2)\cdots)\cdot e_k$, and $|w|=k$ is its length.
--
--   Let $A$ be a finite set of generators and $C$ a finite set of colors. For $N\in\mathbb{N}$ let $\mathcal{B}_N$ be the ball of radius $N$ (reduced word length at most $N$) in the free group $F(A)$, and let $\Gamma_N=\mathrm{Sym}(\mathcal{B}_N)$ be the finite group of all permutations of $\mathcal{B}_N$. Let $\rho_N\colon F(A)\to\Gamma_N$ be the homomorphism sending each generator $a$ to a fixed permutation of $\mathcal{B}_N$ that agrees with left multiplication $g\mapsto ag$ at every $g\in\mathcal{B}_N$ with $ag\in\mathcal{B}_N$. The Cayley port graph of level $N$ has vertex set $\Gamma_N$, ports $A\times\{+1,-1\}$, reversal $(a,\epsilon)\mapsto(a,-\epsilon)$ and moves $x\cdot(a,\epsilon)=x\,\rho_N(a)^{\epsilon}$. The all-colorings graph of level $N$ has vertex set $C^{\Gamma_N}\times\Gamma_N$ and moves $(c,x)\cdot e=(c,\,x\cdot e)$; it is the disjoint union, over all colorings $c$ of $\Gamma_N$, of copies of the Cayley port graph.
--
--   This module glues all levels into one graph.
--
--   1. **Vertices.** $V(A,C)=\bigsqcup_{N\in\mathbb{N}}\bigl(C^{\Gamma_N}\times\Gamma_N\bigr)$, the set of triples $(N,c,x)$ with $N\in\mathbb{N}$, $c\colon\Gamma_N\to C$ and $x\in\Gamma_N$. It is countable, and it is nonempty whenever $C$ is (it contains $(0,c,\mathrm{id})$ for a constant coloring $c$).
--   2. **The sequence graph.** The port graph on $V(A,C)$ with ports $A\times\{+1,-1\}$, reversal $(a,\epsilon)\mapsto(a,-\epsilon)$ and moves
--   $$
--   (N,c,x)\cdot e=(N,\,c,\,x\cdot e),
--   $$
--   that is, the disjoint union of the all-colorings graphs of all levels $N$.
--   3. **The vertex coloring.** $\chi(N,c,x)=c(x)\in C$: every vertex carries the color that its own coloring assigns to its own group element.
--   4. **Level inclusions.** $\iota_N(c,x)=(N,c,x)$. Moves and walks commute with these inclusions: $\iota_N(z)\cdot e=\iota_N(z\cdot e)$ and $\iota_N(z)\cdot w=\iota_N(z\cdot w)$ for every vertex $z$ of the level-$N$ all-colorings graph, every port $e$ and every port word $w$.
--
--   The colored graph $(V(A,C),\chi)$ is a single countable port graph, with $2|A|$ ports at every vertex, that contains at every level $N$ every possible coloring of the Cayley graph of $\Gamma_N$. Counting colorings level by level shows that walks whose colors follow prescribed patterns are rare at large levels, and with $|A|$ and $|C|$ chosen in terms of a parameter $p$ this graph is the one from which the metric blocks of the finite-rank obstruction are built.
--
--   **Formalization Note** The vertex type is `Vertex A C`, the sigma type over `N : ℕ` of `(Cayley A N → C) × Cayley A N` with `Cayley A N = Equiv.Perm (WordBall A N)`. Ports are `A × Bool`, with `true` standing for $a$ and `false` for $a^{-1}$. The graph, coloring and inclusion are `sequenceGraph`, `sequenceColor` and `intoSequence`; `sequence_move` and `sequence_walk` are the simp lemmas of item 4. The permutation attached to each generator is selected by choice, so $\rho_N$ is noncomputable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphColoring.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/GraphColoring.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting

namespace OAI

/-!
# Rare matched walks and the fixed all-colorings graph sequence
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Fintype A] [DecidableEq A]
    (C S : Type*) [Fintype C] [Fintype S]

end DiscreteFree.GraphProducer
end

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A C : Type*) [Fintype A] [DecidableEq A] [Fintype C]

def Vertex := Σ N : ℕ, (Cayley A N → C) × Cayley A N

instance : Countable (Vertex A C) := inferInstanceAs
  (Countable (Σ N : ℕ, (Cayley A N → C) × Cayley A N))

instance [Nonempty C] : Nonempty (Vertex A C) := ⟨⟨0, (fun _ => Classical.arbitrary C), 1⟩⟩

def sequenceGraph : PortGraph (Vertex A C) (A × Bool) where
  reverse := invertPort A
  reverse_involutive := (cayleyGraph A 0).reverse_involutive
  move z e := ⟨z.1, (allColoringsGraph A C z.1).move z.2 e⟩
  move_reverse z e := by
    rcases z with ⟨N,z⟩
    exact congrArg (Sigma.mk N) ((allColoringsGraph A C N).move_reverse z e)

def sequenceColor (z : Vertex A C) : C := z.2.1 z.2.2

def intoSequence (N : ℕ) (z : (Cayley A N → C) × Cayley A N) : Vertex A C := ⟨N,z⟩

omit [Fintype C] in
@[simp] theorem sequence_move (N : ℕ) (z : (Cayley A N → C) × Cayley A N) (e : A × Bool) :
    (sequenceGraph A C).move (intoSequence A C N z) e =
      intoSequence A C N ((allColoringsGraph A C N).move z e) := rfl

omit [Fintype C] in
@[simp] theorem sequence_walk (N : ℕ) (z : (Cayley A N → C) × Cayley A N) (w : List (A × Bool)) :
    (sequenceGraph A C).walk (intoSequence A C N z) w =
      intoSequence A C N ((allColoringsGraph A C N).walk z w) := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih _

variable {S : Type*}

end DiscreteFree.GraphProducer
end

end

end OAI



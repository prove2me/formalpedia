-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_GraphColoring__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:28:35.849354+00:00
-- url     : https://prove2.me/theorems/dcf01327-bab8-4791-96c2-34befa1eddf9
-- title:
--   A countable colored port graph containing every coloring of every finite Cayley port graph
-- statement:
--   A *port graph* on a vertex set $V$ with port set $D$ consists of an involution $e\mapsto\bar e$ of $D$ and a move map $(x,e)\mapsto x\cdot e$ from $V\times D$ to $V$ such that $(x\cdot e)\cdot\bar e=x$. A port word $w=e_1\cdots e_k$ (any finite list of ports) moves $x$ to $x\cdot w=(\cdots((x\cdot e_1)\cdot e_2)\cdots)\cdot e_k$.
--
--   Let $A$ be a finite set of generators with decidable equality and $C$ a finite set of colors. For $N\in\mathbb{N}$ let $B_N$ be the ball of radius $N$ (reduced word length at most $N$) in the free group $F(A)$, let $\Gamma_N=\mathrm{Sym}(B_N)$ be the finite group of all its permutations, and let $\rho_N\colon F(A)\to\Gamma_N$ be the homomorphism sending each generator $a$ to a fixed permutation of $B_N$ that agrees with $g\mapsto a\,g$ wherever $a\,g\in B_N$. The *Cayley port graph* of level $N$ has vertex set $\Gamma_N$, ports $A\times\{+1,-1\}$, reversal $(a,\epsilon)\mapsto(a,-\epsilon)$ and moves $x\cdot(a,\epsilon)=x\,\rho_N(a)^{\epsilon}$. The *all-colorings graph* of level $N$ has vertex set $C^{\Gamma_N}\times\Gamma_N$ and moves $(c,x)\cdot e=(c,\,x\cdot e)$.
--
--   This module glues all levels into a single colored port graph.
--
--   1. **Vertices.**
--   $$
--   V(A,C)=\bigsqcup_{N\in\mathbb{N}}\bigl(C^{\Gamma_N}\times\Gamma_N\bigr),
--   $$
--   the set of triples $(N,c,x)$ with $N\in\mathbb{N}$, $c\colon\Gamma_N\to C$ and $x\in\Gamma_N$. It is countable, and it is nonempty when $C$ is nonempty (it contains $(0,c,\mathrm{id})$ for a constant coloring $c$).
--   2. **Sequence graph.** The port graph on $V(A,C)$ with ports $A\times\{+1,-1\}$, the same reversal, and moves $(N,c,x)\cdot e=(N,\,c,\,x\cdot e)$: the disjoint union of the all-colorings graphs of all levels.
--   3. **Vertex coloring.** $\chi(N,c,x)=c(x)$; each vertex carries the color that its own coloring assigns to its own group element.
--   4. **Level inclusions.** $\iota_N(c,x)=(N,c,x)$. Moves and walks commute with these inclusions: $\iota_N(z)\cdot e=\iota_N(z\cdot e)$ and $\iota_N(z)\cdot w=\iota_N(z\cdot w)$ for every vertex $z$ of the level-$N$ all-colorings graph, every port $e$ and every port word $w$.
--
--   The colored graph $(V(A,C),\chi)$ is one countable port graph, with $2|A|$ ports at every vertex, that contains at each level $N$ every possible coloring of the Cayley port graph of $\Gamma_N$. Counting colorings level by level shows that walks whose colors follow prescribed patterns are rare at a suitable level; with $|A|$ and $|C|$ chosen in terms of a parameter $p$, this is the graph from which the metric blocks of the finite-rank obstruction are built.
--
--   **Formalization Note** The vertex type `Vertex A C` is the sigma type over `N : ℕ` of `(Cayley A N → C) × Cayley A N`, where `Cayley A N = Equiv.Perm (WordBall A N)`; ports are `A × Bool`, with `true` standing for $a$ and `false` for $a^{-1}$. The graph, the coloring and the inclusions are `sequenceGraph`, `sequenceColor` and `intoSequence`; `sequence_move` and `sequence_walk` are the simp lemmas of item 4. The `Countable` and `Nonempty` instances are the facts of item 1.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphColoring.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/GraphColoring.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting__RealL1Renorming

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



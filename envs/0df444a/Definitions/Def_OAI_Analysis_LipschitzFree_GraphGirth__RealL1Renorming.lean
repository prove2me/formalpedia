-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:21:46.714951+00:00
-- url     : https://prove2.me/theorems/24b76468-a200-4933-a75c-60214a72eb8c
-- title:
--   Cayley port graphs of the finite permutation groups of free-group balls, and their all-colorings unions
-- statement:
--   Let $A$ be a finite set with decidable equality, $F(A)$ the free group on $A$, and, for $N\in\mathbb{N}$, let $B_N\subseteq F(A)$ be the finite ball of elements whose reduced word has length at most $N$. Let $\rho_N\colon F(A)\to\mathrm{Sym}(B_N)$ be the homomorphism that sends each generator $a$ to a fixed permutation of $B_N$ agreeing with $g\mapsto a\,g$ at every $g\in B_N$ with $a\,g\in B_N$. A *port graph* on a vertex set $V$ with port set $D$ consists of an involution $e\mapsto\bar e$ of $D$ and a move map $V\times D\to V$, $(x,e)\mapsto x\cdot e$, with $(x\cdot e)\cdot\bar e=x$ for all $x$ and $e$.
--
--   1. **The finite group.** $\Gamma_N=\mathrm{Sym}(B_N)$, the finite group of all permutations of $B_N$, with composition as product.
--   2. **Ports and letters.** The ports are the pairs $(a,s)$ with $a\in A$ and $s\in\{\mathrm{true},\mathrm{false}\}$. The reverse of $(a,s)$ is $(a,\neg s)$, and the letter of a port is $\ell(a,\mathrm{true})=a$ and $\ell(a,\mathrm{false})=a^{-1}$ in $F(A)$. The letter of the reversed port is the inverse letter, $\ell(\bar e)=\ell(e)^{-1}$.
--   3. **Cayley port graph.** The port graph on $\Gamma_N$ with these ports and the moves
--   $$
--   x\cdot e=x\,\rho_N\bigl(\ell(e)\bigr)\qquad(x\in\Gamma_N),
--   $$
--   right multiplication in $\Gamma_N$. Moving along $e$ and then along $\bar e$ returns to $x$, because $\rho_N(\ell(\bar e))=\rho_N(\ell(e))^{-1}$.
--   4. **All-colorings graph.** For an arbitrary set $C$ of colors, the port graph on $C^{\Gamma_N}\times\Gamma_N$ with the same ports, the same reversal and the moves
--   $$
--   (c,x)\cdot e=(c,\ x\cdot e).
--   $$
--   It consists of one copy of the Cayley port graph for every coloring $c\colon\Gamma_N\to C$, and the coloring is carried along unchanged.
--
--   Because $\rho_N$ reproduces the action of the free group on words of length at most $N$, reduced walks of length at most $N$ in the Cayley port graph visit pairwise distinct vertices (this is proved separately), so these finite graphs have large girth. The all-colorings graph lets counting arguments range over every coloring of the same finite graph at once.
--
--   **Formalization Note** `Cayley A N` is an abbreviation for `Equiv.Perm (WordBall A N)`; ports are elements of `A × Bool`, with `invertPort` and `letter`, and `letter_invert` is the identity $\ell(\bar e)=\ell(e)^{-1}$. `cayleyGraph A N` and `allColoringsGraph A C N` are `PortGraph` structures (fields `reverse`, `reverse_involutive`, `move`, `move_reverse`); the module assumes `[Finite A] [DecidableEq A]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphGirth.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/GraphGirth.lean by skeleton subtraction
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

namespace OAI

/-!
# Cayley graphs with injective bounded reduced walks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Finite A] [DecidableEq A]

abbrev Cayley (N : ℕ) := Equiv.Perm (WordBall A N)

def invertPort (e : A × Bool) : A × Bool := (e.1, !e.2)

def letter (e : A × Bool) : FreeGroup A :=
  if e.2 then FreeGroup.of e.1 else (FreeGroup.of e.1)⁻¹

omit [Finite A] [DecidableEq A] in
@[simp] theorem letter_invert (e : A × Bool) : letter A (invertPort A e) = (letter A e)⁻¹ := by
  rcases e with ⟨a, b⟩
  cases b <;> simp [letter, invertPort]

def cayleyGraph (N : ℕ) : PortGraph (Cayley A N) (A × Bool) where
  reverse := invertPort A
  reverse_involutive e := by rcases e with ⟨a,b⟩; cases b <;> rfl
  move x e := x * ballRep A N (letter A e)
  move_reverse x e := by rw [letter_invert, map_inv, mul_inv_cancel_right]

def allColoringsGraph (C : Type*) (N : ℕ) :
    PortGraph ((Cayley A N → C) × Cayley A N) (A × Bool) where
  reverse := invertPort A
  reverse_involutive := (cayleyGraph A N).reverse_involutive
  move x e := (x.1, (cayleyGraph A N).move x.2 e)
  move_reverse x e := by
    change (x.1, (cayleyGraph A N).move ((cayleyGraph A N).move x.2 e)
      ((cayleyGraph A N).reverse e)) = x
    rw [(cayleyGraph A N).move_reverse]

end DiscreteFree.GraphProducer
end

end

end OAI



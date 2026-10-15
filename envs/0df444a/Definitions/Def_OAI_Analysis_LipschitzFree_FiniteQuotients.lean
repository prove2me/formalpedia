-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
-- name    : OAI_Analysis_LipschitzFree_FiniteQuotients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:26:06.327682+00:00
-- url     : https://prove2.me/theorems/fa71ab69-c007-4515-83d6-f23f468bed17
-- title:
--   Finite permutation representations of a free group that act correctly on a ball of words
-- statement:
--   Let $A$ be a finite set and $F(A)$ the free group on $A$; for $g\in F(A)$ let $|g|$ denote the length of its reduced word in the letters $a^{\pm1}$, $a\in A$. For $N\in\mathbb{N}$ the word ball is
--   $$B_N=\{\,g\in F(A):\ |g|\le N\,\},$$
--   a finite set containing the identity $1$.
--
--   1. **Ball permutations.** For every $N$ and every generator $a\in A$ there exists a permutation $\sigma$ of $B_N$ that agrees with left multiplication by $a$ wherever the product stays in the ball:
--   $$\sigma(g)=a\,g\qquad\text{for all } g\in B_N \text{ with } |a\,g|\le N .$$
--   One such permutation is fixed and denoted $\sigma_{N,a}$.
--   2. **Ball representation.** By the universal property of the free group, $a\mapsto\sigma_{N,a}$ extends to a group homomorphism
--   $$\rho_N:F(A)\to\mathrm{Sym}(B_N)$$
--   into the finite symmetric group of $B_N$.
--
--   The homomorphism $\rho_N$ is a finite permutation representation of $F(A)$ that imitates its left multiplication action on words of length at most $N$; it is designed so that $\rho_N$ is injective on $B_N$ and hence no nontrivial reduced word of length at most $N$ acts trivially. It is the source of the large-girth finite graphs of the construction, which are Cayley graphs built from $\rho_N$.
--
--   **Formalization Note** `WordBall A N` is the subtype of `FreeGroup A` cut out by `FreeGroup.norm g ≤ N`, with `Finite` and `Fintype` instances (requiring `[Finite A] [DecidableEq A]`); `ballOne` is $1\in B_N$. `exists_ball_perm` is item 1, `ballPerm A N a` is a permutation chosen by `Classical.choose`, and `ballRep A N` is `FreeGroup.lift (ballPerm A N)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/FiniteQuotients.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/FiniteQuotients.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite permutation representations of balls in free groups
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.GraphProducer

variable (A : Type*) [Finite A] [DecidableEq A]

def WordBall (N : ℕ) := {g : FreeGroup A // FreeGroup.norm g ≤ N}

instance (N : ℕ) : Finite (WordBall A N) := by
  have h := List.finite_length_le (A × Bool) N
  let : Fintype {l : List (A × Bool) // l.length ≤ N} := h.fintype
  let f : WordBall A N → {l : List (A × Bool) // l.length ≤ N} :=
    fun g => ⟨g.val.toWord, g.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (FreeGroup.toWord_injective (congrArg Subtype.val hxy))
  exact Finite.of_injective f hf

instance (N : ℕ) : Fintype (WordBall A N) := Fintype.ofFinite _

def ballOne (N : ℕ) : WordBall A N := ⟨1, by simp⟩

omit [Finite A] in
@[simp] theorem ballOne_val (N : ℕ) : (ballOne A N).val = 1 := rfl

theorem exists_ball_perm (N : ℕ) (a : A) :
    ∃ σ : Equiv.Perm (WordBall A N), ∀ g : WordBall A N,
      ∀ _h : FreeGroup.norm (FreeGroup.of a * g.val) ≤ N,
        (σ g).val = FreeGroup.of a * g.val := by
  let P := {g : WordBall A N // FreeGroup.norm (FreeGroup.of a * g.val) ≤ N}
  let f : P → WordBall A N := fun g => g.val
  let t : P → WordBall A N := fun g => ⟨FreeGroup.of a * g.val.val, g.property⟩
  have hf : Function.Injective f := Subtype.val_injective
  have ht : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val hxy)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f t hf ht
  refine ⟨σ, fun g h => ?_⟩
  exact congrArg Subtype.val (hσ ⟨g, h⟩)

noncomputable def ballPerm (N : ℕ) (a : A) : Equiv.Perm (WordBall A N) :=
  (exists_ball_perm A N a).choose

noncomputable def ballRep (N : ℕ) : FreeGroup A →* Equiv.Perm (WordBall A N) :=
  FreeGroup.lift (ballPerm A N)

end DiscreteFree.GraphProducer

end

end OAI



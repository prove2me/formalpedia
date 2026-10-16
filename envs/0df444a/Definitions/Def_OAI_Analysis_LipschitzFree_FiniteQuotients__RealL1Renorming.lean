-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:18:58.037716+00:00
-- url     : https://prove2.me/theorems/de7bbf11-6006-4782-93a6-69363e9730fb
-- title:
--   Finite permutation representations of a free group that reproduce left multiplication on a ball of words
-- statement:
--   Let $A$ be a finite set with decidable equality and $F(A)$ the free group on $A$. For $g\in F(A)$ write $|g|$ for the length of the reduced word representing $g$ in the letters $a^{\pm1}$, $a\in A$. For $N\in\mathbb{N}$ the word ball is
--   $$
--   B_N=\{\,g\in F(A):\ |g|\le N\,\}.
--   $$
--
--   1. **Word ball.** The set $B_N$ above. It is finite, because there are only finitely many words of length at most $N$ over the finite alphabet of letters $a^{\pm1}$, and it contains the identity $1$.
--   2. **Ball permutations.** For every $N\in\mathbb{N}$ and every $a\in A$ there is a permutation $\sigma$ of $B_N$ that agrees with left multiplication by $a$ wherever the product stays in the ball:
--   $$
--   \sigma(g)=a\,g\qquad\text{for all } g\in B_N \text{ with } |a\,g|\le N .
--   $$
--   One permutation with this property is fixed by choice and denoted $\sigma_{N,a}$.
--   3. **Ball representation.** $\rho_N\colon F(A)\to\mathrm{Sym}(B_N)$ is the group homomorphism into the finite symmetric group of $B_N$ determined, by the universal property of the free group, by $\rho_N(a)=\sigma_{N,a}$ for $a\in A$.
--
--   The homomorphism $\rho_N$ is a finite permutation representation of the free group that imitates its left multiplication action on words of length at most $N$. It produces the finite large-girth graphs of the construction: the Cayley graphs of the finite groups $\mathrm{Sym}(B_N)$ with respect to the permutations $\rho_N(a)^{\pm1}$, in which reduced walks of length at most $N$ do not close up.
--
--   **Formalization Note** `WordBall A N` is the subtype of `FreeGroup A` cut out by `FreeGroup.norm g ≤ N`, with `Finite` and `Fintype` instances; `ballOne` is the identity element of the ball, with the simp lemma `ballOne_val`. Item 2 is the theorem `exists_ball_perm`, `ballPerm A N a` is a permutation chosen from it by `Classical.choose`, and `ballRep A N` is `FreeGroup.lift (ballPerm A N)`. In `Equiv.Perm` the product is composition, $(\sigma\tau)(g)=\sigma(\tau(g))$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/FiniteQuotients.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/FiniteQuotients.lean by skeleton subtraction
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



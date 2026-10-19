-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
-- name    : OAI_Combinatorics_FiniteCircle_MaskBranching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:54:13.641295+00:00
-- url     : https://prove2.me/theorems/71e67527-0e37-428b-b81f-ab747b24f4ce
-- title:
--   Integer frequency trees, their sums and masses, and the mask congruences
-- statement:
--   Let $J_1,J_2,\dots$ be finite sets, where $J_l$ indexes the children of a node at height $l$.
--
--   1. **Frequency trees.** A frequency tree of height $0$ is an integer; a frequency tree of height $l+1$ is a family $t=(t_j)_{j\in J_{l+1}}$ of frequency trees of height $l$. Equivalently, it is an integer label on each leaf, the leaves of height $l$ being the tuples $(j_l,\dots,j_1)\in J_l\times\dots\times J_1$.
--   2. **Sum and mass.** The sum $\Sigma(t)$ and the mass $\|t\|$ are defined recursively by $\Sigma(t)=t$, $\|t\|=|t|$ at height $0$ and
--   $$
--   \Sigma(t)=\sum_{j\in J_{l+1}}\Sigma(t_j),\qquad \|t\|=\sum_{j\in J_{l+1}}\|t_j\|
--   $$
--   at height $l+1$; they are the total and the total absolute value of the leaf labels.
--   3. **Mask children.** For $h\in\mathbb{N}$ and a table $p(l,k)$ of natural numbers, the children at height $l$ are the pairs $(k,b)$ with $k<h$ and $0\le b<p(l,k)$ (the mask tags), a finite set.
--   4. **Mask congruences.** A frequency tree over the mask children satisfies the mask congruences if, at height $0$, nothing is required and, at height $l+1$,
--   $$
--   p(l+1,k)\ \Bigm|\ \Sigma(t)+\sum_{b=0}^{p(l+1,k)-1}b\,\Sigma\bigl(t_{(k,b)}\bigr)\qquad\text{for every }k<h,
--   $$
--   and every child $t_j$ satisfies the mask congruences at height $l$.
--
--   Frequency trees record the integer frequency vectors of characters of the leaf phase group $(\mathbb{Z}/M)^{\text{leaves}}$. The mask congruences are the divisibility conditions satisfied by the frequencies of characters that are trivial on the subgroup of cheap phase shifts of the mask words. They are the hypotheses of the branching estimate: with large distinct primes, a tree satisfying them and having nonzero total sum must branch at every level, which forces its mass to be large.
--
--   **Formalization Note** `FrequencyTree J l` is defined by recursion on $l$ (integers at height $0$, functions `J (l+1) → FrequencyTree J l` above); `frequencySum` is integer-valued and `frequencyMass` is natural-number-valued (the absolute value is `Int.natAbs`). `MaskChildren h p l` is `Σ k : Fin h, Fin (p l k)` with its `Fintype` instance, and `MaskCongruences h p l t` is a recursively defined proposition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskBranching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskBranching.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

def FrequencyTree (J : ℕ → Type) : ℕ → Type _
  | 0 => ℤ
  | l + 1 => J (l + 1) → FrequencyTree J l

noncomputable def frequencySum (J : ℕ → Type) [∀ l, Fintype (J l)] :
    (l : ℕ) → FrequencyTree J l → ℤ
  | 0, t => t
  | l + 1, t => ∑ j, frequencySum J l (t j)

noncomputable def frequencyMass (J : ℕ → Type) [∀ l, Fintype (J l)] :
    (l : ℕ) → FrequencyTree J l → ℕ
  | 0, t => (show ℤ from t).natAbs
  | l + 1, t => ∑ j, frequencyMass J l (t j)

def MaskChildren (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) := Σ k : Fin h, Fin (p l k)

instance maskChildrenFintype (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    Fintype (MaskChildren h p l) := inferInstanceAs (Fintype (Σ k : Fin h, Fin (p l k)))

noncomputable def MaskCongruences (h : ℕ) (p : ℕ → ℕ → ℕ) :
    (l : ℕ) → FrequencyTree (MaskChildren h p) l → Prop
  | 0, _ => True
  | l + 1, t =>
    (∀ k : Fin h, (p (l + 1) k : ℤ) ∣ frequencySum (MaskChildren h p) (l + 1) t +
      ∑ b : Fin (p (l + 1) k), (b.val : ℤ) * frequencySum (MaskChildren h p) l (t ⟨k, b⟩)) ∧
    ∀ j, MaskCongruences h p l (t j)

attribute [reducible] MaskChildren

end FiniteCircle

end OAI



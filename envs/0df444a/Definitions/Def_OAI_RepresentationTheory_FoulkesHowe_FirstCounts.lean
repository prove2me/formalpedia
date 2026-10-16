-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
-- name    : OAI_RepresentationTheory_FoulkesHowe_FirstCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T16:04:02.305358+00:00
-- url     : https://prove2.me/theorems/35eb8c25-1089-4e67-9d46-3ceb79938d79
-- title:
--   Label counts for the first transfer labelling
-- statement:
--   Fix $r,m,k\in\mathbb{N}$. Consider the slots $(i,j)$ with $0\le i\le r$ and $0\le j<r+m$ and the block labels $\mathsf{x},\mathsf{t},\mathsf{y}_0,\dots,\mathsf{y}_{m-1}$. The stage-$k$ labelling $\lambda_k$ of the first transfer assigns, in row $0$, the label $\mathsf{y}_j$ to slot $j$ if $j<k$ and $j<m$, and $\mathsf{t}$ otherwise; in each row $i\ge 1$ it assigns $\mathsf{x}$ to the slots $j<r$ and $\mathsf{y}_{j-r}$ to the slots $j\ge r$.
--
--   The module restates the two row cases of $\lambda_k$ as rewriting lemmas, records that no slot of row $0$ carries the label $\mathsf{x}$, and defines for every label $c$ the count
--   $$
--   N_k(c)=\#\bigl\{(i,j) : 0\le i\le r,\ 0\le j<r+m,\ \lambda_k(i,j)=c\bigr\}=\sum_{i=0}^{r}\sum_{j=0}^{r+m-1}\mathbf{1}\bigl[\lambda_k(i,j)=c\bigr].
--   $$
--
--   The count $N_k(c)$ is the degree, in the variables of block $c$, of the stage-$k$ coordinate polynomial of a flattened form. Directly from the definition, for $k\le m$ one has $N_k(\mathsf{t})=r+m-k$, $N_k(\mathsf{y}_j)=r+1$ for $j<k$, $N_k(\mathsf{y}_j)=r$ for $k\le j<m$, and $N_k(\mathsf{x})=r^2$. For $k<m$ these degrees are what make the polarization step from stage $k$ to stage $k+1$ injective, since the source block $\mathsf{t}$ then has larger degree than the target block $\mathsf{y}_k$.
--
--   **Formalization Note** `firstLabelCount r m k c` is a natural number defined as a sum of indicator values over `Fin (r + 1) × Fin (r + m)`; the label set is `FirstBlock m`, i.e. `Option (Option (Fin m))`. The lemmas `firstLabel_zero` and `firstLabel_succ` are the two row cases of `firstLabel`, and `firstLabel_zero_ne_x` is the statement about row $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FirstCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FirstCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift

namespace OAI

open scoped BigOperators

namespace Problem346

@[simp] theorem firstLabel_zero (r m k : ℕ) (j : Fin (r + m)) :
    firstLabel r m k (0, j) =
      if h : j.val < k ∧ j.val < m then some (some ⟨j.val, h.2⟩) else some none := by
  simp [firstLabel]

@[simp] theorem firstLabel_succ (r m k : ℕ) (i : Fin r) (j : Fin (r + m)) :
    firstLabel r m k (i.succ, j) =
      Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j := by
  simp [firstLabel]

@[simp] theorem firstLabel_zero_ne_x (r m k : ℕ) (j : Fin (r + m)) :
    firstLabel r m k (0, j) ≠ none := by
  simp only [firstLabel_zero]
  split <;> simp

/-- Number of individual factors labelled by a given vector block. -/
def firstLabelCount (r m k : ℕ) (c : FirstBlock m) : ℕ :=
  ∑ p : Fin (r + 1) × Fin (r + m), if firstLabel r m k p = c then 1 else 0

end Problem346

end OAI



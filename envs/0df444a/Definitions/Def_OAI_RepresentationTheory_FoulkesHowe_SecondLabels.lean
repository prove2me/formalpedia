-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels
-- name    : OAI_RepresentationTheory_FoulkesHowe_SecondLabels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T16:13:56.63341+00:00
-- url     : https://prove2.me/theorems/d183b545-e3d7-4a49-8c32-e4d4f5b9df0b
-- title:
--   Block labels for the second transfer
-- statement:
--   Fix $r,b\in\mathbb{N}$ and consider the slots $(i,j)$ with rows $0\le i\le r$ and factor positions $0\le j<b$, representing $r+1$ monomials of degree $b$, one per row. The set of block labels has $r+2$ elements,
--   $$
--   \mathcal{C}_r=\{\mathsf{c}\}\cup\{\mathsf{w}_0,\mathsf{w}_1,\dots,\mathsf{w}_r\},
--   $$
--   where $\mathsf{c}$ stands for a common vector shared by several rows, $\mathsf{w}_0$ for the vector of the fixed first row, and $\mathsf{w}_i$ ($1\le i\le r$) for an independent vector attached to row $i$.
--
--   For a count vector $k=(k_1,\dots,k_r)\in\mathbb{N}^r$ the labelling is
--   $$
--   \lambda_k(0,j)=\mathsf{w}_0,\qquad \lambda_k(i,j)=\begin{cases}\mathsf{c}&\text{if } j<k_i,\\ \mathsf{w}_i&\text{if } j\ge k_i,\end{cases}\qquad(1\le i\le r,\ 0\le j<b).
--   $$
--   So in each row $i\ge 1$ the first $k_i$ factor positions use the common block. Lemmas record the two row cases and the fact that for the zero count vector every slot is labelled by its own row: $\lambda_0(i,j)=\mathsf{w}_i$ for all $i,j$.
--
--   After substituting vectors $c,w_0,\dots,w_r$ for the labels, row $0$ reads $w_0^{\,b}$ and row $i\ge 1$ reads $c^{\min(k_i,b)}\,w_i^{\,b-\min(k_i,b)}$. At $k=0$ the rows are independent pure powers $w_0^b,\dots,w_r^b$; when $b=r+m$ and $k_i=r$ for all $i$, they are $w_0^{r+m}$ and $c^r w_i^{m}$, so a common factor $c^r$ appears in each of the last $r$ arguments. The second transfer moves between these two ends by raising one count $k_i$ at a time.
--
--   **Formalization Note** The label set is `Block r`, defined as `Option (Fin (r+1))`, with `none` for $\mathsf{c}$ and `some i` for $\mathsf{w}_i$. The count vector is a function `k` from `Fin r` to the natural numbers, and Lean's `k i` governs row `i.succ`, i.e. it is $k_{i+1}$ in the notation above; the labelling is `label k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SecondLabels.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SecondLabels.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SecondTransfer

/-- Blocks: `none` is the common vector, `some 0` is the fixed first row,
and `some i.succ` is the independent vector in row `i`. -/
abbrev Block (r : ℕ) := Option (Fin (r+1))

/-- In each nonzero row, its first `k i` factors use the common block. -/
def label {r b : ℕ} (k : Fin r → ℕ) (p : Fin (r+1) × Fin b) : Block r :=
  Fin.cases (some 0) (fun i => if p.2.val < k i then none else some i.succ) p.1

@[simp] theorem label_zero_row {r b : ℕ} (k : Fin r → ℕ) (j : Fin b) :
    label k (0,j) = some 0 := rfl

@[simp] theorem label_succ_row {r b : ℕ} (k : Fin r → ℕ)
    (i : Fin r) (j : Fin b) :
    label k (i.succ,j) = if j.val < k i then none else some i.succ := rfl

@[simp] theorem label_zero {r b : ℕ} (p : Fin (r+1) × Fin b) :
    label (fun _ : Fin r => 0) p = some p.1 := by
  rcases p with ⟨i,j⟩
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

end Problem346.SecondTransfer

end

end OAI



-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
-- name    : OAI_RepresentationTheory_FoulkesHowe_FirstLabels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:48:15.330925+00:00
-- url     : https://prove2.me/theorems/cc747d4e-c5e0-48f9-90b9-65d2b10116e1
-- title:
--   Block labels for the first transfer sequence
-- statement:
--   Fix natural numbers $r,m,k$. Consider a grid of slots $(i,j)$ with rows $0\le i\le r$ and factor positions $0\le j<r+m$; it represents a list of $r+1$ monomials of degree $r+m$, one per row. The set of block labels is
--   $$
--   \mathcal{B}_m=\{\mathsf{x},\ \mathsf{t}\}\cup\{\mathsf{y}_0,\dots,\mathsf{y}_{m-1}\},
--   $$
--   with $m+2$ elements, standing for a vector $x$, a vector $t$, and $m$ further vectors $y_0,\dots,y_{m-1}$.
--
--   The labelling at stage $k$ assigns to each slot the label
--   $$
--   \lambda_k(i,j)=\begin{cases}
--   \mathsf{y}_j & \text{if } i=0,\ j<k \text{ and } j<m,\\
--   \mathsf{t} & \text{if } i=0 \text{ and not } (j<k \text{ and } j<m),\\
--   \mathsf{x} & \text{if } i\ge 1 \text{ and } j<r,\\
--   \mathsf{y}_{j-r} & \text{if } i\ge 1 \text{ and } j\ge r.
--   \end{cases}
--   $$
--   Thus, once vectors are substituted for the labels, each of the rows $1,\dots,r$ reads $x^r y_0\cdots y_{m-1}$, while row $0$ reads $t^{r+m}$ at stage $k=0$ and $y_0\cdots y_{k-1}\,t^{r+m-k}$ at a stage $k\le m$; all stages $k\ge m$ coincide with stage $m$, where row $0$ reads $y_0\cdots y_{m-1}\,t^{r}$. Lemmas record the row-$0$ and the row-$(i\ge 1)$ cases, and that every slot of row $0$ is labelled $\mathsf{t}$ at stage $0$.
--
--   This labelling drives the first differential transfer. For $k<m$, stages $k$ and $k+1$ differ only in the slot $(0,k)$, which is relabelled from $\mathsf{t}$ to $\mathsf{y}_k$; following this chain removes the common product $y_0\cdots y_{m-1}$ from the distinguished first argument.
--
--   **Formalization Note** The label set is `FirstBlock m`, defined as `Option (Option (Fin m))`, with `none` for $\mathsf{x}$, `some none` for $\mathsf{t}$ and `some (some j)` for $\mathsf{y}_j$. Slots are pairs in `Fin (r+1) × Fin (r+m)`, and the split of the positions of rows $i\ge 1$ into the first $r$ and the last $m$ uses `Fin.addCases`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FirstLabels.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FirstLabels.lean by skeleton subtraction
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

namespace OAI

namespace Problem346

/-- Blocks for the first transfer: `none` is x, `some none` is t,
and `some (some j)` is the j-th common product factor. -/
abbrev FirstBlock (m : ℕ) := Option (Option (Fin m))

/-- The slot labels after transferring the first k factors out of the t block. -/
def firstLabel (r m k : ℕ) (p : Fin (r+1) × Fin (r+m)) : FirstBlock m :=
  if p.1 = 0 then
    if h : p.2.val < k ∧ p.2.val < m then some (some ⟨p.2.val, h.2⟩)
    else some none
  else Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) p.2

@[simp] theorem firstLabel_zero_row (r m k : ℕ) (j : Fin (r+m)) :
    firstLabel r m k (0,j) =
      if h : j.val < k ∧ j.val < m then some (some ⟨j.val,h.2⟩) else some none := by
  simp [firstLabel]

@[simp] theorem firstLabel_succ_row (r m k : ℕ) (i : Fin r) (j : Fin (r+m)) :
    firstLabel r m k (i.succ,j) =
      Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j := by
  simp [firstLabel]

@[simp] theorem firstLabel_initial_zero_row (r m : ℕ) (j : Fin (r+m)) :
    firstLabel r m 0 (0,j) = some none := by
  simp

end Problem346

end OAI



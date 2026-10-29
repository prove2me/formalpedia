-- Prove2me | Definitions.Def_SensitivityGraphCheck
-- name    : SensitivityGraphCheck
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-29T00:19:26.877812+00:00
-- url     : https://prove2.me/theorems/e1bc7543-e6c9-4767-be0c-1d4085276993
-- title:
--   Finite graph validation and executable sensitivity-certificate search
-- statement:
--   A raw input records natural-number parameters, a finite cutoff array, a Boolean adjacency table, and a binary labeling table. It contains no proof fields. Its validity predicate is exactly the original graph datum's requirements: positive vertex count greater than one, cutoff bounds and consistency, a loopless regular tournament, and all coherence, defect, and source-set labeling inequalities.
--
--   Every quantified set, coloring, vertex, and tolerance in these requirements ranges over a finite type, so validity has a computable Boolean check. A valid input converts to the original graph datum without changing any numerical parameter.
--
--   The checked search first rejects an invalid graph input. For a valid input, it runs the exact finite profile search at the given state count and depth. The raw-to-certified conversion preserves the original word dynamics. The inverse conversion is used only in proofs of completeness, not by the executable validator.
--
--   This checker supplies exact finite validation and search infrastructure. It supplies no crossing input or feasible runtime guarantee; the mission's existence statement separately requires a positive state count.
-- source:
--   Original exact checked-search reduction of SensitivityVariableWord.exists_215_word, https://prove2.me/theorems/b44a1e84-fdd6-4a5c-a770-91fc1133a055. Source definitions: SensitivityVariableWord.GraphData, step, run, Admissible, Crosses215, https://prove2.me/definitions/1a0f2c01-d616-4449-b679-77a45b8e1182. The variable alphabet and pruning proof generalize the fixed-parameter theorem SensitivityWordFrontier.search_correct, https://prove2.me/theorems/39c67854-b4b0-4292-b640-97e0bef4941e. RawData.Valid reproduces every GraphData field as a finite predicate with Boolean adjacency. Underlying recurrence attribution remains yousofy with Codex, OpenAI/math, Robin Kothari with Codex, and earlier community foundations, via accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. No source is claimed to supply a crossing input or prove the remaining 2.15 existence claim.

import Definitions.Def_SensitivityVariableFrontier

/-!
Finite raw graph and labeling inputs with a decidable validity check.
The validity predicate is exactly the graph part of the general certificate.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 256

namespace SensitivityGraphCheck
open SensitivityProfileCycle SensitivityVariableWord

structure RawData where
  vertices : ℕ
  degree : ℕ
  ordinaryCutoff : ℕ
  sourceCutoff : ℕ
  toleranceCount : ℕ
  cutoffs : Fin toleranceCount → ℕ
  adj : Fin vertices → Fin vertices → Bool
  label : Fin vertices → Fin vertices → Fin 2

def RawData.Valid (D : RawData) : Prop :=
  1 < D.vertices ∧
  4 ≤ D.ordinaryCutoff ∧
  4 ≤ D.sourceCutoff ∧
  extendCutoffs D.cutoffs 0 = D.ordinaryCutoff ∧
  (∀ i, ¬ D.adj i i = true) ∧
  (∀ i j, i ≠ j → (D.adj i j = true ↔ ¬ D.adj j i = true)) ∧
  (∀ i, (Finset.univ.filter (fun j => D.adj i j = true)).card = D.degree) ∧
  (∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
    (∀ i ∈ I, ∀ j ∈ I, D.adj i j = true → D.label i j = colors j) →
      I.card < D.ordinaryCutoff) ∧
  (∀ q : Fin D.toleranceCount,
    ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q.val) →
      I.card < D.cutoffs q) ∧
  (∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
    (∃ s ∈ I, ∀ j ∈ I, j ≠ s → D.adj s j = true) →
    (∀ i ∈ I,
      (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ 0) →
    I.card < D.sourceCutoff)

instance (D : RawData) : Decidable D.Valid := by
  unfold RawData.Valid
  infer_instance

def valid (D : RawData) : Bool := decide D.Valid

def RawData.toGraph (D : RawData) (h : D.Valid) : GraphData where
  vertices := D.vertices
  vertices_gt_one := h.1
  degree := D.degree
  ordinaryCutoff := D.ordinaryCutoff
  ordinary_ge_four := h.2.1
  sourceCutoff := D.sourceCutoff
  source_ge_four := h.2.2.1
  toleranceCount := D.toleranceCount
  cutoffs := D.cutoffs
  cutoff_zero := h.2.2.2.1
  adj := fun i j => D.adj i j = true
  loopless := h.2.2.2.2.1
  complement := fun {i j} hij => h.2.2.2.2.2.1 i j hij
  outdegree := by
    intro i
    convert h.2.2.2.2.2.2.1 i using 1
    congr 1
    ext j
    simp
  label := D.label
  coherent := h.2.2.2.2.2.2.2.1
  defect := by
    intro q I colors hh
    apply h.2.2.2.2.2.2.2.2.1 q I colors
    intro i hi
    convert hh i hi using 1
    congr 1
    ext j
    simp
  source := by
    intro I colors hs hh
    apply h.2.2.2.2.2.2.2.2.2 I colors hs
    intro i hi
    convert hh i hi using 1
    congr 1
    ext j
    simp

noncomputable def ofGraph (G : GraphData) : RawData := by
  classical
  exact {
    vertices := G.vertices
    degree := G.degree
    ordinaryCutoff := G.ordinaryCutoff
    sourceCutoff := G.sourceCutoff
    toleranceCount := G.toleranceCount
    cutoffs := G.cutoffs
    adj := fun i j => decide (G.adj i j)
    label := G.label
  }

def succeeds (D : RawData) (n k : ℕ) : Bool :=
  if h : D.Valid then SensitivityVariableFrontier.succeeds (D.toGraph h) n k else false

end SensitivityGraphCheck



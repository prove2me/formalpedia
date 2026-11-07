-- Prove2me | Definitions.Def_SensitivityGraphLocal
-- name    : SensitivityGraphLocal
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-11-06T18:54:26.404787+00:00
-- url     : https://prove2.me/theorems/dcea1f09-465d-415f-bd27-bf34eb61c716
-- title:
--   Sensitivity graph validation on exact-sized forbidden subsets
-- statement:
--   Let a raw input consist of a finite directed graph, binary edge labels, its regular degree, ordinary and source cutoffs, and a finite list of tolerance cutoffs. This interface keeps the original vertex, cutoff, tournament, and regularity conditions. It replaces the three all-size labeling checks by forbidden configurations at exactly the corresponding cutoff size.
--
--   For an ordinary cutoff, exclude a coherent coloring on every subset of that size. For tolerance $q$, exclude a coloring on a subset of the $q$-cutoff size in which every vertex has at most $q$ outgoing label disagreements. For the source cutoff, exclude a zero-defect coloring on a subset of that size that has a vertex pointing to every other vertex.
--
--   The finite sets of candidates are generated with `powersetCard`. Colorings still range over the full vertex set. The numerical profile recurrence, finite recipe alphabet, dominance pruning, and height test are copied without change from the original checker. The new checker accepts precisely when its local graph checks hold and
--
--   $$H^{43}<K^{20k}$$
--
--   holds for a retained profile at depth $k$, where $K$ is the vertex count. Equivalence to the original checker is a separate theorem. No successful input or practical runtime bound is asserted.
-- source:
--   Original hereditary-subset reduction of SensitivityGraphCheck.RawData.Valid and SensitivityGraphCheck.exists_215_success, https://prove2.me/definitions/e1bc7543-e6c9-4767-be0c-1d4085276993 and https://prove2.me/theorems/6d9893d7-40bb-47ea-acc7-3d8575b5e246. Exact source clauses: coherence, each tolerance-indexed defect bound, and the source-set bound of RawData.Valid. The numerical recurrence and dominance pruning are unchanged from SensitivityVariableFrontier. The subset argument uses Mathlib Finset.exists_subset_card_eq and Finset.powersetCard. This contribution supplies no successful 2.15 witness; the local-check existence theorem is the explicitly open residual problem.

import Definitions.Def_SensitivityGraphCheck

/-! Numerical search on raw graph parameters, independent of validity proofs. -/

set_option autoImplicit false
set_option synthInstance.maxSize 256

namespace SensitivityGraphLocal
open SensitivityProfileCycle SensitivityProfileSearch SensitivityVariableWord
open SensitivityGraphCheck

def rawStep {n : ℕ} (D : RawData) (C : Recipe n) (P : Profile n) : Profile n :=
  ⟨envelope (rawZeroSourceCombined D.vertices D.ordinaryCutoff
      (extendCutoffs D.cutoffs) D.sourceCutoff C P.zero P.one),
    envelope (rawOne D.degree C P.zero P.one)⟩

def rawExpand {n : ℕ} (D : RawData) (s : List (Profile n)) : List (Profile n) :=
  s.flatMap fun P => (SensitivityVariableFrontier.alphabet D.toleranceCount n).map
    fun C => rawStep D C.recipe P

def rawFrontier (D : RawData) (n : ℕ) : ℕ → List (Profile n)
  | 0 => [normalize (unitProfile n)]
  | k+1 => FiniteDominance.prune SensitivityVariableFrontier.Below
      (rawExpand D (rawFrontier D n k))

def rawSucceeds (D : RawData) (n k : ℕ) : Bool :=
  (rawFrontier D n k).any fun P => decide (height P ^ 43 < D.vertices ^ (20*k))

end SensitivityGraphLocal

namespace SensitivityGraphLocal
open SensitivityGraphCheck SensitivityProfileCycle

/-- Graph validation restricted to the first forbidden cardinality in each bound. -/
def LocalValid (D : RawData) : Prop :=
  1 < D.vertices ∧
  4 ≤ D.ordinaryCutoff ∧
  4 ≤ D.sourceCutoff ∧
  extendCutoffs D.cutoffs 0 = D.ordinaryCutoff ∧
  (∀ i, ¬ D.adj i i = true) ∧
  (∀ i j, i ≠ j → (D.adj i j = true ↔ ¬ D.adj j i = true)) ∧
  (∀ i, (Finset.univ.filter (fun j => D.adj i j = true)).card = D.degree) ∧
  (∀ I ∈ (Finset.univ : Finset (Fin D.vertices)).powersetCard D.ordinaryCutoff,
    ∀ colors : Fin D.vertices → Fin 2,
    (∀ i ∈ I, ∀ j ∈ I, D.adj i j = true → D.label i j = colors j) → False) ∧
  (∀ q : Fin D.toleranceCount,
    ∀ I ∈ (Finset.univ : Finset (Fin D.vertices)).powersetCard (D.cutoffs q),
      ∀ colors : Fin D.vertices → Fin 2,
      (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q.val) →
      False) ∧
  (∀ I ∈ (Finset.univ : Finset (Fin D.vertices)).powersetCard D.sourceCutoff,
    ∀ colors : Fin D.vertices → Fin 2,
    (∃ s ∈ I, ∀ j ∈ I, j ≠ s → D.adj s j = true) →
    (∀ i ∈ I,
      (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ 0) →
    False)

instance (D : RawData) : Decidable (LocalValid D) := by
  unfold LocalValid
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- A data-only search guarded by exact-cardinality graph checks. -/
def succeeds (D : RawData) (n k : ℕ) : Bool :=
  if LocalValid D then rawSucceeds D n k else false

end SensitivityGraphLocal



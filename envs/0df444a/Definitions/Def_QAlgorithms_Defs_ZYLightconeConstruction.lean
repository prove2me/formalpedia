-- Prove2me | Definitions.Def_QAlgorithms_Defs_ZYLightconeConstruction
-- name    : QAlgorithms_Defs_ZYLightconeConstruction
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:43:53.837174+00:00
-- url     : https://prove2.me/theorems/0547ebae-555e-4ce6-9686-51504bf693bd
-- title:
--   ZYLightconeConstruction
-- statement:
--   ZYLightconeConstruction
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ZYLightconeConstruction.lean

import Definitions.Def_QAlgorithms_Defs_ZYGraphSchedules
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ZY

variable {N : ℕ}

/-- Implementation helper; source: arxiv-2504.12896v4 PDF p.3. -/
def bfsRefine (G : SimpleGraph (Fin N)) (root : Fin N) : ℕ → Finset (Fin N) → List (Fin N)
  | 0, S => S.sort (· ≤ ·)
  | fuel+1, S => if hs : S.Nonempty then
      let r := if root ∈ S then root else S.min' hs
      let distances := S.attach.image fun v => (G.induce (S : Set (Fin N))).edist
        ⟨r,by dsimp [r]; split_ifs with h; exact h; exact S.min'_mem hs⟩ ⟨v.val,v.property⟩
      (distances.sort (· ≤ ·)).flatMap fun dist =>
        let layer := S.attach.filter fun v => (G.induce (S : Set (Fin N))).edist
          ⟨r,by dsimp [r]; split_ifs with h; exact h; exact S.min'_mem hs⟩
          ⟨v.val,v.property⟩ = dist
        let vertices := layer.image Subtype.val
        let components := vertices.attach.image fun v => vertices.attach.filter fun w =>
          (G.induce (vertices : Set (Fin N))).Reachable v w
        let pieces := components.image fun C => C.image Subtype.val
        (pieces.toList.mergeSort (fun A B => decide ((A.toList.map Fin.val).foldl min N ≤ (B.toList.map Fin.val).foldl min N))).flatMap
          (bfsRefine G root fuel)
    else []

/-- Compute recursive BFS layers from an explicit root; recursively refine connected same-layer pieces until vertices are distinguished; orient edges toward earlier layers and construct the source's topological gate schedule. Tie-break choices are explicit finite classical data. Translate the sink-first source rank to chronological order. DAG, N₋=1, Z-right-Y-left and optimality must be supporting conclusions about the constructed object, not target assumptions/structure fields. Source: arxiv-2504.12896v4 PDF p.3; arxiv-2504.12896v4 PDF p.15; arxiv-2504.12896v4 PDF p.21. -/
def recursiveBFSLayers (G : SimpleGraph (Fin N)) (_connected : G.Connected)
    (root : Fin N) : List (Fin N) := bfsRefine G root (N+1) Finset.univ

/-- Compute recursive BFS layers from an explicit root; recursively refine connected same-layer pieces until vertices are distinguished; orient edges toward earlier layers and construct the source's topological gate schedule. Tie-break choices are explicit finite classical data. Translate the sink-first source rank to chronological order. DAG, N₋=1, Z-right-Y-left and optimality must be supporting conclusions about the constructed object, not target assumptions/structure fields. Source: arxiv-2504.12896v4 PDF p.3; arxiv-2504.12896v4 PDF p.15; arxiv-2504.12896v4 PDF p.21. -/
def lightconeOrientation (G : SimpleGraph (Fin N)) (connected : G.Connected)
    (root : Fin N) : Orientation G where
  arrow := fun i j => decide (G.Adj i j ∧
    ((recursiveBFSLayers G connected root).idxOf j < (recursiveBFSLayers G connected root).idxOf i ∨
      ((recursiveBFSLayers G connected root).idxOf j = (recursiveBFSLayers G connected root).idxOf i ∧ j < i)))
  faithful := by
    intro i j
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have hne := G.ne_of_adj h
      have hij : (i : ℕ) ≠ (j : ℕ) := fun he => hne (Fin.ext he)
      have hsym : G.Adj j i := h.symm
      by_cases he : (recursiveBFSLayers G connected root).idxOf j < (recursiveBFSLayers G connected root).idxOf i
      · exact Or.inl ⟨h,Or.inl he⟩
      · by_cases he2 : (recursiveBFSLayers G connected root).idxOf i < (recursiveBFSLayers G connected root).idxOf j
        · exact Or.inr ⟨hsym,Or.inl he2⟩
        · have heq : (recursiveBFSLayers G connected root).idxOf j = (recursiveBFSLayers G connected root).idxOf i := by omega
          by_cases hj : j < i
          · exact Or.inl ⟨h,Or.inr ⟨heq,hj⟩⟩
          · refine Or.inr ⟨hsym,Or.inr ⟨heq.symm,?_⟩⟩
            simp only [Fin.lt_def] at hj ⊢
            omega
    · rintro (⟨h,_⟩ | ⟨h,_⟩)
      · exact h
      · exact h.symm
  exclusive := by
    intro i j
    simp only [decide_eq_true_eq,Fin.lt_def]
    omega

/-- Compute recursive BFS layers from an explicit root; recursively refine connected same-layer pieces until vertices are distinguished; orient edges toward earlier layers and construct the source's topological gate schedule. Tie-break choices are explicit finite classical data. Translate the sink-first source rank to chronological order. DAG, N₋=1, Z-right-Y-left and optimality must be supporting conclusions about the constructed object, not target assumptions/structure fields. Source: arxiv-2504.12896v4 PDF p.3; arxiv-2504.12896v4 PDF p.15; arxiv-2504.12896v4 PDF p.21. -/
def lightconeGateSequence (G : SimpleGraph (Fin N)) (connected : G.Connected)
    (root : Fin N) : GateSequence (lightconeOrientation G connected root) where
  edges := (directedEdges (lightconeOrientation G connected root)).toList.mergeSort
    (fun e f => decide ((recursiveBFSLayers G connected root).idxOf f.2 ≤
      (recursiveBFSLayers G connected root).idxOf e.2))
  nodup := (Finset.nodup_toList _).mergeSort
  exhaustive := by
    rw [List.toFinset_eq_of_perm _ _ (List.mergeSort_perm _ _),Finset.toList_toFinset]

example (G : SimpleGraph (Fin N)) (root : Fin N) : bfsRefine G root 0 ∅ = [] := by simp [bfsRefine]

end QAlgorithms.ZY



-- Prove2me | Definitions.Def_WeldedPath_Supplement_pLongLabel
-- name    : WeldedPath_Supplement_pLongLabel
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:14:38.397845+00:00
-- url     : https://prove2.me/theorems/58028d7a-cf1a-4b84-bb39-de41186b9fc2
-- title:
--   Recorded inverse-label test for long verifier outputs
-- statement:
--   For a long candidate output, the recorded inverse-label test asks that each of the first $2q+1$ labels $z_i$ have some nonzero structural vertex $v\in V_n\setminus\{0\}$ with $L^{-1}(z_i)=v$ in the label database. The candidate condition includes pairwise distinctness of the output labels. The associated probability $p_{\mathrm{long\text{-}label}$ is defined on the final exact compressed state by the corresponding computational-basis projector. This is the database-side test $\Pi_{\mathrm{AL}}^{(\widehat{\mathrm{cpWT}},>)}$ used to prove the long-output case of Theorem 3.12; including the candidate condition makes explicit the distinctness needed for the ensuing record-count argument.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), proof of Theorem 3.12, long-output case, p.26 (printed p.25), definition of Pi_AL and the |L| ≤ 2q annihilation argument; candidate-path condition from Algorithm 3.9, p.24 (printed p.23).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWtSplit

namespace WeldedPath.Supplement

open QAlgorithms WeldedInstance InjDb

/-- The recorded inverse-label test used for long candidate outputs in the proof of
Theorem 3.12. Every one of the first `2*q+1` distinct nonzero output labels must have a
nonzero structural vertex recorded as its inverse image in the label database. -/
def LongLabelRecorded {n : ℕ} (q : ℕ)
    (out : List (Fin 3 × Qubits (2 * n + 1))) (L : LabelDb n) : Prop :=
  IsCandidatePath out ∧ 2 * q + 1 < out.length ∧
    ∀ i, 1 ≤ i → i ≤ 2 * q + 1 →
      ∃ v : ℕ, IsVertex n v ∧ v ≠ 0 ∧ invL L ((pathLabels out).getD i 0) = some v

open Classical in
/-- Probability of the recorded inverse-label test after the exact compressed execution,
restricted to long candidate outputs. -/
noncomputable def pLongLabel (l : ℕ) {n : ℕ} (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) : ℝ :=
  ‖(diagProj fun p : (QReg n × W) × Db l G =>
      LongLabelRecorded q (out p.1) p.2.1)
    (finalStateDb A (exactCpWT l G) (emptyDb l G))‖ ^ 2

end WeldedPath.Supplement



-- Prove2me | Definitions.Def_LinfContractionFP_Lbl
-- name    : LinfContractionFP_Lbl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:08.403822+00:00
-- url     : https://prove2.me/theorems/93d07b32-b257-4dfe-9b71-bfc96b4b2781
-- title:
--   Face labels $\mathsf{lo}$, $\mathsf{hi}$ (the game labels $-1$, $+1$)
-- statement:
--   The two labels $\mathsf{lo}$ and $\mathsf{hi}$ that a labeling assigns to a face of a box (Definition 1). They are identified with the labels $-1$ and $+1$ of the extremal amplification game (Remark 4); the numerical value $\mathsf{lo}\mapsto-1$, $\mathsf{hi}\mapsto+1$ is used when votes are tallied (Algorithm 3, line 17).
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Definition 1, p.6; Remark 4, p.11

import Mathlib

namespace LinfContractionFP

/-- The two labels `lo` and `hi` of a face (Definition 1, p.6), identified with the labels `−1`
and `+1` of the extremal amplification game (Problem 1 and Remark 4, p.11).

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Definition 1, p.6
("labels ℓ_{i,−}, ℓ_{i,+} ∈ {lo, hi}") and Remark 4, p.11 ("The labels −1 and +1 of Problem 1
are precisely lo and hi returned by Algorithm 2").

**Formalization Note.** One type serves both: `lo` is `−1` and `hi` is `+1`; `Lbl.val` is the
numerical value used in vote tallies (Algorithm 3, line 17). -/
inductive Lbl : Type
  /-- `lo`, the label `−1`. -/
  | lo
  /-- `hi`, the label `+1`. -/
  | hi
  deriving DecidableEq

/-- The numerical value of a label: `lo ↦ −1`, `hi ↦ +1`. -/
def Lbl.val : Lbl → ℤ
  | .lo => -1
  | .hi => 1

end LinfContractionFP



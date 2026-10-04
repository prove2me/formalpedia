-- Prove2me | Definitions.Def_Conway99_Coclique_Overlap_20261004
-- name    : Conway99_Coclique_Overlap_20261004
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T01:44:51.5121+00:00
-- url     : https://prove2.me/theorems/cfd12597-978b-4c1a-96da-aed4e15fcaab
-- title:
--   Coclique vectors in one graph point frame
-- statement:
--   For one finite vertex type and one real 44-dimensional matrix Pi, define y_u as column u and z_C as one seventh of the sum of y_u over C. These pure definitions assert no graph existence, coclique status, or lattice admission.
-- source:
--   proofs/ROOT_COCLIQUE_COMPATIBILITY.md lines 95-107 and 168-184 in archive/clean-start/proof-library.zip, SHA-256 6cbe401d478b7e8627c81d6801585d5949ec254a5bee9878b1f9513cd0244772

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.CocliqueScore

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup E] [Module ℝ E]

noncomputable def cocliqueVector (point : V → E) (C : Finset V) : E :=
  (1 / 7 : ℝ) • ∑ v ∈ C, point v

def pointVector (Pi : Matrix (Fin 44) V ℝ) (u : V) : Fin 44 → ℝ :=
  fun i => Pi i u

noncomputable def graphCocliqueVector (Pi : Matrix (Fin 44) V ℝ)
    (C : Finset V) : Fin 44 → ℝ :=
  cocliqueVector (pointVector Pi) C

end Conway99Formal.CocliqueScore



-- Prove2me | Definitions.Def_Conway99_Admitted_Cocliques_20261003
-- name    : Conway99_Admitted_Cocliques_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T00:17:54.897306+00:00
-- url     : https://prove2.me/theorems/3f20ee22-6af6-4559-8d4d-13d25774c86f
-- title:
--   Admitted coclique and seven-spike vectors in one lattice
-- statement:
--   For a finite point index set V and a real vector space E, a selected additive subgroup L admits a set C when z_C=(sum of its point vectors)/7 belongs to L. Its point p has the associated vector x_Cp=(y_p-z_C)/3. These pure definitions assert neither graph coclique status nor lattice membership of x_Cp.
-- source:
--   proofs/ROOT_COCLIQUE_COMPATIBILITY.md lines 20-51 and 207-223 in archive/clean-start/proof-library.zip, SHA-256 6cbe401d478b7e8627c81d6801585d5949ec254a5bee9878b1f9513cd0244772

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.AdmittedCocliques

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup E] [Module ℝ E]

noncomputable def cocliqueVector (point : V → E) (C : Finset V) : E :=
  (1 / 7 : ℝ) • ∑ u ∈ C, point u

def Admitted (L : AddSubgroup E) (point : V → E) (C : Finset V) : Prop :=
  cocliqueVector point C ∈ L

noncomputable def spikeVector (point : V → E) (C : Finset V) (p : V) : E :=
  (1 / 3 : ℝ) • (point p - cocliqueVector point C)

end Conway99Formal.AdmittedCocliques



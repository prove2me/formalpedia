-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:08.650914+00:00
-- url     : https://prove2.me/theorems/352055fb-3361-5350-b556-01510d7a1066
-- title:
--   Hermitian Insertion Vector Orthogonal
-- statement:
--   Definitions and structural lemmas for Hermitian Insertion Vector Orthogonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
section SpacedProductLowerBound
variable {k : ℕ}
def pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) : Fin m :=
  ⟨if c < i.val then c else c - 1, by split_ifs <;> omega⟩
def ViF (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ) : Fin (2 * (m + 1) + k + 1) → ℂ :=
  fun p => if p = esI k (m + 1) i then 1
    else if h : p.val < m + 1 ∧ p.val ≠ i.val then -star (Vc (pidx m i p.val h) (eI k (m + 1) i)) else 0
variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)
end SpacedProductLowerBound
section N2c
variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)
end N2c
end
end Formalism.FourierDecayAlt.P.SignAntidiagonal



-- Prove2me | Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision
-- name    : Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:52.241237+00:00
-- url     : https://prove2.me/theorems/30457815-8873-43c4-a3ff-09c881c54563
-- title:
--   NPWDivision
-- statement:
--   Definitions and structural lemmas for NPWDivision, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPWDivision.lean

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
noncomputable section
namespace Formalism.FN.WDiv
section General
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
variable [CompleteSpace K]
end General
end Formalism.FN.WDiv
namespace Formalism.FN.WDiv
section PolyDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
def cN (G : K[X]) (N : ℕ) (P : K[X]) : K := P.coeff N / G.coeff N
def QR (G : K[X]) (N : ℕ) : ℕ → K[X] × K[X]
  | 0 => (C (cN G N 1), 1 - C (cN G N 1) * G)
  | m + 1 => (X * (QR G N m).1 + C (cN G N (X * (QR G N m).2)),
      X * (QR G N m).2 - C (cN G N (X * (QR G N m).2)) * G)
variable (G : K[X]) (N : ℕ) {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
  (hGN : ‖G.coeff N‖ * r ^ N = M) (hGle : ∀ j, ‖G.coeff j‖ * r ^ j ≤ M)
  (hGhi : ∀ j, N < j → G.coeff j = 0)
include hr hM hGN hGle hGhi
end PolyDiv
end Formalism.FN.WDiv
namespace Formalism.FN.WDiv
section SeriesDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
def Dq (G : K[X]) (N : ℕ) (f : ℕ → K) (j : ℕ) : K := ∑' m, f m * (QR G N m).1.coeff j
def DR (G : K[X]) (N : ℕ) (f : ℕ → K) (j : ℕ) : K := ∑' m, f m * (QR G N m).2.coeff j
variable (G : K[X]) (N : ℕ) {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
  (hGN : ‖G.coeff N‖ * r ^ N = M) (hGle : ∀ j, ‖G.coeff j‖ * r ^ j ≤ M)
  (hGhi : ∀ j, N < j → G.coeff j = 0)
include hr hM hGN hGle hGhi
end SeriesDiv
section Main
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
def iterF (G : K[X]) (N : ℕ) (H f : ℕ → K) : ℕ → ℕ → K
  | 0 => f
  | i + 1 => fun n => -(cmul (Dq G N (iterF G N H f i)) H n)
end Main
end Formalism.FN.WDiv
namespace Formalism.FN
end Formalism.FN



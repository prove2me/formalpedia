-- Prove2me | Definitions.Def_ProximityTerminalDerivativeCoreV1
-- name    : ProximityTerminalDerivativeCoreV1
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T11:40:09.743679+00:00
-- url     : https://prove2.me/theorems/b70f1b79-0c10-48be-9000-eff86c7923fc
-- title:
--   Terminal derivatives in one distinguished polynomial variable
-- statement:
--   For a polynomial $F$ in four variables over a field, write $R$ for the third variable. This module defines repeated partial differentiation and the first order at which the distinguished-variable degree is zero:
--   $$d_R^jF=\partial_R^jF,\qquad \ell(F)=\min\{j\in\mathbb N:\deg_R(d_R^jF)=0\}.$$
--   The total definition sets $\ell(F)=0$ if that set is empty. The associated theorem proves that the set is nonempty for every polynomial.
--
--   These two definitions supply the interface for terminal-derivative products. The module contains no supporting lemmas; degree bounds and characteristic-dependent nonvanishing belong to the associated proof.
-- source:
--   Derivative-chain support adapted from https://github.com/proximity-prize/proximity-prize/blob/ed2b68c4a330d76dc4ab6693eec81b685b493270/ProximityPrize/SubmissionLower/LowerGeometry.lean#L4020 and the partial-derivative lemmas in LowerFoundation.lean. Finite-product aggregation formalized in this task.
--
--   yukon-proof-operation:71d2a66d-36f6-40c9-bbf4-f29755d30d2f; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTUxNTNhNWM3Y2FhZTRlOThmZmMxOTY5N2VlNDQyYjEyMzIxNmY3OTJhYmQ1ZTBmNTVjMDIzZDVmZjAzYjczYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjcxZDJhNjZkLTM2ZjYtNDBjOS1iYmY0LWYyOTc1NWQzMGQyZjsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eVRlcm1pbmFsRGVyaXZhdGl2ZUNvcmVWMSIsInYiOjJ9]

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped Classical
namespace ProximityTerminalDerivativeCoreV1

noncomputable def dR {K : Type} [Field K] (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  (MvPolynomial.pderiv (2 : Fin 4))^[j] F

noncomputable def chainLength {K : Type} [Field K] (F : MvPolynomial (Fin 4) K) : ℕ :=
  if h : ∃ j, (dR j F).degreeOf 2 = 0 then Nat.find h else 0

end ProximityTerminalDerivativeCoreV1



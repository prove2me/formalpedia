-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:34:02.270979+00:00
-- url     : https://prove2.me/theorems/3a33aa90-fe78-4c36-a69e-a5c857e61b2d
-- title:
--   Centre Block Structure
-- statement:
--   Definitions and structural lemmas for Centre Block Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
section Key
variable {A F : Type} [CommRing A] [CommRing F]
end Key
section Corner
variable {A F : Type} [CommRing A] [CommRing F]
end Corner
section Maps
variable {A F : Type} [CommRing A] [CommRing F]
end Maps
section DVR
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
variable [IsDomain o] [IsDiscreteValuationRing o]
end DVR
section Blocks
variable {A : Type} {r k : ℕ}
variable [CommRing A]
def BT (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧ IsUnit (b22 x).det
def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)
section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
end mk
end Blocks
section Stab
variable {F : Type} [Field F] {r k : ℕ}
end Stab
section Forcing
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}
def cen {A : Type} [CommRing A] (S : Matrix (Fin r) (Fin r) A) : Matrix (Idx r k) (Idx r k) A :=
  mk 1 0 S 1 0 1
variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]
end Forcing
end Formalism.FourierDecayAlt.P.S3x8



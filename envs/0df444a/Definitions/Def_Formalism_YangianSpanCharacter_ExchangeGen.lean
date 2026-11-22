-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_ExchangeGen
-- name    : Formalism_YangianSpanCharacter_ExchangeGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:53.491336+00:00
-- url     : https://prove2.me/theorems/6e591b67-4770-4771-a1e7-fc56a9a0f995
-- title:
--   Exchange Gen
-- statement:
--   Definitions and structural lemmas for Exchange Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/ExchangeGen.lean

import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.YangianSpanCharacter.T
open Matrix
def pt3 {R : Type*} (M : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R :=
  Matrix.of fun a b => M (a.1, a.2.1, b.2.2) (b.1, b.2.1, a.2.2)
def Tbt {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then Tm Y p c ci jl.2 ik.2 else 0
def YBEt : Prop :=
  ∀ (R : Type) [CommRing R] (Y Y' Yb : R),
    ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) - sizeConstantAtParamsWeight R) *
        pt3 ((Yb - Y') • 1 - flipOneThree R) * pt3 ((Yb - Y) • 1 - flipTwoThree R) =
      pt3 ((Yb - Y) • 1 - flipTwoThree R) * pt3 ((Yb - Y') • 1 - flipOneThree R) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) - sizeConstantAtParamsWeight R)
def ExchangeT : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci : A) (Y Yb : R),
    WeylRel p c ci →
      Tbt Yb p c ci * pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) *
          T1 Y p c ci =
        T1 Y p c ci * pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) *
          Tbt Yb p c ci
def Gauge : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci hi θ : A) (Y : R),
    hi * c = c * hi → hi * ci = ci * hi → p * hi = hi * p - hi * θ →
      Tm Y p c ci * Matrix.diagonal (fun _ => hi) =
        Matrix.diagonal (fun _ => hi) * (Tm Y p c ci - !![θ, 0; 0, 0])
def JFlip : Prop :=
  ∀ (R : Type) [CommRing R],
    J0 R * (-J0 R) = 1 ∧ J0 R * (1 - Pf R) * (-J0 R) = pt1 (Pf R)
def E1 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0
def E2 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0
def ExchangeGen : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (M0 Mb : Matrix (Fin 2) (Fin 2) A) (d : R),
    (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 Mb * E2 M0 =
        E2 M0 * E1 Mb * (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) →
      E2 Mbᵀ * pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M0 =
        E1 M0 * pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E2 Mbᵀ
end Formalism.YangianSpanCharacter.T



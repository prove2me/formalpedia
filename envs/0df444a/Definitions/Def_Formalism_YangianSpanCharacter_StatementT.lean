-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_StatementT
-- name    : Formalism_YangianSpanCharacter_StatementT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:39.204971+00:00
-- url     : https://prove2.me/theorems/81dafe37-aa4e-42a9-b776-54e67d977af4
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/StatementT.lean

import Mathlib
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
def J (A : Type*) [Ring A] : Matrix (Fin 2) (Fin 2) A := !![0, 1; -1, 0]
def Tm {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2) (Fin 2) A :=
  !![algebraMap R A Y + p, -c; ci, 0]
def WeylRel {A : Type*} [Ring A] (p c ci : A) : Prop :=
  c * ci = 1 ∧ ci * c = 1 ∧ p * c = c * p + c
def T1 {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then Tm Y p c ci ik.1 jl.1 else 0
def T2 {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then Tm Y p c ci ik.2 jl.2 else 0
def Pf (A : Type*) [Ring A] : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.2 ∧ ik.2 = jl.1 then 1 else 0
def Um {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (s : R) : Matrix (Fin 2) (Fin 2) A :=
  !![1, 0; -algebraMap R A s, 1]
def Uinv {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (s : R) : Matrix (Fin 2) (Fin 2) A :=
  !![1, 0; algebraMap R A s, 1]
def TJT : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci : A) (Y : R),
    WeylRel p c ci → (Tm (Y + 1) p c ci)ᵀ * J A * Tm Y p c ci = J A
def TvJTstar : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] (p c ci : A) (Y : ℝ),
    WeylRel p c ci → (Tm (Y + 1) p c ci).map star * J A * (Tm Y p c ci)ᴴ = J A
def RTT : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci : A) (Y Y' : R),
    WeylRel p c ci →
      ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * T1 Y' p c ci *
          T2 Y p c ci =
        T2 Y p c ci * T1 Y' p c ci *
          ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)
def PlaneWave : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci f : A) (s Y : R),
    f * c = c * f → f * ci = ci * f → p * f = f * p + algebraMap R A s * f * c →
      Um (A := A) s * Uinv s = 1 ∧ Uinv (A := A) s * Um s = 1 ∧
        Tm Y p c ci * Matrix.diagonal (fun _ => f) * Uinv s =
          Matrix.diagonal (fun _ => f) * Tm Y p c ci
def UJU : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (s : R),
    (Um (A := A) s)ᵀ * J A * Um s = J A
def DualityCore : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (TT₀ TT₁ : Matrix (Fin 2) (Fin 2) A)
    (q : Rˣ),
    TT₀ * J A * TT₁ᵀ = (q : R) • J A → TT₀ * (-(((q⁻¹ : Rˣ) : R) • (J A * TT₁ᵀ))) = (J A)ᵀ
def sizeConstantAtParamsWeight (R : Type*) [CommRing R] : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R :=
  Matrix.of fun a b => if a.1 = b.2.1 ∧ a.2.1 = b.1 ∧ a.2.2 = b.2.2 then 1 else 0
def flipOneThree (R : Type*) [CommRing R] : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R :=
  Matrix.of fun a b => if a.1 = b.2.2 ∧ a.2.2 = b.1 ∧ a.2.1 = b.2.1 then 1 else 0
def flipTwoThree (R : Type*) [CommRing R] : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R :=
  Matrix.of fun a b => if a.1 = b.1 ∧ a.2.1 = b.2.2 ∧ a.2.2 = b.2.1 then 1 else 0
def YBE : Prop :=
  ∀ (R : Type) [CommRing R] (u v : R),
    ((u - v) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) - sizeConstantAtParamsWeight R) *
        (u • 1 - flipOneThree R) * (v • 1 - flipTwoThree R) =
      (v • 1 - flipTwoThree R) * (u • 1 - flipOneThree R) *
        ((u - v) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) - sizeConstantAtParamsWeight R)
def J0 (R : Type*) [CommRing R] : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then J R ik.1 jl.1 else 0
def pt0 {R : Type*} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  Matrix.of fun ik jl => M (jl.1, ik.2) (ik.1, jl.2)
def pt1 {R : Type*} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  Matrix.of fun ik jl => M (ik.1, jl.2) (jl.1, ik.2)
def PlusLetter : Prop :=
  ∀ (R : Type) [CommRing R] (D : R),
    pt0 ((D + 1) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) - Pf R) * J0 R *
          (D • 1 - Pf R) = ((D + 1) * (D - 1)) • J0 R ∧
      (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) - Pf R) * J0 R *
          pt0 ((D + 1) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) - Pf R) =
        ((D + 1) * (D - 1)) • J0 R
def MinusLetter : Prop :=
  ∀ (R : Type) [CommRing R] (d : R),
    pt0 (pt1 ((d - 1) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) - Pf R)) * J0 R *
        pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) - Pf R) = (d * (d - 2)) • J0 R ∧
      pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) - Pf R) * J0 R *
          pt0 (pt1 ((d - 1) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) - Pf R)) =
        (d * (d - 2)) • J0 R
open scoped Kronecker in

def FlipCommute : Prop :=
  ∀ (R : Type) [CommRing R] (g gi : Matrix (Fin 2) (Fin 2) R), g * gi = 1 → gi * g = 1 →
    (g ⊗ₖ g) * Pf R = Pf R * (g ⊗ₖ g) ∧ (giᵀ ⊗ₖ g) * pt1 (Pf R) = pt1 (Pf R) * (giᵀ ⊗ₖ g)
def pM : Module.End ℚ (ℤ → ℚ) where
  toFun f n := (n : ℚ) * f n
  map_add' f g := by funext n; simp [mul_add]
  map_smul' a f := by funext n; simp; ring
def cM : Module.End ℚ (ℤ → ℚ) := LinearMap.funLeft ℚ ℚ (fun n : ℤ => n - 1)
def ciM : Module.End ℚ (ℤ → ℚ) := LinearMap.funLeft ℚ ℚ (fun n : ℤ => n + 1)
def WeylModel : Prop := WeylRel pM cM ciM
end Formalism.YangianSpanCharacter.T



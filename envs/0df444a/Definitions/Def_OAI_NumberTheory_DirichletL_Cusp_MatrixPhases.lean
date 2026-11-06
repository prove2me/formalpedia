-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
-- name    : OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:21:00.577632+00:00
-- url     : https://prove2.me/theorems/16231232-748a-4402-94a0-04bafe3dd324
-- title:
--   Matrix Phases
-- statement:
--   Definitions and structural lemmas for Matrix Phases, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
set_option autoImplicit false
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
def U (t : R) : Matrix (Fin 2) (Fin 2) R := !![1,t;0,1]
def L (t : R) : Matrix (Fin 2) (Fin 2) R := !![1,0;t,1]
def E : Matrix (Fin 2) (Fin 2) R := !![0,-1;1,0]
end ShortDraftCusp
namespace ShortDraftConcretePhase
open ShortDraftTrace
end ShortDraftConcretePhase
namespace ShortDraftGauss
open Complex
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGauss
namespace EisensteinRayPhase
abbrev SquareClass := ZMod 2 × ZMod 2
def R (a b : SquareClass) : ℤ :=
  (-1) ^ (a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val)
end EisensteinRayPhase
namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]
end ShortDraftSextic
namespace ShortDraftGaussJacobi
open Finset
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGaussJacobi
namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftQuadraticGauss
namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]
end ShortDraftQuotientPhase
namespace EisensteinEPrimaryPhase
abbrev Coord := ZMod 4 × ZMod 4
abbrev Bit := ZMod 2
def mul (x y : Coord) : Coord :=
  (x.1 * y.1 - x.2 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.2 * y.2)
def odd (x : Coord) : Prop := x.1.val % 2 = 1 ∨ x.2.val % 2 = 1
instance : DecidablePred odd := fun x =>
  inferInstanceAs (Decidable (x.1.val % 2 = 1 ∨ x.2.val % 2 = 1))
def rep (e f : Bit) : Coord :=
  if f = 0 then (if e = 0 then (1, 0) else (-1, 0))
  else (if e = 0 then (1, 2) else (-1, -2))
def norm (x : Coord) : ZMod 4 :=
  x.1 * x.1 - x.1 * x.2 + x.2 * x.2
def ePrimary (x : Coord) : Prop :=
  let cube := mul (mul x x) x
  cube.1 - 2 * cube.2 = 1
instance : DecidablePred ePrimary := fun x =>
  inferInstanceAs (Decidable ((mul (mul x x) x).1 -
    2 * (mul (mul x x) x).2 = 1))
def signBit (x : Coord) : Bit := if ePrimary x then 0 else 1
def normBit (x : Coord) : Bit := if norm x = 1 then 0 else 1
def bits (x : Coord) : Bit × Bit := (signBit x, normBit x)
end EisensteinEPrimaryPhase
namespace ShortDraftGaussianPhaseTable
abbrev SquareClass := ZMod 2 × ZMod 2
def phase (a : SquareClass) : ZMod 4 :=
  if a.2 = 0 then 0 else if a.1 = 0 then 1 else 3
def reciprocity (a b : SquareClass) : ZMod 4 :=
  2 * ((a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val : ℕ) : ZMod 4)
end ShortDraftGaussianPhaseTable
namespace ActualEisensteinCoordinates
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K
def omega : O := hζ.toInteger
def pb : PowerBasis ℤ O := hζ.integralPowerBasis
theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]
theorem pb_gen : pb.gen = omega := by
  exact hζ.integralPowerBasis_gen
theorem exists_coordinates (x : O) :
    ∃ a b : ℤ, x = (a : O) + (b : O) * omega := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨a, b, ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hi1 : (i1 : ℕ) = 1 := rfl
  simpa [a, b, hi0, hi1, pb_gen, smul_eq_mul, mul_comm] using hsum.symm
def i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
def i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
def eval (a b : ℤ) : O := (a : O) + (b : O) * omega
theorem exists_pair (x : O) :
    ∃ p : ℤ × ℤ, eval p.1 p.2 = x := by
  obtain ⟨a, b, h⟩ := exists_coordinates x
  exact ⟨(a, b), h.symm⟩
def coords (x : O) : ℤ × ℤ := Classical.choose (exists_pair x)
def residue (x : O) : EisensteinEPrimaryPhase.Coord :=
  ((coords x).1, (coords x).2)
def lift (v : EisensteinEPrimaryPhase.Coord) : O :=
  eval (v.1.val : ℤ) (v.2.val : ℤ)
def rayBits (x : O) : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit :=
  EisensteinEPrimaryPhase.bits (residue x)
def rayPhaseBits (a b : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) : ℤ :=
  (-1) ^ (a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val)
def rayPhase (x y : O) : ℤ := rayPhaseBits (rayBits x) (rayBits y)
end ActualEisensteinCoordinates
end
end OAI



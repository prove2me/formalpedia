-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
-- name    : MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:49:20.419319+00:00
-- url     : https://prove2.me/theorems/c26b4f6a-048b-4480-a10d-74846b77cb54
-- title:
--   Definitions of BinaryArtinSchreierTower: A uniform effective step of the binary Artin–Schreier tower
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreierTower` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # A uniform effective step of the binary Artin–Schreier tower
--
--   **Definitions** (9): `MIPRE.LowDegree.BinaryArtinSchreier.TowerInvariant` (A valid stage records the exact power-of-two width and the cubic no-root invariant.); `MIPRE.LowDegree.BinaryArtinSchreier.cubicParameterBits` (The uniform parameter `α³ + α²` in the supplied quotient.); `MIPRE.LowDegree.BinaryArtinSchreier.cubicParameterBitsProg`; `MIPRE.LowDegree.BinaryArtinSchreier.parameterOrbitBits` (The coefficient list of the parameter's complete old-field Frobenius product.); `MIPRE.LowDegree.BinaryArtinSchreier.quotientFintype`; `MIPRE.LowDegree.BinaryArtinSchreier.rootVectorBits` (The canonical quotient root, computed by multiplying the encoded unit by `X`.); `MIPRE.LowDegree.BinaryArtinSchreier.rootVectorBitsProg`; `MIPRE.LowDegree.BinaryArtinSchreier.towerStepBits` (Form the parameter's complete Frobenius product and substitute `X² + X`.); `MIPRE.LowDegree.BinaryArtinSchreier.towerStepBitsProg` (A single ambient program for one tower step, valid also on malformed moduli.).
--
--   **Embedded lemmas** (14): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `cubicParameterBitsProg_apply`, `cubicParameterBits_length`, `evalBits_cubicParameterBits`, `evalBits_rootVectorBits`, `parameterOrbitBits_length`, `parameterOrbitBits_spec`, `quotientCharP`, `quotientFiniteDimensional`, `rootVectorBitsProg_apply`, `rootVectorBits_length`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreierTower` (`MIPRE/Foundations/LowDegree/BinaryArtinSchreierTower.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 38 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryArtinSchreierTower.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierTower.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_shiftReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_shiftReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_natDegree_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_polyOfBits_substituteArtinSchreierBits
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_eval_orbitPolynomial
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_map_orbitPolynomialBits
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_orbitPolynomialBits_monic_natDegree
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_root_eq

/-! # A uniform effective step of the binary Artin–Schreier tower -/

noncomputable section

namespace MIPRE.LowDegree.BinaryArtinSchreier

open Cost Cost.PolyTimeFun BinaryPolynomial BinaryQuotient Polynomial

/-- The canonical quotient root, computed by multiplying the encoded unit by `X`. -/
def rootVectorBits (p : BitStr) : BitStr := shiftReduce p (oneBits p)

@[simp] theorem rootVectorBits_length (p : BitStr) : (rootVectorBits p).length = p.length := by
  exact length_shiftReduce p _ (length_oneBits p)

theorem evalBits_rootVectorBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (p : BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) :
    evalBits z (rootVectorBits p) = z := by
  rw [rootVectorBits, evalBits_shiftReduce z p _ (length_oneBits p) hz,
    evalBits_oneBits z p hp, mul_one]

/-- The uniform parameter `α³ + α²` in the supplied quotient. -/
def cubicParameterBits (p : BitStr) : BitStr :=
  let x := rootVectorBits p
  let y := mulReduce p x x
  xorBits (mulReduce p y x) y

@[simp] theorem cubicParameterBits_length (p : BitStr) :
    (cubicParameterBits p).length = p.length := by
  simp only [cubicParameterBits, length_xorBits,
    length_mulReduce p _ _ (rootVectorBits_length p)]
  rw [length_mulReduce p _ _ (length_mulReduce p _ _ (rootVectorBits_length p))]
  exact min_self _

theorem evalBits_cubicParameterBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (p : BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) :
    evalBits z (cubicParameterBits p) = z ^ 3 + z ^ 2 := by
  have hx := rootVectorBits_length p
  have hy := length_mulReduce p (rootVectorBits p) (rootVectorBits p) hx
  rw [cubicParameterBits, evalBits_xor z _ _ (by
    rw [length_mulReduce p _ _ hy, hy]), evalBits_mulReduce z p _ _ hy hz,
    evalBits_mulReduce z p _ _ hx hz, evalBits_rootVectorBits z p hp hz]
  ring

def rootVectorBitsProg : PolyTimeFun BitStr BitStr :=
  shiftReduceProg.comp ((PolyTimeFun.id _).pair oneBitsProg)

def cubicParameterBitsProg : PolyTimeFun BitStr BitStr :=
  let x := rootVectorBitsProg
  let y := mulReduceProg.comp ((PolyTimeFun.id _).pair (x.pair x))
  xorBitsProg.comp ((mulReduceProg.comp ((PolyTimeFun.id _).pair (y.pair x))).pair y)

@[simp] theorem rootVectorBitsProg_apply (p : BitStr) : rootVectorBitsProg p = rootVectorBits p := rfl
@[simp] theorem cubicParameterBitsProg_apply (p : BitStr) :
    cubicParameterBitsProg p = cubicParameterBits p := rfl

/-- Form the parameter's complete Frobenius product and substitute `X² + X`. -/
def towerStepBits (p : BitStr) : BitStr :=
  substituteArtinSchreierBits (orbitPolynomialBits (unary p.length) p (cubicParameterBits p))

/-- A single ambient program for one tower step, valid also on malformed moduli. -/
def towerStepBitsProg : PolyTimeFun BitStr BitStr :=
  substituteArtinSchreierBitsProg.comp (orbitPolynomialBitsProg.comp
    (length.pair ((PolyTimeFun.id _).pair cubicParameterBitsProg)))

@[simp] theorem towerStepBitsProg_apply (p : BitStr) : towerStepBitsProg p = towerStepBits p := rfl

/-- The coefficient list of the parameter's complete old-field Frobenius product. -/
def parameterOrbitBits (p : BitStr) : BitStr :=
  orbitPolynomialBits (unary p.length) p (cubicParameterBits p)

@[simp] theorem parameterOrbitBits_length (p : BitStr) :
    (parameterOrbitBits p).length = p.length + 1 := by
  simp [parameterOrbitBits, orbitPolynomialBits, descendBits, unary]

local instance quotientFintype (p : BitStr) : Fintype (AdjoinRoot (polyOfBits (p ++ [true]))) :=
  Fintype.ofEquiv (Fin (polyOfBits (p ++ [true])).natDegree → ZMod 2)
    (coordinateEquiv _ (monic_polyOfBits_append_true p)).symm.toEquiv

local instance quotientFiniteDimensional (p : BitStr) :
    Module.Finite (ZMod 2) (AdjoinRoot (polyOfBits (p ++ [true]))) :=
  (monic_polyOfBits_append_true p).finite_adjoinRoot

local instance quotientCharP (p : BitStr) [Fact (Irreducible (polyOfBits (p ++ [true])))] :
    CharP (AdjoinRoot (polyOfBits (p ++ [true]))) 2 :=
  charP_of_injective_ringHom (AdjoinRoot.of _).injective 2

theorem quotient_finrank (p : BitStr) :
    Module.finrank (ZMod 2) (AdjoinRoot (polyOfBits (p ++ [true]))) = p.length := by
  rw [(AdjoinRoot.powerBasis' (monic_polyOfBits_append_true p)).finrank]
  exact natDegree_polyOfBits_append_true p

theorem quotient_pow_card (p : BitStr) [Fact (Irreducible (polyOfBits (p ++ [true])))]
    (x : AdjoinRoot (polyOfBits (p ++ [true]))) : x ^ (2 ^ p.length) = x := by
  have hcard : Fintype.card (AdjoinRoot (polyOfBits (p ++ [true]))) = 2 ^ p.length := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, quotient_finrank]
  rw [← hcard]
  exact FiniteField.pow_card x

/-- The descended complete orbit is monic of the old field degree and annihilates
its cubic parameter; repeated conjugates cause no difficulty. -/
theorem parameterOrbitBits_spec (p : BitStr) [Fact (Irreducible (polyOfBits (p ++ [true])))]
    (hp : p ≠ []) :
    (polyOfBits (parameterOrbitBits p)).Monic ∧
      (polyOfBits (parameterOrbitBits p)).natDegree = p.length ∧
      aeval (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2)
        (polyOfBits (parameterOrbitBits p)) = 0 := by
  let f := polyOfBits (p ++ [true])
  have hm : f.Monic := monic_polyOfBits_append_true p
  have hd : p.length = f.natDegree := (natDegree_polyOfBits_append_true p).symm
  have hc : evalBits (AdjoinRoot.root f) (cubicParameterBits p) ^
      (2 ^ (unary p.length).length) = evalBits (AdjoinRoot.root f) (cubicParameterBits p) := by
    simpa [unary] using quotient_pow_card p (evalBits (AdjoinRoot.root f) (cubicParameterBits p))
  have hs := orbitPolynomialBits_monic_natDegree f hm (unary p.length) p (cubicParameterBits p)
    hd rfl hp (cubicParameterBits_length p) hc
  refine ⟨hs.1, by simpa [parameterOrbitBits, unary] using hs.2, ?_⟩
  have he := evalBits_cubicParameterBits (AdjoinRoot.root f) p hp (root_eq f p rfl)
  rw [← he, aeval_def, eval₂_eq_eval_map, parameterOrbitBits,
    map_orbitPolynomialBits f hm (unary p.length) p (cubicParameterBits p) hd rfl hp
      (cubicParameterBits_length p) hc]
  exact eval_orbitPolynomial _ _ (by simpa [unary] using List.length_pos_iff.mpr hp)

/-- One valid power-of-two tower stage gives the next irreducible flat binary polynomial. -/
theorem towerStepBits_irreducible (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (t : ℕ) (hd : p.length = 2 ^ t)
    (hc : Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2))) :
    Irreducible (polyOfBits (towerStepBits p)) := by
  have hp : p ≠ [] := List.length_pos_iff.mp (by rw [hd]; positivity)
  obtain ⟨hg, hgd, hgz⟩ := parameterOrbitBits_spec p hp
  have h := comp_quadratic_irreducible t ((quotient_finrank p).trans hd) _ hc
    (polyOfBits (parameterOrbitBits p)) hg (hgd.trans hd) hgz
  simpa only [towerStepBits, polyOfBits_substituteArtinSchreierBits, quadratic, C_0,
    add_zero, parameterOrbitBits] using h

/-- A valid stage records the exact power-of-two width and the cubic no-root invariant. -/
structure TowerInvariant (p : BitStr) (t : ℕ) : Prop where
  width : p.length = 2 ^ (t + 1)
  irreducible : Irreducible (polyOfBits (p ++ [true]))
  cubic : let : Fact (Irreducible (polyOfBits (p ++ [true]))) := ⟨irreducible⟩
    Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2))

end MIPRE.LowDegree.BinaryArtinSchreier

end



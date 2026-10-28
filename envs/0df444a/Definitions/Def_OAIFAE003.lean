-- Prove2me | Definitions.Def_OAIFAE003
-- name    : OAIFAE003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T19:27:21.858786+00:00
-- url     : https://prove2.me/theorems/f4dd4f57-347e-4ab7-ac86-8dcbba8704c2
-- title:
--   Definitions bundle OAIFAE003 of the split of OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteAlgebraicEnvelopes.main`, carved from OpenAI's openai/math development (OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 822 declarations of OpenAI's Lean: 207 definitions, 7 inductive types or structures, 23 instances and 585 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.blockMap`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.combPermutation`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.equivVal`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.merge`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.codeHom`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.descendCode`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.monoidWithZero`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Selectors.stageEquiv`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.base`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.groupEval`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqFiniteY_4`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqLetterSigmaProdBoolState_4`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigma_5`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigmaΓFamilyQ`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigmaΓFamilyQ_1`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instFintypeLetterSigmaProdBoolState_2`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.commandCode`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.commandPrimcodable`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.dummy`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.leftCross`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.movePrimcodable`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.pathCode`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.pathPrimcodable`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.staticBoundary`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.surfaceCode`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.surfacePrimcodable`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Instruction.code`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Path.Sector.code`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.Action.code`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.push`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.flip`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.rightStep`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.cleanAnchor`, `OAI.FiniteAlgebraicEnvelopes.Enveloping.act`, `OAI.FiniteAlgebraicEnvelopes.FiniteAffine.Free`, `OAI.FiniteAlgebraicEnvelopes.FiniteAffine.N`, `OAI.FiniteAlgebraicEnvelopes.FiniteAffine.Presentation`, `OAI.FiniteAlgebraicEnvelopes.FiniteAffine.base`, `OAI.FiniteAlgebraicEnvelopes.FiniteAffine.equivalence`, `OAI.FiniteAlgebraicEnvelopes.FiniteAffine.freeMap` and 174 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler, in whole or in part: `ActionEnvelope`, `Affine`, `AffineModules`, `AlgebraPresentations`, `BinaryCoherence`, `CantorBricks`, `Control`, `Corners`, `Diagrams`, `Effectivity`, `EndpointCoherence`, `Enveloping`, `FinitePresentation`, `Generators`, `MonoidAlgebras`, `Normalization`, `PartialAffine`, `Quotients`, `Rewriting`, `Selectors`, `SelfReference`, `Steinberg`, `SteinbergLimits`, `SteinbergPresentation`, `TapeFolding`, `Transition`, `TreeCoherence`, `TreeRefinement`, `Trees`, `TwistedSimplicity`, `UniformControl`, `UniformMachines`, `UniformPaths`.
--
--   **Imports.** It imports the published bundle `Def_BooneHigman`; the bundles `OAIFAE000` and `OAIFAE001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIFAE004`; the statement `OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.finitelyPresented`.
-- source:
--   OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler at commit adc7f12

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_OAIFAE000
import Definitions.Def_OAIFAE001

section
-- module Solutions.OAIFAE.Steinberg
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Nonunital correction, Steinberg groups, corners, and kernel annihilation.
-/


namespace FiniteAlgebraicEnvelopes

universe u


/-! The correction for a nonunital coefficient map in the affine transition and product identities.
The proof works over a noncommutative ring. -/


/-! The Steinberg presentation in the Steinberg kernel argument.  No stability or centrality
 theorem is assumed.  Root indices are restricted to the off-diagonal. -/
namespace Steinberg
open scoped commutatorElement

variable {ι R S : Type*} [Ring R] [Ring S]

section MatrixRepresentation
variable [Fintype ι] [DecidableEq ι]

/-- Naturality of the matrix action for a nonunital coefficient map. -/
theorem matrixMap_coefficientMap (ψ : R →ₙ+* S) (z : Group ι R) :
    matrixMap (coefficientMap ψ z) =
      Units.map (correctedMap (matrixNonunitalMap ψ)) (matrixMap z) := by
  have h : (matrixMap (ι := ι) (R := S)).comp (coefficientMap ψ) =
      (Units.map (correctedMap (matrixNonunitalMap ψ))).comp matrixMap := by
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change matrixMap (coefficientMap ψ (root i j hij a)) =
      Units.map _ (matrixMap (root i j hij a))
    rw [coefficientMap_root, matrixMap_root, matrixMap_root]
    apply Units.ext
    change 1 + Matrix.single i j (ψ a) =
      1 + ((1 + Matrix.single i j a) - 1).map ψ
    rw [add_sub_cancel_left, Matrix.map_single _ _ _ ψ]
  exact DFunLike.congr_fun h z

/-- In particular, coefficient maps preserve the full matrix kernel. -/
theorem coefficientMap_preserves_kernel (ψ : R →ₙ+* S) (z : Group ι R)
    (hz : matrixMap z = 1) : matrixMap (coefficientMap ψ z) = 1 := by
  rw [matrixMap_coefficientMap, hz, map_one]

/- The row-and-column argument of the Steinberg kernel argument starts with the column roots.
Taking a finite coproduct is legitimate because these root subgroups commute. -/

theorem column_add (k : ι) (v w : ι → R) :
    column k (v + w) = column k v * column k w := (columnAddHom k).map_add v w

theorem elementary_mulVec (i j : ι) (h : i ≠ j) (a : R) (v : ι → R) :
    Matrix.mulVec (elementary i j h a).val v = v + Pi.single i (a * v j) := by
  rw [elementary_val, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

/-- Conjugation by one root acts on the external column as its elementary matrix. -/
theorem x_conjugate_column (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : R) (v : ι → R) :
    x i j a * column k v * (x i j a)⁻¹ =
      column k (Matrix.mulVec (elementary i j hij a).val v) := by
  have hh : (conjugateAddHom (x i j a)).comp (columnAddHom k) =
      (columnAddHom k).comp (mulVecAddHom (elementary i j hij a).val) := by
    apply AddMonoidHom.pi_ext
    intro l b
    change x i j a * column k (Pi.single l b) * (x i j a)⁻¹ =
      column k (Matrix.mulVec (elementary i j hij a).val (Pi.single l b))
    rw [column_single, elementary_mulVec, column_add, column_single, column_single]
    by_cases hlj : l = j
    · subst l
      rw [Pi.single_eq_same]
      calc
        x i j a * x j k b * (x i j a)⁻¹ = ⁅x i j a, x j k b⁆ * x j k b := by
          simp [commutatorElement_def, mul_assoc]
        _ = x i k (a * b) * x j k b := by rw [x_chain i j k hij hjk hik]
        _ = x j k b * x i k (a * b) := (column_roots_commute i j k (a * b) b).eq
    · rw [Pi.single_eq_of_ne (Ne.symm hlj), mul_zero, x_zero, mul_one]
      rw [(x_distant i j l k hik (Ne.symm hlj) a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun hh v

/-- Words generated without using the index k. -/
def omitting (k : ι) : Subgroup (Group ι R) :=
  Subgroup.closure {g | ∃ (i j : ι) (a : R), i ≠ k ∧ j ≠ k ∧ g = x i j a}

omit [Fintype ι] in
 theorem x_mem_omitting (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) (a : R) :
    x i j a ∈ omitting k := Subgroup.subset_closure ⟨i, j, a, hik, hjk, rfl⟩

/-- External-column action for an arbitrary word omitting k, not just for generators. -/
theorem conjugate_column_of_mem_omitting (k : ι) {z : Group ι R} (hz : z ∈ omitting k)
    (v : ι → R) : z * column k v * z⁻¹ = column k (Matrix.mulVec (matrixMap z).val v) := by
  induction hz using Subgroup.closure_induction generalizing v with
  | mem z hz =>
    obtain ⟨i, j, a, hik, hjk, rfl⟩ := hz
    by_cases hij : i = j
    · subst j; simp
    rw [x_of_ne i j hij, matrixMap_root, ← x_of_ne i j hij]
    exact x_conjugate_column i j k hij hik hjk a v
  | one => simp
  | mul z w _ _ ihz ihw =>
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← ihz, ← ihw]
    group
  | inv z _ ih =>
    have h := ih (Matrix.mulVec ((matrixMap z)⁻¹).val v)
    have hv : Matrix.mulVec (matrixMap z).val
        (Matrix.mulVec ((matrixMap z)⁻¹).val v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hv] at h
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using (congrArg (fun t => z⁻¹ * t * z) h).symm

theorem row_add (k : ι) (v w : ι → R) :
    row k (v + w) = row k v * row k w := (rowAddHom k).map_add v w

theorem elementary_inv_vecMul (i j : ι) (h : i ≠ j) (a : R) (v : ι → R) :
    Matrix.vecMul v ((elementary i j h a)⁻¹).val = v + Pi.single j (-(v i * a)) := by
  rw [elementary_inv_val, Matrix.vecMul_sub, Matrix.vecMul_one, vecMul_single_matrix]
  ext l
  by_cases hl : l = j
  · subst l; simp [sub_eq_add_neg]
  · simp [sub_eq_add_neg, Pi.single_eq_of_ne hl]

/-- Row form of the one-root conjugation identity. -/
theorem x_conjugate_row (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : R) (v : ι → R) :
    x i j a * row k v * (x i j a)⁻¹ =
      row k (Matrix.vecMul v ((elementary i j hij a)⁻¹).val) := by
  have hh : (conjugateAddHom (x i j a)).comp (rowAddHom k) =
      (rowAddHom k).comp (vecMulAddHom ((elementary i j hij a)⁻¹).val) := by
    apply AddMonoidHom.pi_ext
    intro l b
    change x i j a * row k (Pi.single l b) * (x i j a)⁻¹ =
      row k (Matrix.vecMul (Pi.single l b) ((elementary i j hij a)⁻¹).val)
    rw [row_single, elementary_inv_vecMul, row_add, row_single, row_single]
    by_cases hli : l = i
    · subst l
      rw [Pi.single_eq_same]
      calc
        x i j a * x k i b * (x i j a)⁻¹ = ⁅x i j a, x k i b⁆ * x k i b := by
          simp [commutatorElement_def, mul_assoc]
        _ = (⁅x k i b, x i j a⁆)⁻¹ * x k i b := by rw [commutatorElement_inv]
        _ = x k j (-(b * a)) * x k i b := by
          rw [x_chain k i j hik.symm hij hjk.symm, x_neg]
        _ = x k i b * x k j (-(b * a)) :=
          (row_roots_commute j i k (-(b * a)) b).eq
    · rw [Pi.single_eq_of_ne (Ne.symm hli), zero_mul, neg_zero, x_zero, mul_one]
      rw [(x_distant i j k l (Ne.symm hli) hjk a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun hh v

/-- External-row action for arbitrary words omitting k. -/
theorem conjugate_row_of_mem_omitting (k : ι) {z : Group ι R} (hz : z ∈ omitting k)
    (v : ι → R) : z * row k v * z⁻¹ = row k (Matrix.vecMul v ((matrixMap z)⁻¹).val) := by
  induction hz using Subgroup.closure_induction generalizing v with
  | mem z hz =>
    obtain ⟨i, j, a, hik, hjk, rfl⟩ := hz
    by_cases hij : i = j
    · subst j; simp
    rw [x_of_ne i j hij, matrixMap_root, ← x_of_ne i j hij]
    exact x_conjugate_row i j k hij hik hjk a v
  | one => simp
  | mul z w _ _ ihz ihw =>
    simp only [map_mul, mul_inv_rev, Units.val_mul]
    rw [← Matrix.vecMul_vecMul, ← ihz, ← ihw]
    group
  | inv z _ ih =>
    have h := ih (Matrix.vecMul v (matrixMap z).val)
    have hv : Matrix.vecMul (Matrix.vecMul v (matrixMap z).val)
        ((matrixMap z)⁻¹).val = v := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.vecMul_one]
    rw [hv] at h
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using (congrArg (fun t => z⁻¹ * t * z) h).symm

/-- A Steinberg element with trivial matrix and an unused index is central.
This is the first centrality statement in the Steinberg kernel argument, with no rank-stability assumption. -/
theorem central_of_omitting (k : ι) {z : Group ι R} (hz : z ∈ omitting k)
    (hπ : matrixMap z = 1) : z ∈ Subgroup.center (Group ι R) := by
  have hc (i : ι) (a : R) : Commute z (x i k a) := by
    have h := conjugate_column_of_mem_omitting k hz (Pi.single i a)
    simp only [hπ, Units.val_one, Matrix.one_mulVec, column_single] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hr (i : ι) (a : R) : Commute z (x k i a) := by
    have h := conjugate_row_of_mem_omitting k hz (Pi.single i a)
    simp only [hπ, inv_one, Units.val_one, Matrix.vecMul_one, row_single] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hx (i j : ι) (hij : i ≠ j) (a : R) : Commute z (root i j hij a) := by
    rw [← x_of_ne i j hij]
    by_cases hik : i = k
    · subst i; exact hr j a
    by_cases hjk : j = k
    · subst j; exact hc i a
    have hchain := x_chain i k j hik (Ne.symm hjk) hij a (1 : R)
    rw [mul_one] at hchain
    rw [← hchain]
    exact commute_commutator (hc i a) (hr j 1)
  rw [Subgroup.mem_center_iff]
  intro w
  have hw : w ∈ Subgroup.centralizer ({z} : Set (Group ι R)) := by
    apply PresentedGroup.generated_by
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx i j hij a).symm.eq
  exact Subgroup.mem_centralizer_singleton_iff.mp hw

end MatrixRepresentation


/-! Orthogonal equivalent corners, as specified by (corner-equivalence)
in the Steinberg kernel argument. The symbol `e` below is the specified d*, not an involution. -/

section Compression
variable [Fintype ι] [DecidableEq ι]

/-- The actual compression word in the Steinberg kernel argument, not a matrix lift assumed to exist. -/
def compression (c : CornerPair R) (p q : ι) : Group ι R :=
  x p q c.d * x q p (-c.e) * x p q c.d

theorem compression_column_p (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x p k y * (compression c p q)⁻¹ = x p k y := by
  rw [← column_single k p y, compression, conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  simp [Pi.single_apply, hpq.symm, c.e_mul_corner hy]

theorem compression_column_q (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x q k y * (compression c p q)⁻¹ = x p k (c.d * y) := by
  rw [← column_single k q y, ← column_single k p (c.d * y), compression,
    conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l
    simp [hpq, hpq.symm, ← mul_assoc, c.ed, c.left_of_corner hy]
  · by_cases hlq : l = q
    · subst l
      simp [hpq, hpq.symm, ← mul_assoc, c.ed, c.left_of_corner hy]
    · simp [Pi.single_apply, hlp, hlq]

theorem compression_row_p (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x k p y * (compression c p q)⁻¹ = x k p y := by
  rw [← row_single k p y, compression, conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  simp [Pi.single_apply, hpq.symm, c.corner_mul_d hy]

theorem compression_row_q (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x k q y * (compression c p q)⁻¹ = x k p (y * c.e) := by
  rw [← row_single k q y, ← row_single k p (y * c.e), compression,
    conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l
    simp [hpq, mul_assoc, c.ed, c.right_of_corner hy]
  · by_cases hlq : l = q
    · subst l
      simp [hpq, hpq.symm, mul_assoc, c.ed, c.right_of_corner hy]
    · simp [Pi.single_apply, hlp, hlq]

/-- Subgroup generated by root coefficients in an idempotent corner. -/
def cornerSubgroup (E : R) : Subgroup (Group ι R) :=
  Subgroup.closure {z | ∃ i j y, E * y * E = y ∧ z = x i j y}

omit [Fintype ι] [DecidableEq ι] in
theorem commutator_mem_subgroup (K : Subgroup (Group ι R)) {a b : Group ι R}
    (ha : a ∈ K) (hb : b ∈ K) : ⁅a, b⁆ ∈ K := by
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

/-- Compression sends all corner words into the subgroup with an unused index. -/
theorem compression_mem_omitting (c : CornerPair R) (p q r : ι)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z : Group ι R} (hz : z ∈ cornerSubgroup c.E) :
    compression c p q * z * (compression c p q)⁻¹ ∈ omitting q := by
  let C := (MulAut.conj (compression c p q)).toMonoidHom
  have hle : cornerSubgroup c.E ≤ (omitting q).comap C := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, j, y, hy, rfl⟩
    change C (x i j y) ∈ omitting q
    by_cases hij : i = j
    · subst j; simp
    by_cases hip : i = p
    · subst i
      by_cases hjq : j = q
      · subst j
        have hroot : x p q y = ⁅x p r y, x r q c.E⁆ := by
          rw [x_chain p r q hpr hqr.symm hpq, c.right_of_corner hy]
        rw [hroot, map_commutatorElement]
        change ⁅compression c p q * x p r y * (compression c p q)⁻¹,
          compression c p q * x r q c.E * (compression c p q)⁻¹⁆ ∈ omitting q
        rw [compression_column_p c p q r hpq hpr hqr y hy,
          compression_row_q c p q r hpq hpr hqr c.E (by rw [c.E_idem, c.E_idem])]
        exact commutator_mem_subgroup _ (x_mem_omitting _ _ _ hpq hqr.symm _)
          (x_mem_omitting _ _ _ hqr.symm hpq _)
      · change compression c p q * x p j y * (compression c p q)⁻¹ ∈ omitting q
        rw [compression_column_p c p q j hpq hij (Ne.symm hjq) y hy]
        exact x_mem_omitting _ _ _ hpq hjq _
    by_cases hiq : i = q
    · subst i
      by_cases hjp : j = p
      · subst j
        have hroot : x q p y = ⁅x q r y, x r p c.E⁆ := by
          rw [x_chain q r p hqr hpr.symm hpq.symm, c.right_of_corner hy]
        rw [hroot, map_commutatorElement]
        change ⁅compression c p q * x q r y * (compression c p q)⁻¹,
          compression c p q * x r p c.E * (compression c p q)⁻¹⁆ ∈ omitting q
        rw [compression_column_q c p q r hpq hpr hqr y hy,
          compression_row_p c p q r hpq hpr hqr c.E (by rw [c.E_idem, c.E_idem])]
        exact commutator_mem_subgroup _ (x_mem_omitting _ _ _ hpq hqr.symm _)
          (x_mem_omitting _ _ _ hqr.symm hpq _)
      · change compression c p q * x q j y * (compression c p q)⁻¹ ∈ omitting q
        rw [compression_column_q c p q j hpq (Ne.symm hjp) hij y hy]
        exact x_mem_omitting _ _ _ hpq (Ne.symm hij) _
    by_cases hjp : j = p
    · subst j
      change compression c p q * x i p y * (compression c p q)⁻¹ ∈ omitting q
      rw [compression_row_p c p q i hpq (Ne.symm hip) (Ne.symm hiq) y hy]
      exact x_mem_omitting _ _ _ hiq hpq _
    by_cases hjq : j = q
    · subst j
      change compression c p q * x i q y * (compression c p q)⁻¹ ∈ omitting q
      rw [compression_row_q c p q i hpq (Ne.symm hip) (Ne.symm hiq) y hy]
      exact x_mem_omitting _ _ _ hiq hpq _
    have h₁ := x_distant p q i j (Ne.symm hjp) (Ne.symm hiq) c.d y
    have h₂ := x_distant q p i j (Ne.symm hjq) (Ne.symm hip) (-c.e) y
    have hW : Commute (compression c p q) (x i j y) := (h₁.mul_left h₂).mul_left h₁
    change compression c p q * x i j y * (compression c p q)⁻¹ ∈ omitting q
    rw [hW.eq, mul_inv_cancel_right]
    exact x_mem_omitting _ _ _ hiq hjq _
  exact hle hz

/-- the Steinberg kernel argument, corner-centrality. No relation for opposite roots is assumed. -/
theorem central_of_corner (c : CornerPair R) (p q r : ι)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z : Group ι R} (hz : z ∈ cornerSubgroup c.E) (hπ : matrixMap z = 1) :
    z ∈ Subgroup.center (Group ι R) := by
  have hc := central_of_omitting q
    (compression_mem_omitting c p q r hpq hpr hqr hz)
    (by simp [hπ])
  have hn := (inferInstance : (Subgroup.center (Group ι R)).Normal).conj_mem
    _ hc (compression c p q)⁻¹
  simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
    inv_mul_cancel, one_mul, mul_one] using hn

end Compression

section OrthogonalCorners
variable [DecidableEq ι]

theorem x_commute_of_zero_nonopposite (i j k l : ι) (a b : R)
    (hab : a * b = 0) (hba : b * a = 0) (hnot : i ≠ l ∨ j ≠ k) :
    Commute (x i j a) (x k l b) := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hkl : k = l
  · subst l; simp
  by_cases hjk : j = k
  · subst k
    have hil : i ≠ l := hnot.resolve_right (not_not_intro rfl)
    apply commutatorElement_eq_one_iff_commute.mp
    rw [x_chain i j l hij hkl hil, hab, x_zero]
  by_cases hil : i = l
  · subst l
    apply Commute.symm
    apply commutatorElement_eq_one_iff_commute.mp
    rw [x_chain k i j hkl hij (Ne.symm hjk), hba, x_zero]
  exact x_distant i j k l hil hjk a b

/-- Opposite roots also commute for orthogonal corner coefficients; this follows
from a third root index, not from an additional Steinberg defining relation. -/
theorem x_commute_orthogonal_corners
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {E F : R} (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0)
    (i j k l : ι) (a b : R) (ha : E * a * E = a) (hb : F * b * F = b) :
    Commute (x i j a) (x k l b) := by
  have hab := corner_product_zero hEF ha hb
  have hba := corner_product_zero hFE hb ha
  by_cases hij : i = j
  · subst j; simp
  by_cases hil : i = l
  · subst l
    by_cases hjk : j = k
    · subst k
      obtain ⟨r, hri, hrj⟩ := hthird i j
      have haE : a * E = a := by
        calc
          a * E = (E * a * E) * E := by rw [ha]
          _ = a := by rw [mul_assoc, hE, ha]
      have hEb : E * b = 0 := by
        calc
          E * b = E * (F * b * F) := by rw [hb]
          _ = 0 := by simp only [← mul_assoc, hEF, zero_mul]
      have hbE : b * E = 0 := by
        calc
          b * E = (F * b * F) * E := by rw [hb]
          _ = 0 := by simp only [mul_assoc, hFE, mul_zero]
      have hx : x i j a = ⁅x i r a, x r j E⁆ := by
        rw [x_chain i r j (Ne.symm hri) hrj hij, haE]
      rw [hx]
      apply Commute.symm
      apply commute_commutator
      · exact (x_commute_of_zero_nonopposite i r j i a b hab hba (Or.inr hrj)).symm
      · exact (x_commute_of_zero_nonopposite r j j i E b hEb hbE (Or.inl hri)).symm
    · exact x_commute_of_zero_nonopposite i j k i a b hab hba (Or.inr hjk)
  · exact x_commute_of_zero_nonopposite i j k l a b hab hba (Or.inl hil)

/-- the Steinberg kernel argument, orthogonal-root-images, extended from roots to all words. -/
theorem cornerSubgroups_commute
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {E F : R} (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0)
    {z w : Group ι R} (hz : z ∈ cornerSubgroup E) (hw : w ∈ cornerSubgroup F) :
    Commute z w := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, j, a, ha, rfl⟩ := hz
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨k, l, b, hb, rfl⟩ := hw
      exact x_commute_orthogonal_corners hthird hE hEF hFE i j k l a b ha hb
    | one => exact Commute.one_right _
    | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_right ih₂
    | inv _ _ ih => exact ih.inv_right
  | one => exact Commute.one_left _
  | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_left ih₂
  | inv _ _ ih => exact ih.inv_left

end OrthogonalCorners

section BalancedDiagonal
variable [Fintype ι] [DecidableEq ι]

/-- Weyl word for an involutive unit b=b⁻¹. -/
def weyl (b : R) (p q : ι) : Group ι R :=
  x p q b * x q p (-b) * x p q b

theorem weyl_column_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x p k y * (weyl b p q)⁻¹ = x q k (-(b * y)) := by
  rw [← column_single k p y, ← column_single k q (-(b * y)), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq.symm, ← mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq.symm, ← mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

theorem weyl_column_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x q k y * (weyl b p q)⁻¹ = x p k (b * y) := by
  rw [← column_single k q y, ← column_single k p (b * y), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq, hpq.symm, ← mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq, hpq.symm, ← mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

theorem weyl_row_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x k p y * (weyl b p q)⁻¹ = x k q (-(y * b)) := by
  rw [← row_single k p y, ← row_single k q (-(y * b)), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq, hpq.symm, mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq, hpq.symm, mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

theorem weyl_row_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x k q y * (weyl b p q)⁻¹ = x k p (y * b) := by
  rw [← row_single k q y, ← row_single k p (y * b), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq, mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq, hpq.symm, mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

def balanced (b : R) (p q : ι) : Group ι R := weyl b p q * weyl (-1) p q

theorem balanced_column_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x p k y * (balanced b p q)⁻¹ = x p k (b * y) := by
  rw [balanced, conjugate_mul, weyl_column_p (-1) (by simp) p q k hpq hpk hqk,
    weyl_column_q b hb p q k hpq hpk hqk]
  simp

theorem balanced_column_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x q k y * (balanced b p q)⁻¹ = x q k (b * y) := by
  rw [balanced, conjugate_mul, weyl_column_q (-1) (by simp) p q k hpq hpk hqk,
    weyl_column_p b hb p q k hpq hpk hqk]
  simp

theorem balanced_row_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x k p y * (balanced b p q)⁻¹ = x k p (y * b) := by
  rw [balanced, conjugate_mul, weyl_row_p (-1) (by simp) p q k hpq hpk hqk,
    weyl_row_q b hb p q k hpq hpk hqk]
  simp

theorem balanced_row_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x k q y * (balanced b p q)⁻¹ = x k q (y * b) := by
  rw [balanced, conjugate_mul, weyl_row_q (-1) (by simp) p q k hpq hpk hqk,
    weyl_row_p b hb p q k hpq hpk hqk]
  simp

/-- Exact balanced diagonal action, including the roots internal to its pair. -/
theorem balanced_root (b : R) (hb : b * b = 1)
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    (p q : ι) (hpq : p ≠ q) (i j : ι) (y : R) :
    balanced b p q * x i j y * (balanced b p q)⁻¹ =
      x i j (pairScalar b p q i * y * pairScalar b p q j) := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hip : i = p
  · subst i
    by_cases hjq : j = q
    · subst j
      obtain ⟨r, hrp, hrq⟩ := hthird p q
      have hroot : x p q y = ⁅x p r y, x r q (1 : R)⁆ := by
        rw [x_chain p r q (Ne.symm hrp) hrq hpq, mul_one]
      rw [hroot]
      change (MulAut.conj (balanced b p q)) ⁅x p r y, x r q (1 : R)⁆ = _
      rw [map_commutatorElement]
      simp only [MulAut.conj_apply]
      rw [balanced_column_p b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        balanced_row_q b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        x_chain p r q (Ne.symm hrp) hrq hpq]
      simp [pairScalar]
    · simpa [pairScalar, Ne.symm hij, hjq] using
        balanced_column_p b hb p q j hpq hij (Ne.symm hjq) y
  by_cases hiq : i = q
  · subst i
    by_cases hjp : j = p
    · subst j
      obtain ⟨r, hrp, hrq⟩ := hthird p q
      have hroot : x q p y = ⁅x q r y, x r p (1 : R)⁆ := by
        rw [x_chain q r p (Ne.symm hrq) hrp hpq.symm, mul_one]
      rw [hroot]
      change (MulAut.conj (balanced b p q)) ⁅x q r y, x r p (1 : R)⁆ = _
      rw [map_commutatorElement]
      simp only [MulAut.conj_apply]
      rw [balanced_column_q b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        balanced_row_p b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        x_chain q r p (Ne.symm hrq) hrp hpq.symm]
      simp [pairScalar]
    · simpa [pairScalar, Ne.symm hij, hjp] using
        balanced_column_q b hb p q j hpq (Ne.symm hjp) hij y
  by_cases hjp : j = p
  · subst j
    simpa [pairScalar, hip, hiq] using
      balanced_row_p b hb p q i hpq (Ne.symm hip) (Ne.symm hiq) y
  by_cases hjq : j = q
  · subst j
    simpa [pairScalar, hip, hiq] using
      balanced_row_q b hb p q i hpq (Ne.symm hip) (Ne.symm hiq) y
  have hc (a : R) : Commute (weyl a p q) (x i j y) := by
    have h₁ := x_distant p q i j (Ne.symm hjp) (Ne.symm hiq) a y
    have h₂ := x_distant q p i j (Ne.symm hjq) (Ne.symm hip) (-a) y
    exact (h₁.mul_left h₂).mul_left h₁
  have hD : Commute (balanced b p q) (x i j y) := (hc b).mul_left (hc (-1))
  rw [hD.eq, mul_inv_cancel_right]
  simp [pairScalar, hip, hiq, hjp, hjq]

/-- Scalar diagonal lift in rank six, exactly the three factors in the source. -/
def scalarDiagonal (b : R) : Group (Fin 6) R :=
  balanced b 0 1 * balanced b 2 3 * balanced b 4 5

omit [Fintype ι] [DecidableEq ι] in
theorem scalarDiagonal_root (b : R) (hb : b * b = 1) (i j : Fin 6) (y : R) :
    scalarDiagonal b * x i j y * (scalarDiagonal b)⁻¹ = x i j (b * y * b) := by
  have ht : ∀ s t : Fin 6, ∃ k, k ≠ s ∧ k ≠ t :=
    fun s t => Fin.exists_ne_and_ne_of_two_lt s t (by decide)
  rw [scalarDiagonal, conjugate_mul, conjugate_mul,
    balanced_root b hb ht 4 5 (by decide),
    balanced_root b hb ht 2 3 (by decide),
    balanced_root b hb ht 0 1 (by decide)]
  have hleft (t : Fin 6) :
      pairScalar b 0 1 t * pairScalar b 2 3 t * pairScalar b 4 5 t = b := by
    fin_cases t <;> simp [pairScalar]
  have hright (t : Fin 6) :
      pairScalar b 4 5 t * pairScalar b 2 3 t * pairScalar b 0 1 t = b := by
    fin_cases t <;> simp [pairScalar]
  congr 1
  calc
    _ = (pairScalar b 0 1 i * pairScalar b 2 3 i * pairScalar b 4 5 i) * y *
        (pairScalar b 4 5 j * pairScalar b 2 3 j * pairScalar b 0 1 j) := by
      simp only [mul_assoc]
    _ = b * y * b := by rw [hleft, hright]

end BalancedDiagonal

section CornerImages
variable [DecidableEq ι]

theorem coefficientMap_mem_corner (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) (z : Group ι R) :
    coefficientMap (cornerMap ψ E hE hc) z ∈ cornerSubgroup E := by
  change z ∈ (cornerSubgroup E).comap (coefficientMap (cornerMap ψ E hE hc))
  apply PresentedGroup.generated_by
  rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
  change coefficientMap (cornerMap ψ E hE hc) (root i j hij a) ∈ cornerSubgroup E
  rw [coefficientMap_root, ← x_of_ne i j hij]
  exact Subgroup.subset_closure ⟨i, j, _, cornerMap_corner ψ E hE hc a, rfl⟩

/-- Centrality of every corner image of an arbitrary matrix-kernel element. -/
theorem coefficientMap_corner_central (ψ : R →ₙ+* S) (c : CornerPair S)
    (hE : ∀ a, Commute c.E (ψ a)) (p q r : ι)
    [Fintype ι] (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z : Group ι R} (hz : matrixMap z = 1) :
    coefficientMap (cornerMap ψ c.E c.E_idem hE) z ∈ Subgroup.center (Group ι S) :=
  central_of_corner c p q r hpq hpr hqr
    (coefficientMap_mem_corner ψ c.E c.E_idem hE z)
    (coefficientMap_preserves_kernel _ z hz)

end CornerImages

/-- the Steinberg kernel argument, corner-comparison, with exact group elements rather than K₂ classes. -/
theorem corner_comparison (ψ : R →ₙ+* S) (c : CornerPair S)
    (hE : ∀ a, Commute c.E (ψ a)) (hF : ∀ a, Commute c.F (ψ a))
    (hd : ∀ a, Commute c.d (ψ a)) (he : ∀ a, Commute c.e (ψ a))
    {z : Group (Fin 6) R} (hz : matrixMap z = 1) :
    coefficientMap (cornerMap ψ c.E c.E_idem hE) z =
      coefficientMap (cornerMap ψ c.F c.F_idem hF) z := by
  let D := scalarDiagonal c.swapScalar
  have hmaps : ((MulAut.conj D).toMonoidHom).comp
      (coefficientMap (cornerMap ψ c.E c.E_idem hE)) =
      coefficientMap (cornerMap ψ c.F c.F_idem hF) := by
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change D * coefficientMap _ (root i j hij a) * D⁻¹ =
      coefficientMap _ (root i j hij a)
    rw [coefficientMap_root, coefficientMap_root, ← x_of_ne i j hij,
      ← x_of_ne i j hij]
    rw [scalarDiagonal_root c.swapScalar c.swapScalar_square]
    congr 1
    simp only [cornerMap_apply]
    calc
      c.swapScalar * (ψ a * c.E) * c.swapScalar =
          ψ a * (c.swapScalar * c.E * c.swapScalar) := by
        rw [← mul_assoc c.swapScalar, (c.swapScalar_commute (hE a) (hF a) (hd a) (he a)).eq]
        simp only [mul_assoc]
      _ = ψ a * c.F := by rw [c.swapScalar_E_swapScalar]
  have hcentral := coefficientMap_corner_central ψ c hE (0 : Fin 6) 1 2
    (by decide) (by decide) (by decide) hz
  have hc := Subgroup.mem_center_iff.mp hcentral D
  have h := DFunLike.congr_fun hmaps z
  change D * coefficientMap _ z * D⁻¹ = coefficientMap _ z at h
  rw [hc, mul_inv_cancel_right] at h
  exact h

/-- Orthogonal corner images split without any residual central factor. -/
theorem coefficientMap_corner_sum [DecidableEq ι]
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    (ψ : R →ₙ+* S) (E F : S) (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0)
    (hcE : ∀ a, Commute E (ψ a)) (hcF : ∀ a, Commute F (ψ a)) (z : Group ι R) :
    coefficientMap (cornerMap ψ (E + F) (orthogonal_sum_idem hE hF hEF hFE)
      (fun a => (hcE a).add_left (hcF a))) z =
      coefficientMap (cornerMap ψ E hE hcE) z *
        coefficientMap (cornerMap ψ F hF hcF) z := by
  let fE := coefficientMap (ι := ι) (cornerMap ψ E hE hcE)
  let fF := coefficientMap (ι := ι) (cornerMap ψ F hF hcF)
  have hc (v w : Group ι R) : Commute (fE v) (fF w) :=
    cornerSubgroups_commute hthird hE hEF hFE
      (coefficientMap_mem_corner ψ E hE hcE v)
      (coefficientMap_mem_corner ψ F hF hcF w)
  let f : Group ι R →* Group ι S := {
    toFun := fun v => fE v * fF v
    map_one' := by simp
    map_mul' := fun v w => by
      simp only [map_mul]
      calc
        fE v * fE w * (fF v * fF w) = fE v * (fE w * fF v) * fF w := by group
        _ = fE v * (fF v * fE w) * fF w := by rw [(hc w v).eq]
        _ = fE v * fF v * (fE w * fF w) := by group }
  have hmaps : coefficientMap (ι := ι)
      (cornerMap ψ (E + F) (orthogonal_sum_idem hE hF hEF hFE)
        (fun a => (hcE a).add_left (hcF a))) = f := by
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change coefficientMap _ (root i j hij a) =
      coefficientMap _ (root i j hij a) * coefficientMap _ (root i j hij a)
    simp only [coefficientMap_root, cornerMap_apply, mul_add, root_add]
  exact DFunLike.congr_fun hmaps z

namespace SupportedPair
variable {ψ : R →ₙ+* S} (p q : SupportedPair ψ)

def image : Group (Fin 6) R →* Group (Fin 6) S :=
  coefficientMap (cornerMap ψ p.E p.E_idem p.commE)

theorem image_eq (hpq : p.V * q.U = 0) (hqp : q.V * p.U = 0)
    {z : Group (Fin 6) R} (hz : matrixMap z = 1) : p.image z = q.image z :=
  corner_comparison ψ (p.corners q hpq hqp) p.commE q.commE
    (fun a => (q.commU a).mul_left (p.commV a))
    (fun a => (p.commU a).mul_left (q.commV a)) hz

theorem image_split (r : SupportedPair ψ) (hsum : q.E + r.E = p.E)
    (hqr : q.V * r.U = 0) (hrq : r.V * q.U = 0) (z : Group (Fin 6) R) :
    p.image z = q.image z * r.image z := by
  have hqrE := q.E_mul_E r hqr
  have hrqE := r.E_mul_E q hrq
  have hm : cornerMap ψ p.E p.E_idem p.commE =
      cornerMap ψ (q.E + r.E) (orthogonal_sum_idem q.E_idem r.E_idem hqrE hrqE)
        (fun a => (q.commE a).add_left (r.commE a)) := by
    ext a
    simp only [cornerMap_apply, hsum]
  change coefficientMap _ z = _
  rw [hm]
  exact coefficientMap_corner_sum
    (fun i j => Fin.exists_ne_and_ne_of_two_lt i j (by decide))
    ψ q.E r.E q.E_idem r.E_idem hqrE hrqE q.commE r.commE z

/-- The source four-corner swindle. All comparison and commutation facts above
hold in St₆ itself, so the final cancellation is an equality of group elements. -/
theorem annihilation (hpq : p.V * q.U = 0) (hqp : q.V * p.U = 0)
    (hsum : p.E + q.E = ψ 1) {z : Group (Fin 6) R} (hz : matrixMap z = 1) :
    coefficientMap ψ z = 1 := by
  have heq := p.image_eq q hpq hqp hz
  have h00 := (p.comp p).image_eq q (p.comp_cross_right q p hpq)
    (p.comp_cross_left q p hqp) hz
  have h01 := (p.comp q).image_eq q (p.comp_cross_right q q hpq)
    (p.comp_cross_left q q hqp) hz
  have hchildren : p.image z = (p.comp p).image z * (p.comp q).image z :=
    p.image_split (p.comp p) (p.comp q) (p.comp_split q hsum)
      (by rw [p.comp_cross p q, hpq]) (by rw [p.comp_cross q p, hqp]) z
  rw [h00, h01, ← heq] at hchildren
  have hpone : p.image z = 1 := by
    have h : p.image z * 1 = p.image z * p.image z := by simpa using hchildren
    exact (mul_left_cancel h).symm
  have hqone : q.image z = 1 := heq ▸ hpone
  have hmaps : cornerMap ψ (p.E + q.E)
      (orthogonal_sum_idem p.E_idem q.E_idem (p.E_mul_E q hpq) (q.E_mul_E p hqp))
      (fun a => (p.commE a).add_left (q.commE a)) = ψ := by
    ext a
    simp only [cornerMap_apply, hsum, ← map_mul, mul_one]
  have hsplit := coefficientMap_corner_sum
    (fun i j : Fin 6 => Fin.exists_ne_and_ne_of_two_lt i j (by decide))
    ψ p.E q.E p.E_idem q.E_idem (p.E_mul_E q hpq) (q.E_mul_E p hqp)
    p.commE q.commE z
  rw [hmaps] at hsplit
  change coefficientMap ψ z = p.image z * q.image z at hsplit
  simpa only [hpone, hqone, one_mul] using hsplit

end SupportedPair

end Steinberg

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Affine
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Rank-six affine relations, modules, and finite affine presentations.
-/


/- The rank-six affine presentation. -/
namespace FiniteAlgebraicEnvelopes

namespace FiniteAffine
open scoped commutatorElement
variable {R : Type*} [Ring R]
abbrev Free (R : Type*) [Ring R] := Monoid.Coprod (Steinberg.Group (Fin 6) R) (FreeGroup (Fin 6))
def freeP (a : Fin 6) : Free R := Monoid.Coprod.inr (FreeGroup.of a)
abbrev freeX (a b : Fin 6) (r : R) : Free R := Monoid.Coprod.inl (Steinberg.x a b r)

def relatorPP (ab : Fin 6 × Fin 6) : Free R := ⁅freeP (R:=R) ab.1,freeP (R:=R) ab.2⁆
def relatorC (F : Finset R) (z : F × Fin 6 × Fin 6 × Fin 6) : Free R :=
  if z.2.2.2 ≠ z.2.2.1 then ⁅freeX z.2.1 z.2.2.1 (z.1 : R),freeP z.2.2.2⁆ else 1
def relatorU (ab : Fin 6 × Fin 6) : Free R :=
  if ab.1 ≠ ab.2 then ⁅freeX ab.1 ab.2 (1:R),freeP ab.2⁆ * (freeP ab.1)⁻¹ else 1
def relatorD (D : Finset R) (z : D × Fin 6 × Fin 6) : Free R :=
  ⁅freeX z.2.1 z.2.2 (z.1 : R),freeP z.2.2⁆
def relators (F D : Finset R) : Set (Free R) :=
  Set.range relatorPP ∪ Set.range (relatorC F) ∪ Set.range relatorU ∪ Set.range (relatorD D)
def N (F D : Finset R) : Subgroup (Free R) := Subgroup.normalClosure (relators F D)
instance instNormalFreeN (F D : Finset R) : (N F D).Normal := inferInstanceAs (Subgroup.normalClosure _).Normal
abbrev Presentation (F D : Finset R) := Free R ⧸ N F D
noncomputable def base (F D : Finset R) : Steinberg.Group (Fin 6) R →* Presentation F D :=
  (QuotientGroup.mk' (N F D)).comp Monoid.Coprod.inl
noncomputable def p (F D : Finset R) (a : Fin 6) : Presentation F D :=
  QuotientGroup.mk' (N F D) (freeP a)

theorem killRelator (F D : Finset R) {x : Free R} (hx : x ∈ relators F D) :
    QuotientGroup.mk' (N F D) x = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hx)

theorem p_commute (F D : Finset R) (a b : Fin 6) : Commute (p F D a) (p F D b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := killRelator F D (x:=relatorPP (R:=R) (a,b)) (by
    exact Or.inl (Or.inl (Or.inl ⟨(a,b),rfl⟩)))
  simpa only [relatorPP,map_commutatorElement,p] using h

theorem central_finite (F D : Finset R) (r : R) (hr : r ∈ F) (a b c : Fin 6) (hcb : c ≠ b) :
    Commute (AffinePresentation.X (base F D) a b r) (p F D c) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := killRelator F D (x:=relatorC F (⟨r,hr⟩,a,b,c)) (by
    exact Or.inl (Or.inl (Or.inr ⟨(⟨r,hr⟩,a,b,c),rfl⟩)))
  simpa only [relatorC,ite_eq_left hcb,map_commutatorElement,p,AffinePresentation.X,base,MonoidHom.comp_apply] using h

theorem unit (F D : Finset R) (a b : Fin 6) (hab : a ≠ b) :
    ⁅AffinePresentation.X (base F D) a b 1,p F D b⁆ = p F D a := by
  apply mul_inv_eq_one.mp
  have h := killRelator F D (x:=relatorU (R:=R) (a,b)) (by
    exact Or.inl (Or.inr ⟨(a,b),rfl⟩))
  simpa only [relatorU,ite_eq_left hab,map_mul,map_inv,map_commutatorElement,p,
    AffinePresentation.X,base,MonoidHom.comp_apply] using h

theorem ideal (F D : Finset R) (d : R) (hd : d ∈ D) (a b : Fin 6) :
    ⁅AffinePresentation.X (base F D) a b d,p F D b⁆ = 1 := by
  have h := killRelator F D (x:=relatorD D (⟨d,hd⟩,a,b)) (by
    exact Or.inr ⟨(⟨d,hd⟩,a,b),rfl⟩)
  simpa only [relatorD,map_commutatorElement,p,AffinePresentation.X,base,MonoidHom.comp_apply] using h

variable (F D : Finset R) (h1 : (1:R) ∈ F) (hgen : Subring.closure (↑F : Set R) = ⊤)
include h1 hgen in
theorem central : ∀ r : R, ∀ a b c : Fin 6, c ≠ b →
    Commute (AffinePresentation.X (base F D) a b r) (p F D c) :=
  AffinePresentation.coefficients (base F D) (p F D) F h1 hgen (central_finite F D)

noncomputable def fromAffine : AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) →* Presentation F D :=
  AffinePresentation.lift (base F D) (p F D) (p_commute F D) (central F D h1 hgen)
    (unit F D) (↑D : Set R) (fun d hd a b _ => ideal F D d hd a b)


noncomputable def translation (a : Fin 6) (r : R) :
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) :=
  SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single a (Submodule.Quotient.mk r)))

@[simp] theorem translation_zero (a : Fin 6) : translation D a (0:R) = 1 := by
  simp [translation]

theorem root_translation (a b c : Fin 6) (hab : a ≠ b) (r s : R) :
    ⁅(SemidirectProduct.inr (Steinberg.root a b hab r) :
      AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R))),translation D c s⁆ =
      translation D a (if b=c then r*s else 0) := by
  rw [translation, AffineAction.root_translation]
  by_cases h : b=c
  · subst c
    simp only [Pi.single_eq_same,ite_true]
    rfl
  · simp [h]

noncomputable def freeMap : Free R →*
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) :=
  Monoid.Coprod.lift SemidirectProduct.inr (FreeGroup.lift (translation D · 1))
@[simp] theorem freeMap_P (a : Fin 6) : freeMap D (freeP a) = translation D a 1 := by
  simp [freeMap,freeP]
@[simp] theorem freeMap_X (a b : Fin 6) (r : R) :
    freeMap D (freeX a b r) = SemidirectProduct.inr (Steinberg.x a b r) := by
  simp [freeMap]

theorem freeMap_relators : ∀ x ∈ relators F D, freeMap D x = 1 := by
  intro x hx
  rcases hx with ((⟨⟨a,b⟩,rfl⟩ | ⟨⟨⟨r,hr⟩,a,b,c⟩,rfl⟩) | ⟨⟨a,b⟩,rfl⟩) | ⟨⟨⟨d,hd⟩,a,b⟩,rfl⟩
  · simp only [relatorPP,map_commutatorElement,freeMap_P]
    apply Commute.commutator_eq
    exact (Commute.all _ _).map SemidirectProduct.inl
  · simp only [relatorC]
    split_ifs with hcb
    · simp only [map_commutatorElement,freeMap_X,freeMap_P]
      by_cases hab : a=b
      · subst b; simp
      · rw [Steinberg.x_of_ne a b hab,root_translation D a b c hab]
        simp [Ne.symm hcb]
    · exact map_one _
  · simp only [relatorU]
    split_ifs with hab
    · simp only [map_mul,map_inv,map_commutatorElement,freeMap_X,freeMap_P]
      rw [Steinberg.x_of_ne a b hab,root_translation D a b b hab]
      simp
    · exact map_one _
  · simp only [relatorD,map_commutatorElement,freeMap_X,freeMap_P]
    by_cases hab : a=b
    · subst b; simp
    · rw [Steinberg.x_of_ne a b hab,root_translation D a b b hab]
      simp only [ite_true,mul_one,translation]
      have hz : (Submodule.Quotient.mk d : R ⧸ Submodule.span R (↑D : Set R)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span hd)
      rw [hz,Pi.single_zero,ofAdd_zero,map_one]

noncomputable def toAffine : Presentation F D →*
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) :=
  QuotientGroup.lift (N F D) (freeMap D) (by
    apply Subgroup.normalClosure_le_normal
    exact freeMap_relators F D)

@[simp] theorem toAffine_base (x : Steinberg.Group (Fin 6) R) :
    toAffine F D (base F D x) = SemidirectProduct.inr x := by
  change freeMap D (Monoid.Coprod.inl x) = _
  simp [freeMap]
@[simp] theorem toAffine_p (a : Fin 6) : toAffine F D (p F D a) = translation D a 1 := by
  change freeMap D (freeP a) = _
  exact freeMap_P D a

@[simp] theorem fromAffine_inr (x : Steinberg.Group (Fin 6) R) :
    fromAffine F D h1 hgen (SemidirectProduct.inr x) = base F D x := by
  simp only [fromAffine,AffinePresentation.lift,SemidirectProduct.lift_inr]
@[simp] theorem fromAffine_translation (a : Fin 6) (r : R) :
    fromAffine F D h1 hgen (translation D a r) =
      AffinePresentation.w (base F D) (p F D) a r := by
  simp only [fromAffine,AffinePresentation.lift,translation,SemidirectProduct.lift_inl]
  apply AffinePresentation.translations_single_mk

/-- The quotient is generated by its base and its six designated translations. -/
theorem hom_ext {Q : Type*} [Group Q] {f g : Presentation F D →* Q}
    (hb : f.comp (base F D) = g.comp (base F D)) (hp : ∀ a, f (p F D a) = g (p F D a)) : f=g := by
  apply MonoidHom.cancel_right (QuotientGroup.mk'_surjective (N F D)) |>.mp
  apply Monoid.Coprod.hom_ext
  · exact hb
  · apply FreeGroup.ext_hom
    exact hp

/-- The natural affine quotient has no additional kernel. -/
noncomputable def equivalence : Presentation F D ≃*
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) := by
  let f := toAffine F D
  let g := fromAffine F D h1 hgen
  have hgf : g.comp f = MonoidHom.id _ := by
    apply hom_ext F D
    · ext x : 1
      simp [f,g]
    · intro a
      simp only [MonoidHom.comp_apply,toAffine_p,fromAffine_translation,MonoidHom.id_apply,f,g]
      exact AffinePresentation.w_one (base F D) (p F D) (unit F D) a
  have hfg : f.comp g = MonoidHom.id _ := by
    apply SemidirectProduct.hom_ext
    · apply MonoidHom.toAdditive.injective
      apply AddMonoidHom.pi_ext
      intro a x
      obtain ⟨r,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R (↑D : Set R)) x
      change f (g (translation D a r)) = translation D a r
      rw [fromAffine_translation]
      simp only [AffinePresentation.w,AffinePresentation.wcolumn,map_commutatorElement,
        AffinePresentation.X,toAffine_base,toAffine_p,f]
      rw [Steinberg.x_of_ne a _ (AffinePresentation.other_ne a).symm,root_translation]
      simp
    · ext x : 1
      simp [f,g]
  exact { f with invFun := g, left_inv := DFunLike.congr_fun hgf, right_inv := DFunLike.congr_fun hfg }

end FiniteAffine
end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Enveloping
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Tensor-enveloping algebra actions, simplicity, and elementary row control.
-/


namespace FiniteAlgebraicEnvelopes.RowControl
open Enveloping
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B] [IsSimpleRing A]

def act (g : Steinberg.Group (Fin 6) (Coeff k B)) (v : Fin 6 → B) : Fin 6 → B :=
  (AffineAction.action g (Multiplicative.ofAdd v)).toAdd

@[simp] theorem act_one (v : Fin 6 → B) : act (k:=k) 1 v = v := by simp [act]
@[simp] theorem act_root (a b : Fin 6) (hab : a ≠ b) (r : Coeff k B) (v : Fin 6 → B) :
    act (Steinberg.root a b hab r) v = fun j => if j=a then v j + r • v b else v j := by
  funext j
  simp [act]

def Related (i : A →ₙₐ[k] B) (v w : Fin 6 → A) : Prop :=
  ∃ g : Steinberg.Group (Fin 6) (Coeff k B), act g (i ∘ v) = i ∘ w

end FiniteAlgebraicEnvelopes.RowControl

end OAI
end

section
-- module Solutions.OAIFAE.Transition
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite weak transition components and finite-scan instruction semantics.
-/

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation

variable {α : Type*} {r : α → α → Prop}

instance instFintypeDirection : Fintype Direction := ⟨{.left, .right}, by intro x; cases x <;> simp⟩

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIFAE.Control
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.instPrimcodableSector _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control and bounded compiler orbit normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Cleanup
open Relation
variable {S Γ : Type*}

instance instFintypeHead : Fintype Head := ⟨{.cleanup,.raw}, by intro h; cases h <;> simp⟩

end FiniteAlgebraicEnvelopes.Compiler.Cleanup

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
variable {S Γ : Type*}

instance instFintypeHead : Fintype Head :=
  ⟨{.initial,.left,.right,.workspace,.suffix,.start},by intro h; cases h <;> simp⟩

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

instance stepDecidable : DecidableRel (Step (S := S) blank) := fun v w => by
  letI : Decidable (Scan.Step (table blank) (toScan v) (toScan w)) :=
    inferInstanceAs (Decidable (_ = _))
  exact decidable_of_iff _ (step_iff_scan blank v w).symm

end FiniteAlgebraicEnvelopes.Compiler.Validator

end OAI
end

section
-- module Solutions.OAIFAE.Normalization
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_append (u v : List (Letter S Γ Q)) :
    present A M (u++v) = present A M u * present A M v := rfl

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_context {u v : List (Letter S Γ Q)} (he : present A M u = present A M v)
    (x y : List (Letter S Γ Q)) : present A M (x++u++y) = present A M (x++v++y) := by
  simp only [present_append,he]

end

open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- Singleton raw words are fixed, but adjacent full raw words call the program
    on their concatenation, exactly as in the manuscript. -/
theorem normal_raw_product (f : List S → List S) (u v : List S) :
    normal A M f (raw (Q := Q) A.blank u ++ raw A.blank v) = raw A.blank (f (u++v)) := by
  have hn : Path.shape (raw (Q := Q) A.blank u ++ raw A.blank v) ≠ .zero := by
    simp [raw,encode,Path.encode,Path.path_mul_path,Surface.raw,Scan.literal]
  rw [normal,ite_eq_right hn]
  simp [RawRuns.source,RawRuns.splitRun,realize]

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/

end OAI
end

section
-- module Solutions.OAIFAE.Effectivity
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive encodings and effective finite compiler data.
-/

/- Effectivity dependencies for the source compiler and its bounded recursive
   evaluator. No partial function is completed by classical choice. -/
namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

theorem traverse_fix (f : α →. β) (l : List α) (acc : List β) :
    PFun.fix (traverseStep f) (l,acc) = (traverse f l).map (acc++·) := by
  induction l generalizing acc with
  | nil =>
    apply Part.ext
    intro out
    rw [PFun.mem_fix_iff]
    simp [traverseStep,traverse]
  | cons a l ih =>
    apply Part.ext
    intro out
    rw [PFun.mem_fix_iff]
    simp only [traverseStep,Part.mem_map_iff,Sum.inr.injEq,
      Sum.inr_ne_inl,exists_false,and_false,false_or]
    constructor
    · rintro ⟨⟨l',acc'⟩,⟨b,hb,he⟩,h⟩
      rcases he with ⟨rfl,rfl⟩
      rw [ih] at h
      rcases (Part.mem_map_iff _).mp h with ⟨bs,hbs,rfl⟩
      refine ⟨b::bs,Part.mem_bind_iff.mpr ⟨b,hb,(Part.mem_map_iff _).mpr ⟨bs,hbs,rfl⟩⟩,?_⟩
      simp [List.append_assoc]
    · intro h
      rcases h with ⟨bs,hbs,rfl⟩
      change bs ∈ (f a).bind (fun b => (traverse f l).map (b::·)) at hbs
      rcases Part.mem_bind_iff.mp hbs with ⟨b,hb,hrest⟩
      rcases (Part.mem_map_iff _).mp hrest with ⟨tail,htail,rfl⟩
      refine ⟨(l,acc++[b]),⟨b,hb,rfl⟩,?_⟩
      rw [ih]
      apply (Part.mem_map_iff _).mpr
      exact ⟨tail,htail,by simp [List.append_assoc]⟩

variable [Primcodable α] [Primcodable β]

theorem partrec_traverse {f : α →. β} (hf : Partrec f) : Partrec (traverse f) := by
  have hs : Partrec (traverseStep f) := by
    have ht : Computable (fun s : List α × List β => s.1.head?) :=
      Primrec.list_head?.to_comp.comp Computable.fst
    have hb : Partrec₂ (fun (s : List α × List β) (a : α) =>
        (f a).map fun b => (Sum.inr (s.1.tail,s.2++[b]) : List β ⊕ (List α × List β))) := by
      change Partrec (fun sa : (List α × List β) × α =>
        (f sa.2).map fun b => (Sum.inr (sa.1.1.tail,sa.1.2++[b]) : List β ⊕ (List α × List β)))
      apply (hf.comp Computable.snd).map
      exact (Computable.sumInr.comp
        ((Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
        (Primrec.list_append.to_comp.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Primrec.list_cons.to_comp.comp Computable.snd (Computable.const []))))).to₂
    exact (Partrec.optionCasesOn_right ht
      (Computable.sumInl.comp Computable.snd) hb).of_eq
      (by intro s; rcases s with ⟨l,acc⟩; cases l <;> rfl)
  exact ((Partrec.fix hs).comp (Computable.id.pair (Computable.const []))).of_eq fun l => by
    simpa only [id_eq,List.nil_append,Part.map_id' (fun _ => rfl)] using traverse_fix f l []

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

def Action.code : Action C S ≃ C ⊕ (List S ⊕ List S) where
  toFun
    | .keep c => .inl c
    | .raw x => .inr (.inl x)
    | .call x => .inr (.inr x)
  invFun
    | .inl c => .keep c
    | .inr (.inl x) => .raw x
    | .inr (.inr x) => .call x
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with c | (x|x) <;> rfl

instance instPrimcodableAction [Primcodable C] [Primcodable S] : Primcodable (Action C S) :=
  Primcodable.ofEquiv _ Action.code

def push : Item C S → List (Action C S) → List (Action C S)
  | .inl c,p => .keep c::p
  | .inr x,[] => [.raw x]
  | .inr x,.keep c::p => .raw x::.keep c::p
  | .inr x,.raw y::p => .call (x++y)::p
  | .inr x,.call y::p => .call (x++y)::p

theorem plan_cons (a : Item C S) (w : List (Item C S)) :
    plan (a::w) = push a (plan w) := by
  cases a with
  | inl c => simp only [plan,push]
  | inr x =>
    cases w with
    | nil => simp [plan,splitRun,push]
    | cons b w =>
      cases b with
      | inl c => simp [plan,splitRun,push]
      | inr y =>
        rw [plan,plan]
        simp only [splitRun]
        cases (splitRun w).1 <;> simp [push]

theorem plan_fold (w : List (Item C S)) : plan w = w.foldr push [] := by
  induction w with
  | nil => simp [plan]
  | cons a w ih => rw [plan_cons,ih]; rfl

variable [Primcodable C] [Primcodable S]

 theorem Action.primrec_code : Primrec (Action.code (C := C) (S := S)) := Primrec.of_equiv
 theorem Action.primrec_decode : Primrec (Action.code (C := C) (S := S)).symm := Primrec.of_equiv_symm
 theorem Action.primrec_keep : Primrec (Action.keep (C := C) (S := S)) :=
  (Action.primrec_decode.comp Primrec.sumInl).of_eq fun _ => rfl
 theorem Action.primrec_raw : Primrec (Action.raw (C := C) (S := S)) :=
  (Action.primrec_decode.comp (Primrec.sumInr.comp Primrec.sumInl)).of_eq fun _ => rfl
 theorem Action.primrec_call : Primrec (Action.call (C := C) (S := S)) :=
  (Action.primrec_decode.comp (Primrec.sumInr.comp Primrec.sumInr)).of_eq fun _ => rfl

 theorem Action.primrec_cases {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → Action C S} {k : α → C → β} {r t : α → List S → β}
    (hf : Primrec f) (hk : Primrec₂ k) (hr : Primrec₂ r) (ht : Primrec₂ t) :
    Primrec (fun a => match f a with | .keep c => k a c | .raw x => r a x | .call x => t a x) := by
  have hh : Primrec₂ (fun a (b : List S ⊕ List S) => b.elim (r a) (t a)) :=
    (Primrec.sumCasesOn Primrec.snd
      (hr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (ht.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (Action.primrec_code.comp hf) hk hh).of_eq fun a => by
    cases f a <;> rfl

 theorem primrec_push : Primrec₂ (push (C := C) (S := S)) := by
  have hl : Primrec₂ (fun (p : Item C S × List (Action C S)) (c : C) => Action.keep c::p.2) :=
    (Primrec.list_cons.comp (Action.primrec_keep.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have hr : Primrec₂ (fun (p : Item C S × List (Action C S)) (x : List S) =>
      match p.2 with
      | [] => [Action.raw x]
      | .keep c::l => Action.raw x::.keep c::l
      | .raw y::l => Action.call (x++y)::l
      | .call y::l => Action.call (x++y)::l) := by
    have hc : Primrec₂ (fun (p : (Item C S × List (Action C S)) × List S)
        (q : Action C S × List (Action C S)) =>
        match q.1 with
        | .keep c => Action.raw p.2::.keep c::q.2
        | .raw y => Action.call (p.2++y)::q.2
        | .call y => Action.call (p.2++y)::q.2) := by
      exact (Action.primrec_cases (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp
          (Action.primrec_raw.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.list_cons.comp (Action.primrec_keep.comp Primrec.snd)
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to₂
        (Primrec.list_cons.comp
          (Action.primrec_call.comp (Primrec.list_append.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
        (Primrec.list_cons.comp
          (Action.primrec_call.comp (Primrec.list_append.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂).to₂
    exact (Primrec.list_casesOn (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Action.primrec_raw.comp Primrec.snd) (Primrec.const [])) hc).to₂.of_eq
      (by intro p x; cases p.2 with
        | nil => rfl
        | cons a l => cases a <;> rfl)
  exact (Primrec.sumCasesOn Primrec.fst hl hr).to₂.of_eq fun a p => by
    cases a with
    | inl c => rfl
    | inr x => cases p with
      | nil => rfl
      | cons a p => cases a <;> rfl

 theorem primrec_plan : Primrec (plan (C := C) (S := S)) :=
  (Primrec.list_foldr Primrec.id (Primrec.const [])
    (primrec_push.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun w => (plan_fold w).symm)

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

variable [Primcodable H] [Primcodable B] [Primcodable T]

theorem Sector.primrec_code : Primrec (Sector.code (H := H) (B := B) (T := T)) := Primrec.of_equiv
theorem Sector.primrec_decode : Primrec (Sector.code (H := H) (B := B) (T := T)).symm :=
  Primrec.of_equiv_symm

theorem Sector.primrec_left : Primrec (Sector.left (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp Sector.primrec_code
theorem Sector.primrec_head : Primrec (Sector.head (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp Sector.primrec_code)
theorem Sector.primrec_right : Primrec (Sector.right (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code))
theorem Sector.primrec_lb : Primrec (Sector.leftBoundary (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))
theorem Sector.primrec_rb : Primrec (Sector.rightBoundary (Head := H) (Base := B) (Tag := T)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))

theorem Sector.primrec_mk {α : Type*} [Primcodable α]
    {l r : α → List (B×T)} {q : α → H} {a b : α → Bool}
    (hl : Primrec l) (hq : Primrec q) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => (⟨l x,q x,r x,a x,b x⟩ : Sector H B T)) :=
  Sector.primrec_decode.comp (hl.pair (hq.pair (hr.pair (ha.pair hb))))

theorem primrec_baseSkeleton : Primrec (baseSkeleton (H := H) (B := B) (T := T)) :=
  (Primrec.list_map
    (Primrec.list_append.comp (Primrec.list_reverse.comp Sector.primrec_left) Sector.primrec_right)
    (Primrec.fst.comp Primrec.snd).to₂).pair (Sector.primrec_lb.pair Sector.primrec_rb)

variable [Fintype H] [Fintype B] [Fintype T]

 theorem primrec_wordList {α : Type*} [Fintype α] [Primcodable α] : Primrec (wordList α) := by
  exact (Primrec.nat_rec₁ [[]]
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap (Primrec.const (finiteList α))
        (Primrec.list_map (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
    fun n => by induction n <;> simp_all [wordList]

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {H T : Type*}

def Instruction.code : Instruction H T ≃ H × T × Bool where
  toFun i := (i.head,i.tag,i.cross)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableInstruction [Primcodable H] [Primcodable T] : Primcodable (Instruction H T) :=
  Primcodable.ofEquiv _ Instruction.code

theorem Instruction.primrec_head [Primcodable H] [Primcodable T] :
    Primrec (Instruction.head (Head := H) (Tag := T)) := Primrec.fst.comp Primrec.of_equiv

theorem Instruction.primrec_tag [Primcodable H] [Primcodable T] :
    Primrec (Instruction.tag (Head := H) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.of_equiv)

theorem Instruction.primrec_cross [Primcodable H] [Primcodable T] :
    Primrec (Instruction.cross (Head := H) (Tag := T)) :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

def flip (v : Sector H B T) : Sector H B T :=
  ⟨v.right,v.head,v.left,v.rightBoundary,v.leftBoundary⟩

def rightStep (table : Table H B T) (v : Sector H B T) : Option (Sector H B T) :=
  match v.right with
  | [] => if v.rightBoundary then (table.boundary v.head).map fun q => {v with head := q} else none
  | (b,t)::r => (table.cell v.head b t).map fun a =>
      if a.cross then {v with left := (b,a.tag)::v.left,head := a.head,right := r}
      else {v with head := a.head,right := (b,a.tag)::r}

theorem step_rightStep (table : Table H B T) (v : Sector H B T) :
    step table v = if table.direction v.head = .right then rightStep table v
      else (rightStep table (flip v)).map flip := by
  rcases v with ⟨l,q,r,a,b⟩
  cases hd : table.direction q with
  | right =>
    cases r with
    | nil => simp [step,rightStep,hd]
    | cons c r => cases c; simp [step,rightStep,hd]
  | left =>
    cases l with
    | nil =>
      cases a <;> simp [step,rightStep,hd,flip,Option.map_map,Function.comp_def]
    | cons c l =>
      rcases c with ⟨b,t⟩
      cases hh : table.cell q b t with
      | none => simp [step,rightStep,hd,flip,hh]
      | some i => cases hi : i.cross <;> simp [step,rightStep,hd,hh,hi,flip]

variable [Primcodable H] [Primcodable B] [Primcodable T]

 theorem primrec_flip : Primrec (flip (H := H) (B := B) (T := T)) :=
  Sector.primrec_mk Sector.primrec_right Sector.primrec_head Sector.primrec_left
    Sector.primrec_rb Sector.primrec_lb

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Effect
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [Primcodable α] [DecidableEq α]

 theorem primrec_priorityList {p q : α → Bool} (hp : Primrec p) (hq : Primrec q) :
    Primrec (priorityList p q) := by
  have hf := primrec_listFilter Primrec.id (hp.comp Primrec.snd).to₂
  have hg := primrec_listFilter Primrec.id (hq.comp Primrec.snd).to₂
  unfold priorityList
  simp only [← Bool.cond_eq_ite]
  exact Primrec.cond (primrec_listIsEmpty.comp hf)
    (Primrec.cond (primrec_listIsEmpty.comp hg) Primrec.id hg) hf

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect

theorem primrec_codeOrder (α : Type*) [Primcodable α] :
    letI := codeOrder α
    PrimrecRel (fun a b : α => a ≤ b) :=
  Primrec.nat_le.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
noncomputable instance instPrimcodableHeadOfFintype {S Q : Type*} [Fintype S] [Fintype Q] : Primcodable (Control.Head S Q) := finitePrimcodable _
noncomputable instance instPrimcodableHeadOfFintype_1 {H : Type*} [Fintype H] : Primcodable (Surface.Head H) := finitePrimcodable _

namespace Surface
open Scan
variable {S Γ H : Type*} [Fintype S] [Fintype Γ] [Fintype H]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq H] (blank : Γ)

 def cleanAnchor (c : Base S × Tag S Γ) : Bool :=
  match c.1 with
  | .anchor _ => decide (c.2 = clean blank)
  | _ => false

omit [Fintype S] [Fintype Γ] in
 theorem trimQuota_drop (l : Cells S Γ) :
    trimQuota blank l = l.dropWhile (fun c => decide (c = Validator.cell blank .workspace)) := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases h : c = Validator.cell blank .workspace <;>
      simp [trimQuota,h,ih]

omit [DecidableEq S] [DecidableEq Γ] in
 theorem primrec_cleanupOutput : Primrec (Cleanup.output (S := S) blank) := by
  have hfinite : Primrec (fun c : Base S × Tag S Γ =>
      (Cleanup.emit c).map (Cleanup.letter blank)) := Primrec.dom_finite _
  exact (Primrec.listFilterMap Primrec.id (hfinite.comp Primrec.snd).to₂).of_eq fun l => by
    simp only [Cleanup.output, List.map_filterMap, id_eq]

end Surface

namespace Scan
variable {H H' B T : Type*} [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T]
 theorem primrec_mapHead {f : H → H'} (hf : Primrec f) : Primrec (mapHead (B := B) (T := T) f) :=
  Sector.primrec_mk Sector.primrec_left (hf.comp Sector.primrec_head) Sector.primrec_right
    Sector.primrec_lb Sector.primrec_rb
end Scan

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Path
open FiniteAlgebraicEnvelopes.Effect
variable {C H : Type*}

def Sector.code : Sector C H ≃ List C × (H × (List C × (Bool × Bool))) where
  toFun v := (v.left,v.head,v.right,v.leftBoundary,v.rightBoundary)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableSector [Primcodable C] [Primcodable H] : Primcodable (Sector C H) :=
  Primcodable.ofEquiv _ Sector.code

variable [Primcodable C] [Primcodable H]

theorem Sector.primrec_code : Primrec (Sector.code (C := C) (H := H)) := Primrec.of_equiv
theorem Sector.primrec_decode : Primrec (Sector.code (C := C) (H := H)).symm :=
  Primrec.of_equiv_symm

theorem Sector.primrec_left : Primrec (Sector.left (C := C) (H := H)) :=
  Primrec.fst.comp Sector.primrec_code
theorem Sector.primrec_head : Primrec (Sector.head (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp Sector.primrec_code)
theorem Sector.primrec_right : Primrec (Sector.right (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code))
theorem Sector.primrec_lb : Primrec (Sector.leftBoundary (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))
theorem Sector.primrec_rb : Primrec (Sector.rightBoundary (C := C) (H := H)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))

theorem Sector.primrec_mk {α : Type*} [Primcodable α]
    {l r : α → List C} {q : α → H} {a b : α → Bool}
    (hl : Primrec l) (hq : Primrec q) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => (⟨l x,q x,r x,a x,b x⟩ : Sector C H)) :=
  Sector.primrec_decode.comp (hl.pair (hq.pair (hr.pair (ha.pair hb))))

variable [Fintype C] [Fintype H] [DecidableEq C] [DecidableEq H]
noncomputable instance instPrimcodableLetter : Primcodable (Letter C H) := finitePrimcodable _

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H K B T : Type*} [Primcodable H] [Primcodable K] [Primcodable B] [Primcodable T]
 theorem primrec_literal {m : H → K} (hm : Primrec m) : Primrec (literal (B := B) (T := T) m) :=
  Path.Sector.primrec_mk Sector.primrec_left (hm.comp Sector.primrec_head) Sector.primrec_right
    Sector.primrec_lb Sector.primrec_rb
 theorem primrec_unliteral : Primrec (unliteral (H := H) (B := B) (T := T)) :=
  Sector.primrec_mk Path.Sector.primrec_left Path.Sector.primrec_head Path.Sector.primrec_right
    Path.Sector.primrec_lb Path.Sector.primrec_rb
end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
end

section
-- module Solutions.OAIFAE.Rewriting
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Newman normalization, block coding, canonical representatives, and static tests.
-/

/- Rewriting layer for the self-reference construction.  No assumptions on
   either main theorem are introduced here. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation

variable {S : Type*}

variable [DecidableEq S]

variable [Primcodable S]

 theorem primrec_rootNext : Primrec₂ (@rootNext S _) := by
  apply Primrec₂.of_eq (Primrec.list_rec Primrec.snd (Primrec.const none)
    ((Primrec.ite
      (Primrec.eq.comp
        (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.option_some.comp (Primrec.list_append.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_drop.comp
          (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)).to₂
  intro w rs
  induction rs with
  | nil => rfl
  | cons p rs ih =>
      simpa [rootNext] using (congrArg
        (fun t => if w.take p.1.length = p.1 then some (p.2++w.drop p.1.length) else t) ih)

 theorem primrec_next : Primrec₂ (@next S _) := by
  have hor : Primrec₂ (Option.or : Option (List S) → Option (List S) → Option (List S)) :=
    Primrec.option_orElse.of_eq (by intro a b; cases a <;> rfl)
  apply Primrec₂.of_eq (Primrec.list_rec Primrec.snd
    (primrec_rootNext.comp (Primrec.const []) Primrec.fst)
    ((hor.comp
      (primrec_rootNext.comp
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        ((Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂))).to₂)).to₂
  intro rs w
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa [next] using (congrArg
        (fun t => (rootNext (a::w) rs).or (t.map (a::·))) ih)

end

/- The marker/constant-width code used in the self-reference construction.
   A block has its marker only at the start, not at the end. -/

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} (wf : WellFounded r)
variable (q : List A → Q)

/-- Literal characterization which requires no class tests longer than w. -/
theorem eq_least_iff [Std.Trichotomous r] {w v : List A} : v=least wf q w ↔
    v.length≤w.length ∧ q v=q w ∧
      ∀ t, t.length≤w.length → q t=q w → ¬ List.Shortlex r t v := by
  constructor
  · rintro rfl
    exact ⟨least_length wf q w,least_class wf q w,fun _ ht hq => least_min wf q ht hq⟩
  · rintro ⟨hv,hq,hm⟩
    exact Std.Trichotomous.trichotomous _ _
      (least_min wf q hv hq) (hm _ (least_length wf q w) (least_class wf q w))

end Canonical

open Relation
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.Selectors
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

namespace Search

section
variable {A : Type*} [DecidableEq A]

theorem lexBool_eq [LinearOrder A] (u v : List A) :
    lexBool (fun a b : A => decide (a<b)) u v = decide (List.Lex (·<·) u v) := by
  induction u generalizing v with
  | nil => cases v <;> simp [lexBool]
  | cons a u ih =>
    cases v with
    | nil => simp [lexBool]
    | cons b v =>
      by_cases hab : a=b
      · subst b
        simp [lexBool,ih,List.lex_cons_iff]
      · simp only [lexBool,ite_eq_right hab]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · exact List.Lex.rel
        · intro h
          cases h with
          | rel h => exact h
          | cons h => exact False.elim (hab rfl)

variable [Primcodable A]

 theorem primrec_shortlex [LinearOrder A] (hr : PrimrecRel (fun a b : A => a<b)) :
    PrimrecRel (List.Shortlex (fun a b : A => a<b)) := by
  have hlex : PrimrecRel (List.Lex (fun a b : A => a<b)) := by
    apply PrimrecRel.of_eq
      (Primrec.eq.comp₂ (primrec_lexBool (fun a b : A => decide (a<b)) hr.decide)
        (Primrec.const true).to₂)
    intro u v
    rw [lexBool_eq,decide_eq_true_eq]
  exact ((Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)).or
    ((Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)).and hlex)).of_eq
      (fun p => List.shortlex_def.symm)

end

variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r) (q : List A → Option Q)

variable [Primcodable A] [Primcodable S] [Primcodable Q]
omit [Std.Trichotomous r]

omit [DecidableEq A] in
 theorem primrec_words : Primrec (Static.words A) := by
  exact (Primrec.nat_rec₁ [[]]
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap (Primrec.const (Static.letters A))
        (Primrec.list_map (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
    fun n => by induction n <;> simp_all [Static.words]

omit [DecidableEq A] [Fintype A] in
 theorem primrec_pickStep (hr : PrimrecRel (List.Shortlex r))
    {X : Type*} [Primcodable X] {v : X → Option Q} {b : X → List A} {p : X → List A × Option Q}
    (hv : Primrec v) (hb : Primrec b) (hp : Primrec p) :
    Primrec (fun x => Canonical.pickStep (r:=r) (v x) (b x) (p x)) :=
  Primrec.ite ((Primrec.eq.comp (Primrec.snd.comp hp) hv).and
    (hr.comp (Primrec.fst.comp hp) hb)) (Primrec.fst.comp hp) hb

end Search
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Selectors

section
variable {S : Type*} [DecidableEq S] [Primcodable S]

omit [DecidableEq S] in
 theorem primrec_maxLength : Primrec (@maxLength S) :=
  (Primrec.list_foldr (Primrec.list_map Primrec.id (Primrec.list_length.comp Primrec.snd).to₂)
    (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

 theorem primrec_tuples (z : S) : Primrec (tuples z) := by
  have hc : Primrec (fun i => (Encodable.decode (α:=List (List S)) i).getD [[]]) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [[]])
  have hz : PrimrecPred (fun ws : List (List S) => ∀ w∈ws,z∉w) :=
    ((primrec_mem.comp (Primrec.const z) Primrec.id).not).forall_mem_list
  exact Primrec.ite ((Primrec.eq.comp hc (Primrec.const [])).not.and
    ((primrec_nodup.comp hc).and (hz.comp hc))) hc (Primrec.const [[]])

 theorem primrec_sizes (z : S) : Primrec (sizes z) := by
  have hm := primrec_maxLength.comp (primrec_tuples z)
  have hs : Primrec₂ (fun i v => max (max (i+2) (maxLength (tuples z (i+1))+1))
      (2*v+3+maxLength (tuples z i))) := by
    exact (Primrec.nat_max.comp
      (Primrec.nat_max.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
        (Primrec.succ.comp (hm.comp (Primrec.succ.comp Primrec.fst))))
      (Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 3))
        (hm.comp Primrec.fst))).to₂
  exact (Primrec.nat_rec₁ (maxLength (tuples z 0)+1) hs).of_eq (by
    intro i
    induction i <;> simp_all [sizes])

end

variable {S : Type*} [DecidableEq S] [Primcodable S]

def stageEquiv : Stage S ≃ ℕ × List (List S) where
  toFun s := (s.size,s.bodies)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableStage : Primcodable (Stage S) := Primcodable.ofEquiv _ stageEquiv

omit [DecidableEq S] in
theorem primrec_stage_size : Primrec (@Stage.size S) := Primrec.fst.comp Primrec.of_equiv

omit [DecidableEq S] in
theorem primrec_stage_bodies : Primrec (@Stage.bodies S) := Primrec.snd.comp Primrec.of_equiv

theorem primrec_stages (z : S) : Primrec (stages z) :=
  Primrec.of_equiv_symm.comp ((primrec_sizes z).pair (primrec_tuples z))

omit [DecidableEq S] in
theorem primrec_wrap (a : Markers S) : Primrec₂ a.wrap := by
  exact (Primrec.list_cons.comp (Primrec.const a.d)
    (Primrec.list_append.comp (Primrec.list_append.comp
      (Primrec.list_append.comp ((primrec_replicate a.l).comp Primrec.fst) Primrec.snd)
      ((primrec_replicate a.r).comp Primrec.fst)) (Primrec.const [a.h]))).to₂

theorem primrec_rules (a : Markers S) : Primrec₂ (rules a) := by
  exact (Primrec.list_map Primrec.snd
    ((primrec_wrap a).comp (Primrec.fst.comp Primrec.fst) Primrec.snd |>.pair
      (Primrec.ite (Primrec.eq.comp
        (Primrec.list_head?.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp Primrec.snd)) (Primrec.const []) (Primrec.const [a.zero]))).to₂).to₂

theorem primrec_allowed : PrimrecRel (fun (rs : List (List S × List S)) s => allowed rs s = true) := by
  have hh : PrimrecRel (fun (w : List S) (rs : List (List S × List S)) => next rs w = none) :=
    (Primrec.eq.comp (primrec_next.comp Primrec.snd Primrec.fst) (Primrec.const none)).primrecRel
  exact (hh.forall_mem_list.comp (primrec_stage_bodies.comp Primrec.snd) Primrec.fst).of_eq
    (by intro p; simp [allowed,List.all_eq_true,Option.isNone_iff_eq_none])

theorem primrec_choose (a : Markers S) {X : Type*} [Primcodable X]
    {rs : X → List (List S × List S)} {s : X → Stage S} {n : X → ℕ}
    (hr : Primrec rs) (hs : Primrec s) (hn : Primrec n) :
    Primrec (fun x => choose (a:=a) (rs x) (s x) (n x)) :=
  Primrec.ite
    ((Primrec.nat_le.comp (primrec_stage_size.comp hs) hn).and (primrec_allowed.comp hr hs))
    (Primrec.list_append.comp hr ((primrec_rules a).comp
      (primrec_stage_size.comp hs) (primrec_stage_bodies.comp hs))) hr

theorem primrec_process (a : Markers S) (ss : ℕ → Stage S) (hss : Primrec ss) :
    Primrec₂ (fun p : List (List S × List S) × ℕ => process (a:=a) p.1 ss p.2) := by
  apply Primrec₂.of_eq (Primrec.nat_rec Primrec.fst
    (primrec_choose a (Primrec.snd.comp Primrec.snd)
      (hss.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst)).to₂)
  intro p j
  induction j with
  | zero => rfl
  | succ j ih => simp only [process,ih]

end FiniteAlgebraicEnvelopes.Bootstrap.Selectors

end OAI
end

section
-- module Solutions.OAIFAE.Quotients
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*}

theorem partrec_traverse_parameter [Primcodable X] [Primcodable A] [Primcodable B]
    {f : X → A → Part B} (hf : Partrec₂ f) : Partrec₂ (fun x => traverse (f x)) := by
  have hp : Primrec (fun p : X × List A => p.2.map (p.1,·)) :=
    Primrec.list_map Primrec.snd ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂
  exact ((partrec_traverse hf).comp hp.to_comp).of_eq (by
    intro p
    exact (traverse_comp (Function.uncurry f) (p.1,·) p.2).symm)
end Effect

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section

namespace Quotient
open Relation
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))

omit [DecidableEq S] in
 theorem present_step {n : ℕ} {rs : List (List S × List S)} (hrs : rs ∈ T n)
    {u v : List S} (hu : u.length ≤ n) (h : Step rs u v) : present T u=present T v := by
  cases h with
  | @apply a b hab x y =>
    have ha : a.length ≤ n := by simp only [List.length_append] at hu; omega
    have hh : present T a=present T b :=
      PresentedMonoid.mk_eq_mk_of_rel ⟨n,rs,hrs,hab,ha⟩
    simp only [present_append,hh]

end Quotient

open Relation

namespace Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

omit [DecidableEq S] wf good stable in
 theorem irreducible_of_short {rs : List (List S × List S)} {w : List S}
    (h : ∀ p∈rs,w.length<p.1.length) : Irreducible (Step rs) w := by
  intro v hv
  cases hv with
  | @apply u v huv x y =>
    have hh := h (u,v) huv
    simp only [List.length_append] at hh
    omega

omit [DecidableEq S] wf good stable in
 theorem present_absorbs (z : S) {rs : List (List S × List S)}
    (hrs : rs∈T 2) (hz : Absorbs rs z) :
    ∀ w,present T [z]*present T w=present T [z] ∧
      present T w*present T [z]=present T [z] := by
  have hza (a : S) : present T [z]*present T [a]=present T [z] :=
    PresentedMonoid.mk_eq_mk_of_rel ⟨2,rs,hrs,(hz a).1,by simp⟩
  have haz (a : S) : present T [a]*present T [z]=present T [z] :=
    PresentedMonoid.mk_eq_mk_of_rel ⟨2,rs,hrs,(hz a).2,by simp⟩
  intro w
  induction w with
  | nil => simp
  | cons a w ih =>
    have hh : present T (a::w)=present T [a]*present T w := rfl
    rw [hh]
    exact ⟨by rw [←mul_assoc,hza,ih.1],by rw [mul_assoc,ih.2,haz]⟩

@[instance_reducible]
noncomputable def monoidWithZero (z : S) {rs : List (List S × List S)}
    (hrs : rs∈T 2) (hz : Absorbs rs z) : MonoidWithZero (Mon T) where
  __ := (inferInstance : Monoid (Mon T))
  zero := present T [z]
  zero_mul x := by
    obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
    exact (present_absorbs T z hrs hz w.toList).1
  mul_zero x := by
    obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
    exact (present_absorbs T z hrs hz w.toList).2

end Quotient
end

namespace Static
variable {S A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_short (hc : 1<C.width+1) {n : ℕ} {p : List S × List S}
    (hp : p∈table C wf q z n) : 1<p.1.length := by
  obtain ⟨w,_,hn,_,he,_⟩ := (mem_table C wf q z).mp hp
  rw [he,C.encode_length]
  have hl : 1≤w.length := List.length_pos_iff.mpr hn
  exact hc.trans_le (by simpa using Nat.mul_le_mul_left (C.width+1) hl)
end Static

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation
variable {S : Type*}

theorem irreducible_of_no_infix {rs : List (List S × List S)} {w : List S}
    (h : ∀ p∈rs, ¬ p.1 <:+: w) : Irreducible (Step rs) w := by
  intro v hv
  cases hv with
  | @apply u v hp x y => exact h (u,v) hp ⟨x,y,rfl⟩

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_mono {k n : ℕ} (hkn : k≤n) {p : List S × List S}
    (hp : p∈table C wf q z k) : p∈table C wf q z n := by
  obtain ⟨w,hw,hn,he,hl,hr⟩ := (mem_table C wf q z).mp hp
  exact (mem_table C wf q z).mpr ⟨w,hw.trans hkn,hn,he,hl,hr⟩

omit [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q] in
theorem output_eq_iff (hz : z∉C.Alphabet) (u v : List A) :
    output C wf q z u=output C wf q z v ↔ q u=q v := by
  constructor
  · intro he
    by_cases hu : q u=none <;> by_cases hv : q v=none
    · exact hu.trans hv.symm
    · have hh : z∈C.encode (Canonical.least wf q v) := by
        rw [output,ite_eq_left hu,output,ite_eq_right hv] at he
        rw [←he]; simp
      exact False.elim (hz (C.mem_alphabet hh))
    · have hh : z∈C.encode (Canonical.least wf q u) := by
        rw [output,ite_eq_right hu,output,ite_eq_left hv] at he
        rw [he]; simp
      exact False.elim (hz (C.mem_alphabet hh))
    · rw [output,ite_eq_right hu,output,ite_eq_right hv] at he
      have h := C.encode_injective he
      exact (Canonical.least_class wf q u).symm.trans
        ((congrArg q h).trans (Canonical.least_class wf q v))
  · exact output_congr C wf q z
end Static

namespace Base
variable {A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [DecidableEq S] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (q : List A → Option Q) (g : List B → Option R) (z : S)

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem isolate_left (hz : z∉C.Alphabet) (hd : Disjoint C.Alphabet D.Alphabet)
    {n : ℕ} {p : List S × List S} (hp : p∈table C D wf wg q g z n) :
    p∈Static.table C wf q z n ∨ ∃ s∈p.1,s∉C.Alphabet := by
  rcases (mem_table C D wf wg q g z).mp hp with hp | hp | hp
  · obtain ⟨b,hb,_⟩ := (mem_absorption z).mp hp
    exact Or.inr ⟨z,by rcases hb with h | h <;> simp [h],hz⟩
  · exact Or.inl (Static.table_mono C wf q z (Nat.div_le_self n _) hp)
  · obtain ⟨hn,hs⟩ := Static.table_support D wg g z hp
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hn
    exact Or.inr ⟨b,hb,fun hc => Set.disjoint_left.mp hd hc (hs b hb)⟩
end Base

namespace Quotient
variable [DecidableEq S] {A M : Type*} [Monoid M]
variable {T : ℕ → Part (List (List S × List S))} (C : BlockCode A S)

def codeHom : FreeMonoid A →* Mon T where
  toFun w := present T (C.encode w.toList)
  map_one' := by simp
  map_mul' u v := by simp only [FreeMonoid.toList_mul,BlockCode.encode_append,present_append]

variable (e : FreeMonoid A →* M) (he : Function.Surjective e)
  (hc : ∀ u v : List A,present T (C.encode u)=present T (C.encode v) ↔
    e (FreeMonoid.ofList u)=e (FreeMonoid.ofList v))

noncomputable def descendCode : M →* Mon T where
  toFun x := codeHom C (he x).choose
  map_one' := by
    have hx : e (he 1).choose=e 1 := (he 1).choose_spec.trans e.map_one.symm
    exact (hc _ []).mpr hx
  map_mul' x y := by
    change present T (C.encode ((he (x*y)).choose.toList)) =
      present T (C.encode ((he x).choose.toList))*present T (C.encode ((he y).choose.toList))
    rw [←present_append,←BlockCode.encode_append]
    apply (hc _ _).mpr
    change e (he (x*y)).choose=e ((he x).choose * (he y).choose)
    rw [e.map_mul,(he (x*y)).choose_spec,(he x).choose_spec,(he y).choose_spec]

omit [DecidableEq S] in
theorem descendCode_apply (w : List A) :
    descendCode C e he hc (e (FreeMonoid.ofList w))=present T (C.encode w) :=
  (hc _ w).mpr (he (e (FreeMonoid.ofList w))).choose_spec

end Quotient

end

variable {S : Type*}

namespace Base
variable {A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [DecidableEq S] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (q : List A → Option Q) (g : List B → Option R) (zero sep : S)

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem isolate_separator (hz : zero∉C.Alphabet) (hsep : zero≠sep)
    (hsD : sep∉D.Alphabet) (hd : Disjoint C.Alphabet D.Alphabet)
    {n : ℕ} {p : List S × List S} (hp : p∈table C D wf wg q g zero n) :
    p∈Static.table C wf q zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep := by
  rcases (mem_table C D wf wg q g zero).mp hp with hp | hp | hp
  · obtain ⟨b,hb,_⟩ := (mem_absorption zero).mp hp
    exact Or.inr ⟨zero,by rcases hb with h | h <;> simp [h],hz,hsep⟩
  · exact Or.inl (Static.table_mono C wf q zero (Nat.div_le_self n _) hp)
  · obtain ⟨hn,hs⟩ := Static.table_support D wg g zero hp
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hn
    exact Or.inr ⟨b,hb,(fun hc => Set.disjoint_left.mp hd hc (hs b hb)),
      fun he => hsD (he ▸ hs b hb)⟩
end Base

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {A B : Type*}

 theorem primrec_words [Primcodable A] : Primrec₂ (@words A) := by
  exact (Primrec.nat_rec (Primrec.const [[]])
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap Primrec.fst
        (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
            fun ls n => by induction n <;> simp_all [words]

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.WordProblem

 theorem primrec_letterShortlex (n : ℕ) : PrimrecRel (List.Shortlex (letterRel n)) := by
  let ord : LinearOrder (Fin n × Bool) := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact @Bootstrap.Search.primrec_shortlex _ _ _ ord ⟨inferInstance,Primrec.dom_finite _⟩

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
end

section
-- module Solutions.OAIFAE.PartialAffine
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine
namespace Dyad

theorem primrec_neg : Primrec neg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

theorem primrec_add : Primrec₂ add := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap (primrec_pow2.comp bk))
    (Primrec.nat_mul.comp bp (primrec_pow2.comp ak))).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp an (primrec_pow2.comp bk))
      (Primrec.nat_mul.comp bn (primrec_pow2.comp ak))).pair
        (Primrec.nat_add.comp ak bk))).to₂

theorem primrec_mul : Primrec₂ mul := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bp) (Primrec.nat_mul.comp an bn)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bn) (Primrec.nat_mul.comp an bp)).pair
      (Primrec.nat_add.comp ak bk))).to₂

theorem primrec_le : Primrec₂ le := by
  have ap : Primrec (fun p : Dyad × Dyad => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : Dyad × Dyad => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : Dyad × Dyad => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : Dyad × Dyad => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : Dyad × Dyad => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : Dyad × Dyad => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_le.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp ap (primrec_pow2.comp bk))
      (Primrec.nat_mul.comp bn (primrec_pow2.comp ak)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp bp (primrec_pow2.comp ak))
      (Primrec.nat_mul.comp an (primrec_pow2.comp bk)))).decide).to₂

theorem primrec_eq : Primrec₂ eq :=
  (Primrec.and.comp (primrec_le.comp Primrec.fst Primrec.snd)
    (primrec_le.comp Primrec.snd Primrec.fst)).to₂

theorem primrec_max : Primrec₂ max :=
  (Primrec.ite (Primrec.eq.comp primrec_le (Primrec.const true)) Primrec.snd Primrec.fst).to₂

end Dyad

namespace Slope
theorem val_pos (a : Slope) : 0<val a := by rw [val_eq]; positivity
theorem primrec_dyad : Primrec dyad :=
  (Dyad.primrec_pow2.comp Primrec.fst).pair ((Primrec.const 0).pair Primrec.snd)
theorem primrec_mul : Primrec₂ mul :=
  ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
theorem primrec_inv : Primrec inv := Primrec.snd.pair Primrec.fst
end Slope

namespace Bound

def sup : Option Dyad → Option Dyad → Option Dyad
  | none,b => b
  | a,none => a
  | some a,some b => some (Dyad.max a b)

theorem dom_sup (a b : Option Dyad) (x : ℚ) :
    dom ((sup a b).map Dyad.val) x ↔ dom (a.map Dyad.val) x ∧ dom (b.map Dyad.val) x := by
  cases a <;> cases b <;> simp [sup,dom,Dyad.val_max]

theorem dom_preimage (r : Option Dyad) (c : Slope) (d : Dyad) (x : ℚ) :
    dom ((r.map fun r => Dyad.mul (Slope.dyad (Slope.inv c)) (Dyad.add r (Dyad.neg d))).map Dyad.val) x ↔
      dom (r.map Dyad.val) (Slope.val c*x+Dyad.val d) := by
  cases r with
  | none => simp [dom]
  | some r =>
    simp only [Option.map_some,dom,Dyad.val_mul,Dyad.val_add,Dyad.val_neg]
    rw [show Dyad.val (Slope.dyad (Slope.inv c)) = (Slope.val c)⁻¹ from Slope.val_inv c,
      ← sub_eq_add_neg]
    rw [← div_eq_inv_mul,div_le_iff₀ (Slope.val_pos c)]
    constructor <;> intro h <;> linarith

theorem primrec_sup : Primrec₂ sup := by
  have hh : Primrec (fun p : Option Dyad × Option Dyad =>
      (Option.casesOn p.1 p.2 (fun a => Option.casesOn p.2 (some a) (fun b => some (Dyad.max a b))) : Option Dyad)) := by
    apply Primrec.option_casesOn Primrec.fst Primrec.snd
    exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.option_some.comp (Dyad.primrec_max.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂
  exact hh.of_eq (by intro p; rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl)
end Bound

namespace Data
def mul (a b : Data) : Data :=
  (Slope.mul a.1 b.1, Dyad.add (Dyad.mul (Slope.dyad a.1) b.2.1) a.2.1,
    Bound.sup b.2.2 (a.2.2.map fun r =>
      Dyad.mul (Slope.dyad (Slope.inv b.1)) (Dyad.add r (Dyad.neg b.2.1))))
def one : Data := ((0,0),Dyad.zero,none)

 theorem act_mul (a b : Data) (x : ℚ) : act (mul a b) x = (act b x).bind (act a) := by
  have hd : Bound.dom ((mul a b).2.2.map Dyad.val) x ↔
      Bound.dom (b.2.2.map Dyad.val) x ∧
      Bound.dom (a.2.2.map Dyad.val) (Slope.val b.1*x+Dyad.val b.2.1) := by
    rw [mul,Bound.dom_sup,Bound.dom_preimage]
  simp only [act,hd]
  split_ifs <;> simp_all only [Option.bind_some,Option.bind_none,act,↓reduceIte,
    and_true,true_and,false_and,not_false_eq_true]
  change some (Slope.val (Slope.mul a.1 b.1)*x+
    Dyad.val (Dyad.add (Dyad.mul (Slope.dyad a.1) b.2.1) a.2.1)) = _
  rw [Slope.val_mul,Dyad.val_add,Dyad.val_mul]
  change some (Slope.val a.1*Slope.val b.1*x+(Slope.val a.1*Dyad.val b.2.1+Dyad.val a.2.1)) = _
  congr 1
  ring

 theorem represent_mul (a b : Data) : represent (mul a b)=represent a*represent b := by
  funext o
  cases o with
  | none => rfl
  | some x => exact act_mul a b x

 theorem represent_one : represent one=1 := by
  funext o
  change represent one o = o
  cases o <;> simp [represent,act,one,Bound.dom,Slope.val_eq,Dyad.val_zero]

/-- The three literal parameters determine exactly a partial affine map. -/
def params (a : Data) : ℚ × ℚ × Option ℚ :=
  (Slope.val a.1,Dyad.val a.2.1,a.2.2.map Dyad.val)

 theorem represent_of_params {a b : Data} (h : params a=params b) : represent a=represent b := by
  have hs := congrArg Prod.fst h
  have ht := congrArg (fun p : ℚ × ℚ × Option ℚ => p.2.1) h
  have hd := congrArg (fun p : ℚ × ℚ × Option ℚ => p.2.2) h
  funext o
  cases o <;> simp_all [params,represent,act]

theorem domain_eq {a b : Data} (h : represent a=represent b) (x : ℚ) :
    Bound.dom (a.2.2.map Dyad.val) x ↔ Bound.dom (b.2.2.map Dyad.val) x := by
  have hh := congrFun h (some x)
  simp only [represent,Option.bind_some,act] at hh
  split_ifs at hh <;> simp_all

 theorem params_of_represent {a b : Data} (h : represent a=represent b) : params a=params b := by
  have hd : a.2.2.map Dyad.val=b.2.2.map Dyad.val := by
    cases ha : a.2.2.map Dyad.val with
    | none =>
      cases hb : b.2.2.map Dyad.val with
      | none => rfl
      | some s =>
        have hh := (domain_eq h (s-1)).mp (by simp [ha,Bound.dom])
        simp only [hb,Bound.dom] at hh
        linarith
    | some r =>
      cases hb : b.2.2.map Dyad.val with
      | none =>
        have hh := (domain_eq h (r-1)).mpr (by simp [hb,Bound.dom])
        simp only [ha,Bound.dom] at hh
        linarith
      | some s =>
        apply congrArg some
        apply le_antisymm
        · have hh := (domain_eq h s).mpr (by simp [hb,Bound.dom])
          simpa only [ha,Bound.dom] using hh
        · have hh := (domain_eq h r).mp (by simp [ha,Bound.dom])
          simpa only [hb,Bound.dom] using hh
  let x : ℚ := (a.2.2.map Dyad.val).getD 0
  have hx : Bound.dom (a.2.2.map Dyad.val) x := by
    cases ha : a.2.2.map Dyad.val <;> simp [x,ha,Bound.dom]
  have hx' : Bound.dom (a.2.2.map Dyad.val) (x+1) := by
    cases ha : a.2.2.map Dyad.val <;> simp [x,ha,Bound.dom]
  have hv (y : ℚ) (hy : Bound.dom (a.2.2.map Dyad.val) y) :
      Slope.val a.1*y+Dyad.val a.2.1=Slope.val b.1*y+Dyad.val b.2.1 := by
    have hh := congrFun h (some y)
    simp only [represent,Option.bind_some,act,ite_eq_left hy,ite_eq_left ((domain_eq h y).mp hy),Option.some.injEq] at hh
    exact hh
  have h0 := hv x hx
  have h1 := hv (x+1) hx'
  have hs : Slope.val a.1=Slope.val b.1 := by nlinarith
  have ht : Dyad.val a.2.1=Dyad.val b.2.1 := by rw [hs] at h0; linarith
  exact Prod.ext hs (Prod.ext ht hd)

 theorem represent_eq_iff (a b : Data) : represent a=represent b ↔ params a=params b :=
  ⟨params_of_represent,represent_of_params⟩

end Data

namespace Bound
def eq : Option Dyad → Option Dyad → Bool
  | none,none => true
  | some a,some b => Dyad.eq a b
  | _,_ => false

 theorem eq_correct (a b : Option Dyad) : eq a b=true ↔ a.map Dyad.val=b.map Dyad.val := by
  cases a <;> cases b <;> simp [eq,Dyad.eq_correct]

 theorem primrec_eq : Primrec₂ eq := by
  have hh : Primrec (fun p : Option Dyad × Option Dyad =>
      (Option.casesOn p.1 (Option.casesOn p.2 true (fun _ => false))
        (fun a => Option.casesOn p.2 false (fun b => Dyad.eq a b)) : Bool)) := by
    apply Primrec.option_casesOn Primrec.fst
    · exact Primrec.option_casesOn Primrec.snd (Primrec.const true) (Primrec.const false).to₂
    · exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst) (Primrec.const false)
        (Dyad.primrec_eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact hh.of_eq (by intro p; rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl)

 theorem primrec_preimage {X : Type*} [Primcodable X]
    {r : X → Option Dyad} {c : X → Slope} {d : X → Dyad}
    (hr : Primrec r) (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun x => (r x).map fun b =>
      Dyad.mul (Slope.dyad (Slope.inv (c x))) (Dyad.add b (Dyad.neg (d x)))) :=
  Primrec.option_map hr
    ((Dyad.primrec_mul.comp (Slope.primrec_dyad.comp (Slope.primrec_inv.comp (hc.comp Primrec.fst)))
      (Dyad.primrec_add.comp Primrec.snd (Dyad.primrec_neg.comp (hd.comp Primrec.fst)))).to₂)
end Bound

namespace Data
def eq (a b : Data) : Bool :=
  Dyad.eq (Slope.dyad a.1) (Slope.dyad b.1) &&
    Dyad.eq a.2.1 b.2.1 && Bound.eq a.2.2 b.2.2

 theorem eq_correct (a b : Data) : eq a b=true ↔ represent a=represent b := by
  rw [represent_eq_iff]
  simp only [eq,Bool.and_eq_true,Dyad.eq_correct,Bound.eq_correct,params,Prod.mk.injEq]
  change ((Slope.val a.1=Slope.val b.1) ∧ (Dyad.val a.2.1=Dyad.val b.2.1)) ∧ _ ↔ _
  exact and_assoc

 theorem primrec_mul : Primrec₂ mul := by
  have ac : Primrec (fun p : Data × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have ad : Primrec (fun p : Data × Data => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ar : Primrec (fun p : Data × Data => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bc : Primrec (fun p : Data × Data => p.2.1) := Primrec.fst.comp Primrec.snd
  have bd : Primrec (fun p : Data × Data => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have br : Primrec (fun p : Data × Data => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Slope.primrec_mul.comp ac bc).pair
    ((Dyad.primrec_add.comp (Dyad.primrec_mul.comp (Slope.primrec_dyad.comp ac) bd) ad).pair
      (Bound.primrec_sup.comp br (Bound.primrec_preimage ar bc bd)))).to₂

 theorem primrec_eq : Primrec₂ eq := by
  exact (Primrec.and.comp
    (Primrec.and.comp
      (Dyad.primrec_eq.comp (Slope.primrec_dyad.comp (Primrec.fst.comp Primrec.fst))
        (Slope.primrec_dyad.comp (Primrec.fst.comp Primrec.snd)))
      (Dyad.primrec_eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    (Bound.primrec_eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
end Data

def evaluate (w : List Letter) : Data := w.foldr (fun i d => Data.mul (generator i) d) Data.one

 theorem represent_evaluate (w : List Letter) : Data.represent (evaluate w)=value w := by
  induction w with
  | nil => exact Data.represent_one
  | cons i w ih =>
    simpa only [evaluate,List.foldr_cons,value,List.map_cons,List.prod_cons,Function.comp_apply]
      using (Data.represent_mul (generator i) (evaluate w)).trans (congrArg (Data.represent (generator i)*·) ih)

 theorem primrec_evaluate : Primrec evaluate :=
  Primrec.list_foldr Primrec.id (Primrec.const Data.one)
    (Data.primrec_mul.comp ((Primrec.dom_finite generator).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- Lemma partial-affine, algorithmic part: a primitive-recursive equality test
    for the actual partial maps, not classical decidability. -/
 theorem primrec_word_equivalence : PrimrecPred (fun p : List Letter × List Letter => value p.1=value p.2) := by
  have hh : PrimrecPred (fun p : List Letter × List Letter => Data.eq (evaluate p.1) (evaluate p.2)=true) :=
    Primrec.eq.comp (Data.primrec_eq.comp (primrec_evaluate.comp Primrec.fst)
      (primrec_evaluate.comp Primrec.snd)) (Primrec.const true)
  exact hh.of_eq fun p => by rw [Data.eq_correct,represent_evaluate,represent_evaluate]

/-- The manuscript's auxiliary monoid is generated by the six actual partial
    affine maps. `none` is an undefined value; composition is right first. -/
def monoid : Submonoid (Function.End (Option ℚ)) :=
  Submonoid.closure (Set.range (Data.represent ∘ generator))

 theorem value_mem (w : List Letter) : value w∈monoid := by
  apply Submonoid.list_prod_mem
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  exact Submonoid.subset_closure ⟨i,rfl⟩

 theorem exists_word {a : Function.End (Option ℚ)} (ha : a∈monoid) : ∃ w,value w=a := by
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    exact ⟨[i],by simp [value]⟩
  | one => exact ⟨[],rfl⟩
  | mul a b ha hb ia ib =>
    obtain ⟨u,rfl⟩ := ia
    obtain ⟨v,rfl⟩ := ib
    exact ⟨u++v,by simp [value]⟩

def wordValue (w : List Letter) : monoid := ⟨value w,value_mem w⟩

 theorem wordValue_surjective : Function.Surjective wordValue := by
  intro a
  obtain ⟨w,hw⟩ := exists_word a.property
  exact ⟨w,Subtype.ext hw⟩

instance instFGSubtypeEndOptionRatMemSubmonoidMonoid : Monoid.FG monoid := by
  unfold monoid
  infer_instance

instance instCountableSubtypeEndOptionRatMemSubmonoidMonoid : Countable monoid := Function.Surjective.countable wordValue_surjective

 theorem generator_tail0 : Data.represent (generator 4)=tail 0 := by
  funext o
  cases o <;> simp [Data.represent,Data.act,generator,tail,Bound.dom,Slope.val_eq,Dyad.val_zero]

 theorem generator_tail1 : Data.represent (generator 5)=tail 1 := by
  funext o
  cases o <;> simp [Data.represent,Data.act,generator,tail,Bound.dom,Slope.val_eq,Dyad.val_zero,Dyad.val_one]

 theorem generator_u (o : Option ℚ) : Data.represent (generator 0) o=o.map (fun x => x/2) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val_zero,
    div_eq_mul_inv,mul_comm]

 theorem generator_v (o : Option ℚ) : Data.represent (generator 1) o=o.map (fun x => (x+1)/2) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val]
  ring

 theorem generator_ui (o : Option ℚ) : Data.represent (generator 2) o=o.map (fun x => 2*x) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val_zero]

 theorem generator_vi (o : Option ℚ) : Data.represent (generator 3) o=o.map (fun x => 2*x-1) := by
  cases o <;> simp [Data.represent,Data.act,generator,Bound.dom,Slope.val_eq,Dyad.val]
  ring

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIFAE.TapeFolding
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.WordProgramming
open Encodable
variable {S : Type} [Primcodable S]

/-- The source fixed-point equation for word algorithms, as literal equality of
    partial functions, including their domains. -/
theorem fixed_point {F : Nat.Partrec.Code → List S →. List S}
    (hF : Partrec₂ F) : ∃ c, eval c = F c := by
  let G : Nat.Partrec.Code → ℕ →. ℕ := fun c n =>
    (F c ((decode n).getD [])).map encode
  have hG : Partrec₂ G := by
    exact ((hF.comp Computable.fst
      ((Computable.option_getD (Computable.decode.comp Computable.snd)
        (Computable.const [])))).map (Computable.encode.comp Computable.snd).to₂).to₂
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hG
  refine ⟨c,?_⟩
  funext w
  simp only [eval,hc,G,encodek,Option.getD_some]
  apply Part.ext
  intro out
  simp [encodek]

end FiniteAlgebraicEnvelopes.WordProgramming

namespace FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine
open Turing Turing.ToPartrec Turing.PartrecToTM2 StackLift RawTM StackTape

variable (S : Type) [Fintype S] [Primcodable S] [DecidableEq S]

/-- A literal raw-letter stack program, with its finite control part. -/
structure Raw where
  Q : Type
  finiteQ : Fintype Q
  start : Q
  code : Q → TM2.Stmt (fun _ : K' => Symbol S) Q (Store S)

attribute [instance] Raw.finiteQ

/-- A finite tape machine with distinguished literal input/output states. -/
structure TapeProgram where
  Q : Type
  finiteQ : Fintype Q
  [inhabitedQ : Inhabited Q]
  start : Q
  stop : Q
  code : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Q
  safe : TapeSafety.Preserves code

attribute [instance] TapeProgram.finiteQ TapeProgram.inhabitedQ

end FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine

end OAI
end

section
-- module Solutions.OAIFAE.UniformMachines
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Parameterized effective machine realization and uniform finite data.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode
open Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]
noncomputable instance instPrimcodableMove : Primcodable Move := Primcodable.ofEquiv (Fin (Fintype.card Move)) (Fintype.equivFin Move)

 theorem primrec_transition : Primrec (fun x : (ℕ × Control Q) × (Bool×Γ) =>
    transition A M p x.1.1 x.1.2 x.2) := by
  let X := (ℕ × Control Q) × (Bool×Γ)
  have hn : Primrec (fun x : X => x.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun x : X => x.2) := Primrec.snd
  have hbranch : Primrec (fun z : X × ℕ =>
      if z.2=0 then (some (Sum.inl 1,(true,z.1.2.2),Move.stay) : Option (Cmd Q Γ))
      else if z.2=1 then if z.1.2.2=A.blank then some (.inl 3,z.1.2,Move.stay)
        else some (.inl 1,z.1.2,Move.right)
      else if z.2=2 then if z.1.2.1 then some (.inr M.initial,(false,z.1.2.2),Move.stay)
        else some (.inl 2,z.1.2,Move.left)
      else if z.2-3<z.1.1.1+2 then if z.2-3<z.1.1.1+1 then
        some (.inl (z.2+1),(z.1.2.1,A.input p),Move.right)
        else some (.inl 2,z.1.2,Move.stay)
      else none) := by
    have hz : Primrec (fun z : X × ℕ => z.1.2) := ha.comp Primrec.fst
    have mk (c : Control Q) (mv : Move) : Primrec (fun z : X × ℕ => some (c,z.1.2,mv)) :=
      Primrec.option_some.comp ((Primrec.const c).pair (hz.pair (Primrec.const mv)))
    have hemit : Primrec (fun z : X × ℕ =>
        some ((Sum.inl (z.2+1) : Control Q),(z.1.2.1,A.input p),Move.right)) :=
      Primrec.option_some.comp ((Primrec.sumInl.comp (Primrec.succ.comp Primrec.snd)).pair
        (((Primrec.fst.comp hz).pair (Primrec.const _)).pair (Primrec.const _)))
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      ((Primrec.dom_finite (fun a : Bool×Γ =>
        (some (.inl 1,(true,a.2),Move.stay) : Option (Cmd Q Γ)))).comp hz)
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      ((Primrec.dom_finite (fun a : Bool×Γ => if a.2=A.blank then
        (some (.inl 3,a,Move.stay) : Option (Cmd Q Γ)) else some (.inl 1,a,Move.right))).comp hz)
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 2))
      ((Primrec.dom_finite (fun a : Bool×Γ => if a.1 then
        (some (.inr M.initial,(false,a.2),Move.stay) : Option (Cmd Q Γ)) else some (.inl 2,a,Move.left))).comp hz)
    exact Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 3))
      (Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.const 2)))
      (Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 3))
        (Primrec.succ.comp (hn.comp Primrec.fst))) hemit (mk (.inl 2) .stay)) (Primrec.const none)
  exact (Primrec.sumCasesOn (Primrec.snd.comp Primrec.fst) hbranch.to₂
    ((Primrec.dom_finite (fun z : Q × (Bool×Γ) =>
      (M.transition z.1 z.2.2).map fun c =>
        ((Sum.inr c.state : Control Q),(false,c.write),c.move))).comp
          (Primrec.snd.pair (ha.comp Primrec.fst))).to₂).of_eq fun x => by
            cases x.1.2 <;> rfl

 theorem primrec_support : Primrec (support (Q := Q)) := by
  exact Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 5)))
      (Primrec.sumInl.comp Primrec.snd).to₂) (Primrec.const _)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {P α : Type*} [Primcodable P] [Primcodable α] [DecidableEq α]

omit [DecidableEq α] in
/-- Finite weak-component search is primitive recursive uniformly in a
    primitive-recursive edge table, not just separately at every table. -/
theorem primrec_expand_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : P × List α × List α => expand (r x.1) x.2.1 x.2.2) := by
  apply Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
  apply primrec_listFilter (Primrec.fst.comp Primrec.snd)
  unfold Primrec₂
  apply primrec_listAny (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  unfold Primrec₂
  let X := ((P × List α × List α) × α) × α
  have hp : Primrec (fun x : X => x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun x : X => x.2) := Primrec.snd
  have hb : Primrec (fun x : X => x.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.or.comp (hr.comp (hp.pair (ha.pair hb))) (hr.comp (hp.pair (hb.pair ha)))

omit [DecidableEq α] in
theorem primrec_search_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : (P × List α × α) × ℕ => search (r x.1.1) x.1.2.1 x.1.2.2 x.2) := by
  change Primrec₂ (fun (x : P × List α × α) n => search (r x.1) x.2.1 x.2.2 n)
  exact (Primrec.nat_rec
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    ((primrec_expand_family hr).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.snd)))).to₂).of_eq
            (fun x n => by induction n <;> simp_all [search])

omit [DecidableEq α] in
theorem primrec_component_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : P × List α × α => component (r x.1) x.2.1 x.2.2) :=
  (primrec_search_family hr).comp
    (Primrec.id.pair (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))

end FiniteAlgebraicEnvelopes.Effect.Graph

end OAI
end

section
-- module Solutions.OAIFAE.UniformControl
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform validation, simulation, and finite control.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
variable (table : P → Table H B T)
variable (hb : Primrec (fun x : P × H => (table x.1).boundary x.2))
variable (hc : Primrec (fun x : P × H × B × T => (table x.1).cell x.2.1 x.2.2.1 x.2.2.2))
variable (hd : Primrec (fun x : P × H => decide ((table x.1).direction x.2 = .right)))

include hb hc in
theorem primrec_rightStep : Primrec (fun x : P × Sector H B T => rightStep (table x.1) x.2) := by
  let X := P × Sector H B T
  have hv : Primrec (fun x : X => x.2) := Primrec.snd
  have hl := Sector.primrec_left.comp hv
  have hh := Sector.primrec_head.comp hv
  have hr := Sector.primrec_right.comp hv
  have hla := Sector.primrec_lb.comp hv
  have hra := Sector.primrec_rb.comp hv
  have hnil : Primrec (fun x : X => if x.2.rightBoundary then
      ((table x.1).boundary x.2.head).map (fun q => {x.2 with head := q}) else none) := by
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond hra
    · apply Primrec.option_map (hb.comp (Primrec.fst.pair hh))
      exact (Sector.primrec_mk (hl.comp Primrec.fst) Primrec.snd (hr.comp Primrec.fst)
        (hla.comp Primrec.fst) (hra.comp Primrec.fst)).to₂
    · exact Primrec.const none
  have hcons : Primrec₂ (fun (x : X) (p : (B×T) × List (B×T)) =>
      ((table x.1).cell x.2.head p.1.1 p.1.2).map fun a =>
        if a.cross then {x.2 with left := (p.1.1,a.tag)::x.2.left,head := a.head,right := p.2}
        else {x.2 with head := a.head,right := (p.1.1,a.tag)::p.2}) := by
    unfold Primrec₂
    apply Primrec.option_map (hc.comp
      ((Primrec.fst.comp Primrec.fst).pair ((hh.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))))
    unfold Primrec₂
    let Y := (X × ((B×T) × List (B×T))) × Instruction H T
    have hx : Primrec (fun y : Y => y.1.1) := Primrec.fst.comp Primrec.fst
    have hp : Primrec (fun y : Y => y.1.2) := Primrec.snd.comp Primrec.fst
    have hi : Primrec (fun y : Y => y.2) := Primrec.snd
    have hcell : Primrec (fun y : Y => (y.1.2.1.1,y.2.tag)) :=
      (Primrec.fst.comp (Primrec.fst.comp hp)).pair (Instruction.primrec_tag.comp hi)
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond (Instruction.primrec_cross.comp hi)
    · exact Sector.primrec_mk (Primrec.list_cons.comp hcell (hl.comp hx))
        (Instruction.primrec_head.comp hi) (Primrec.snd.comp hp) (hla.comp hx) (hra.comp hx)
    · exact Sector.primrec_mk (hl.comp hx) (Instruction.primrec_head.comp hi)
        (Primrec.list_cons.comp hcell (Primrec.snd.comp hp)) (hla.comp hx) (hra.comp hx)
  exact (Primrec.list_casesOn hr hnil hcons).of_eq fun x => by
    cases h : x.2.right with
    | nil => simp [rightStep,h]
    | cons a l => cases a; simp [rightStep,h]

include hb hc hd in
theorem primrec_step : Primrec (fun x : P × Sector H B T => step (table x.1) x.2) := by
  have hr := primrec_rightStep table hb hc
  exact (Primrec.cond (hd.comp (Primrec.fst.pair (Sector.primrec_head.comp Primrec.snd)))
    hr (Primrec.option_map (hr.comp (Primrec.fst.pair (Scan.primrec_flip.comp Primrec.snd)))
      (Scan.primrec_flip.comp Primrec.snd).to₂)).of_eq fun x => by
        simpa only [Bool.cond_decide] using (step_rightStep (table x.1) x.2).symm

variable [Fintype B] [Fintype T]
theorem primrec_sectorList : Primrec (fun x : List H × ℕ => sectorList (B := B) (T := T) x.1 x.2) := by
  apply Primrec.list_flatMap Primrec.fst
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp (Primrec.snd.comp Primrec.fst))
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  unfold Primrec₂
  have hm (a b : Bool) : Primrec (fun p : (((List H × ℕ) × H) × List (B×T)) × List (B×T) =>
      (⟨p.1.2,p.1.1.2,p.2,a,b⟩ : Sector H B T)) :=
    Sector.primrec_mk (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
      (Primrec.const a) (Primrec.const b)
  exact Primrec.list_cons.comp (hm false false) (Primrec.list_cons.comp (hm false true)
    (Primrec.list_cons.comp (hm true false) (Primrec.list_cons.comp (hm true true) (Primrec.const []))))

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

omit [DecidableEq H] [DecidableEq T] in
theorem primrec_universeList :
    Primrec (fun x : List H × Sector H B T => universeList x.1 x.2) := by
  apply primrec_listFilter (primrec_sectorList.comp (Primrec.fst.pair
    (Primrec.nat_add.comp (Primrec.list_length.comp (Sector.primrec_left.comp Primrec.snd))
      (Primrec.list_length.comp (Sector.primrec_right.comp Primrec.snd)))))
  exact (Primrec.eq.decide.comp (primrec_baseSkeleton.comp Primrec.snd)
    (primrec_baseSkeleton.comp (Primrec.snd.comp Primrec.fst))).to₂

include hb hc hd in
theorem primrec_componentList {support : P → List H} (hs : Primrec support) :
    Primrec (componentList table support) := by
  have he : Primrec (fun x : P × Sector H B T × Sector H B T =>
      decide (step (table x.1) x.2.1=some x.2.2)) :=
    Primrec.eq.decide.comp ((primrec_step table hb hc hd).comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
  exact (primrec_component_family (r := fun p a b => decide (step (table p) a=some b)) he).comp (Primrec.fst.pair
    ((primrec_universeList.comp ((hs.comp Primrec.fst).pair Primrec.snd)).pair Primrec.snd))

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator

variable {S Q Q' H C : Type*}

def surfaceCode : Surface.Head H ≃ Fin 3 ⊕ H where
  toFun | .raw => .inl 0 | .pending => .inl 1 | .cleanup => .inl 2 | .internal q => .inr q
  invFun | .inl k => if k=0 then .raw else if k=1 then .pending else .cleanup
         | .inr q => .internal q
  left_inv q := by cases q <;> rfl
  right_inv q := by cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => rfl

def pathCode : Path.Letter C H ≃ Fin 3 ⊕ (C ⊕ (C ⊕ H)) where
  toFun | .zero => .inl 0 | .enter => .inl 1 | .leave => .inl 2
        | .left c => .inr (.inl c) | .right c => .inr (.inr (.inl c))
        | .head q => .inr (.inr (.inr q))
  invFun | .inl k => if k=0 then .zero else if k=1 then .enter else .leave
         | .inr (.inl c) => .left c | .inr (.inr (.inl c)) => .right c
         | .inr (.inr (.inr q)) => .head q
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => cases q with
      | inl c => rfl
      | inr q => cases q <;> rfl

scoped instance surfacePrimcodable [Primcodable H] : Primcodable (Surface.Head H) :=
  Primcodable.ofEquiv _ surfaceCode
scoped instance pathPrimcodable [Primcodable C] [Primcodable H] : Primcodable (Path.Letter C H) :=
  Primcodable.ofEquiv _ pathCode

variable [Fintype S] [Primcodable Q]
theorem primrec_simCode : Primrec (simCode (S := S) (Q := Q)) := Primrec.of_equiv
theorem primrec_simDecode : Primrec (simCode (S := S) (Q := Q)).symm := Primrec.of_equiv_symm
theorem primrec_ofStatic : Primrec (ofStatic (S := S) (Q := Q)) :=
  primrec_simDecode.comp Primrec.sumInl
theorem primrec_dynamic : Primrec (dynamic (S := S) (Q := Q)) :=
  primrec_simDecode.comp Primrec.sumInr

theorem primrec_controlCode : Primrec (controlCode (S := S) (Q := Q)) := Primrec.of_equiv
theorem primrec_controlDecode : Primrec (controlCode (S := S) (Q := Q)).symm := Primrec.of_equiv_symm
theorem primrec_machine : Primrec (Control.Head.machine (S := S) (Q := Q)) :=
  primrec_controlDecode.comp Primrec.sumInr

theorem primrec_surfaceCode [Primcodable H] : Primrec (surfaceCode (H := H)) := Primrec.of_equiv
theorem primrec_surfaceDecode [Primcodable H] : Primrec (surfaceCode (H := H)).symm := Primrec.of_equiv_symm
theorem primrec_internal [Primcodable H] : Primrec (Surface.Head.internal (H := H)) :=
  primrec_surfaceDecode.comp Primrec.sumInr

theorem primrec_pathCode [Primcodable C] [Primcodable H] : Primrec (pathCode (C := C) (H := H)) :=
  Primrec.of_equiv
theorem primrec_pathDecode [Primcodable C] [Primcodable H] : Primrec (pathCode (C := C) (H := H)).symm :=
  Primrec.of_equiv_symm

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q Q' P : Type*}

def commandCode : Command Q Γ ≃ Q × Γ × Move where
  toFun c := (c.state,c.write,c.move)
  invFun c := ⟨c.1,c.2.1,c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable scoped instance movePrimcodable : Primcodable Move := Effect.finitePrimcodable _
noncomputable scoped instance commandPrimcodable [Primcodable Q] [Primcodable Γ] : Primcodable (Command Q Γ) :=
  Primcodable.ofEquiv _ commandCode

theorem primrec_commandCode [Primcodable Q] [Primcodable Γ] : Primrec (commandCode (Q := Q) (Γ := Γ)) :=
  Primrec.of_equiv

theorem primrec_commandState [Primcodable Q] [Primcodable Γ] : Primrec (Command.state (Q := Q) (Γ := Γ)) :=
  Primrec.fst.comp primrec_commandCode

theorem primrec_commandWrite [Primcodable Q] [Primcodable Γ] : Primrec (Command.write (Q := Q) (Γ := Γ)) :=
  Primrec.fst.comp (Primrec.snd.comp primrec_commandCode)

theorem primrec_commandMove [Primcodable Q] [Primcodable Γ] : Primrec (Command.move (Q := Q) (Γ := Γ)) :=
  Primrec.snd.comp (Primrec.snd.comp primrec_commandCode)

theorem primrec_commandMk [Primcodable P] [Primcodable Q] [Primcodable Γ]
    {q : P → Q} {a : P → Γ} {d : P → Move} (hq : Primrec q) (ha : Primrec a) (hd : Primrec d) :
    Primrec (fun p => (⟨q p,a p,d p⟩ : Command Q Γ)) :=
  Primrec.of_equiv_symm.comp (hq.pair (ha.pair hd))

variable [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q']
theorem primrec_stateMap {f : P → Q → Q'} (hf : Primrec (fun x : P × Q => f x.1 x.2)) :
    Primrec (fun x : P × Simulator.Head S Q => stateMap (f x.1) x.2) := by
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd)
    (primrec_ofStatic.comp Primrec.snd).to₂
    (primrec_dynamic.comp ((Primrec.fst.comp Primrec.snd).pair
      (hf.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))))).to₂).of_eq
        (fun x => by cases x.2 <;> rfl)

theorem primrec_controlMap {f : P → Q → Q'} (hf : Primrec (fun x : P × Q => f x.1 x.2)) :
    Primrec (fun x : P × Control.Head S Q => controlMap (f x.1) x.2) := by
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd)
    (primrec_controlDecode.comp (Primrec.sumInl.comp Primrec.snd)).to₂
    (primrec_machine.comp ((primrec_stateMap hf).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂).of_eq
        (fun x => by cases x.2 <;> rfl)

theorem primrec_instruction [Primcodable Γ] {q : P → Q} {t : P → Γ} {b : P → Bool}
    (hq : Primrec q) (ht : Primrec t) (hb : Primrec b) :
    Primrec (fun p => (⟨q p,t p,b p⟩ : Instruction Q Γ)) :=
  Primrec.of_equiv_symm.comp (hq.pair (ht.pair hb))

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q P : Type*} [Fintype S] [Fintype Γ] [DecidableEq S] [DecidableEq Γ]
  [Primcodable Γ] [Primcodable Q] [Primcodable P]
variable (A : Alphabet S Γ) (M : P → Machine Q Γ)
  (hinit : Primrec (fun p => (M p).initial))
  (htrans : Primrec (fun x : P × Q × Γ => (M x.1).transition x.2.1 x.2.2))

def dummy : Machine Unit Γ := ⟨(),fun _ _ => none⟩

omit [Fintype S] [Fintype Γ] [DecidableEq S] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem static_cell (p : P) (s : Static S) (b : Base S) (t : Tag S Γ) :
    cell A (M p) (ofStatic s) b t=
      (cell A dummy (ofStatic s) b t).map
        (Scan.mapInstruction (stateMap (fun _ : Unit => (M p).initial))) := by
  cases s with
  | start | rewind | finish | ok => rfl
  | scan r =>
    cases r <;> cases b <;>
      simp [cell,ofStatic,stateMap,Scan.mapInstruction,dummy]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap,Option.map_map,Function.comp_def]

include hinit in
omit [DecidableEq S] [Primcodable Γ] in
theorem primrec_staticCell : Primrec (fun x : P × Static S × Base S × Tag S Γ =>
    cell A (M x.1) (ofStatic x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Static S × Base S × Tag S Γ =>
      cell A dummy (ofStatic x.2.1) x.2.2.1 x.2.2.2) :=
    (Primrec.dom_finite (fun y : Static S × Base S × Tag S Γ =>
      cell A dummy (ofStatic y.1) y.2.1 y.2.2)).comp Primrec.snd
  have hp := primrec_stateMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Static S × Base S × Tag S Γ)
      (c : Instruction (Simulator.Head S Unit) (Tag S Γ)) =>
      Scan.mapInstruction (stateMap (fun _ : Unit => (M x.1).initial)) c) :=
    (primrec_instruction (hp.comp ((Primrec.fst.comp Primrec.fst).pair
      (Instruction.primrec_head.comp Primrec.snd)))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => (static_cell A M x.1 x.2.1 x.2.2.1 x.2.2.2).symm

def leftCross : Base S → Option Bool
  | .workspace => some true | .cutC => some false | _ => none

omit [DecidableEq S] [Primcodable Γ] in
theorem primrec_leftCell : Primrec (fun x : P × Q × Base S × Tag S Γ =>
    cell A (M x.1) (.left x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Q × Base S × Tag S Γ => leftCross x.2.2.1) :=
    (Primrec.dom_finite (leftCross (S := S))).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec₂ (fun (x : P × Q × Base S × Tag S Γ) (b : Bool) =>
      (⟨.run x.2.1,x.2.2.2,b⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) :=
    (primrec_instruction
      (primrec_dynamic.comp ((Primrec.const false).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => by cases x.2.2.1 <;> rfl

include htrans in
omit [DecidableEq S] in
theorem primrec_runWorkspace : Primrec (fun x : P × Q × Tag S Γ =>
    cell A (M x.1) (.run x.2.1) .workspace x.2.2) := by
  have ht : Primrec (fun x : P × Q × Tag S Γ => x.2.2) := Primrec.snd.comp Primrec.snd
  have hw : Primrec (fun x : Tag S Γ => x.work) := Primrec.dom_finite _
  have hc := htrans.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hw.comp ht)))
  have hz : Primrec (fun x : P × Q × Tag S Γ =>
      some (⟨.rewind .readout,x.2.2,false⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) :=
    Primrec.option_some.comp (primrec_instruction (Primrec.const _) ht (Primrec.const false))
  have hd : Primrec₂ (fun (x : P × Q × Tag S Γ) (c : Command Q Γ) =>
      some (⟨(if c.move = .left then .left c.state else .run c.state),
        {x.2.2 with work := c.write}, c.move == .right⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) := by
    unfold Primrec₂
    apply Primrec.option_some.comp
    apply primrec_instruction
    · exact (primrec_dynamic.comp
        (((Primrec.dom_finite (fun d : Move => decide (d=.left))).comp
          ((primrec_commandMove (Q := Q) (Γ := Γ)).comp Primrec.snd)).pair
            (primrec_commandState.comp Primrec.snd))).of_eq fun x => by
              simp only [dynamic, decide_eq_true_eq]
    · exact (Primrec.dom_finite (fun p : Tag S Γ × Γ => {p.1 with work := p.2})).comp
        ((ht.comp Primrec.fst).pair ((primrec_commandWrite (Q := Q) (Γ := Γ)).comp Primrec.snd))
    · exact (Primrec.dom_finite (fun d : Move => d == .right)).comp
        ((primrec_commandMove (Q := Q) (Γ := Γ)).comp Primrec.snd)
  exact (Primrec.option_casesOn hc hz hd).of_eq fun x => by
    simp only [cell]
    cases (M x.1).transition x.2.1 x.2.2.work <;> rfl

include htrans in
theorem primrec_runCell : Primrec (fun x : P × Q × Base S × Tag S Γ =>
    cell A (M x.1) (.run x.2.1) x.2.2.1 x.2.2.2) := by
  have hb : Primrec (fun x : P × Q × Base S × Tag S Γ => decide (x.2.2.1=.workspace)) :=
    (Primrec.dom_finite (fun b : Base S => decide (b=.workspace))).comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.cond hb
    ((primrec_runWorkspace A M htrans).comp (Primrec.fst.pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.const none)).of_eq fun x => by cases x.2.2.1 <;> rfl

include hinit htrans in
theorem primrec_simCell : Primrec (fun x : P × Simulator.Head S Q × Base S × Tag S Γ =>
    (Simulator.table A (M x.1)).cell x.2.1 x.2.2.1 x.2.2.2) := by
  let X := P × Simulator.Head S Q × Base S × Tag S Γ
  have hp : Primrec (fun x : X => x.1) := Primrec.fst
  have hbt : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have hs : Primrec₂ (fun (x : X) (s : Static S) => cell A (M x.1) (ofStatic s) x.2.2.1 x.2.2.2) :=
    ((primrec_staticCell A M hinit).comp
      ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst)))).to₂
  have hd : Primrec₂ (fun (x : X) (d : Bool × Q) => cell A (M x.1) (dynamic d) x.2.2.1 x.2.2.2) := by
    unfold Primrec₂
    exact (Primrec.cond (Primrec.fst.comp Primrec.snd)
      ((primrec_leftCell A M).comp ((hp.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair (hbt.comp Primrec.fst))))
      ((primrec_runCell A M htrans).comp ((hp.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair (hbt.comp Primrec.fst))))).of_eq fun x => by
          cases h : x.2.1 <;> simp [dynamic,h]
  exact (Primrec.sumCasesOn (primrec_simCode.comp (Primrec.fst.comp Primrec.snd)) hs hd).of_eq
    fun x => by cases x.2.1 <;> rfl

def staticBoundary : Static S → Option (Static S)
  | .start => some (.rewind .input) | .rewind r => some (.scan r)
  | .scan .input => some (.rewind .spare) | .finish => some .ok | _ => none

omit [Fintype Γ] [DecidableEq S] [Primcodable Γ] in
theorem primrec_simBoundary : Primrec (fun x : P × Simulator.Head S Q =>
    (Simulator.table A (M x.1)).boundary x.2) := by
  have hs : Primrec₂ (fun (_ : P × Simulator.Head S Q) (s : Static S) =>
      (staticBoundary s).map (ofStatic (Q := Q))) :=
    (Primrec.option_map ((Primrec.dom_finite (staticBoundary (S := S))).comp Primrec.snd)
      (primrec_ofStatic.comp Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd) hs (Primrec.const none).to₂).of_eq
    fun x => by
      cases x.2 <;> simp [simCode,table,staticBoundary,ofStatic]
      rename_i r; cases r <;> rfl

omit [Fintype Γ] [DecidableEq S] [Primcodable Γ] in
theorem primrec_simDirection : Primrec (fun x : P × Simulator.Head S Q =>
    decide ((Simulator.table A (M x.1)).direction x.2 = .right)) := by
  have hs : Primrec₂ (fun (_ : P × Simulator.Head S Q) (s : Static S) =>
      decide ((Simulator.table A dummy).direction (ofStatic s) = .right)) :=
    ((Primrec.dom_finite (fun s : Static S =>
      decide ((Simulator.table A dummy).direction (ofStatic s) = .right))).comp Primrec.snd).to₂
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd) hs
    (Primrec.not.comp (Primrec.fst.comp Primrec.snd)).to₂).of_eq
      fun x => by cases x.2 <;> rfl

omit [Fintype S] [DecidableEq S] [Primcodable Q] in
theorem validatorHead_map {Q' : Type*} (f : Q → Q') (h : Validator.Head) :
    controlMap (S := S) f (Control.validatorHead h)=Control.validatorHead h := by
  cases h <;> rfl

omit [Fintype S] [Fintype Γ] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem staticControl_cell (p : P) (k : Fin 5) (b : Base S) (t : Tag S Γ) :
    (Control.table A (M p)).cell (staticControl k) b t =
      ((Control.table A dummy).cell (staticControl k) b t).map
        (Scan.mapInstruction (controlMap (fun _ : Unit => (M p).initial))) := by
  have hm :
      Scan.mapInstruction (T := Tag S Γ) (controlMap (fun _ : Unit => (M p).initial)) ∘
        Scan.mapInstruction (Control.validatorHead (S := S)) =
          Scan.mapInstruction (Control.validatorHead (S := S) (Q := Q)) := by
    funext c
    cases c with | mk q t b => simp [Scan.mapInstruction,validatorHead_map]
  fin_cases k <;>
    simp [staticControl,controlCode,Control.table,Control.toValidator,Option.map_map,hm]

omit [Fintype S] [Fintype Γ] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem staticControl_boundary (p : P) (k : Fin 5) :
    (Control.table A (M p)).boundary (staticControl k) =
      ((Control.table A dummy).boundary (staticControl k)).map
        (controlMap (fun _ : Unit => (M p).initial)) := by
  have hm : controlMap (fun _ : Unit => (M p).initial) ∘
      Control.validatorHead (S := S) = Control.validatorHead (S := S) (Q := Q) := by
    funext q; exact validatorHead_map _ q
  fin_cases k <;>
    simp [staticControl,controlCode,Control.table,Control.toValidator,Option.map_map,hm]

include hinit in
omit [Primcodable Γ] in
theorem primrec_controlStaticCell : Primrec (fun x : P × Fin 5 × Base S × Tag S Γ =>
    (Control.table A (M x.1)).cell (staticControl x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Fin 5 × Base S × Tag S Γ =>
      (Control.table A dummy).cell (staticControl x.2.1) x.2.2.1 x.2.2.2) :=
    (Primrec.dom_finite (fun y : Fin 5 × Base S × Tag S Γ =>
      (Control.table A dummy).cell (staticControl y.1) y.2.1 y.2.2)).comp Primrec.snd
  have hp := primrec_controlMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Fin 5 × Base S × Tag S Γ)
      (c : Instruction (Control.Head S Unit) (Tag S Γ)) =>
      Scan.mapInstruction (controlMap (fun _ : Unit => (M x.1).initial)) c) :=
    (primrec_instruction (hp.comp ((Primrec.fst.comp Primrec.fst).pair
      (Instruction.primrec_head.comp Primrec.snd)))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => (staticControl_cell A M x.1 x.2.1 x.2.2.1 x.2.2.2).symm

include hinit htrans in
theorem primrec_controlCell : Primrec (fun x : P × Control.Head S Q × Base S × Tag S Γ =>
    (Control.table A (M x.1)).cell x.2.1 x.2.2.1 x.2.2.2) := by
  let X := P × Control.Head S Q × Base S × Tag S Γ
  have hp : Primrec (fun x : X => x.1) := Primrec.fst
  have hbt : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have hs := ((primrec_controlStaticCell A M hinit).comp
    ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst)))).to₂
  have hd : Primrec₂ (fun (x : X) (q : Simulator.Head S Q) =>
      ((Simulator.table A (M x.1)).cell q x.2.2.1 x.2.2.2).map
        (Scan.mapInstruction Control.Head.machine)) := by
    unfold Primrec₂
    apply Primrec.option_map ((primrec_simCell A M hinit htrans).comp
      ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst))))
    exact (primrec_instruction (primrec_machine.comp (Instruction.primrec_head.comp Primrec.snd))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp (Primrec.fst.comp Primrec.snd)) hs hd).of_eq
    fun x => by cases x.2.1 <;> rfl

include hinit in
omit [Fintype Γ] [Primcodable Γ] in
theorem primrec_controlBoundary : Primrec (fun x : P × Control.Head S Q =>
    (Control.table A (M x.1)).boundary x.2) := by
  have hp := primrec_controlMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Control.Head S Q) (k : Fin 5) =>
      (Control.table A (M x.1)).boundary (staticControl k)) := by
    unfold Primrec₂
    exact (Primrec.option_map
      ((Primrec.dom_finite (fun k : Fin 5 => (Control.table A dummy).boundary (staticControl k))).comp Primrec.snd)
      (hp.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂).of_eq
        fun x => (staticControl_boundary A M x.1.1 x.2).symm
  have hd : Primrec₂ (fun (x : P × Control.Head S Q) (q : Simulator.Head S Q) =>
      ((Simulator.table A (M x.1)).boundary q).map Control.Head.machine) :=
    (Primrec.option_map ((primrec_simBoundary A M).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
        (primrec_machine.comp Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd) hs hd).of_eq
    fun x => by cases x.2 <;> rfl

omit [Fintype Γ] [Primcodable Γ] in
theorem primrec_controlDirection : Primrec (fun x : P × Control.Head S Q =>
    decide ((Control.table A (M x.1)).direction x.2 = .right)) := by
  have hs : Primrec₂ (fun (_ : P × Control.Head S Q) (k : Fin 5) =>
      decide ((Control.table A dummy).direction (staticControl k) = .right)) :=
    ((Primrec.dom_finite (fun k : Fin 5 =>
      decide ((Control.table A dummy).direction (staticControl k) = .right))).comp Primrec.snd).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd) hs
    ((primrec_simDirection A M).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
      fun x => by cases x.2 <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {S Q : Type*} [Fintype S]

variable [Primcodable Q]
theorem primrec_simSupport : Primrec (simSupport (S := S) (Q := Q)) := by
  have hr : Primrec (Simulator.Head.run (S := S) (Q := Q)) :=
    primrec_dynamic.comp ((Primrec.const false).pair Primrec.id)
  have hl : Primrec (Simulator.Head.left (S := S) (Q := Q)) :=
    primrec_dynamic.comp ((Primrec.const true).pair Primrec.id)
  exact Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_flatMap Primrec.id ((Primrec.list_cons.comp hr
      (Primrec.list_cons.comp hl (Primrec.const []))).comp Primrec.snd).to₂)

theorem primrec_controlSupport : Primrec (controlSupport (S := S) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_map primrec_simSupport (primrec_machine.comp Primrec.snd).to₂)

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
namespace Surface.Uniform
open Surface HeadCodec
open scoped HeadCodec
open Scan
variable {S Γ H : Type*} [Fintype S] [Fintype Γ] [Primcodable H]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq H] (blank : Γ)

omit [Fintype S] [Fintype Γ] [Primcodable H] [DecidableEq H] in
 theorem rawSweep_takeDrop (l r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H) blank l r lb rb =
      ⟨l.dropWhile (cleanAnchor blank),.raw,
        (l.takeWhile (cleanAnchor blank)).reverse ++ r,lb,rb⟩ := by
  induction l generalizing r with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨b,t⟩
    cases b with
    | anchor a =>
      by_cases h : t = clean blank
      · simp [rawSweep,h,cleanAnchor,ih,List.reverse_cons,List.append_assoc]
      · simp [rawSweep,h,cleanAnchor]
    | cutC | cutD | workspace => simp [rawSweep,cleanAnchor]

omit [DecidableEq H] in
 theorem primrec_rawSweep : Primrec (fun p : (Cells S Γ × Cells S Γ) × Bool × Bool =>
    rawSweep (H := H) blank p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp := Primrec.dom_finite (cleanAnchor (S := S) blank)
  exact (Scan.Sector.primrec_mk
    ((Primrec.list_dropWhile hp).comp (Primrec.fst.comp Primrec.fst))
    (Primrec.const Head.raw)
    (Primrec.list_append.comp
      (Primrec.list_reverse.comp ((Primrec.list_takeWhile hp).comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).of_eq
      fun p => (rawSweep_takeDrop blank _ _ _ _).symm

 theorem primrec_rawNormal : Primrec (rawNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .raw) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.raw)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .raw then
      rawSweep blank v.left v.right v.leftBoundary v.rightBoundary else v) :=
    Primrec.ite hg ((primrec_rawSweep blank).comp
      ((Scan.Sector.primrec_left.pair Scan.Sector.primrec_right).pair
        (Scan.Sector.primrec_lb.pair Scan.Sector.primrec_rb))) Primrec.id
  exact hh.of_eq fun v => by cases h : v.head <;> simp [rawNormal,h]

 theorem primrec_trimQuota : Primrec (trimQuota (S := S) blank) :=
  (Primrec.list_dropWhile (Primrec.dom_finite _)).of_eq fun l => (trimQuota_drop blank l).symm

 theorem primrec_quotaNormal : Primrec (quotaNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _))
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)
      then {v with left := trimQuota blank v.left} else v) :=
    Primrec.ite hg
      (Scan.Sector.primrec_mk ((primrec_trimQuota blank).comp Scan.Sector.primrec_left)
        Scan.Sector.primrec_head Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
      Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases r <;> simp [quotaNormal]

 theorem primrec_unmerge : Primrec (unmerge (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      ((Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_left) (Primrec.const _)).and
        (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _)))
  have hl : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk
      (Primrec.list_tail.comp Scan.Sector.primrec_left) (Primrec.const Head.raw)
      (Primrec.const []) Scan.Sector.primrec_lb (Primrec.const true))
  have hr : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk (Primrec.const [])
      (Primrec.const Head.raw) (Primrec.list_tail.comp Scan.Sector.primrec_right)
      (Primrec.const true) Scan.Sector.primrec_rb)
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)
      then [rawNormal blank ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩,
        rawNormal blank ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩]
      else [v]) :=
    Primrec.ite hg (Primrec.list_cons.comp hl
      (Primrec.list_cons.comp hr (Primrec.const [])))
      (Primrec.list_cons.comp Primrec.id (Primrec.const []))
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases l with
    | nil => cases q <;> simp [unmerge]
    | cons c l =>
      cases r with
      | nil => cases q <;> simp [unmerge]
      | cons d r => cases q <;> simp [unmerge]

 theorem primrec_pendingPreprocess : Primrec (pendingPreprocess (S := S) (H := H) blank) :=
  (primrec_unmerge blank).comp (primrec_quotaNormal blank)
omit [DecidableEq S] [DecidableEq Γ] in
 theorem primrec_cleanupNormal : Primrec (cleanupNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .cleanup) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.cleanup)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .cleanup then
      (⟨[],if v.leftBoundary then .raw else .cleanup,
        Cleanup.output blank v.left.reverse ++ v.right,v.leftBoundary,v.rightBoundary⟩ : Sector S Γ H)
      else v) :=
    Primrec.ite hg (Scan.Sector.primrec_mk (Primrec.const [])
      ((Primrec.dom_finite (fun b : Bool => if b then (Head.raw : Head H) else .cleanup)).comp
        Scan.Sector.primrec_lb)
      (Primrec.list_append.comp ((primrec_cleanupOutput blank).comp
        (Primrec.list_reverse.comp Scan.Sector.primrec_left)) Scan.Sector.primrec_right)
      Scan.Sector.primrec_lb Scan.Sector.primrec_rb) Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases lb <;> rfl

 theorem primrec_cleanupPreprocess : Primrec (cleanupPreprocess (S := S) (H := H) blank) :=
  (primrec_rawNormal blank).comp (primrec_cleanupNormal blank)
end Surface.Uniform
end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIFAE.UniformPaths
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Path.Uniform
open FiniteAlgebraicEnvelopes.Compiler.Path HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {C H : Type*} [Primcodable C] [Primcodable H]

theorem primrec_left : Primrec (Letter.left (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp Primrec.sumInl)
theorem primrec_right : Primrec (Letter.right (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))
theorem primrec_head : Primrec (Letter.head (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem primrec_head? : Primrec (fun a : Letter C H => match a with | .head q => some q | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim (Primrec.const none)
      (primrec_sumElim (Primrec.const none) Primrec.option_some))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_left? : Primrec (fun a : Letter C H => match a with | .left c => some c | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim Primrec.option_some (Primrec.const none))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_right? : Primrec (fun a : Letter C H => match a with | .right c => some c | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim (Primrec.const none)
      (primrec_sumElim Primrec.option_some (Primrec.const none)))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_heads : Primrec (heads (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_head?.comp Primrec.snd).to₂
theorem primrec_lefts : Primrec (lefts (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_left?.comp Primrec.snd).to₂
theorem primrec_rights : Primrec (rights (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_right?.comp Primrec.snd).to₂
 theorem primrec_encode : Primrec (encode (C := C) (H := H)) := by
  have hl : Primrec (fun v : Sector C H => v.left.reverse.map (Letter.left : C → Letter C H)) :=
    Primrec.list_map (Primrec.list_reverse.comp Sector.primrec_left)
      (primrec_left.comp Primrec.snd).to₂
  have hr : Primrec (fun v : Sector C H => v.right.map (Letter.right : C → Letter C H)) :=
    Primrec.list_map Sector.primrec_right (primrec_right.comp Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp
      ((Primrec.dom_finite (fun b : Bool => if b then ([.enter] : List (Letter C H)) else [])).comp
        Sector.primrec_lb) hl)
      (Primrec.list_cons.comp (primrec_head.comp Sector.primrec_head) (Primrec.const []))) hr)
    ((Primrec.dom_finite (fun b : Bool => if b then ([.leave] : List (Letter C H)) else [])).comp
      Sector.primrec_rb)

 theorem primrec_glue : Primrec₂ (glue (C := C) (H := H)) := by
  have hn : Primrec (fun p : List (Letter C H) × List (List (Letter C H)) =>
      if p.1 = [] then [] else [p.1]) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const [])) (Primrec.const [])
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
  have hc : Primrec₂ (fun (p : List (Letter C H) × List (List (Letter C H)))
      (ct : List (Letter C H) × List (List (Letter C H))) => (p.1++ct.1)::ct.2) :=
    (Primrec.list_cons.comp (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_casesOn Primrec.snd hn hc).to₂.of_eq fun u w => by
    cases w <;> cases u <;> rfl

variable [DecidableEq C] [DecidableEq H]

omit [Primcodable C] [Primcodable H] in
 theorem cuts_fold (w : List (Letter C H)) :
    cuts w = w.foldr (fun a cs => if a = .leave then [.leave]::cs else glue [a] cs) [] := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [cuts,ih]

 theorem primrec_cuts : Primrec (cuts (C := C) (H := H)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const Letter.leave))
      (Primrec.list_cons.comp (Primrec.const [Letter.leave]) (Primrec.snd.comp Primrec.snd))
      (primrec_glue.comp (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
        (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun w => (cuts_fold w).symm

omit [DecidableEq C] [DecidableEq H] in
 theorem primrec_mem (a : Letter C H) : PrimrecPred (fun w : List (Letter C H) => a ∈ w) := by
  exact ((Primrec.eq.comp Primrec.id (Primrec.const a)).exists_mem_list).of_eq fun w => by simp

 theorem primrec_decode : Primrec (decode (C := C) (H := H)) := by
  let make : List (Letter C H) × H → Sector C H := fun p =>
    ⟨(lefts p.1).reverse,p.2,rights p.1,decide (.enter ∈ p.1),decide (.leave ∈ p.1)⟩
  have hm : Primrec make := Sector.primrec_mk
    (Primrec.list_reverse.comp (primrec_lefts.comp Primrec.fst)) Primrec.snd
    (primrec_rights.comp Primrec.fst) ((primrec_mem .enter).decide.comp Primrec.fst)
    ((primrec_mem .leave).decide.comp Primrec.fst)
  have ht : Primrec (fun p : List (Letter C H) × H =>
      if encode (make p) = p.1 then some (make p) else none) :=
    Primrec.ite (Primrec.eq.comp (primrec_encode.comp hm) Primrec.fst)
      (Primrec.option_some.comp hm) (Primrec.const none)
  have hh : Primrec (fun w : List (Letter C H) => if (heads w).length = 1 then
      (heads w).head?.bind (fun q => if encode (make (w,q)) = w then some (make (w,q)) else none)
      else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp primrec_heads) (Primrec.const 1))
      (Primrec.option_bind (Primrec.list_head?.comp primrec_heads) ht.to₂) (Primrec.const none)
  exact hh.of_eq fun w => by
    unfold decode
    cases h : heads w with
    | nil => simp
    | cons q t => cases t with
      | nil => simp only [List.length_singleton,↓reduceIte,List.head?_cons,Option.bind_some]; rfl
      | cons q' t => simp

end FiniteAlgebraicEnvelopes.Compiler.Path.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]

variable [LinearOrder (Sector H B T)]

theorem primrec_representative (table : P → Table H B T) {support : P → List H}
    {entry success : Sector H B T → Bool}
    (hb : Primrec (fun x : P × H => (table x.1).boundary x.2))
    (hc : Primrec (fun x : P × H × B × T => (table x.1).cell x.2.1 x.2.2.1 x.2.2.2))
    (hd : Primrec (fun x : P × H => decide ((table x.1).direction x.2 = .right)))
    (hs : Primrec support) (hp : Primrec entry) (hq : Primrec success)
    (hle : PrimrecRel (fun a b : Sector H B T => a ≤ b)) :
    Primrec (representative table support entry success) :=
  Primrec.option_getD.comp ((primrec_listMin hle).comp
    ((primrec_priorityList hp hq).comp (primrec_componentList table hb hc hd hs))) Primrec.snd

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Control.Uniform
variable {S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_entry (blank : Γ) : PrimrecPred (Entry (S := S) (Q := Q) blank) :=
  (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.initial)).and
    (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right)
      (Primrec.const (some (Validator.cell blank .cutD))))

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_success : PrimrecPred (Success (S := S) (Γ := Γ) (Q := Q)) :=
  (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const (Head.machine .ok))).and
    ((Primrec.eq.comp Scan.Sector.primrec_right (Primrec.const [])).and
      (Primrec.eq.comp Scan.Sector.primrec_rb (Primrec.const true)))
end Control.Uniform

namespace Surface.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

theorem primrec_internalPreprocess (hrep : Primrec rep) : Primrec (internalPreprocess blank rep) := by
  have hp := primrec_pendingPreprocess (S := S) (H := Control.Head S Q) blank
  have hc := primrec_cleanupPreprocess (S := S) (H := Control.Head S Q) blank
  have hl : Primrec (fun w : Control.Sector S Γ Q =>
      pendingPreprocess blank (⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hp.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.pending)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  have hr : Primrec (fun w : Control.Sector S Γ Q =>
      cleanupPreprocess blank (⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hc.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.cleanup)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  exact (Primrec.ite (Control.Uniform.primrec_entry blank) hl
    (Primrec.ite Control.Uniform.primrec_success (Primrec.list_cons.comp hr (Primrec.const []))
      (Primrec.list_cons.comp (Scan.primrec_mapHead HeadCodec.primrec_internal)
        (Primrec.const [])))).comp hrep

theorem primrec_preprocess (hrep : Primrec rep) : Primrec (preprocess blank rep) := by
  let inside : Head (Control.Head S Q) → Control.Head S Q
    | .internal q => q
    | _ => .initial
  have hin : Primrec inside :=
    ((primrec_sumElim (Primrec.const Control.Head.initial) Primrec.id).comp primrec_surfaceCode).of_eq
      fun q => by cases q <;> rfl
  have hv : Primrec (fun x : P × Sector S Γ (Control.Head S Q) =>
      (⟨x.2.left,inside x.2.head,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩ : Control.Sector S Γ Q)) :=
    (Scan.Sector.primrec_mk Scan.Sector.primrec_left
        (hin.comp Scan.Sector.primrec_head) Scan.Sector.primrec_right
          Scan.Sector.primrec_lb Scan.Sector.primrec_rb).comp (Primrec.snd (α :=P))
  have hi : Primrec (fun x : P × Sector S Γ (Control.Head S Q) =>
      internalPreprocess blank rep
        (x.1,⟨x.2.left,inside x.2.head,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩)) :=
    (primrec_internalPreprocess blank rep hrep).comp (Primrec.fst.pair hv)
  have hg (q : Head (Control.Head S Q)) :
      PrimrecPred (fun x : P × Sector S Γ (Control.Head S Q) => x.2.head = q) :=
    Primrec.eq.comp (Scan.Sector.primrec_head.comp Primrec.snd) (Primrec.const q)
  exact (Primrec.ite (hg .raw)
      (Primrec.list_cons.comp ((primrec_rawNormal blank).comp Primrec.snd) (Primrec.const []))
      (Primrec.ite (hg .pending) ((primrec_pendingPreprocess blank).comp Primrec.snd)
        (Primrec.ite (hg .cleanup)
          (Primrec.list_cons.comp ((primrec_cleanupPreprocess blank).comp Primrec.snd) (Primrec.const [])) hi))).of_eq
    fun x => by rcases x with ⟨p,l,q,r,lb,rb⟩; cases q <;> simp [preprocess,inside]
end Surface.Uniform

namespace Path.Uniform
variable {P C H : Type*} [Primcodable P] [Primcodable C] [Primcodable H]
  [DecidableEq C] [DecidableEq H]

theorem primrec_prepareChunk_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (Letter C H) =>
      prepareChunk (fun v => norm (x.1,v)) x.2) := by
  exact (Primrec.option_casesOn (primrec_decode.comp Primrec.snd)
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    (Primrec.list_map (hn.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      (primrec_encode.comp Primrec.snd).to₂).to₂).of_eq
        fun x => by cases h : decode x.2 <;> simp [prepareChunk,h]

theorem primrec_prepareChunks_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (List (Letter C H)) =>
      prepareChunks (fun v => norm (x.1,v)) x.2) :=
  Primrec.list_flatMap Primrec.snd ((primrec_prepareChunk_family hn).comp
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem primrec_prepare_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (Letter C H) =>
      prepare (fun v => norm (x.1,v)) x.2) :=
  (primrec_prepareChunks_family hn).comp (Primrec.fst.pair (primrec_cuts.comp Primrec.snd))
end Path.Uniform

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

theorem primrec_sectorPreprocess (hrep : Primrec rep) : Primrec (sectorPreprocess blank rep) :=
  Primrec.list_map ((Surface.Uniform.primrec_preprocess blank rep hrep).comp
    (Primrec.fst.pair (Scan.primrec_unliteral.comp Primrec.snd)))
    ((Scan.primrec_literal Primrec.id).comp Primrec.snd).to₂

theorem primrec_preprocess (hrep : Primrec rep) : Primrec (preprocess blank rep) :=
  Path.Uniform.primrec_prepare_family (primrec_sectorPreprocess blank rep hrep)

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Effect
variable {P α β : Type*} [Primcodable P] [Primcodable α] [Primcodable β]

omit [Primcodable P] [Primcodable α] [Primcodable β] in
theorem traverse_map_parameter (f : P × α → Part β) (p : P) (l : List α) :
    traverse f (l.map (p,·))=traverse (fun a => f (p,a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,traverse,ih]

theorem partrec_traverse_family {f : P × α → Part β} (hf : Partrec f) :
    Partrec (fun x : P × List α => traverse (fun a => f (x.1,a)) x.2) := by
  have hp : Primrec (fun x : P × List α => x.2.map (x.1,·)) :=
    Primrec.list_map Primrec.snd ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂
  exact ((partrec_traverse hf).comp hp.to_comp).of_eq fun x => traverse_map_parameter f x.1 x.2
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns.Uniform
variable {P C S : Type*} [Primcodable P] [Primcodable C] [Primcodable S]

theorem partrec_action {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × Action C S => Action.partial (fun w => f (x.1,w)) x.2) := by
  have hh : Partrec₂ (fun (x : P × Action C S) (b : List S ⊕ List S) =>
      b.elim (fun w => Part.some (Sum.inr w : Item C S))
        (fun w => (f (x.1,w)).map (Sum.inr (α := C)))) := by
    exact (Partrec.sumCasesOn_right Computable.snd
      (Computable.sumInr.comp Computable.snd).to₂
      (((hf.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)).map
        (Computable.sumInr.comp Computable.snd).to₂).to₂)).to₂
  exact (Partrec.sumCasesOn_right (Action.primrec_code.to_comp.comp Computable.snd)
    (Computable.sumInl.comp Computable.snd).to₂ hh).of_eq fun x => by cases x.2 <;> rfl

theorem partrec_execute {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × List (Action C S) => execute (fun w => f (x.1,w)) x.2) := by
  apply (Effect.partrec_traverse_family (partrec_action (C := C) hf)).of_eq
  intro x
  induction x.2 with
  | nil => rfl
  | cons a l ih => simp only [Effect.traverse,execute,ih]

theorem partrec_partialSource {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × List (Item C S) => partialSource (fun w => f (x.1,w)) x.2) :=
  (partrec_execute hf).comp (Computable.fst.pair (primrec_plan.to_comp.comp Computable.snd))
end FiniteAlgebraicEnvelopes.Compiler.RawRuns.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P] [Primcodable S]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_raw : Primrec (raw (S := S) (Q := Q) blank) := by
  have hp : Primrec (fun w : List S => (⟨[],Surface.Head.raw,
      w.map (Validator.cell blank ∘ Base.anchor),true,true⟩ : Surface.Sector S Γ (Control.Head S Q))) :=
    Scan.Sector.primrec_mk (Primrec.const []) (Primrec.const Surface.Head.raw)
      (Primrec.list_map Primrec.id ((Primrec.dom_finite _).comp Primrec.snd).to₂)
      (Primrec.const true) (Primrec.const true)
  exact Path.Uniform.primrec_encode.comp ((Scan.primrec_literal Primrec.id).comp hp)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_rawLetters : Primrec (rawLetters (S := S) (Γ := Γ) (Q := Q)) := by
  let f : Base S × Tag S Γ → Option S := fun c => match c.1 with | .anchor s => some s | _ => none
  have hp : Primrec (fun a : Letter S Γ Q => match a with
      | .right (.anchor s,_) => some s | _ => none) := by
    exact (Primrec.option_bind Path.Uniform.primrec_right?
      ((Primrec.dom_finite f).comp Primrec.snd).to₂).of_eq fun a => by
        cases a <;> simp only [Option.bind_none, Option.bind_some]
        case right c => cases c with | mk b t => cases b <;> rfl
  exact Primrec.listFilterMap Primrec.id (hp.comp Primrec.snd).to₂

theorem primrec_readRaw : Primrec (readRaw (S := S) (Q := Q) blank) :=
  Primrec.ite (Primrec.eq.comp ((primrec_raw blank).comp primrec_rawLetters) Primrec.id)
    (Primrec.option_some.comp primrec_rawLetters) (Primrec.const none)

theorem primrec_classify : Primrec (classify (S := S) (Q := Q) blank) := by
  exact (Primrec.option_casesOn (primrec_readRaw blank) Primrec.sumInl
    (Primrec.sumInr.comp Primrec.snd).to₂).of_eq fun w => by
      cases h : readRaw blank w <;> simp [classify,h]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_realize : Primrec (realize (S := S) (Q := Q) blank) := by
  exact (Primrec.sumCasesOn Primrec.id Primrec.snd.to₂
    ((primrec_raw blank).comp Primrec.snd).to₂).of_eq fun w => by cases w <;> rfl

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]
theorem primrec_codedTransition : Primrec (fun x : ℕ × Control Q × (Bool×Γ) =>
    (codedMachine A M p x.1).transition x.2.1 x.2.2) := by
  have ht := (primrec_transition A M p).comp
    ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_map ht
    (primrec_commandMk (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂

variable {T : Type*} [Fintype T]

theorem primrec_heads : Primrec (heads (T := T) (Q := Q)) :=
  primrec_controlSupport.comp primrec_support

end

open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

theorem primrec_codedRepresentative : Primrec (codedRepresentative A M p B) := by
  let := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  apply Scan.Uniform.primrec_representative
  · exact primrec_controlBoundary B (codedMachine A M p) (Primrec.const _)
  · exact primrec_controlCell B (codedMachine A M p) (Primrec.const _) (primrec_codedTransition A M p)
  · exact primrec_controlDirection B (codedMachine A M p)
  · exact primrec_heads
  · exact (Compiler.Control.Uniform.primrec_entry B.blank).decide
  · exact (Compiler.Control.Uniform.primrec_success).decide
  · exact Effect.primrec_codeOrder _

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

open Compiler Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]

omit [DecidableEq T] [DecidableEq Q] in
theorem primrec_surfaces : Primrec (surfaces (T := T) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _) (Primrec.list_map primrec_heads
    (primrec_internal.comp Primrec.snd).to₂)

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_letters : Primrec (letters (T := T) (Γ := Γ) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_map primrec_surfaces (Path.Uniform.primrec_head.comp Primrec.snd).to₂)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIFAE.SelfReference
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace Projection
variable {A B : Type*}

variable [Primcodable A] [Primcodable B]
 theorem primrec_left : Primrec (left (A:=A) (B:=B)) := by
  have hh : Primrec (fun a : A ⊕ B => match a with | .inl a => some a | .inr _ => none) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂
      (Primrec.const none).to₂).of_eq (by intro a; cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (hh.comp Primrec.snd).to₂
 theorem primrec_right : Primrec (right (A:=A) (B:=B)) := by
  have hh : Primrec (fun a : A ⊕ B => match a with | .inl _ => none | .inr b => some b) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂
      (Primrec.option_some.comp Primrec.snd).to₂).of_eq (by intro a; cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (hh.comp Primrec.snd).to₂
end Projection

namespace Tested
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec

variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

omit [Fintype Q] [Primcodable T] [Primcodable Γ] in
 theorem primrec_combine : Primrec (combine (T:=T) (Γ:=Γ) (Q:=Q)) := by
  let : DecidablePred (fun q : Class T Γ Q => q.1=([Path.Letter.zero] : List (X T Γ Q))) :=
    fun _ => inferInstance
  have hp : PrimrecPred (fun q : Class T Γ Q => q.1=([Path.Letter.zero] : List (X T Γ Q))) :=
    Primrec.eq.comp Primrec.fst (Primrec.const _)
  exact Primrec.ite hp (Primrec.const none) (Primrec.option_some.comp Primrec.id)

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable T] [Primcodable Γ] in
 theorem primrec_letters : Primrec (letters (T:=T) (Γ:=Γ) (Q:=Q)) :=
  Primrec.list_append.comp (Primrec.list_map ParameterCode.primrec_letters
    (Primrec.sumInl.comp Primrec.snd).to₂) (Primrec.const _)

end Tested
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform

section
variable {P A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]

section Computability
variable [Primcodable P] [Primcodable A] [Primcodable S] [Primcodable Q]
  (code : P → List A → List S) (lt : P → List A → List A → Bool) (z : S)
  (hc : Primrec₂ code) (hl : Primrec (fun x : P × List A × List A => lt x.1 x.2.1 x.2.2))
variable {X : Type*} [Primcodable X]

omit [DecidableEq A] in
include hl in
 theorem primrec_pickStep {p : X → P} {q : X → Option Q} {best : X → List A}
    {v : X → List A × Option Q} (hp : Primrec p) (hq : Primrec q)
    (hb : Primrec best) (hv : Primrec v) :
    Primrec (fun x => pickStep (lt (p x)) (q x) (best x) (v x)) :=
  Primrec.ite ((Primrec.eq.comp (Primrec.snd.comp hv) hq).and
    (Primrec.eq.comp (hl.comp (hp.pair ((Primrec.fst.comp hv).pair hb))) (Primrec.const true)))
    (Primrec.fst.comp hv) hb

omit [DecidableEq A] in
include hl in
 theorem primrec_pick {p : X → P} {q : X → Option Q} {w : X → List A}
    {ps : X → List (List A × Option Q)} (hp : Primrec p) (hq : Primrec q)
    (hw : Primrec w) (hps : Primrec ps) :
    Primrec (fun x => pick (lt (p x)) (ps x) (w x) (q x)) :=
  Primrec.list_foldl hps hw (primrec_pickStep lt hl (hp.comp Primrec.fst)
    (hq.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

omit [DecidableEq A] [DecidableEq S] in
include hc hl in
 theorem primrec_output : Primrec (fun x : P × List (List A × Option Q) × (List A × Option Q) =>
    output (code x.1) (lt x.1) z x.2.1 x.2.2) := by
  have hv : Primrec (fun x : P × List (List A × Option Q) × (List A × Option Q) => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hv) (Primrec.const none))
    (Primrec.const [z]) (hc.comp Primrec.fst (primrec_pick lt hl Primrec.fst
      (Primrec.snd.comp hv) (Primrec.fst.comp hv) (Primrec.fst.comp Primrec.snd)))

omit [DecidableEq A] in
include hc hl in
 theorem primrec_table : Primrec (fun x : P × List (List A × Option Q) => table (code x.1) (lt x.1) z x.2) := by
  apply Primrec.list_flatMap Primrec.snd
  have hp : Primrec (fun x : (P × List (List A × Option Q)) × (List A × Option Q) => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hout := (primrec_output code lt z hc hl).comp
    (hp.pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hcode := hc.comp hp (Primrec.fst.comp Primrec.snd)
  exact (Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])).not.and
    (Primrec.eq.comp hout hcode).not)
    (Primrec.list_cons.comp (hcode.pair hout) (Primrec.const [])) (Primrec.const [])).to₂

omit [DecidableEq A] in
include hc hl in
 theorem partrec_compute {ls : P → List A} (hs : Primrec ls)
    {f : P → List A → Part (Option Q)} (hf : Partrec₂ f) :
    Partrec₂ (fun p => compute (ls p) (code p) (lt p) z (f p)) := by
  have hp : Partrec₂ (fun p w => (f p w).map (w,·)) :=
    (hf.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂
  have hw : Primrec (fun x : P × ℕ => words (ls x.1) x.2) :=
    Uniform.primrec_words.comp (hs.comp Primrec.fst) Primrec.snd
  exact (((Effect.partrec_traverse_parameter hp).comp Computable.fst hw.to_comp).map
    ((primrec_table code lt z hc hl).to_comp.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂).to₂
end Computability

end

variable {P S A B Q R : Type*} [Primcodable S] [Fintype S]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]

section Computability
variable [Primcodable P] [Primcodable A] [Primcodable B] [Primcodable Q] [Primcodable R]
variable (a : Selectors.Markers S) (ls : P → List A) (ms : P → List B)
    (code : P → List A → List S) (code' : P → List B → List S)
    (lt : P → List A → List A → Bool) (lt' : P → List B → List B → Bool)
    (d e : P → ℕ) (f : P → List A → Part (Option Q)) (g : P → List B → Part (Option R))
variable (hls : Primrec ls) (hms : Primrec ms) (hc : Primrec₂ code) (hc' : Primrec₂ code')
    (hlt : Primrec (fun x : P × List A × List A => lt x.1 x.2.1 x.2.2))
    (hlt' : Primrec (fun x : P × List B × List B => lt' x.1 x.2.1 x.2.2))
    (hd : Primrec d) (he : Primrec e) (hf : Partrec₂ f) (hg : Partrec₂ g)
include hls hms hc hc' hlt hlt' hd he hf hg in
omit [DecidableEq A] [DecidableEq B] in
 theorem partrec_bases : Partrec₂ (fun p => bases a.zero (ls p) (ms p) (code p) (code' p)
    (lt p) (lt' p) (d p) (e p) (f p) (g p)) := by
  have h1 : Partrec (fun x : P × ℕ => compute (ls x.1) (code x.1) (lt x.1) a.zero (f x.1) (x.2/d x.1)) :=
    (partrec_compute code lt a.zero hc hlt hls hf).comp Computable.fst
      (Primrec.nat_div.to_comp.comp Computable.snd (hd.to_comp.comp Computable.fst))
  have h2 : Partrec (fun x : (P × ℕ) × List (List S × List S) =>
        compute (ms x.1.1) (code' x.1.1) (lt' x.1.1) a.zero (g x.1.1) (x.1.2/e x.1.1)) :=
    (partrec_compute code' lt' a.zero hc' hlt' hms hg).comp (Computable.fst.comp Computable.fst)
      (Primrec.nat_div.to_comp.comp (Computable.snd.comp Computable.fst)
        (he.to_comp.comp (Computable.fst.comp Computable.fst)))
  exact (h1.bind (h2.map (Primrec.list_append.to_comp.comp
    (Primrec.list_append.to_comp.comp (Computable.const (Base.absorption a.zero))
      (Computable.snd.comp Computable.fst)) Computable.snd).to₂).to₂).to₂

include hls hms hc hc' hlt hlt' hd he hf hg in
omit [DecidableEq A] [DecidableEq B] in
 theorem partrec_tables : Partrec₂ (fun p => tables a (ls p) (ms p) (code p) (code' p)
    (lt p) (lt' p) (d p) (e p) (f p) (g p)) := by
  have hb := partrec_bases a ls ms code code' lt lt' d e f g hls hms hc hc' hlt hlt' hd he hf hg
  exact (hb.map ((Selectors.primrec_process a _ (Selectors.primrec_stages a.zero)).to_comp.comp
    (Computable.snd.pair (Computable.snd.comp Computable.fst))
    (Computable.snd.comp Computable.fst)).to₂).to₂
end Computability

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap.LexBinary
variable {A B S : Type*}

variable [DecidableEq A]

variable [DecidableEq S]

omit [DecidableEq S]
variable [Primcodable A] [Primcodable S]
 theorem primrec_words (a c : S) : Primrec (words a c) := by
  have h (z : S) : Primrec (fun x : ℕ × List (List S) => x.2.map (z::·)) :=
    Primrec.list_map Primrec.snd (Primrec.list_cons.comp (Primrec.const z) Primrec.snd).to₂
  exact (Primrec.nat_rec₁ [[]] (Primrec.list_append.comp (h a) (h c)).to₂).of_eq (by
    intro n; induction n <;> simp_all [words])

 theorem primrec_tail (a c : S) : Primrec (fun x : ℕ × List A × A => tail a c x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD []).comp ((primrec_words a c).comp Primrec.fst)
    (Primrec.list_idxOf.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))

 theorem primrec_encode (b a c : S) : Primrec (fun x : ℕ × List A × List A => encode b a c x.1 x.2.1 x.2.2) := by
  exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.const b) ((primrec_tail a c).comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)))).to₂

end FiniteAlgebraicEnvelopes.Bootstrap.LexBinary

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec

 theorem raw_encode (c : Nat.Partrec.Code) : raw (Encodable.encode c)=WordProgramming.eval c := by
  funext w
  simp [raw]

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] in
 theorem primrec_width : Primrec (width (Γ:=Γ) (Q:=Q) k) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.list_length.comp Tested.primrec_letters) (Primrec.const _)) (Primrec.const 2)

attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigma
omit [Primcodable Γ] in
 theorem primrec_codeT : Primrec₂ (codeT (Γ:=Γ) (Q:=Q) (k:=k)) :=
  (LexBinary.primrec_encode 0 1 2).comp
    ((primrec_width.comp Primrec.fst).pair
      ((Tested.primrec_letters.comp Primrec.fst).pair Primrec.snd))

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] in
 theorem primrec_codeG : Primrec₂ (codeG (Γ:=Γ) (Q:=Q) (k:=k)) :=
  (LexBinary.primrec_encode 3 4 5).comp
    ((primrec_width.comp Primrec.fst).pair ((Primrec.const _).pair Primrec.snd))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]

noncomputable instance dec_relT (n : ℕ) : DecidableRel (relT (Γ:=Γ) (Q:=Q) n) := fun _ _ => Nat.decLt _ _
noncomputable instance dec_relG (k : ℕ) : DecidableRel (relG k) := fun _ _ => Nat.decLt _ _

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end OAI
end

section
-- module Solutions.OAIFAE.MonoidAlgebras
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

end

open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)
local instance instDecidableEqXSigma_5 : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance instDecidableEqLetterSigmaProdBoolState_4 (n : ℕ) : DecidableEq (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance
local instance instDecidableEqFiniteY_4 (n : ℕ) : DecidableEq (FiniteY (Γ:=Γ) (Q:=Q) n) := inferInstance
local instance instFintypeLetterSigmaProdBoolState_2 (n : ℕ) : Fintype (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance

def base (n j : ℕ) : List (List Sigma × List Sigma) :=
  Base.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (wf_relT n) (wf_relG k) (Search.value (finiteTest A M n)) (Search.value (testG s n)) markers.zero j

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

theorem wf_sigma : WellFounded (fun a b : Sigma => a<b) := InvImage.wf Fin.val Nat.lt_wfRel.wf

def groupEval : FreeMonoid (Z k) →* G where
  toFun w := evalWord s w.toList
  map_one' := rfl
  map_mul' u v := WordProblem.evalWord_append s u.toList v.toList

 theorem groupEval_surjective (hs : Subgroup.closure (Set.range s)=⊤) : Function.Surjective (groupEval s) := by
  intro g
  obtain ⟨w,hw⟩ := FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hs g
  refine ⟨FreeMonoid.ofList (FreeGroup.toWord w),?_⟩
  change evalWord s (FreeGroup.toWord w)=g
  rw [WordProblem.evalWord_eq_lift,FreeGroup.mk_toWord]
  exact hw

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

local instance instDecidableEqXSigmaΓFamilyQ : DecidableEq (Tested.X Sigma family.Γ family.Q) := inferInstance

end

open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))
local instance instDecidableEqXSigmaΓFamilyQ_1 : DecidableEq (Tested.X Sigma family.Γ family.Q) := inferInstance

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end

section
-- module Solutions.OAIFAE.Corners
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tensor embeddings and the nonunital corner maps between the two algebras.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

def U : monoid := wordValue [0]
def V : monoid := wordValue [1]
def UI : monoid := wordValue [2]
def VI : monoid := wordValue [3]
def E0 : monoid := wordValue [4]
def E1 : monoid := wordValue [5]
def Eh : monoid := U*E1*UI

@[simp] theorem U_apply (o : Option ℚ) : U.val o=o.map (fun x => x/2) := by
  simpa [U,wordValue,value] using generator_u o
@[simp] theorem V_apply (o : Option ℚ) : V.val o=o.map (fun x => (x+1)/2) := by
  simpa [V,wordValue,value] using generator_v o
@[simp] theorem UI_apply (o : Option ℚ) : UI.val o=o.map (fun x => 2*x) := by
  simpa [UI,wordValue,value] using generator_ui o
@[simp] theorem VI_apply (o : Option ℚ) : VI.val o=o.map (fun x => 2*x-1) := by
  simpa [VI,wordValue,value] using generator_vi o
@[simp] theorem E0_val : E0.val=tail 0 := by
  simpa [E0,wordValue,value] using generator_tail0
@[simp] theorem E1_val : E1.val=tail 1 := by
  simpa [E1,wordValue,value] using generator_tail1

@[simp] theorem U_UI : U*UI=1 := by
  apply Subtype.ext
  funext o
  change U.val (UI.val o)=o
  cases o <;> simp
@[simp] theorem UI_U : UI*U=1 := by
  apply Subtype.ext
  funext o
  change UI.val (U.val o)=o
  cases o <;> simp
  ring
@[simp] theorem V_VI : V*VI=1 := by
  apply Subtype.ext
  funext o
  change V.val (VI.val o)=o
  cases o <;> simp
@[simp] theorem VI_V : VI*V=1 := by
  apply Subtype.ext
  funext o
  change VI.val (V.val o)=o
  cases o <;> simp
  ring

theorem U_tail (r : ℚ) : U.val*tail r*UI.val=tail (r/2) := by
  funext o
  cases o with
  | none =>
    change U.val ((tail r) (UI.val none))=none
    simp [tail]
  | some x =>
    change U.val ((tail r) (UI.val (some x)))=(tail (r/2)) (some x)
    simp only [UI_apply,Option.map_some,tail,Option.bind_some]
    by_cases hr : r≤2*x
    · have hr' : r/2≤x := by linarith
      simp [hr,hr']
    · have hr' : ¬r/2≤x := by linarith
      simp [hr,hr']

theorem V_tail (r : ℚ) : V.val*tail r*VI.val=tail ((r+1)/2) := by
  funext o
  cases o with
  | none =>
    change V.val ((tail r) (VI.val none))=none
    simp [tail]
  | some x =>
    change V.val ((tail r) (VI.val (some x)))=(tail ((r+1)/2)) (some x)
    simp only [VI_apply,Option.map_some,tail,Option.bind_some]
    by_cases hr : r≤2*x-1
    · have hr' : (r+1)/2≤x := by linarith
      simp [hr,hr']
    · have hr' : ¬(r+1)/2≤x := by linarith
      simp [hr,hr']

@[simp] theorem Eh_val : Eh.val=tail (1/2) := by
  exact (congrArg (fun e => U.val*e*UI.val) E1_val).trans (U_tail 1)

@[simp] theorem U_E0_UI : U*E0*UI=E0 := by
  apply Subtype.ext
  change U.val*E0.val*UI.val=E0.val
  rw [E0_val,U_tail]
  norm_num
@[simp] theorem U_E1_UI : U*E1*UI=Eh := rfl
@[simp] theorem V_E0_VI : V*E0*VI=Eh := by
  apply Subtype.ext
  change V.val*E0.val*VI.val=Eh.val
  rw [E0_val,Eh_val,V_tail]
  norm_num
@[simp] theorem V_E1_VI : V*E1*VI=E1 := by
  apply Subtype.ext
  change V.val*E1.val*VI.val=E1.val
  rw [E1_val,V_tail]
  norm_num

 theorem tails_mul {a b c : monoid} {r s : ℚ} (ha : a.val=tail r) (hb : b.val=tail s)
    (hc : c.val=tail (max r s)) : a*b=c := by
  apply Subtype.ext
  change a.val*b.val=c.val
  rw [ha,hb,hc,tail_mul]

@[simp] theorem E0_E0 : E0*E0=E0 := tails_mul E0_val E0_val (by simp)
@[simp] theorem E0_Eh : E0*Eh=Eh := tails_mul E0_val Eh_val (by norm_num)
@[simp] theorem E0_E1 : E0*E1=E1 := tails_mul E0_val E1_val (by norm_num)
@[simp] theorem Eh_E0 : Eh*E0=Eh := tails_mul Eh_val E0_val (by norm_num)
@[simp] theorem Eh_Eh : Eh*Eh=Eh := tails_mul Eh_val Eh_val (by simp)
@[simp] theorem Eh_E1 : Eh*E1=E1 := tails_mul Eh_val E1_val (by norm_num)
@[simp] theorem E1_E0 : E1*E0=E1 := tails_mul E1_val E0_val (by norm_num)
@[simp] theorem E1_Eh : E1*Eh=E1 := tails_mul E1_val Eh_val (by norm_num)
@[simp] theorem E1_E1 : E1*E1=E1 := tails_mul E1_val E1_val (by simp)

end FiniteAlgebraicEnvelopes.PartialAffine

namespace FiniteAlgebraicEnvelopes.PartialAffine.Corner
open MonoidAlgebra
variable (k : Type*) [CommRing k]

def b (a : monoid) : MonoidAlgebra k monoid := single a 1
@[simp] theorem b_mul (a c : monoid) : b k a*b k c=b k (a*c) := by simp [b,single_mul_single]
@[simp] theorem b_one : b k 1=1 := rfl

def q : MonoidAlgebra k monoid := b k E0-b k E1
def q0 : MonoidAlgebra k monoid := b k E0-b k Eh
def q1 : MonoidAlgebra k monoid := b k Eh-b k E1

theorem q_idem : q k*q k=q k := by
  simp only [q,sub_mul,mul_sub,b_mul,E0_E0,E0_E1,E1_E0,E1_E1]
  abel
 theorem q0_idem : q0 k*q0 k=q0 k := by
  simp only [q0,sub_mul,mul_sub,b_mul,E0_E0,E0_Eh,Eh_E0,Eh_Eh]
  abel
 theorem q1_idem : q1 k*q1 k=q1 k := by
  simp only [q1,sub_mul,mul_sub,b_mul,Eh_Eh,Eh_E1,E1_Eh,E1_E1]
  abel
 theorem q0_q1 : q0 k*q1 k=0 := by
  simp only [q0,q1,sub_mul,mul_sub,b_mul,E0_Eh,E0_E1,Eh_Eh,Eh_E1]
  abel
 theorem q1_q0 : q1 k*q0 k=0 := by
  simp only [q0,q1,sub_mul,mul_sub,b_mul,Eh_E0,Eh_Eh,E1_E0,E1_Eh]
  abel
 theorem q0_add_q1 : q0 k+q1 k=q k := by unfold q0 q1 q; abel
 theorem q_q0 : q k*q0 k=q0 k := by rw [←q0_add_q1,add_mul,q0_idem,q1_q0,add_zero]
 theorem q0_q : q0 k*q k=q0 k := by rw [←q0_add_q1,mul_add,q0_idem,q0_q1,add_zero]
 theorem q_q1 : q k*q1 k=q1 k := by rw [←q0_add_q1,add_mul,q0_q1,q1_idem,zero_add]
 theorem q1_q : q1 k*q k=q1 k := by rw [←q0_add_q1,mul_add,q1_q0,q1_idem,zero_add]

def s0 : MonoidAlgebra k monoid := b k U*q k
def s1 : MonoidAlgebra k monoid := b k V*q k
def t0 : MonoidAlgebra k monoid := q k*b k UI
def t1 : MonoidAlgebra k monoid := q k*b k VI

 theorem conjugate0 : b k U*q k*b k UI=q0 k := by
  simp only [q,q0,mul_sub,sub_mul,b_mul,U_E0_UI,U_E1_UI]
 theorem conjugate1 : b k V*q k*b k VI=q1 k := by
  simp only [q,q1,mul_sub,sub_mul,b_mul,V_E0_VI,V_E1_VI]

 theorem t0_s0 : t0 k*s0 k=q k := by
  unfold t0 s0
  calc
    _=q k*(b k UI*b k U)*q k := by simp only [mul_assoc]
    _=q k := by rw [b_mul,UI_U,b_one,mul_one,q_idem]
 theorem t1_s1 : t1 k*s1 k=q k := by
  unfold t1 s1
  calc
    _=q k*(b k VI*b k V)*q k := by simp only [mul_assoc]
    _=q k := by rw [b_mul,VI_V,b_one,mul_one,q_idem]
 theorem s0_t0 : s0 k*t0 k=q0 k := by
  unfold s0 t0
  rw [mul_assoc,←mul_assoc (q k),q_idem,←mul_assoc,conjugate0]
 theorem s1_t1 : s1 k*t1 k=q1 k := by
  unfold s1 t1
  rw [mul_assoc,←mul_assoc (q k),q_idem,←mul_assoc,conjugate1]

 theorem s0_q : s0 k*q k=s0 k := by unfold s0; rw [mul_assoc,q_idem]
 theorem s1_q : s1 k*q k=s1 k := by unfold s1; rw [mul_assoc,q_idem]
 theorem q_t0 : q k*t0 k=t0 k := by unfold t0; rw [←mul_assoc,q_idem]
 theorem q_t1 : q k*t1 k=t1 k := by unfold t1; rw [←mul_assoc,q_idem]
 theorem q0_s0 : q0 k*s0 k=s0 k := by rw [←s0_t0,mul_assoc,t0_s0,s0_q]
 theorem q1_s1 : q1 k*s1 k=s1 k := by rw [←s1_t1,mul_assoc,t1_s1,s1_q]
 theorem t0_q0 : t0 k*q0 k=t0 k := by rw [←s0_t0,←mul_assoc,t0_s0,q_t0]
 theorem t1_q1 : t1 k*q1 k=t1 k := by rw [←s1_t1,←mul_assoc,t1_s1,q_t1]
 theorem q_s0 : q k*s0 k=s0 k := by nth_rw 1 [←q0_s0 k]; rw [←mul_assoc,q_q0,q0_s0]
 theorem q_s1 : q k*s1 k=s1 k := by nth_rw 1 [←q1_s1 k]; rw [←mul_assoc,q_q1,q1_s1]
 theorem t0_q : t0 k*q k=t0 k := by nth_rw 1 [←t0_q0 k]; rw [mul_assoc,q0_q,t0_q0]
 theorem t1_q : t1 k*q k=t1 k := by nth_rw 1 [←t1_q1 k]; rw [mul_assoc,q1_q,t1_q1]
 theorem t0_s1 : t0 k*s1 k=0 := by
  nth_rw 1 [←t0_q0 k,←q1_s1 k]
  calc
    _=t0 k*(q0 k*q1 k)*s1 k := by simp only [mul_assoc]
    _=0 := by rw [q0_q1,mul_zero,zero_mul]
 theorem t1_s0 : t1 k*s0 k=0 := by
  nth_rw 1 [←t1_q1 k,←q0_s0 k]
  calc
    _=t1 k*(q1 k*q0 k)*s0 k := by simp only [mul_assoc]
    _=0 := by rw [q1_q0,mul_zero,zero_mul]
 theorem s0_t0_add_s1_t1 : s0 k*t0 k+s1 k*t1 k=q k := by rw [s0_t0,s1_t1,q0_add_q1]

end FiniteAlgebraicEnvelopes.PartialAffine.Corner

section
namespace FiniteAlgebraicEnvelopes.PartialAffine.Corner
open scoped TensorProduct
variable (k B : Type*) [CommRing k] [Ring B] [Algebra k B]

def cornerTensor : B →ₙₐ[k] B ⊗[k] MonoidAlgebra k monoid where
  toFun x := x ⊗ₜ[k] q k
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' x y := TensorProduct.add_tmul _ _ _
  map_mul' x y := by rw [Algebra.TensorProduct.tmul_mul_tmul,q_idem]
  map_smul' r x := TensorProduct.smul_tmul' _ _ _

def coefficient0 : MonoidAlgebra k monoid →ₗ[k] k where
  toFun f := f.coeff E0
  map_add' f g := by simp
  map_smul' r f := by simp

def cornerRetract : B ⊗[k] MonoidAlgebra k monoid →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap.comp (TensorProduct.map (LinearMap.id : B →ₗ[k] B) (coefficient0 k))

end FiniteAlgebraicEnvelopes.PartialAffine.Corner

end

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def coefficient (f : A →ₙₐ[k] A) : Enveloping.Coeff k A →ₙₐ[k] Enveloping.Coeff k A := map f (op f)

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

def act (r : Coeff k A) (a : A) : A := representation k A r a

@[simp] theorem act_zero (a : A) : act k A 0 a=0 := by simp [act]
@[simp] theorem act_tmul (a b c : A) : act k A (a⊗ₜ[k] MulOpposite.op b) c=a*c*b := tmul_smul k A a b c
end FiniteAlgebraicEnvelopes.Enveloping

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open scoped TensorProduct
variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def actingLinear (f : A →ₙₐ[k] A) (a : A) : Enveloping.Coeff k A →ₗ[k] A :=
  ((LinearMap.applyₗ (R:=k) (M₂:=A) a).comp (Enveloping.representation k A).toLinearMap).comp (linear (coefficient f))

@[simp] theorem actingLinear_apply (f : A →ₙₐ[k] A) (a : A) (r : Enveloping.Coeff k A) :
    actingLinear f a r=Enveloping.act k A (coefficient f r) a := rfl

@[simp] theorem actingLinear_tmul (f : A →ₙₐ[k] A) (a b c : A) :
    actingLinear f c (a⊗ₜ[k] MulOpposite.op b)=f a*c*f b := Enveloping.act_tmul k A _ _ _
end FiniteAlgebraicEnvelopes.NonunitalTensor

end

end OAI
end

section
-- module Solutions.OAIFAE.SteinbergLimits
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Steinberg sequential limits, annihilated kernels, and injective torus maps.
-/

section

namespace FiniteAlgebraicEnvelopes.Steinberg
variable {R : Type*} [Ring R]

abbrev ElementaryGroup (R : Type*) [Ring R] :=
  (matrixMap : Group (Fin 6) R →* (Matrix (Fin 6) (Fin 6) R)ˣ).range

def elementaryQuotient : Group (Fin 6) R →* ElementaryGroup R := matrixMap.rangeRestrict

theorem elementaryQuotient_surjective : Function.Surjective (elementaryQuotient (R:=R)) :=
  MonoidHom.rangeRestrict_surjective _

def elementaryTransition (ψ : R →ₙ+* R) : Monoid.End (ElementaryGroup R) :=
  ((correctedUnits ψ).comp (ElementaryGroup R).subtype).codRestrict (ElementaryGroup R) (by
    intro a
    obtain ⟨z,hz⟩ := a.property
    refine ⟨coefficientMap ψ z,?_⟩
    rw [matrixMap_coefficientMap,hz]
    rfl)

theorem elementary_natural (ψ : R →ₙ+* R) (z : Group (Fin 6) R) :
    elementaryQuotient (coefficientMap ψ z)=elementaryTransition ψ (elementaryQuotient z) := by
  apply Subtype.ext
  exact matrixMap_coefficientMap ψ z

end FiniteAlgebraicEnvelopes.Steinberg
end

namespace FiniteAlgebraicEnvelopes.Steinberg

section
open scoped commutatorElement
variable {R : Type*} [Ring R]

/-- Ring coefficients whose root elements belong to a subgroup form a subring.
The rank-six third index is used in the multiplication step. -/
def coefficientSubring (H : Subgroup (Group (Fin 6) R))
    (h1 : ∀ i j (hij : i≠j), root i j hij (1:R)∈H) : Subring R where
  carrier := {r | ∀ i j (hij : i≠j), root i j hij r∈H}
  zero_mem' := by intro i j hij; rw [root_zero]; exact H.one_mem
  one_mem' := h1
  add_mem' := by
    intro r s hr hs i j hij
    rw [←root_add]
    exact H.mul_mem (hr i j hij) (hs i j hij)
  neg_mem' := by
    intro r hr i j hij
    rw [root_neg]
    exact H.inv_mem (hr i j hij)
  mul_mem' := by
    intro r s hr hs i j hij
    obtain ⟨k,hki,hkj⟩ := freshThird i j
    rw [←root_chain i k j hki.symm hkj hij]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hr i k hki.symm) (hs k j hkj))
      (H.inv_mem (hr i k hki.symm))) (H.inv_mem (hs k j hkj))

def rootGenerators (S : Set R) : Set (Group (Fin 6) R) :=
  (fun p : RootIndex × R => root p.1.1.1 p.1.1.2 p.1.2 p.2) '' (Set.univ ×ˢ insert 1 S)

end

open scoped commutatorElement
variable {R : Type*} [Ring R]

variable (r : R → R → Prop)
def ringRelators : Set (Group (Fin 6) R) :=
  {z | ∃ (i j : Fin 6) (hij : i≠j) (a b : R), r a b ∧ z=root i j hij a*(root i j hij b)⁻¹}

def ringKernel : Subgroup (Group (Fin 6) R) := Subgroup.normalClosure (ringRelators r)
instance instNormalGroupFinOfNatNatRingKernel : (ringKernel r).Normal := Subgroup.normalClosure_normal
abbrev RingQuotientGroup := Group (Fin 6) R ⧸ ringKernel r

def quotientRoot (i j : Fin 6) (hij : i≠j) (a : R) : RingQuotientGroup r :=
  QuotientGroup.mk' (ringKernel r) (root i j hij a)

@[simp] theorem quotientRoot_add (i j : Fin 6) (hij : i≠j) (a b : R) :
    quotientRoot r i j hij a * quotientRoot r i j hij b=quotientRoot r i j hij (a+b) := by
  rw [quotientRoot,quotientRoot,←map_mul,root_add]
  rfl

theorem quotientRoot_chain (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    ⁅quotientRoot r i j hij a,quotientRoot r j k hjk b⁆=quotientRoot r i k hik (a*b) := by
  simp only [quotientRoot,←map_commutatorElement]
  rw [root_chain i j k hij hjk hik]

theorem quotientRoot_rel {a b : R} (hr : r a b) (i j : Fin 6) (hij : i≠j) :
    quotientRoot r i j hij a=quotientRoot r i j hij b := by
  apply mul_inv_eq_one.mp
  change QuotientGroup.mk' (ringKernel r) (root i j hij a)*
    (QuotientGroup.mk' (ringKernel r) (root i j hij b))⁻¹=1
  rw [←map_inv,←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_normalClosure ⟨i,j,hij,a,b,hr,rfl⟩

theorem quotientRoot_congr {a b : R} (hr : RingQuot.Rel r a b) :
    ∀ (i j : Fin 6) (hij : i≠j), quotientRoot r i j hij a=quotientRoot r i j hij b := by
  induction hr with
  | of hr => exact quotientRoot_rel r hr
  | add_left hr ih =>
    intro i j hij
    rw [←quotientRoot_add,←quotientRoot_add,ih i j hij]
  | mul_left hr ih =>
    intro i j hij
    obtain ⟨k,hki,hkj⟩ := thirdIndex i j
    rw [←quotientRoot_chain r i k j hki.symm hkj hij,
      ←quotientRoot_chain r i k j hki.symm hkj hij,ih i k hki.symm]
  | mul_right hr ih =>
    intro i j hij
    obtain ⟨k,hki,hkj⟩ := thirdIndex i j
    rw [←quotientRoot_chain r i k j hki.symm hkj hij,
      ←quotientRoot_chain r i k j hki.symm hkj hij,ih k j hkj]

def ringQuotRoot (i j : Fin 6) (hij : i≠j) (a : RingQuot r) : RingQuotientGroup r :=
  Quot.lift (quotientRoot r i j hij) (fun _ _ h => quotientRoot_congr r h i j hij) a.toQuot

@[simp] theorem ringQuotRoot_mk (i j : Fin 6) (hij : i≠j) (a : R) :
    ringQuotRoot r i j hij (RingQuot.mkRingHom r a)=quotientRoot r i j hij a := by
  rw [RingQuot.mkRingHom_def]
  rfl

theorem ringQuotRoot_add (i j : Fin 6) (hij : i≠j) (a b : RingQuot r) :
    ringQuotRoot r i j hij a * ringQuotRoot r i j hij b=ringQuotRoot r i j hij (a+b) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  obtain ⟨b,rfl⟩ := RingQuot.mkRingHom_surjective r b
  rw [←map_add,ringQuotRoot_mk,ringQuotRoot_mk,ringQuotRoot_mk,quotientRoot_add]

theorem ringQuotRoot_chain (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : RingQuot r) :
    ⁅ringQuotRoot r i j hij a,ringQuotRoot r j k hjk b⁆=ringQuotRoot r i k hik (a*b) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  obtain ⟨b,rfl⟩ := RingQuot.mkRingHom_surjective r b
  rw [←map_mul,ringQuotRoot_mk,ringQuotRoot_mk,ringQuotRoot_mk,quotientRoot_chain]

theorem ringQuotRoot_distant (i j k l : Fin 6) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) (a b : RingQuot r) :
    ⁅ringQuotRoot r i j hij a,ringQuotRoot r k l hkl b⁆=1 := by
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  obtain ⟨b,rfl⟩ := RingQuot.mkRingHom_surjective r b
  rw [ringQuotRoot_mk,ringQuotRoot_mk]
  exact ((root_distant i j k l hij hkl hil hjk a b).map (QuotientGroup.mk' (ringKernel r))).commutator_eq

def quotientBackward : Group (Fin 6) (RingQuot r) →* RingQuotientGroup r :=
  PresentedGroup.toGroup (f:=fun z : Generator (Fin 6) (RingQuot r) =>
    ringQuotRoot r z.1.1.1 z.1.1.2 z.1.2 z.2) (by
      intro w hw
      cases hw with
      | additive i j hij a b =>
        simp only [map_mul,map_inv,freeRoot,FreeGroup.lift_apply_of]
        rw [ringQuotRoot_add,mul_inv_cancel]
      | chain i j k hij hjk hik a b =>
        simp only [map_mul,map_inv,map_commutatorElement,freeRoot,FreeGroup.lift_apply_of]
        rw [ringQuotRoot_chain r i j k hij hjk hik,mul_inv_cancel]
      | distant i j k l hij hkl hil hjk a b =>
        simp only [map_commutatorElement,freeRoot,FreeGroup.lift_apply_of]
        exact ringQuotRoot_distant r i j k l hij hkl hil hjk a b)

@[simp] theorem quotientBackward_root (i j : Fin 6) (hij : i≠j) (a : RingQuot r) :
    quotientBackward r (root i j hij a)=ringQuotRoot r i j hij a := PresentedGroup.toGroup.of _

def quotientForward : RingQuotientGroup r →* Group (Fin 6) (RingQuot r) :=
  QuotientGroup.lift (ringKernel r) (coefficientMap (RingQuot.mkRingHom r).toNonUnitalRingHom) (by
    apply Subgroup.normalClosure_le_normal
    rintro z ⟨i,j,hij,a,b,hab,rfl⟩
    change coefficientMap _ (root i j hij a*(root i j hij b)⁻¹)=1
    rw [map_mul,map_inv,coefficientMap_root,coefficientMap_root]
    change root i j hij (RingQuot.mkRingHom r a)*(root i j hij (RingQuot.mkRingHom r b))⁻¹=1
    rw [RingQuot.mkRingHom_rel hab,mul_inv_cancel])

@[simp] theorem quotientForward_quotientRoot (i j : Fin 6) (hij : i≠j) (a : R) :
    quotientForward r (quotientRoot r i j hij a)=root i j hij (RingQuot.mkRingHom r a) :=
  coefficientMap_root _ _ _ _ _

theorem quotientForward_backward : (quotientForward r).comp (quotientBackward r)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
  obtain ⟨a,rfl⟩ := RingQuot.mkRingHom_surjective r a
  change quotientForward r (quotientBackward r (root i j hij (RingQuot.mkRingHom r a)))=_
  rw [quotientBackward_root,ringQuotRoot_mk,quotientForward_quotientRoot]
  rfl

theorem quotientBackward_forward : (quotientBackward r).comp (quotientForward r)=MonoidHom.id _ := by
  apply MonoidHom.cancel_right (QuotientGroup.mk'_surjective (ringKernel r)) |>.mp
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
  change quotientBackward r (quotientForward r (quotientRoot r i j hij a))=quotientRoot r i j hij a
  rw [quotientForward_quotientRoot,quotientBackward_root,ringQuotRoot_mk]

def ringQuotEquivalence : RingQuotientGroup r ≃* Group (Fin 6) (RingQuot r) :=
  { quotientForward r with
    invFun := quotientBackward r
    left_inv := DFunLike.congr_fun (quotientBackward_forward r)
    right_inv := DFunLike.congr_fun (quotientForward_backward r) }

end FiniteAlgebraicEnvelopes.Steinberg

end

end OAI
end

section
-- module Solutions.OAIFAE.AlgebraPresentations
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentations of tensor, opposite, contracted, unitized, and coefficient algebras.
-/

namespace FiniteAlgebraicEnvelopes.Steinberg
variable {ι : Type*} {R S : Type*} [Ring R] [Ring S]

def coefficientEquiv (e : R ≃+* S) : Group ι R ≃* Group ι S :=
  { coefficientMap e.toRingHom.toNonUnitalRingHom with
    invFun := coefficientMap e.symm.toRingHom.toNonUnitalRingHom
    left_inv := by
      have he : (coefficientMap e.symm.toRingHom.toNonUnitalRingHom).comp
          (coefficientMap e.toRingHom.toNonUnitalRingHom)=MonoidHom.id (Group ι R) := by
        apply PresentedGroup.ext
        rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
        change coefficientMap _ (coefficientMap _ (root i j hij a))=root i j hij a
        simp only [coefficientMap_root]
        change root i j hij (e.symm (e a))=root i j hij a
        rw [e.symm_apply_apply]
      exact DFunLike.congr_fun he
    right_inv := by
      have he : (coefficientMap e.toRingHom.toNonUnitalRingHom).comp
          (coefficientMap e.symm.toRingHom.toNonUnitalRingHom)=MonoidHom.id (Group ι S) := by
        apply PresentedGroup.ext
        rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
        change coefficientMap _ (coefficientMap _ (root i j hij a))=root i j hij a
        simp only [coefficientMap_root]
        change root i j hij (e (e.symm a))=root i j hij a
        rw [e.apply_symm_apply]
      exact DFunLike.congr_fun he }

end FiniteAlgebraicEnvelopes.Steinberg

end

end OAI
end

section
-- module Solutions.OAIFAE.AffineModules
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Affine module presentations, stabilized actions, and finite stabilizers.
-/

namespace FiniteAlgebraicEnvelopes.MatrixModule
open scoped BigOperators
variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

/-- In particular the literal Steinberg action depends only on its elementary matrix. -/
theorem steinberg_action :
    (unitsAction (V:=V)).comp (Steinberg.matrixMap (ι:=Fin 6) (R:=R))=AffineAction.action := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨a,b⟩,hab⟩,r⟩
  change unitsAction (Steinberg.matrixMap (Steinberg.root a b hab r))=AffineAction.action (Steinberg.root a b hab r)
  rw [Steinberg.matrixMap_root,AffineAction.action_root]
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  change applyMatrix (1+Matrix.single a b r) v.toAdd=(AffineAction.elementary a b hab r v).toAdd
  rw [applyMatrix_add,applyMatrix_one,applyMatrix_single]
  exact (AffineAction.elementary_column a b hab r v.toAdd).symm

end FiniteAlgebraicEnvelopes.MatrixModule

section
namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

def elementaryAction : Steinberg.ElementaryGroup R →* MulAut (Multiplicative (Fin 6 → V)) :=
  (unitsAction (V:=V)).comp (Steinberg.ElementaryGroup R).subtype

@[simp] theorem elementaryAction_quotient (x : Steinberg.Group (Fin 6) R) :
    elementaryAction (V:=V) (Steinberg.elementaryQuotient x)=AffineAction.action x :=
  DFunLike.congr_fun (steinberg_action (R:=R) (V:=V)) x
end FiniteAlgebraicEnvelopes.MatrixModule

end

namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V W : Type*} [Ring R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]

theorem columnEquiv_action (e : V ≃ₗ[R] W) (x : Steinberg.Group (Fin 6) R)
    (v : Multiplicative (Fin 6 → V)) :
    columnEquiv e (AffineAction.action x v)=AffineAction.action x (columnEquiv e v) := by
  rw [←elementaryAction_quotient,←elementaryAction_quotient]
  apply Multiplicative.toAdd.injective
  funext i
  change e (∑ j, (Steinberg.matrixMap x).val i j • v.toAdd j)=
    ∑ j, (Steinberg.matrixMap x).val i j • e (v.toAdd j)
  simp

def affineEquiv (e : V ≃ₗ[R] W) : AffineAction.Group (R:=R) (V:=V) ≃* AffineAction.Group (R:=R) (V:=W) :=
  SemidirectProduct.congr (columnEquiv e) (MulEquiv.refl _) (by
    intro x
    apply MulEquiv.ext
    intro v
    exact columnEquiv_action e x v)

end FiniteAlgebraicEnvelopes.MatrixModule

end

end OAI
end

section
-- module Solutions.OAIFAE.SteinbergPresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite free-algebra Steinberg presentations and transport to finitely presented algebras.
-/

namespace FiniteAlgebraicEnvelopes.SteinbergFiniteFree

section
open scoped commutatorElement
open SmallSystem
variable {A Q Q' : Type*} [Group Q] [Group Q']
variable (S : SmallSystem A Q) (T : SmallSystem A Q') (f : Q →* Q')
variable (hf : ∀ i j a, f (S.small i j a)=T.small i j a)

variable (A : Type*)
def polynomialBackward : Steinberg.Group (Fin 6) (Polynomial A) →* Presentation A :=
  PresentedGroup.toGroup (f:=fun z : Steinberg.Generator (Fin 6) (Polynomial A) =>
    (presentSystem A).polynomial z.2 z.1.1.1 z.1.1.2) (by
    intro w hw
    cases hw with
    | additive i j hij a b =>
      simp only [map_mul,map_inv,Steinberg.freeRoot,FreeGroup.lift_apply_of]
      rw [←SmallSystem.polynomial_add,mul_inv_cancel]
    | chain i j k hij hjk hik a b =>
      simp only [map_mul,map_inv,map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
      rw [SmallSystem.polynomial_chain _ a b i j k hij hjk hik,mul_inv_cancel]
    | distant i j k l hij hkl hil hjk a b =>
      simp only [map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
      exact (SmallSystem.polynomial_distant _ a b i j k l hil hjk).commutator_eq)

@[simp] lemma polynomialBackward_root (i j : Fin 6) (hij : i≠j) (p : Polynomial A) :
    polynomialBackward A (Steinberg.root i j hij p)=(presentSystem A).polynomial p i j :=
  PresentedGroup.toGroup.of _

end

open scoped commutatorElement
open SmallSystem
variable (A : Type*)

def actualSmall (i j : Fin 6) (a : Option A) : Steinberg.Group (Fin 6) (Polynomial A) :=
  if hij : i=j then 1 else Steinberg.root i j hij (MonoidAlgebra.single (FreeMonoid.ofList a.toList) 1)

@[simp] lemma actualSmall_diagonal (i : Fin 6) (a : Option A) : actualSmall A i i a=1 := by simp [actualSmall]
lemma actualSmall_off (i j : Fin 6) (hij : i≠j) (a : Option A) :
    actualSmall A i j a=Steinberg.root i j hij (MonoidAlgebra.single (FreeMonoid.ofList a.toList) 1) := by
  simp [actualSmall,hij]

lemma actualSmall_square (i j : Fin 6) (a : Option A) : actualSmall A i j a*actualSmall A i j a=1 := by
  by_cases hij : i=j
  · subst j; simp
  · rw [actualSmall_off A i j hij a,Steinberg.root_add,←MonoidAlgebra.single_add,show (1 : ZMod 2)+1=0 from by decide,
      MonoidAlgebra.single_zero,Steinberg.root_zero]

lemma actualSmall_distant (i j k l : Fin 6) (a b : Option A) (hil : i≠l) (hjk : j≠k) :
    Commute (actualSmall A i j a) (actualSmall A k l b) := by
  by_cases hij : i=j
  · subst j; simp
  by_cases hkl : k=l
  · subst l; simp
  rw [actualSmall_off A i j hij a,actualSmall_off A k l hkl b]
  exact Steinberg.root_distant i j k l hij hkl hil hjk _ _

lemma actualSmall_unit_left (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅actualSmall A i j none,actualSmall A j k a⁆=actualSmall A i k a := by
  rw [actualSmall_off A i j hij,actualSmall_off A j k hjk,actualSmall_off A i k hik,
    Steinberg.root_chain i j k hij hjk hik]
  simp only [Option.toList_none,FreeMonoid.ofList_nil,←MonoidAlgebra.one_def,one_mul]

lemma actualSmall_unit_right (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅actualSmall A i j a,actualSmall A j k none⁆=actualSmall A i k a := by
  rw [actualSmall_off A i j hij,actualSmall_off A j k hjk,actualSmall_off A i k hik,
    Steinberg.root_chain i j k hij hjk hik]
  simp only [Option.toList_none,FreeMonoid.ofList_nil,←MonoidAlgebra.one_def,mul_one]

def actualSystem : SmallSystem A (Steinberg.Group (Fin 6) (Polynomial A)) where
  small := actualSmall A
  diagonal := actualSmall_diagonal A
  square := actualSmall_square A
  distant := actualSmall_distant A
  unit_left := actualSmall_unit_left A
  unit_right := actualSmall_unit_right A

lemma actual_word (w : List A) (i j : Fin 6) (hij : i≠j) :
    (actualSystem A).word w i j=Steinberg.root i j hij (MonoidAlgebra.single (FreeMonoid.ofList w) 1) := by
  induction w generalizing i j with
  | nil => exact actualSmall_off A i j hij none
  | cons a w ih =>
    cases w with
    | nil => exact actualSmall_off A i j hij (some a)
    | cons b w =>
      have hmi := middle_ne_left i j
      have hmj := middle_ne_right i j
      rw [SmallSystem.word_cons _ (by simp) a i j hij]
      change ⁅actualSmall A i (middle i j) (some a),_⁆=_
      rw [actualSmall_off A i (middle i j) (Ne.symm hmi),ih _ j hmj,
        Steinberg.root_chain i (middle i j) j (Ne.symm hmi) hmj hij,
        MonoidAlgebra.single_mul_single,one_mul]
      rfl

lemma actual_polynomial (p : Polynomial A) (i j : Fin 6) (hij : i≠j) :
    (actualSystem A).polynomial p i j=Steinberg.root i j hij p := by
  apply polynomial_induction (fun p => (actualSystem A).polynomial p i j=Steinberg.root i j hij p)
  · simp
  · intro w
    rw [SmallSystem.polynomial_single,actual_word A _ i j hij,FreeMonoid.ofList_toList]
  · intro p q hp hq
    rw [SmallSystem.polynomial_add,hp,hq,Steinberg.root_add]

def polynomialForward : Presentation A →* Steinberg.Group (Fin 6) (Polynomial A) :=
  (actualSystem A).fromPresentation

lemma polynomial_forward_backward :
    (polynomialForward A).comp (polynomialBackward A)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i,j⟩,hij⟩,p⟩
  change polynomialForward A (polynomialBackward A (Steinberg.root i j hij p))=Steinberg.root i j hij p
  rw [polynomialBackward_root]
  rw [SmallSystem.map_polynomial (presentSystem A) (actualSystem A) (polynomialForward A)
    (fun i j a => (actualSystem A).fromPresentation_small i j a),actual_polynomial A p i j hij]

lemma polynomial_backward_forward :
    (polynomialBackward A).comp (polynomialForward A)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨⟨i,j⟩,a⟩
  change polynomialBackward A (polynomialForward A (presentSmall A i j a))=presentSmall A i j a
  change polynomialBackward A ((actualSystem A).fromPresentation (presentSmall A i j a))=_
  rw [SmallSystem.fromPresentation_small]
  change polynomialBackward A (actualSmall A i j a)=_
  by_cases hij : i=j
  · subst j; simp only [actualSmall_diagonal,map_one,present_diagonal]
  · rw [actualSmall_off A i j hij,polynomialBackward_root,SmallSystem.polynomial_single]
    simp only [FreeMonoid.toList_ofList,SmallSystem.word_option]
    rfl

def polynomialEquivalence : Presentation A ≃* Steinberg.Group (Fin 6) (Polynomial A) :=
  { polynomialForward A with
    invFun := polynomialBackward A
    left_inv := DFunLike.congr_fun (polynomial_backward_forward A)
    right_inv := DFunLike.congr_fun (polynomial_forward_backward A) }

instance polynomial_finitelyPresented [Finite A] : Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (Polynomial A)) :=
  Group.IsFinitelyPresented.equiv (polynomialEquivalence A)

/-- A finite rank-six presentation for the noncommutative free algebra over F₂.
All long-word and additive Steinberg relations follow from the finite small-root relations. -/
instance freeAlgebra_finitelyPresented [Finite A] :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (FreeAlgebra (ZMod 2) A)) :=
  Group.IsFinitelyPresented.equiv (Steinberg.coefficientEquiv
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R:=ZMod 2) (X:=A)).symm.toRingEquiv)

end FiniteAlgebraicEnvelopes.SteinbergFiniteFree

end

end OAI
end

section
-- module Solutions.OAIFAE.ActionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Full finitely presented faithful two-transitive action envelope and type-(A) applications.
-/

namespace FiniteAlgebraicEnvelopes.Steinberg
open scoped commutatorElement
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def weylUnit (p q : ι) (hpq : p≠q) (u : Rˣ) : Group ι R :=
  root p q hpq (u:R)*root q p hpq.symm (-(↑(u⁻¹):R))*root p q hpq (u:R)

theorem weylUnit_matrix (p q : ι) (hpq : p≠q) (u : Rˣ) :
    (matrixMap (weylUnit p q hpq u)).val=1-Matrix.single p p (1:R)-Matrix.single q q (1:R)+
      Matrix.single p q (u:R)-Matrix.single q p (↑(u⁻¹):R) := by
  simp only [weylUnit,map_mul,Units.val_mul,matrixMap_root,elementary_val]
  simp only [add_mul,mul_add,one_mul,mul_one,Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hpq.symm,
    mul_neg,neg_mul,Units.mul_inv,Units.inv_mul,←Matrix.single_neg,add_zero]
  abel

def balancedUnit (p q : ι) (hpq : p≠q) (u : Rˣ) : Group ι R :=
  weylUnit p q hpq u*weylUnit p q hpq (-1)

theorem balancedUnit_matrix (p q : ι) (hpq : p≠q) (u : Rˣ) :
    matrixMap (balancedUnit p q hpq u)=diagonalUnits (fun i => if i=p then u else if i=q then u⁻¹ else 1) := by
  apply Units.ext
  rw [balancedUnit,map_mul,Units.val_mul,weylUnit_matrix,weylUnit_matrix,diagonalUnits_val]
  simp only [Units.val_neg,Units.val_one,inv_neg,inv_one]
  simp only [add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,
    Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne _ _ _ _ hpq,
    Matrix.single_mul_single_of_ne _ _ _ _ hpq.symm,
    mul_neg,←Matrix.single_neg,add_zero]
  ext i j
  by_cases hip : i=p <;> by_cases hiq : i=q <;> by_cases hij : i=j
  all_goals subst_vars
  all_goals simp_all [Matrix.single,Matrix.diagonal,eq_comm]

theorem balancedUnit_commutator (p q r : ι) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (a b : Rˣ) :
    ⁅matrixMap (balancedUnit p q hpq a),matrixMap (balancedUnit p r hpr b)⁆=
      singleDiagonal p ⁅a,b⁆ := by
  rw [balancedUnit_matrix,balancedUnit_matrix,←map_commutatorElement]
  change diagonalUnits _=diagonalUnits _
  congr 1
  funext i
  by_cases hip : i=p <;> by_cases hiq : i=q <;> by_cases hir : i=r
  all_goals simp_all [commutatorElement_def,eq_comm]

theorem singleDiagonal_commutator_mem (p q r : ι) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (a b : Rˣ) :
    singleDiagonal p ⁅a,b⁆ ∈ (matrixMap : Group ι R →* (Matrix ι ι R)ˣ).range := by
  refine ⟨⁅balancedUnit p q hpq a,balancedUnit p r hpr b⁆,?_⟩
  rw [map_commutatorElement,balancedUnit_commutator p q r hpq hpr hqr]

variable {G : Type*} [_root_.Group G]

def elementaryEmbedding (f : G×G →* Rˣ) (b : Rˣ)
    (hc : ∀ g : G, ⁅f (g,g),b⁆=f (g,1)) :
    G →* (matrixMap : Group (Fin 6) R →* (Matrix (Fin 6) (Fin 6) R)ˣ).range :=
  (inputDiagonal f).codRestrict _ (by
    intro g
    change singleDiagonal (0:Fin 6) (f (g,1)) ∈ _
    rw [←hc g]
    exact singleDiagonal_commutator_mem 0 1 2 (by decide) (by decide) (by decide) _ _)

end FiniteAlgebraicEnvelopes.Steinberg

end

end OAI
end

section
-- module Solutions.OAIFAE.BinaryCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Binary combs, folds, permutations, and coherent exchanges.
-/

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory

section
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma combSwap_square {n i : ℕ} (hi : i<n) : combSwap d q n i * combSwap d q n i=1 := by
  rw [combSwap,ite_eq_left hi]
  split_ifs <;> rw [← map_mul]
  · rw [q.square,map_one]
  · rw [combHead_square,map_one]

lemma combSwap_distant {n i j : ℕ} (hij : i+1<j) (hj : j<n) :
    Commute (combSwap d q n i) (combSwap d q n j) := by
  rw [combSwap_internal d q (by omega),combSwap,ite_eq_left hj]
  let z := if j+1=n then q.c else combHead d q
  change Commute (rightPower d i (combHead d q)) (rightPower d j z)
  have hn : j=i+(2+(j-i-2)) := by omega
  rw [hn,rightPower_add,show 2+(j-i-2)=(j-i-2)+2 by omega,
    rightPower_succ,rightPower_succ]
  exact (combHead_distant d q (rightPower d (j-i-2) z)).map (rightPower d i)

lemma combSwap_relations (n : ℕ) : Adjacent.Relations (combSwap d q n) n :=
  ⟨fun _ hi => combSwap_square d q hi,
   fun _ hi => combSwap_braid d q hi,
   fun _ _ hij hj => combSwap_distant d q hij hj⟩

/-- The literal symmetric-group action on every nonempty right comb. -/
def combPermutation (n : ℕ) : Equiv.Perm (Fin (n+1)) →* H :=
  Adjacent.permutationLift (combSwap_relations d q n)

@[simp] lemma combPermutation_swap (n : ℕ) (i : Fin n) :
    combPermutation d q n (Equiv.swap i.castSucc i.succ) = combSwap d q n i :=
  Adjacent.permutationLift_swap _ i

end

section
universe u
variable {H : Type u} [Group H] (d : Data H)

/-- Flatten `(comb (m+1), comb (n+1))` to the right comb. As every nonempty
object is positive, the value only depends on the size of the left block. -/
def merge : ℕ → H
  | 0 => 1
  | m+1 => right d (merge m) * d.a⁻¹

@[simp] lemma merge_zero : merge d 0=1 := rfl
@[simp] lemma merge_succ (m : ℕ) : merge d (m+1)=right d (merge d m)*d.a⁻¹ := rfl

lemma merge_coherence (m n : ℕ) :
    merge d (m+n+1) * left d (merge d m) = merge d m * right d (merge d n) * d.a⁻¹ := by
  induction m with
  | zero => simp only [Nat.zero_add,merge_zero,map_one,mul_one,one_mul,merge_succ]
  | succ m ih =>
    rw [Nat.succ_add]
    change (right d (merge d (m+n+1))*d.a⁻¹) * left d (right d (merge d m)*d.a⁻¹) =
      (right d (merge d m)*d.a⁻¹) * right d (merge d n)*d.a⁻¹
    rw [map_mul,map_inv]
    have ht : d.a⁻¹*left d (right d (merge d m))=
        right d (left d (merge d m))*d.a⁻¹ := by
      rw [← assoc_LR d (merge d m)]; group
    have hp : (right d d.a)⁻¹*d.a⁻¹*(left d d.a)⁻¹=d.a⁻¹*d.a⁻¹ := by
      simpa only [mul_inv_rev,left,right,MonoidHom.coe_mk,OneHom.coe_mk,mul_assoc] using
        (congrArg (fun z : H=>z⁻¹) d.pentagon).symm
    calc
      _=right d (merge d (m+n+1)) * right d (left d (merge d m)) *
          d.a⁻¹*(left d d.a)⁻¹ := by
        calc
          _=right d (merge d (m+n+1)) * (d.a⁻¹*left d (right d (merge d m))) *
            (left d d.a)⁻¹ := by group
          _=_ := by rw [ht]; group
      _=right d (merge d m * right d (merge d n) * d.a⁻¹) * d.a⁻¹*(left d d.a)⁻¹ := by
        rw [← map_mul,ih]
      _=right d (merge d m) * right d (right d (merge d n)) * (d.a⁻¹*d.a⁻¹) := by
        rw [map_mul,map_mul,map_inv]; rw [← hp]; group
      _=right d (merge d m) * d.a⁻¹ * right d (merge d n) * d.a⁻¹ := by
        have hh := assoc_RR d (merge d n)
        calc
          _=right d (merge d m) * d.a⁻¹ *
             (d.a*right d (right d (merge d n))*d.a⁻¹) * d.a⁻¹ := by group
          _=_ := by rw [hh]

def blockMap (m p : ℕ) (f g : H) : H :=
  merge d p * d.tensor (f,g) * (merge d m)⁻¹

@[simp] lemma blockMap_id (m : ℕ) : blockMap d m m 1 1=1 := by
  rw [blockMap,show d.tensor (1,1)=1 from map_one d.tensor,mul_one,mul_inv_cancel]

end

universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma combSwap_succ {n i : ℕ} (hi : i<n) :
    combSwap d q (n+1) (i+1) = right d (combSwap d q n i) := by
  simp only [combSwap,show i+1<n+1 by omega,hi,↓reduceIte,
    Nat.add_right_cancel_iff,rightPower_succ]

lemma merge_right (m : ℕ) (g : H) :
    merge d m * right d g * (merge d m)⁻¹ = rightPower d (m+1) g := by
  induction m with
  | zero => simp only [merge_zero,one_mul,mul_one,inv_one,rightPower_succ,rightPower_zero]
  | succ m ih =>
    rw [merge_succ,rightPower_succ]
    have ha : d.a⁻¹ * right d g * d.a = right d (right d g) := by
      calc
        _ = d.a⁻¹ * (d.a * right d (right d g) * d.a⁻¹) * d.a := by rw [assoc_RR]
        _ = _ := by group
    calc
      _=right d (merge d m) * (d.a⁻¹*right d g*d.a) * (right d (merge d m))⁻¹ := by group
      _=right d (merge d m * right d g * (merge d m)⁻¹) := by
        rw [ha,map_mul,map_mul,map_inv]
      _=_ := congrArg (right d) ih

lemma merge_left_right (m : ℕ) (g : H) :
    merge d (m+1) * left d (right d g) * (merge d (m+1))⁻¹ =
      right d (merge d m * left d g * (merge d m)⁻¹) := by
  have ha : d.a⁻¹ * left d (right d g) * d.a = right d (left d g) := by
    rw [← assoc_LR d g]; group
  rw [merge_succ]
  calc
    _=right d (merge d m) * (d.a⁻¹*left d (right d g)*d.a) * (right d (merge d m))⁻¹ := by group
    _=_ := by rw [ha,map_mul,map_mul,map_inv]

lemma merge_left_head_base :
    merge d 2 * left d (combHead d q) * (merge d 2)⁻¹ = combHead d q := by
  have hM : merge d 2 = (d.a*d.a)⁻¹ * left d d.a := by
    have hp : d.a*d.a = left d d.a*d.a*right d d.a := d.pentagon
    rw [merge_succ,merge_succ,merge_zero,map_one,one_mul,map_inv,hp]
    group
  have hH := combHead_conj_first d q
  change (d.a*d.a)*combHead d q*(d.a*d.a)⁻¹=left d (left d q.c) at hH
  rw [hM,combHead,map_mul,map_mul,map_inv]
  calc
    _=(d.a*d.a)⁻¹ * left d (left d q.c) * (d.a*d.a) := by group; simp only [zpow_ofNat, pow_two, mul_assoc]
    _=_ := by rw [← hH]; dsimp only [combHead]; group

lemma merge_left_head (m : ℕ) :
    merge d (m+2) * left d (combHead d q) * (merge d (m+2))⁻¹ = combHead d q := by
  have hm : merge d (m+2)=right d (right d (merge d m))*merge d 2 := by
    simp only [merge_succ,map_mul,merge_zero,map_one,one_mul]
    group
  rw [hm]
  calc
    _=right d (right d (merge d m)) *
      (merge d 2*left d (combHead d q)*(merge d 2)⁻¹) *
      (right d (right d (merge d m)))⁻¹ := by group
    _=right d (right d (merge d m))*combHead d q*(right d (right d (merge d m)))⁻¹ := by
      rw [merge_left_head_base]
    _=combHead d q := by
      rw [← (combHead_distant d q (merge d m)).eq,mul_assoc,mul_inv_cancel,mul_one]

lemma combSwap_left {m i : ℕ} (hi : i < m) (n : ℕ) :
    merge d m * left d (combSwap d q m i) * (merge d m)⁻¹ =
      combSwap d q (m+n+1) i := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero =>
      cases m with
      | zero =>
        rw [combSwap_last,rightPower_zero,merge_succ,merge_zero,map_one,one_mul,
          inv_inv,combSwap_internal d q (by omega),rightPower_zero]
        rfl
      | succ m =>
        rw [combSwap_internal d q (by omega),rightPower_zero,merge_left_head,
          combSwap_internal d q (by omega),rightPower_zero]
    | succ i =>
      rw [combSwap_succ d q (by omega),merge_left_right,ih (by omega),
        show m+1+n+1=(m+n+1)+1 by omega,combSwap_succ d q (by omega)]

lemma combSwap_shift {n i : ℕ} (hi : i<n) (m : ℕ) :
    rightPower d m (combSwap d q n i) = combSwap d q (m+n) (m+i) := by
  simp only [combSwap,hi,show m+i < m+n by omega,↓reduceIte,
    show m+i+1=m+(i+1) by omega,Nat.add_left_cancel_iff,rightPower_add]

lemma combSwap_right {n i : ℕ} (hi : i<n) (m : ℕ) :
    merge d m * right d (combSwap d q n i) * (merge d m)⁻¹ =
      combSwap d q (m+n+1) (m+1+i) := by
  rw [merge_right,combSwap_shift d q hi]
  congr 1; omega

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma combPermutation_sum_left (m n : ℕ) (p : Equiv.Perm (Fin (m+1))) :
    combPermutation d q (m+n+1) (sumPermutation m n (p,1)) =
      merge d m * left d (combPermutation d q m p) * (merge d m)⁻¹ := by
  induction p using Adjacent.permutation_induction with
  | hone => simp only [show (1,1)= (1 : Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin (n+1))) from rfl,
      map_one,mul_one,mul_inv_cancel]
  | hswap i =>
    let j : Fin (m+n+1) := ⟨i,by omega⟩
    have hh : sumPermutation m n (Equiv.swap i.castSucc i.succ,1)=
        Equiv.swap j.castSucc j.succ := by
      rw [sumPermutation_swap_left]
      congr 1
    rw [hh,combPermutation_swap,combPermutation_swap,combSwap_left d q i.isLt]
  | hmul p r hp hr =>
    have hh : sumPermutation m n (p*r,1)=sumPermutation m n (p,1)*sumPermutation m n (r,1) :=
      (sumPermutation m n).map_mul (p,1) (r,1)
    rw [hh,map_mul,hp,hr,map_mul,map_mul]
    group

lemma combPermutation_sum_right (m n : ℕ) (p : Equiv.Perm (Fin (n+1))) :
    combPermutation d q (m+n+1) (sumPermutation m n (1,p)) =
      merge d m * right d (combPermutation d q n p) * (merge d m)⁻¹ := by
  induction p using Adjacent.permutation_induction with
  | hone => simp only [show (1,1)= (1 : Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin (n+1))) from rfl,
      map_one,mul_one,mul_inv_cancel]
  | hswap i =>
    let j : Fin (m+n+1) := ⟨m+1+i,by omega⟩
    have hh : sumPermutation m n (1,Equiv.swap i.castSucc i.succ)=
        Equiv.swap j.castSucc j.succ := by
      rw [sumPermutation_swap_right]
      congr 1
    rw [hh,combPermutation_swap,combPermutation_swap,combSwap_right d q i.isLt]
  | hmul p r hp hr =>
    have hh : sumPermutation m n (1,p*r)=sumPermutation m n (1,p)*sumPermutation m n (1,r) :=
      (sumPermutation m n).map_mul (1,p) (1,r)
    rw [hh,map_mul,hp,hr,map_mul,map_mul]
    group

lemma combPermutation_sum (m n : ℕ) (p : Equiv.Perm (Fin (m+1))) (r : Equiv.Perm (Fin (n+1))) :
    combPermutation d q (m+n+1) (sumPermutation m n (p,r)) =
      blockMap d m m (combPermutation d q m p) (combPermutation d q n r) := by
  have hh : sumPermutation m n (p,r)=sumPermutation m n (p,1)*sumPermutation m n (1,r) :=
    (sumPermutation m n).map_mul (p,1) (1,r)
  rw [hh,map_mul,combPermutation_sum_left,combPermutation_sum_right]
  dsimp only [blockMap,left,right,MonoidHom.coe_mk,OneHom.coe_mk]
  rw [show d.tensor (combPermutation d q m p,combPermutation d q n r)=
      d.tensor (combPermutation d q m p,1)*d.tensor (1,combPermutation d q n r) from
        by simpa only [Prod.mk_mul_mk,mul_one,one_mul] using map_mul d.tensor (combPermutation d q m p,1) (1,combPermutation d q n r)]
  group

/-- The symmetric coherence value of a bijection of two positive finite ordinals.
Both sides may use different (provably equal) numeral expressions. -/
def equivVal {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) : H :=
  combPermutation d q m (e.trans (finCongr (congrArg (fun k=>k+1) (equiv_size e).symm)))

@[simp] lemma equivVal_same {m : ℕ} (e : Equiv.Perm (Fin (m+1))) :
    equivVal d q e=combPermutation d q m e := rfl

@[simp] lemma equivVal_refl (m : ℕ) : equivVal d q (Equiv.refl (Fin (m+1)))=1 :=
  map_one (combPermutation d q m)

@[simp] lemma equivVal_cast {m n : ℕ} (h : m=n) :
    equivVal d q (finCongr (congrArg (fun k=>k+1) h))=1 := by
  subst n
  exact equivVal_refl d q m

lemma equivVal_trans {m n k : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) (f : Fin (n+1) ≃ Fin (k+1)) :
    equivVal d q (e.trans f)=equivVal d q f*equivVal d q e := by
  have hm := equiv_size e
  have hn := equiv_size f
  subst n k
  exact map_mul (combPermutation d q m) f e

@[simp] lemma equivVal_symm {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) :
    equivVal d q e.symm=(equivVal d q e)⁻¹ := by
  have hm := equiv_size e
  subst n
  exact map_inv (combPermutation d q m) e

lemma equivVal_sum {m n p r : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (r+1)) :
    equivVal d q (sumEquiv e f)=blockMap d m p (equivVal d q e) (equivVal d q f) := by
  have hm := equiv_size e
  have hn := equiv_size f
  subst p r
  exact combPermutation_sum d q m n e f

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

namespace FiniteAlgebraicEnvelopes
namespace BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma equivVal_transport {m n p r : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) (f : Fin (p+1) ≃ Fin (r+1))
    (hm : m=p) (hn : n=r)
    (h : ∀ (i : Fin (m+1)) (j : Fin (p+1)),(i:ℕ)=(j:ℕ) → (e i : ℕ)=(f j : ℕ)) :
    equivVal d q e=equivVal d q f := by
  subst p r
  congr 1
  apply Equiv.ext
  intro i
  exact Fin.ext (h i i rfl)

lemma equivVal_order {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1))
    (h : ∀ i,(e i : ℕ)=i) : equivVal d q e=1 := by
  have he := equiv_size e
  subst n
  have hh : e=Equiv.refl _ := by apply Equiv.ext; intro i; exact Fin.ext (h i)
  rw [hh,equivVal_refl]

lemma combPermutation_finSwap (n i : ℕ) :
    combPermutation d q n (Adjacent.finSwap n i) = combSwap d q n i := by
  by_cases hi : i<n
  · rw [Adjacent.finSwap_lt hi]
    exact combPermutation_swap d q n ⟨i,hi⟩
  · simp only [Adjacent.finSwap,hi,↓reduceDIte,map_one,combSwap,↓reduceIte]

lemma combPermutation_descending (n i k : ℕ) :
    combPermutation d q n (Adjacent.descending (Adjacent.finSwap n) i k)=
      Adjacent.descending (combSwap d q n) i k := by
  rw [Adjacent.map_descending]
  congr 1
  funext j
  exact combPermutation_finSwap d q n j

lemma descending_comb_head (n : ℕ) :
    Adjacent.descending (combSwap d q (n+1)) 0 (n+1)=merge d n*q.c := by
  induction n with
  | zero => simp only [Adjacent.descending,Nat.zero_le,↓reduceIte,mul_one,combSwap_last,
      rightPower_zero,merge_zero,one_mul]
  | succ n ih =>
    rw [Adjacent.descending_head]
    have hh : Adjacent.descending (fun i=>combSwap d q (n+1+1) (i+1)) 0 (n+1)=
        right d (Adjacent.descending (combSwap d q (n+1)) 0 (n+1)) := by
      rw [Adjacent.map_descending]
      apply Adjacent.descending_congr
      intro j hj
      exact combSwap_succ d q hj
    rw [hh,ih,map_mul,combSwap_internal d q (by omega),rightPower_zero,merge_succ]
    have hx : right d q.c * combHead d q=d.a⁻¹*q.c := by
      have h := congrArg (fun z:H=>d.a⁻¹*z) q.hexagon
      change d.a⁻¹*q.c=d.a⁻¹*(d.a*right d q.c*d.a⁻¹*left d q.c*d.a) at h
      dsimp only [combHead]
      calc
        _=d.a⁻¹*(d.a*right d q.c*d.a⁻¹*left d q.c*d.a) := by group
        _=_ := h.symm
    rw [mul_assoc,hx,mul_assoc]

lemma equivVal_exchange_zero (n : ℕ) :
    equivVal d q (exchangeEquiv 0 n)=merge d n*q.c := by
  let p := Adjacent.descending (Adjacent.finSwap (n+1)) 0 (n+1)
  have hp (i : Fin (n+1+1)) :
      (p i : ℕ)=if (i:ℕ)=0 then n+1 else if (i:ℕ)≤n+1 then i-1 else i := by
    rw [← Adjacent.natExtend_apply (n+1+1) p i]
    rw [Adjacent.natExtend_descending _ _ _ le_rfl,Adjacent.descending_nat_zero_apply]
  have he : equivVal d q (exchangeEquiv 0 n)=equivVal d q p := by
    apply equivVal_transport d q _ _ (by omega) (by omega)
    intro i j hij
    obtain ⟨k,rfl⟩ := (sumIndex 0 n).surjective i
    cases k with
    | inl k =>
      rw [exchangeEquiv_left,sumIndex_right_val,hp]
      have hk : (k:ℕ)=0 := by omega
      simp only [sumIndex_left_val] at hij
      simp only [show (j:ℕ)=0 by omega,↓reduceIte,hk]
    | inr k =>
      rw [exchangeEquiv_right,sumIndex_left_val,hp]
      simp only [sumIndex_right_val] at hij
      simp only [show ¬ (j:ℕ)=0 by omega,show (j:ℕ)≤n+1 by omega,↓reduceIte]
      omega
  rw [he,equivVal_same,combPermutation_descending,descending_comb_head]

end BinaryGroupCategory
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma merge_left_merge (n : ℕ) : merge d (n+1)*left d (merge d n)=merge d n*d.a⁻¹ := by
  simpa only [Nat.add_zero,merge_zero,map_one,mul_one] using merge_coherence d n 0

lemma exchange_scalar_step (m n : ℕ) :
    blockMap d (n+1) (n+1) (merge d n*q.c) 1 *
      right d (merge d n*q.c*(merge d m)⁻¹) =
        merge d n*q.c*(merge d (m+1))⁻¹ := by
  have hx : d.a⁻¹*left d q.c*d.a*right d q.c=q.c*d.a := by
    have h := hexagon_equation_reverse d q
    change d.a*q.c*d.a=left d q.c*d.a*right d q.c at h
    calc
      _=d.a⁻¹*(left d q.c*d.a*right d q.c) := by group
      _=_ := by rw [← h]; group
  change merge d (n+1)*left d (merge d n*q.c)*(merge d (n+1))⁻¹*
    right d (merge d n*q.c*(merge d m)⁻¹)=_
  rw [map_mul,map_mul,map_mul,map_inv]
  calc
    _=(merge d (n+1)*left d (merge d n))*left d q.c*
        (merge d (n+1))⁻¹*right d (merge d n)*right d q.c*(right d (merge d m))⁻¹ := by group
    _=merge d n*(d.a⁻¹*left d q.c*d.a*right d q.c)*(right d (merge d m))⁻¹ := by
      rw [merge_left_merge,merge_succ]; group
    _=_ := by rw [hx,merge_succ]; group

lemma equivVal_exchange (m n : ℕ) :
    equivVal d q (exchangeEquiv m n)=merge d n*q.c*(merge d m)⁻¹ := by
  induction m with
  | zero => simpa only [merge_zero,inv_one,mul_one] using equivVal_exchange_zero d q n
  | succ m ih =>
    let e₁ := sumEquiv (Equiv.refl (Fin 1)) (exchangeEquiv m n)
    let c := finCongr (congrArg (fun k=>k+1) (show 0+(n+m+1)+1=(0+n+1)+m+1 by omega))
    let e₂ := sumEquiv (exchangeEquiv 0 n) (Equiv.refl (Fin (m+1)))
    let e := e₁.trans (c.trans e₂)
    have he : equivVal d q (exchangeEquiv (m+1) n)=equivVal d q e := by
      apply equivVal_transport d q _ _ (by omega) (by omega)
      intro i j hij
      rw [exchangeEquiv_val]
      have h₁ : (e₁ j : ℕ)=if (j:ℕ)<1 then (j:ℕ) else
          1+(if (j:ℕ)-1< m+1 then n+1+((j:ℕ)-1) else (j:ℕ)-1-(m+1)) := by
        exact sumEquiv_valWith (Equiv.refl (Fin 1)) (exchangeEquiv m n) id
          (fun k=>if k< m+1 then n+1+k else k-(m+1)) (fun _=>rfl)
          (exchangeEquiv_val m n) j
      have h₂ : (e₂ (c (e₁ j)) : ℕ)=if (c (e₁ j) : ℕ)< n+2 then
          (if (c (e₁ j) : ℕ)<1 then n+1+(c (e₁ j) : ℕ) else (c (e₁ j) : ℕ)-1)
        else n+2+((c (e₁ j) : ℕ)-(n+2)) := by
        simpa only [Nat.zero_add,Nat.add_zero,Nat.add_assoc,id_eq,show 1+1=2 from rfl] using
          sumEquiv_valWith (exchangeEquiv 0 n) (Equiv.refl (Fin (m+1)))
            (fun k=>if k<1 then n+1+k else k-1) id
            (exchangeEquiv_val 0 n) (fun _=>rfl) (c (e₁ j))
      change _=(e₂ (c (e₁ j)) : ℕ)
      rw [h₂]
      change _=if (e₁ j : ℕ)< n+2 then
        (if (e₁ j : ℕ)<1 then n+1+(e₁ j : ℕ) else (e₁ j : ℕ)-1)
        else n+2+((e₁ j : ℕ)-(n+2))
      rw [h₁]
      split_ifs <;> omega
    rw [he]
    change equivVal d q (e₁.trans (c.trans e₂))=_
    have hc : equivVal d q c=1 := equivVal_cast d q (by omega)
    rw [equivVal_trans,equivVal_trans,hc,mul_one]
    dsimp only [e₁,e₂]
    rw [equivVal_sum,equivVal_sum,equivVal_refl,equivVal_refl,equivVal_exchange_zero,ih]
    simp only [Nat.zero_add]
    have hb (g : H) : blockMap d 0 0 1 g=right d g := by
      simp only [blockMap,merge_zero,one_mul,inv_one,mul_one]; rfl
    rw [hb]
    exact exchange_scalar_step d q m n

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

end

end OAI
end

section
-- module Solutions.OAIFAE.CantorBricks
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Cantor prefixes, bricks, charts, finite-table group, localization, and displacement.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable

namespace Prefix
variable {X : Type u}

def oneBit (x : X) (b : Bool) : Prefix X := by
  classical
  exact ⟨fun y => if y=x then [b] else [],
    (Set.finite_singleton x).subset (by
      intro y hy
      by_contra hn
      exact hy (ite_eq_right hn))⟩

@[simp] theorem oneBit_word (x y : X) (b : Bool) :
    (oneBit x b).word y = if y=x then [b] else [] := by classical exact rfl

lemma mem_oneBit (x : X) (b : Bool) (z : Cube X) :
    (∃ w, (oneBit x b).attach w=z) ↔ z x 0=b := by
  classical
  constructor
  · rintro ⟨w,rfl⟩
    simp [attach,Stream'.cons]
  · intro hz
    refine ⟨fun y => if y=x then Stream'.tail (z y) else z y,?_⟩
    funext y n
    by_cases hy : y=x
    · subst y
      cases n with
      | zero => simpa [attach,Stream'.appendStream',Stream'.cons] using hz.symm
      | succ n => simp [attach,Stream'.cons,Stream'.tail,Stream'.get]
    · simp [attach,hy]

end Prefix

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- A finite prefix-replacement table, with one input-group twist on each brick.
The uniqueness clauses say that the source and target bricks are partitions. -/
structure Table (f : Equiv.Perm (Cube X)) where
  index : Type
  finite : Fintype index
  source : index → Prefix X
  target : index → Prefix X
  label : index → Γ
  source_cover : ∀ z : Cube X, ∃! i, ∃ w, (source i).attach w=z
  target_cover : ∀ z : Cube X, ∃! i, ∃ w, (target i).attach w=z
  chart : ∀ i z, f ((source i).attach z) = (target i).attach (twist (label i) z)

/-- Concrete permutation model generated by finite twisted dyadic tables. -/
def group : Subgroup (Equiv.Perm (Cube X)) :=
  Subgroup.closure {f | Nonempty (Table (Γ:=Γ) f)}

lemma twist_table (g : Γ) : Nonempty (Table (Γ:=Γ) (twist (X:=X) g)) := by
  refine ⟨⟨PUnit,inferInstance,fun _ => Prefix.empty,fun _ => Prefix.empty,
    fun _ => g,?_,?_,?_⟩⟩
  · intro z
    exact ⟨PUnit.unit,⟨z,Prefix.empty_attach z⟩,fun i _ => Subsingleton.elim _ _⟩
  · intro z
    exact ⟨PUnit.unit,⟨z,Prefix.empty_attach z⟩,fun i _ => Subsingleton.elim _ _⟩
  · intro i z
    simp

def embedding : Γ →* group (Γ:=Γ) (X:=X) :=
  (twistHom (Γ:=Γ) (X:=X)).codRestrict _
    (fun g => Subgroup.subset_closure (twist_table g))

end

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type u}

@[ext] lemma ext {p q : Prefix X} (h : ∀ x, p.word x=q.word x) : p=q := by
  cases p with | mk p hp => cases q with | mk q hq =>
    have he : p=q := funext h
    cases he
    rfl

lemma mem_range_iff (p : Prefix X) (z : Cube X) :
    (∃ w, p.attach w=z) ↔ ∀ x, (z x).take (p.word x).length = p.word x := by
  constructor
  · rintro ⟨w,rfl⟩ x
    exact (Stream'.take_append_of_le_length _ _ _ le_rfl).trans List.take_length
  · intro h
    refine ⟨fun x => (z x).drop (p.word x).length,?_⟩
    funext x
    change Stream'.appendStream' (p.word x) ((z x).drop (p.word x).length)=z x
    rw [← h x]
    simp

def comp (p q : Prefix X) : Prefix X :=
  ⟨fun x => p.word x ++ q.word x,(p.finite_support.union q.finite_support).subset
    (by
      intro x hx
      by_cases hp : p.word x=[]
      · exact Or.inr (by intro hq; exact hx (by simp [hp,hq]))
      · exact Or.inl hp)⟩

@[simp] lemma comp_word (p q : Prefix X) (x : X) :
    (p.comp q).word x = p.word x ++ q.word x := rfl

@[simp] lemma comp_attach (p q : Prefix X) (z : Cube X) :
    (p.comp q).attach z = p.attach (q.attach z) := by
  funext x
  exact Stream'.append_append_stream _ _ _

def Extends (p q : Prefix X) : Prop := ∀ x, p.word x <+: q.word x

def remainder (p q : Prefix X) : Prefix X :=
  ⟨fun x => (q.word x).drop (p.word x).length,q.finite_support.subset
    (by intro x hx hq; exact hx (by simp [hq]))⟩

@[simp] lemma remainder_word (p q : Prefix X) (x : X) :
    (p.remainder q).word x = (q.word x).drop (p.word x).length := rfl

lemma comp_remainder {p q : Prefix X} (h : p.Extends q) : p.comp (p.remainder q)=q := by
  apply Prefix.ext
  intro x
  change p.word x ++ (q.word x).drop (p.word x).length=q.word x
  obtain ⟨r,hr⟩ := h x
  rw [← hr]
  simp

/-- Nonempty intersection of the two dyadic bricks. -/
def Compatible (p q : Prefix X) : Prop := ∃ z, (∃ w,p.attach w=z) ∧ ∃ w,q.attach w=z

def commonPoint {p q : Prefix X} (h : p.Compatible q) : Cube X := h.choose

lemma commonPoint_mem_left {p q : Prefix X} (h : p.Compatible q) :
    ∃ w, p.attach w=commonPoint h := h.choose_spec.1

lemma commonPoint_mem_right {p q : Prefix X} (h : p.Compatible q) :
    ∃ w, q.attach w=commonPoint h := h.choose_spec.2

/-- Intersection is again one brick: take the longer prefix at each coordinate. -/
def meet {p q : Prefix X} (h : p.Compatible q) : Prefix X :=
  ⟨fun x => ((commonPoint h) x).take (max (p.word x).length (q.word x).length),
    (p.finite_support.union q.finite_support).subset (by
      intro x hx
      by_contra hn
      have hp : p.word x=[] := by simpa using (not_or.mp hn).1
      have hq : q.word x=[] := by simpa using (not_or.mp hn).2
      exact hx (by simp [hp,hq]))⟩

lemma meet_extends_left {p q : Prefix X} (h : p.Compatible q) : p.Extends (meet h) := by
  intro x
  have hp := (mem_range_iff p _).mp (commonPoint_mem_left h) x
  rw [← hp]
  exact Stream'.take_prefix_take_left _ _ _ (le_max_left _ _)

lemma meet_extends_right {p q : Prefix X} (h : p.Compatible q) : q.Extends (meet h) := by
  intro x
  have hq := (mem_range_iff q _).mp (commonPoint_mem_right h) x
  rw [← hq]
  exact Stream'.take_prefix_take_left _ _ _ (le_max_right _ _)

lemma mem_range_of_extends {p q : Prefix X} (h : p.Extends q) {z : Cube X}
    (hz : ∃ w,q.attach w=z) : ∃ w,p.attach w=z := by
  obtain ⟨w,rfl⟩ := hz
  rw [← comp_remainder h,comp_attach]
  exact ⟨_,rfl⟩

lemma mem_meet_iff {p q : Prefix X} (h : p.Compatible q) (z : Cube X) :
    (∃ w,(meet h).attach w=z) ↔ (∃ w,p.attach w=z) ∧ ∃ w,q.attach w=z := by
  constructor
  · intro hz
    exact ⟨mem_range_of_extends (meet_extends_left h) hz,
      mem_range_of_extends (meet_extends_right h) hz⟩
  · rintro ⟨hp,hq⟩
    apply (mem_range_iff _ _).mpr
    intro x
    change (z x).take (((commonPoint h) x).take _).length =
      ((commonPoint h) x).take (max (p.word x).length (q.word x).length)
    rw [Stream'.length_take]
    have hp' := (mem_range_iff p _).mp hp x
    have hq' := (mem_range_iff q _).mp hq x
    have hc₁ := (mem_range_iff p _).mp (commonPoint_mem_left h) x
    have hc₂ := (mem_range_iff q _).mp (commonPoint_mem_right h) x
    rcases le_total (p.word x).length (q.word x).length with hl|hl
    · rw [max_eq_right hl,hq',hc₂]
    · rw [max_eq_left hl,hp',hc₁]

end Prefix

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- The induced coordinate permutation on finite prefixes. -/
def twistPrefix (g : Γ) (p : Prefix X) : Prefix X :=
  ⟨fun x => p.word (g⁻¹ • x),p.finite_support.preimage
    (MulAction.injective (g⁻¹ : Γ)).injOn⟩

@[simp] lemma twistPrefix_word (g : Γ) (p : Prefix X) (x : X) :
    (twistPrefix g p).word x=p.word (g⁻¹ • x) := rfl

@[simp] lemma twist_attach (g : Γ) (p : Prefix X) (z : Cube X) :
    twist g (p.attach z) = (twistPrefix g p).attach (twist g z) := rfl

lemma untwist_attach (g : Γ) (p : Prefix X) (z : Cube X) :
    twist g ((twistPrefix g⁻¹ p).attach z) = p.attach (twist g z) := by
  ext x n
  simp [Prefix.attach]

end

section
universe u
attribute [local instance] Classical.propDecidable

/-- A finite dyadic partition of the entire cube. -/
structure Partition (X : Type u) where
  index : Type
  finite : Fintype index
  brick : index → Prefix X
  cover : ∀ z : Cube X, ∃! i, ∃ w,(brick i).attach w=z

namespace Partition
variable {X : Type u}

def trivial : Partition X where
  index := PUnit
  finite := inferInstance
  brick _ := Prefix.empty
  cover z := ⟨PUnit.unit,⟨z,Prefix.empty_attach z⟩,fun _ _=>Subsingleton.elim _ _⟩

abbrev bit (x : X) : Partition X where
  index := Bool
  finite := inferInstance
  brick := Prefix.oneBit x
  cover z := ⟨z x 0,(Prefix.mem_oneBit x _ z).mpr rfl,
    fun b hb => ((Prefix.mem_oneBit x b z).mp hb).symm⟩

def RefineIndex (P Q : Partition X) (i : P.index) := {j : P.index // j≠i} ⊕ Q.index

instance refineIndex_finite (P Q : Partition X) (i : P.index) : Fintype (RefineIndex P Q i) := by
  letI := P.finite
  letI := Q.finite
  exact inferInstanceAs (Fintype ({j : P.index // j≠i} ⊕ Q.index))

def refineBrick (P Q : Partition X) (i : P.index) : RefineIndex P Q i → Prefix X
  | Sum.inl j => P.brick j.val
  | Sum.inr j => (P.brick i).comp (Q.brick j)

lemma refine_cover (P Q : Partition X) (i : P.index) :
    ∀ z : Cube X, ∃! j : RefineIndex P Q i, ∃ w,(refineBrick P Q i j).attach w=z := by
  intro z
  obtain ⟨k,⟨v,hv⟩,hk⟩ := P.cover z
  by_cases hki : k=i
  · subst k
    obtain ⟨j,⟨w,hw⟩,hj⟩ := Q.cover v
    refine ⟨Sum.inr j,⟨w,?_⟩,?_⟩
    · change ((P.brick i).comp (Q.brick j)).attach w=z
      rw [Prefix.comp_attach,hw,hv]
    · intro b hb
      cases b with
      | inl b =>
          have hb' : b.val=i := hk _ hb
          exact (b.property hb').elim
      | inr b =>
          obtain ⟨a,ha⟩ := hb
          have hab : (Q.brick b).attach a=v :=
            (P.brick i).attach_injective ((Prefix.comp_attach _ _ _).symm.trans (ha.trans hv.symm))
          exact congrArg Sum.inr (hj b ⟨a,hab⟩)
  · refine ⟨Sum.inl ⟨k,hki⟩,⟨v,hv⟩,?_⟩
    intro b hb
    cases b with
    | inl b =>
        exact congrArg Sum.inl (Subtype.ext (hk _ hb))
    | inr b =>
        obtain ⟨w,hw⟩ := hb
        have hik : i=k := hk i ⟨(Q.brick b).attach w,
          (Prefix.comp_attach _ _ _).symm.trans hw⟩
        exact (hki hik.symm).elim

def refinement (P Q : Partition X) (i : P.index) : Partition X where
  index := RefineIndex P Q i
  finite := refineIndex_finite P Q i
  brick := refineBrick P Q i
  cover := refine_cover P Q i

end Partition

namespace Prefix
variable {X : Type u}

/-- The brick occurs as one member of an actual finite partition. -/
def HasPartition (p : Prefix X) : Prop := ∃ P : Partition X, ∃ i, P.brick i=p

lemma empty_hasPartition : (empty : Prefix X).HasPartition :=
  ⟨Partition.trivial,PUnit.unit,rfl⟩

lemma oneBit_hasPartition (x : X) (b : Bool) : (oneBit x b).HasPartition :=
  ⟨Partition.bit x,b,rfl⟩

lemma comp_hasPartition {p q : Prefix X} (hp : p.HasPartition) (hq : q.HasPartition) :
    (p.comp q).HasPartition := by
  obtain ⟨P,i,hi⟩ := hp
  obtain ⟨Q,j,hj⟩ := hq
  refine ⟨P.refinement Q i,Sum.inr j,?_⟩
  change (P.brick i).comp (Q.brick j)=p.comp q
  rw [hi,hj]

def atWord (x : X) (w : List Bool) : Prefix X :=
  ⟨fun y => if y=x then w else [],(Set.finite_singleton x).subset (by
    intro y hy
    by_contra hn
    exact hy (ite_eq_right hn))⟩

@[simp] lemma atWord_word (x y : X) (w : List Bool) :
    (atWord x w).word y=if y=x then w else [] := rfl

lemma atWord_nil (x : X) : atWord x []=empty := by
  apply Prefix.ext
  intro y
  simp [empty]

lemma atWord_cons (x : X) (b : Bool) (w : List Bool) :
    atWord x (b::w)=(oneBit x b).comp (atWord x w) := by
  apply Prefix.ext
  intro y
  by_cases hy : y=x <;> simp [hy]

lemma atWord_hasPartition (x : X) (w : List Bool) : (atWord x w).HasPartition := by
  induction w with
  | nil => rw [atWord_nil]; exact empty_hasPartition
  | cons b w ih =>
      rw [atWord_cons]
      exact comp_hasPartition (oneBit_hasPartition x b) ih

def erase (p : Prefix X) (x : X) : Prefix X :=
  ⟨fun y => if y=x then [] else p.word y,p.finite_support.subset (by
    intro y hy he
    exact hy (by simp [he]))⟩

@[simp] lemma erase_word (p : Prefix X) (x y : X) :
    (p.erase x).word y=if y=x then [] else p.word y := rfl

lemma atWord_comp_erase (p : Prefix X) (x : X) :
    (atWord x (p.word x)).comp (p.erase x)=p := by
  apply Prefix.ext
  intro y
  by_cases hy : y=x
  · subst y; simp
  · simp [hy]

/-- Every finite dyadic brick has a finite dyadic complement partition. -/
theorem hasPartition (p : Prefix X) : p.HasPartition := by
  suffices ∀ (s : Finset X) (q : Prefix X),
      (∀ x,q.word x≠[] → x∈s) → q.HasPartition by
    exact this p.finite_support.toFinset p (by intro x hx; simpa using hx)
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro q hq
      have he : q=empty := by
        apply Prefix.ext
        intro x
        have hx : q.word x=[] := by
          by_contra hn
          exact Finset.notMem_empty x (hq x hn)
        exact hx
      rw [he]
      exact empty_hasPartition
  | @insert x s hx ih =>
      intro q hq
      have he : (q.erase x).HasPartition := ih _ (by
        intro y hy
        have hne : y≠x := by intro hyx; subst y; simp at hy
        have hn : q.word y≠[] := by simpa [hne] using hy
        exact (Finset.mem_insert.mp (hq y hn)).resolve_left hne)
      have hh := comp_hasPartition (atWord_hasPartition x (q.word x)) he
      rwa [atWord_comp_erase] at hh

end Prefix

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

@[simp] lemma twist_inv_twist (g : Γ) (z : Cube X) : twist g⁻¹ (twist g z)=z := by
  ext x n
  simp

@[simp] lemma twist_twist_inv (g : Γ) (z : Cube X) : twist g (twist g⁻¹ z)=z := by
  ext x n
  simp

lemma twist_twist (g h : Γ) (z : Cube X) : twist g (twist h z)=twist (g*h) z := by
  ext x n
  simp [mul_smul]

namespace Table

/-- Target partition follows from the source partition and the bijective charts. -/
lemma transport_partition {I : Type} (f : Equiv.Perm (Cube X))
    (p q : I → Prefix X) (a : I → Γ)
    (hp : ∀ z : Cube X, ∃! i, ∃ w, (p i).attach w=z)
    (hchart : ∀ i z, f ((p i).attach z) = (q i).attach (twist (a i) z)) :
    ∀ z : Cube X, ∃! i, ∃ w, (q i).attach w=z := by
  intro z
  obtain ⟨i,⟨w,hw⟩,hi⟩ := hp (f.symm z)
  refine ⟨i,⟨twist (a i) w,?_⟩,?_⟩
  · rw [← hchart,hw,Equiv.apply_symm_apply]
  · intro j hj
    apply hi j
    obtain ⟨v,hv⟩ := hj
    refine ⟨twist (a j)⁻¹ v,?_⟩
    apply f.injective
    rw [hchart,twist_twist_inv,hv,Equiv.apply_symm_apply]

def inverse {f : Equiv.Perm (Cube X)} (A : Table (Γ:=Γ) f) : Table (Γ:=Γ) f⁻¹ where
  index := A.index
  finite := A.finite
  source := A.target
  target := A.source
  label i := (A.label i)⁻¹
  source_cover := A.target_cover
  target_cover := A.source_cover
  chart i z := by
    apply f.injective
    change f (f.symm ((A.target i).attach z)) = _
    rw [Equiv.apply_symm_apply,A.chart,twist_twist_inv]

variable {f g : Equiv.Perm (Cube X)}

/-- The nonempty intersections of the intermediate partitions. -/
def Overlap (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) :=
  {ij : A.index × B.index // (A.target ij.1).Compatible (B.source ij.2)}

instance overlap_fintype (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) : Fintype (Overlap A B) := by
  letI := A.finite
  letI := B.finite
  exact inferInstanceAs (Fintype {ij : A.index × B.index //
    (A.target ij.1).Compatible (B.source ij.2)})

def middle (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B) : Prefix X :=
  Prefix.meet ij.property

def leftRemainder (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B) : Prefix X :=
  (A.target ij.val.1).remainder (middle A B ij)

def rightRemainder (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B) : Prefix X :=
  (B.source ij.val.2).remainder (middle A B ij)

def domain (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B) : Prefix X :=
  (A.source ij.val.1).comp (twistPrefix (A.label ij.val.1)⁻¹ (leftRemainder A B ij))

def codomain (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B) : Prefix X :=
  (B.target ij.val.2).comp (twistPrefix (B.label ij.val.2) (rightRemainder A B ij))

lemma leftFactor (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B) :
    (A.target ij.val.1).comp (leftRemainder A B ij)=middle A B ij :=
  Prefix.comp_remainder (Prefix.meet_extends_left ij.property)

lemma rightFactor (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B) :
    (B.source ij.val.2).comp (rightRemainder A B ij)=middle A B ij :=
  Prefix.comp_remainder (Prefix.meet_extends_right ij.property)

lemma domain_chart (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B)
    (z : Cube X) :
    f ((domain A B ij).attach z) = (middle A B ij).attach (twist (A.label ij.val.1) z) := by
  rw [domain,Prefix.comp_attach,A.chart,untwist_attach,← Prefix.comp_attach,leftFactor]

lemma compose_chart (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B)
    (z : Cube X) :
    (g*f) ((domain A B ij).attach z) =
      (codomain A B ij).attach (twist (B.label ij.val.2 * A.label ij.val.1) z) := by
  change g (f ((domain A B ij).attach z)) = _
  rw [domain_chart,← rightFactor A B ij,Prefix.comp_attach,B.chart,twist_attach,
    twist_twist,codomain,Prefix.comp_attach]

lemma mem_domain_iff (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (ij : Overlap A B)
    (z : Cube X) :
    (∃ w,(domain A B ij).attach w=z) ↔
      (∃ w,(A.source ij.val.1).attach w=z) ∧
      ∃ w,(B.source ij.val.2).attach w=f z := by
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨⟨(twistPrefix (A.label ij.val.1)⁻¹ (leftRemainder A B ij)).attach w,
      (Prefix.comp_attach _ _ _).symm⟩,?_⟩
    rw [domain_chart]
    exact Prefix.mem_range_of_extends (Prefix.meet_extends_right ij.property) ⟨_,rfl⟩
  · rintro ⟨⟨v,hv⟩,hb⟩
    have ha : ∃ w,(A.target ij.val.1).attach w=f z :=
      ⟨twist (A.label ij.val.1) v,by rw [← A.chart,hv]⟩
    obtain ⟨w,hw⟩ := (Prefix.mem_meet_iff ij.property (f z)).mpr ⟨ha,hb⟩
    refine ⟨twist (A.label ij.val.1)⁻¹ w,?_⟩
    apply f.injective
    rw [domain_chart,twist_twist_inv]
    exact hw

lemma domain_partition (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) :
    ∀ z : Cube X, ∃! ij : Overlap A B, ∃ w,(domain A B ij).attach w=z := by
  intro z
  obtain ⟨i,hi,huniq⟩ := A.source_cover z
  obtain ⟨j,hj,huniq'⟩ := B.source_cover (f z)
  have hcompat : (A.target i).Compatible (B.source j) := by
    refine ⟨f z,?_,hj⟩
    obtain ⟨w,hw⟩ := hi
    exact ⟨twist (A.label i) w,by rw [← A.chart,hw]⟩
  let ij : Overlap A B := ⟨(i,j),hcompat⟩
  refine ⟨ij,(mem_domain_iff A B ij z).mpr ⟨hi,hj⟩,?_⟩
  intro kl hkl
  obtain ⟨hk,hl⟩ := (mem_domain_iff A B kl z).mp hkl
  apply Subtype.ext
  exact Prod.ext (huniq _ hk) (huniq' _ hl)

/-- Composition is obtained by the literal common refinement of the middle bricks. -/
def compose (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) : Table (Γ:=Γ) (g*f) where
  index := Overlap A B
  finite := overlap_fintype A B
  source := domain A B
  target := codomain A B
  label ij := B.label ij.val.2 * A.label ij.val.1
  source_cover := domain_partition A B
  target_cover := transport_partition _ _ _ _ (domain_partition A B) (compose_chart A B)
  chart := compose_chart A B

end Table

lemma mem_group_iff_table (f : Equiv.Perm (Cube X)) :
    f ∈ group (Γ:=Γ) (X:=X) ↔ Nonempty (Table (Γ:=Γ) f) := by
  constructor
  · intro hf
    change f ∈ Subgroup.closure {f | Nonempty (Table (Γ:=Γ) f)} at hf
    induction hf using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => rw [← twist_one (Γ:=Γ) (X:=X)]; exact twist_table 1
    | mul x y hx hy ihx ihy =>
      obtain ⟨A⟩ := ihx
      obtain ⟨B⟩ := ihy
      exact ⟨B.compose A⟩
    | inv x hx ih =>
      obtain ⟨A⟩ := ih
      exact ⟨A.inverse⟩
  · intro hf
    exact Subgroup.subset_closure hf

end

universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type u}

/-- A finite rectangular neighbourhood of a cube point. -/
def box (z : Cube X) (s : Finset X) (n : ℕ) : Prefix X :=
  ⟨fun x => if x∈s then (z x).take n else [],s.finite_toSet.subset (by
    intro x hx
    by_contra hn
    exact hx (ite_eq_right hn))⟩

@[simp] lemma box_word (z : Cube X) (s : Finset X) (n : ℕ) (x : X) :
    (box z s n).word x = if x∈s then (z x).take n else [] := rfl

end Prefix

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Conjugate a cube permutation into a brick, extending by identity. -/
def localizePerm (p : Prefix X) : Equiv.Perm (Cube X) →* Equiv.Perm (Cube X) :=
  Equiv.Perm.ofSubtype.comp
    (Equiv.ofInjective p.attach p.attach_injective).permCongrHom.toMonoidHom

lemma localizePerm_attach (p : Prefix X) (f : Equiv.Perm (Cube X)) (z : Cube X) :
    localizePerm p f (p.attach z)=p.attach (f z) := by
  change Equiv.Perm.ofSubtype
    ((Equiv.ofInjective p.attach p.attach_injective).permCongr f) (p.attach z)=_
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (show p.attach z∈Set.range p.attach from ⟨z,rfl⟩)]
  simp [Equiv.permCongr,Equiv.equivCongr]

lemma localizePerm_outside (p : Prefix X) (f : Equiv.Perm (Cube X))
    {z : Cube X} (hz : z∉Set.range p.attach) : localizePerm p f z=z :=
  Equiv.Perm.ofSubtype_apply_of_not_mem _ hz

namespace Table
variable {f : Equiv.Perm (Cube X)}

abbrev sourcePartition (A : Table (Γ:=Γ) f) : Partition X :=
  ⟨A.index,A.finite,A.source,A.source_cover⟩

abbrev targetPartition (A : Table (Γ:=Γ) f) : Partition X :=
  ⟨A.index,A.finite,A.target,A.target_cover⟩

/-- Insert a whole finite table into one member of a finite partition. -/
def localize (A : Table (Γ:=Γ) f) (P : Partition X) (i : P.index) :
    Table (Γ:=Γ) (localizePerm (P.brick i) f) where
  index := {j : P.index // j≠i} ⊕ A.index
  finite := P.refineIndex_finite A.sourcePartition i
  source := P.refineBrick A.sourcePartition i
  target := P.refineBrick A.targetPartition i
  label := fun j => match j with | Sum.inl _ => 1 | Sum.inr k => A.label k
  source_cover := P.refine_cover A.sourcePartition i
  target_cover := P.refine_cover A.targetPartition i
  chart := by
    intro j z
    cases j with
    | inl k =>
        change localizePerm (P.brick i) f ((P.brick k.val).attach z)=
          (P.brick k.val).attach (twist 1 z)
        have hz : (P.brick k.val).attach z∉Set.range (P.brick i).attach := by
          intro hi
          obtain ⟨l,hl,huniq⟩ := P.cover ((P.brick k.val).attach z)
          exact k.property ((huniq k.val ⟨z,rfl⟩).trans (huniq i hi).symm)
        rw [localizePerm_outside _ _ hz,twist_one]
        rfl
    | inr k =>
        change localizePerm (P.brick i) f (((P.brick i).comp (A.source k)).attach z)=
          ((P.brick i).comp (A.target k)).attach (twist (A.label k) z)
        rw [Prefix.comp_attach,Prefix.comp_attach,localizePerm_attach,A.chart]

end Table

lemma localizePerm_table (p : Prefix X) {f : Equiv.Perm (Cube X)}
    (hf : Nonempty (Table (Γ:=Γ) f)) : Nonempty (Table (Γ:=Γ) (localizePerm p f)) := by
  obtain ⟨A⟩ := hf
  obtain ⟨P,i,hi⟩ := p.hasPartition
  rw [← hi]
  exact ⟨A.localize P i⟩

/-- Every brick contains a canonical isomorphic copy of the entire twisted group. -/
def localize (p : Prefix X) : group (Γ:=Γ) (X:=X) →* group (Γ:=Γ) (X:=X) :=
  ((localizePerm p).comp (group (Γ:=Γ) (X:=X)).subtype).codRestrict _ (by
    intro f
    exact (mem_group_iff_table _).mpr (localizePerm_table p ((mem_group_iff_table _).mp f.property)))

@[simp] lemma localize_val (p : Prefix X) (f : group (Γ:=Γ) (X:=X)) :
    (localize p f).val=localizePerm p f.val := rfl

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.TwistedSimplicity
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Partition refinement, simplicity, faithful group embedding, and countability.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Partition
variable {X : Type v}

/-- The chart coordinates of a finite dyadic partition. -/
def coordinateEquiv (P : Partition X) : P.index × Cube X ≃ Cube X :=
  Equiv.ofBijective (fun a => (P.brick a.1).attach a.2) (by
    constructor
    · rintro ⟨i,z⟩ ⟨j,w⟩ he
      obtain ⟨k,hk,huniq⟩ := P.cover ((P.brick i).attach z)
      have hij : i=j := (huniq i ⟨z,rfl⟩).trans (huniq j ⟨w,he.symm⟩).symm
      subst j
      exact Prod.ext rfl ((P.brick i).attach_injective he)
    · intro z
      obtain ⟨i,⟨w,hw⟩,_⟩ := P.cover z
      exact ⟨(i,w),hw⟩)

@[simp] lemma coordinateEquiv_apply (P : Partition X) (i : P.index) (z : Cube X) :
    P.coordinateEquiv (i,z)=(P.brick i).attach z := rfl

@[simp] lemma coordinateEquiv_symm_attach (P : Partition X) (i : P.index) (z : Cube X) :
    P.coordinateEquiv.symm ((P.brick i).attach z)=(i,z) :=
  P.coordinateEquiv.symm_apply_apply (i,z)

/-- Untwisted chart bijection between any two equally sized dyadic partitions. -/
def mapPerm (P Q : Partition X) (e : P.index ≃ Q.index) : Equiv.Perm (Cube X) :=
  (P.coordinateEquiv.symm.trans (Equiv.prodCongr e (Equiv.refl (Cube X)))).trans Q.coordinateEquiv

@[simp] lemma mapPerm_attach (P Q : Partition X) (e : P.index ≃ Q.index)
    (i : P.index) (z : Cube X) :
    P.mapPerm Q e ((P.brick i).attach z)=(Q.brick (e i)).attach z := by
  simp [mapPerm]

variable {Γ : Type u} [Group Γ] [MulAction Γ X]

def mapTable (P Q : Partition X) (e : P.index ≃ Q.index) :
    Table (Γ:=Γ) (P.mapPerm Q e) where
  index := P.index
  finite := P.finite
  source := P.brick
  target i := Q.brick (e i)
  label _ := 1
  source_cover := P.cover
  target_cover := by
    intro z
    obtain ⟨i,hi,huniq⟩ := Q.cover z
    refine ⟨e.symm i,?_,?_⟩
    · simpa using hi
    · intro j hj
      apply e.injective
      simpa using huniq (e j) hj
  chart := by intro i z; simp

def changeChart (P Q : Partition X) (e : P.index ≃ Q.index) : group (Γ:=Γ) (X:=X) :=
  ⟨P.mapPerm Q e,(mem_group_iff_table _).mpr ⟨P.mapTable Q e⟩⟩

@[simp] lemma changeChart_apply (P Q : Partition X) (e : P.index ≃ Q.index)
    (i : P.index) (z : Cube X) :
    (P.changeChart (Γ:=Γ) Q e).val ((P.brick i).attach z)=(Q.brick (e i)).attach z :=
  P.mapPerm_attach Q e i z

end Partition

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Separate coordinate twists on the components of a disjoint union of cubes. -/
def componentTwist {I : Type} : (I → Γ) →* Equiv.Perm (I × Cube X) where
  toFun a := {
    toFun := fun iz => (iz.1,twist (a iz.1) iz.2)
    invFun := fun iz => (iz.1,twist (a iz.1)⁻¹ iz.2)
    left_inv := by intro ⟨i,z⟩; simp
    right_inv := by intro ⟨i,z⟩; simp }
  map_one' := by
    apply Equiv.ext
    intro ⟨i,z⟩
    change (i,twist (1 : Γ) z)=(i,z)
    simp
  map_mul' a b := by
    apply Equiv.ext
    intro ⟨i,z⟩
    exact Prod.ext rfl (twist_twist _ _ _).symm

def decoratePerm (P : Partition X) : (P.index → Γ) →* Equiv.Perm (Cube X) :=
  P.coordinateEquiv.permCongrHom.toMonoidHom.comp componentTwist

@[simp] lemma decoratePerm_attach (P : Partition X) (a : P.index → Γ) (i : P.index)
    (z : Cube X) :
    decoratePerm P a ((P.brick i).attach z)=(P.brick i).attach (twist (a i) z) := by
  change P.coordinateEquiv.permCongr (componentTwist a) ((P.brick i).attach z)=_
  simp [Equiv.permCongr,Equiv.equivCongr,componentTwist]

def decorateTable (P : Partition X) (a : P.index → Γ) : Table (Γ:=Γ) (decoratePerm P a) where
  index := P.index
  finite := P.finite
  source := P.brick
  target := P.brick
  label := a
  source_cover := P.cover
  target_cover := P.cover
  chart := decoratePerm_attach P a

/-- A direct product of local coordinate copies of the acting group. -/
def decorate (P : Partition X) : (P.index → Γ) →* group (Γ:=Γ) (X:=X) :=
  (decoratePerm P).codRestrict _ (fun a => (mem_group_iff_table _).mpr ⟨decorateTable P a⟩)

@[simp] lemma decorate_val (P : Partition X) (a : P.index → Γ) :
    (decorate P a).val=decoratePerm P a := rfl

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma localizePerm_conj {p q : Prefix X} (h : Equiv.Perm (Cube X))
    (hh : ∀ z,h (p.attach z)=q.attach z) (f : Equiv.Perm (Cube X)) :
    h * localizePerm p f * h⁻¹=localizePerm q f := by
  apply Equiv.ext
  intro z
  change h (localizePerm p f (h.symm z))=localizePerm q f z
  by_cases hz : z∈Set.range q.attach
  · obtain ⟨w,rfl⟩ := hz
    have hi : h.symm (q.attach w)=p.attach w := by rw [← hh,h.symm_apply_apply]
    rw [hi,localizePerm_attach,hh,localizePerm_attach]
  · have hp : h.symm z∉Set.range p.attach := by
      rintro ⟨w,hw⟩
      apply hz
      refine ⟨w,?_⟩
      rw [← hh,hw,h.apply_symm_apply]
    rw [localizePerm_outside _ _ hp,localizePerm_outside _ _ hz,h.apply_symm_apply]

lemma localize_conj {p q : Prefix X} (h : group (Γ:=Γ) (X:=X))
    (hh : ∀ z,h.val (p.attach z)=q.attach z) (f : group (Γ:=Γ) (X:=X)) :
    h * localize p f * h⁻¹=localize q f :=
  Subtype.ext (localizePerm_conj h.val hh f.val)

end

section
universe u v
attribute [local instance] Classical.propDecidable
open scoped commutatorElement
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Partition

/-- Simultaneously refine every brick by the same finite partition. -/
abbrev allRefine (P Q : Partition X) : Partition X where
  index := P.index × Q.index
  finite := by letI := P.finite; letI := Q.finite; exact inferInstance
  brick ij := (P.brick ij.1).comp (Q.brick ij.2)
  cover z := by
    obtain ⟨i,⟨w,hw⟩,hi⟩ := P.cover z
    obtain ⟨j,⟨a,ha⟩,hj⟩ := Q.cover w
    refine ⟨(i,j),⟨a,?_⟩,?_⟩
    · rw [Prefix.comp_attach,ha,hw]
    · rintro ⟨k,l⟩ ⟨b,hb⟩
      rw [Prefix.comp_attach] at hb
      have hki : k=i := hi k ⟨(Q.brick l).attach b,hb⟩
      subst k
      have hl : l=j := hj l ⟨b,(P.brick i).attach_injective (hb.trans hw.symm)⟩
      exact Prod.ext rfl hl

/-- Permute all members of a partition, preserving their cube tails. -/
def permute (P : Partition X) : Equiv.Perm P.index →* group (Γ:=Γ) (X:=X) where
  toFun e := P.changeChart P e
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := P.cover z
    exact P.changeChart_apply P 1 i w
  map_mul' e f := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := P.cover z
    change (P.changeChart (Γ:=Γ) P (e*f)).val ((P.brick i).attach w)=
      (P.changeChart (Γ:=Γ) P e).val ((P.changeChart (Γ:=Γ) P f).val ((P.brick i).attach w))
    simp only [changeChart_apply,Equiv.Perm.mul_apply]

@[simp] lemma permute_attach (P : Partition X) (e : Equiv.Perm P.index)
    (i : P.index) (z : Cube X) :
    (P.permute (Γ:=Γ) e).val ((P.brick i).attach z)=(P.brick (e i)).attach z :=
  P.changeChart_apply P e i z

end Partition

end

section
universe u v
attribute [local instance] Classical.propDecidable
open scoped commutatorElement
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

@[simp] lemma localize_empty (f : group (Γ:=Γ) (X:=X)) : localize Prefix.empty f=f := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  change localizePerm Prefix.empty f.val z=f.val z
  simpa only [Prefix.empty_attach] using localizePerm_attach Prefix.empty f.val z

end

universe u v
attribute [local instance] Classical.propDecidable

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Trees
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Coordinate grids, binary trees, and tree-pair representatives.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma extends_of_compatible_of_length_le {p q : Prefix X} (h : p.Compatible q)
    (hl : ∀ x,(p.word x).length≤(q.word x).length) : p.Extends q := by
  intro x
  have hp := (mem_range_iff p _).mp (commonPoint_mem_left h) x
  have hq := (mem_range_iff q _).mp (commonPoint_mem_right h) x
  rw [← hp,← hq]
  exact Stream'.take_prefix_take_left _ _ _ (hl x)

/-- A finite list of splitting coordinates can dominate any finite prefix. -/
lemma exists_length_bound (p : Prefix X) :
    ∃ l : List X, ∀ x,(p.word x).length≤l.count x := by
  classical
  let S := p.finite_support.toFinset
  let l := S.toList.flatMap (fun x => List.replicate (p.word x).length x)
  refine ⟨l,?_⟩
  intro x
  by_cases hx : p.word x=[]
  · simp [hx]
  · have hxS : x∈S.toList := by simpa [S] using hx
    have hc := count_flatMap_ge (fun x => List.replicate (p.word x).length x) S.toList hxS x
    simpa using hc

end Prefix
namespace Partition
variable {X : Type v}

/-- Repeated simultaneous bisections, recording all colours with multiplicity.
This is a genuine finite forest partition, not an assumed normal form. -/
abbrev grid : List X → Partition X
  | [] => trivial
  | x::l => (bit x).allRefine (grid l)

@[simp] lemma grid_length (l : List X) (i : (grid l).index) (x : X) :
    (((grid l).brick i).word x).length = l.count x := by
  classical
  induction l with
  | nil => simp [grid,trivial,Prefix.empty]
  | cons y l ih =>
      change ((Prefix.oneBit y i.1).word x ++ ((grid l).brick i.2).word x).length = _
      rw [List.length_append,ih]
      by_cases hxy : x=y
      · subst y; simp [Nat.add_comm]
      · simp [hxy,Ne.symm hxy]

end Partition
end

section
universe u v
attribute [local instance] Classical.propDecidable

namespace Prefix
variable {X : Type v}
@[simp] lemma empty_comp (p : Prefix X) : empty.comp p=p := by ext x; simp [empty]
@[simp] lemma comp_empty (p : Prefix X) : p.comp empty=p := by ext x; simp [empty]
lemma comp_assoc (p q r : Prefix X) : (p.comp q).comp r=p.comp (q.comp r) := by
  ext x; simp [List.append_assoc]
end Prefix
namespace Tree
variable {X : Type v}

def brick : (t : Tree X) → t.Leaves → Prefix X
  | .leaf,_ => Prefix.empty
  | .split x a _,Sum.inl i => (Prefix.oneBit x false).comp (brick a i)
  | .split x _ b,Sum.inr j => (Prefix.oneBit x true).comp (brick b j)

lemma cover (t : Tree X) : ∀ z : Cube X,∃! i : t.Leaves, ∃ w,(t.brick i).attach w=z := by
  induction t with
  | leaf => exact Partition.trivial.cover
  | split x a b ha hb =>
    intro z
    obtain ⟨c,⟨w,hw⟩,hc⟩ := (Partition.bit x).cover z
    cases c with
    | false =>
      obtain ⟨i,⟨v,hv⟩,hi⟩ := ha w
      refine ⟨Sum.inl i,⟨v,?_⟩,?_⟩
      · change ((Prefix.oneBit x false).comp (a.brick i)).attach v=z
        rw [Prefix.comp_attach,hv,hw]
      · intro j hj
        cases j with
        | inl j =>
          obtain ⟨r,hr⟩ := hj
          rw [brick,Prefix.comp_attach] at hr
          exact congrArg Sum.inl (hi j ⟨r,(Prefix.oneBit x false).attach_injective (hr.trans hw.symm)⟩)
        | inr j =>
          obtain ⟨r,hr⟩ := hj
          have he : true=false := hc true ⟨(b.brick j).attach r,(Prefix.comp_attach _ _ _).symm.trans hr⟩
          cases he
    | true =>
      obtain ⟨i,⟨v,hv⟩,hi⟩ := hb w
      refine ⟨Sum.inr i,⟨v,?_⟩,?_⟩
      · change ((Prefix.oneBit x true).comp (b.brick i)).attach v=z
        rw [Prefix.comp_attach,hv,hw]
      · intro j hj
        cases j with
        | inl j =>
          obtain ⟨r,hr⟩ := hj
          have he : false=true := hc false ⟨(a.brick j).attach r,(Prefix.comp_attach _ _ _).symm.trans hr⟩
          cases he
        | inr j =>
          obtain ⟨r,hr⟩ := hj
          rw [brick,Prefix.comp_attach] at hr
          exact congrArg Sum.inr (hi j ⟨r,(Prefix.oneBit x true).attach_injective (hr.trans hw.symm)⟩)

abbrev partition (t : Tree X) : Partition X where
  index := t.Leaves
  finite := leaves_fintype t
  brick := t.brick
  cover := t.cover

def grid : List X → Tree X
  | [] => .leaf
  | x::l => .split x (grid l) (grid l)

@[simp] lemma grid_length (l : List X) (i : (grid l).Leaves) (x : X) :
    (((grid l).brick i).word x).length=l.count x := by
  classical
  induction l with
  | nil => simp [grid,brick,Prefix.empty]
  | cons y l ih =>
    cases i with
    | inl i =>
      change ((Prefix.oneBit y false).word x ++ ((grid l).brick i).word x).length=_
      rw [List.length_append,ih]
      by_cases hxy : x=y
      · subst y; simp [Nat.add_comm]
      · simp [hxy,Ne.symm hxy]
    | inr i =>
      change ((Prefix.oneBit y true).word x ++ ((grid l).brick i).word x).length=_
      rw [List.length_append,ih]
      by_cases hxy : x=y
      · subst y; simp [Nat.add_comm]
      · simp [hxy,Ne.symm hxy]

def graft : (t : Tree X) → (t.Leaves → Tree X) → Tree X
  | .leaf,f => f PUnit.unit
  | .split x a b,f => .split x (graft a (fun i => f (Sum.inl i))) (graft b (fun i => f (Sum.inr i)))

def graftLeaves : (t : Tree X) → (f : t.Leaves → Tree X) →
    (t.graft f).Leaves ≃ (i : t.Leaves) × (f i).Leaves
  | .leaf,f => {
      toFun := fun j => ⟨PUnit.unit,j⟩
      invFun := fun ⟨PUnit.unit,j⟩ => j
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨i,j⟩; cases i; rfl }
  | .split x a b,f => {
      toFun := fun j => match j with
        | Sum.inl j => ⟨Sum.inl (((graftLeaves a (fun i => f (Sum.inl i))).toFun j).1),((graftLeaves a (fun i => f (Sum.inl i))).toFun j).2⟩
        | Sum.inr j => ⟨Sum.inr (((graftLeaves b (fun i => f (Sum.inr i))).toFun j).1),((graftLeaves b (fun i => f (Sum.inr i))).toFun j).2⟩
      invFun := fun ⟨i,j⟩ => match i with
        | Sum.inl i => Sum.inl ((graftLeaves a (fun i => f (Sum.inl i))).invFun ⟨i,j⟩)
        | Sum.inr i => Sum.inr ((graftLeaves b (fun i => f (Sum.inr i))).invFun ⟨i,j⟩)
      left_inv := by
        rintro (j|j)
        · exact congrArg Sum.inl ((graftLeaves a (fun i => f (Sum.inl i))).left_inv j)
        · exact congrArg Sum.inr ((graftLeaves b (fun i => f (Sum.inr i))).left_inv j)
      right_inv := by
        rintro ⟨i,j⟩
        cases i with
        | inl i =>
          exact congrArg (fun z : (i : a.Leaves) × (f (Sum.inl i)).Leaves =>
            (⟨Sum.inl z.1,z.2⟩ : (i : (split x a b).Leaves) × (f i).Leaves))
            ((graftLeaves a (fun i => f (Sum.inl i))).right_inv ⟨i,j⟩)
        | inr i =>
          exact congrArg (fun z : (i : b.Leaves) × (f (Sum.inr i)).Leaves =>
            (⟨Sum.inr z.1,z.2⟩ : (i : (split x a b).Leaves) × (f i).Leaves))
            ((graftLeaves b (fun i => f (Sum.inr i))).right_inv ⟨i,j⟩) }

lemma graft_prefix (t : Tree X) (f : t.Leaves → Tree X) (j : (t.graft f).Leaves) :
    (t.graft f).brick j=(t.brick (t.graftLeaves f j).1).comp ((f (t.graftLeaves f j).1).brick (t.graftLeaves f j).2) := by
  induction t with
  | leaf =>
      change (f PUnit.unit).brick j=Prefix.empty.comp ((f PUnit.unit).brick j)
      exact (Prefix.empty_comp _).symm
  | split x a b ha hb =>
    cases j with
    | inl j =>
      change (Prefix.oneBit x false).comp ((a.graft _).brick j)=_
      rw [ha]
      exact (Prefix.comp_assoc _ _ _).symm
    | inr j =>
      change (Prefix.oneBit x true).comp ((b.graft _).brick j)=_
      rw [hb]
      exact (Prefix.comp_assoc _ _ _).symm

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma eq_of_compatible_of_length_eq {p q : Prefix X} (h : p.Compatible q)
    (hl : ∀ x,(p.word x).length=(q.word x).length) : p=q := by
  apply ext
  intro x
  exact (((extends_of_compatible_of_length_le h (fun x => (hl x).le)) x)).eq_of_length (hl x)

def schedule (p : Prefix X) : List X :=
  p.finite_support.toFinset.toList.flatMap (fun x => List.replicate (p.word x).length x)

@[simp] lemma schedule_count (p : Prefix X) (x : X) :
    p.schedule.count x=(p.word x).length := by
  classical
  rw [schedule,count_repeated_nodup _ (Finset.nodup_toList _)]
  by_cases hx : p.word x=[] <;> simp [hx]

end Prefix
namespace Partition
variable {X : Type v}

lemma brick_injective (P : Partition X) : Function.Injective P.brick := by
  intro i j he
  let z := (P.brick i).attach (fun _ _ => false)
  obtain ⟨k,hk,hu⟩ := P.cover z
  exact (hu i ⟨(fun _ _ => false),rfl⟩).trans
    (hu j ⟨(fun _ _ => false),by rw [← he]⟩).symm

def indexEquivOfBricks (P Q : Partition X)
    (h : ∀ i,∃ j,P.brick i=Q.brick j) : P.index ≃ Q.index :=
  Equiv.ofBijective (fun i => (h i).choose) (by
    constructor
    · intro i j hij
      apply P.brick_injective
      exact (h i).choose_spec.trans ((congrArg Q.brick hij).trans (h j).choose_spec.symm)
    · intro j
      let z := (Q.brick j).attach (fun _ _ => false)
      obtain ⟨i,hi,hu⟩ := P.cover z
      have hk : ∃ w,(Q.brick (h i).choose).attach w=z := by
        rw [← (h i).choose_spec]; exact hi
      obtain ⟨k,hk',hu'⟩ := Q.cover z
      exact ⟨i,(hu' _ hk).trans (hu' j ⟨_,rfl⟩).symm⟩)

lemma indexEquivOfBricks_spec (P Q : Partition X) (h : ∀ i,∃ j,P.brick i=Q.brick j) (i : P.index) :
    P.brick i=Q.brick (P.indexEquivOfBricks Q h i) := (h i).choose_spec

lemma exists_tree_grid_bound {I : Type} [Fintype I] (p : I → Prefix X) :
    ∃ l : List X,∀ i x,((p i).word x).length≤l.count x := by
  classical
  choose l hl using fun i => (p i).exists_length_bound
  refine ⟨Finset.univ.toList.flatMap l,?_⟩
  intro i x
  exact (hl i x).trans (Prefix.count_flatMap_ge l Finset.univ.toList (by simp) x)

lemma grid_bricks_of_lengths (P : Partition X) (l : List X)
    (hl : ∀ i x,((P.brick i).word x).length=l.count x) :
    ∀ i,∃ j,P.brick i=(Tree.grid l).brick j := by
  intro i
  let z := (P.brick i).attach (fun _ _ => false)
  obtain ⟨j,hj,_⟩ := (Tree.grid l).cover z
  refine ⟨j,Prefix.eq_of_compatible_of_length_eq ⟨z,⟨_,rfl⟩,hj⟩ ?_⟩
  intro x
  rw [hl,Tree.grid_length]

end Partition
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Generators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Concrete finite generators of the twisted group.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators

abbrev left (x : X) := Prefix.oneBit x false
abbrev right (x : X) := Prefix.oneBit x true

def associator (x : X) : group (Γ:=Γ) (X:=X) :=
  (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition.changeChart
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm

def flip (x : X) : group (Γ:=Γ) (X:=X) :=
  (Partition.bit x).permute Equiv.boolNot

lemma flip_left (x : X) (z : Cube X) :
    (flip (Γ:=Γ) x).val ((left x).attach z)=(right x).attach z :=
  (Partition.bit x).permute_attach Equiv.boolNot false z

/-- Four untwisted elements, together with the root and one half-copy of the
acting group. This is an explicitly finitely generated subgroup when Γ is FG. -/
def finiteSet (x : X) : Finset (group (Γ:=Γ) (X:=X)) :=
  {associator x,localize (left x) (associator x),flip x,localize (left x) (flip x)}

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

@[simp] lemma twistPrefix_oneBit (g : Γ) (x : X) (b : Bool) :
    twistPrefix g (Prefix.oneBit x b)=Prefix.oneBit (g • x) b := by
  ext y
  simp only [twistPrefix_word,Prefix.oneBit_word,inv_smul_eq_iff]

namespace Generators
/-- The untwisted coordinate baker: move a leading bit from x to y. -/
def baker (x y : X) : group (Γ:=Γ) (X:=X) :=
  (Partition.bit x).changeChart (Partition.bit y) (Equiv.refl Bool)

@[simp] lemma baker_attach (x y : X) (b : Bool) (z : Cube X) :
    (baker (Γ:=Γ) x y).val ((Prefix.oneBit x b).attach z)=
      (Prefix.oneBit y b).attach z :=
  (Partition.bit x).changeChart_apply (Partition.bit y) (Equiv.refl Bool) b z

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma oneBit_outside (x : X) {a b : Bool} (hab : a≠b) (z : Cube X) :
    (Prefix.oneBit x a).attach z∉Set.range (Prefix.oneBit x b).attach := by
  intro h
  exact hab (((Prefix.mem_oneBit x a _).mp ⟨z,rfl⟩).symm.trans
    ((Prefix.mem_oneBit x b _).mp h))

def sumElement (y : X) (g h : group (Γ:=Γ) (X:=X)) : group (Γ:=Γ) (X:=X) :=
  localize (Prefix.oneBit y false) g * localize (Prefix.oneBit y true) h

@[simp] lemma sumElement_left (y : X) (g h : group (Γ:=Γ) (X:=X)) (z : Cube X) :
    (sumElement y g h).val ((Prefix.oneBit y false).attach z)=
      (Prefix.oneBit y false).attach (g.val z) := by
  change localizePerm (Prefix.oneBit y false) g.val
    (localizePerm (Prefix.oneBit y true) h.val ((Prefix.oneBit y false).attach z))=_
  rw [localizePerm_outside _ _ (oneBit_outside y Bool.false_ne_true z),localizePerm_attach]

@[simp] lemma sumElement_right (y : X) (g h : group (Γ:=Γ) (X:=X)) (z : Cube X) :
    (sumElement y g h).val ((Prefix.oneBit y true).attach z)=
      (Prefix.oneBit y true).attach (h.val z) := by
  change localizePerm (Prefix.oneBit y false) g.val
    (localizePerm (Prefix.oneBit y true) h.val ((Prefix.oneBit y true).attach z))=_
  rw [localizePerm_attach,localizePerm_outside _ _ (oneBit_outside y (Ne.symm Bool.false_ne_true) (h.val z))]

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators

variable (x : X) [MulAction.IsPretransitive Γ X]

omit [MulAction.IsPretransitive Γ X] in
@[simp] lemma flip_attach (x : X) (b : Bool) (z : Cube X) :
    (flip (Γ:=Γ) x).val ((Prefix.oneBit x b).attach z)=
      (Prefix.oneBit x (!b)).attach z :=
  (Partition.bit x).permute_attach Equiv.boolNot b z

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.FinitePresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentation seeds, localization, and structural relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

/-- An actual finitely presented source for the finite-table group. The two
copies of Γ map to the root and one half-cube, and the free factor maps to the
four explicit untwisted generators. Its quotient kernel is a construction,
not an extra main-theorem hypothesis. -/
def Seed := Monoid.Coprod (Monoid.Coprod Γ Γ)
  (FreeGroup (finiteSet (Γ:=Γ) x))

instance instGroupSeed : Group (Seed (Γ:=Γ) x) :=
  inferInstanceAs (Group (Monoid.Coprod (Monoid.Coprod Γ Γ)
    (FreeGroup (finiteSet (Γ:=Γ) x))))

def evaluation : Seed (Γ:=Γ) x →* group (Γ:=Γ) (X:=X) :=
  Monoid.Coprod.lift
    (Monoid.Coprod.lift embedding ((localize (left x)).comp embedding))
    (FreeGroup.lift (fun a : finiteSet (Γ:=Γ) x => a.val))

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Generators
variable (x : X)

def rootWord : Γ →* Seed (Γ:=Γ) x := Monoid.Coprod.inl.comp Monoid.Coprod.inl
def halfWord : Γ →* Seed (Γ:=Γ) x := Monoid.Coprod.inl.comp Monoid.Coprod.inr

def flipWord : Seed (Γ:=Γ) x :=
  Monoid.Coprod.inr (FreeGroup.of (⟨flip x,by simp [finiteSet]⟩ : finiteSet (Γ:=Γ) x))

def rightWord : Γ →* Seed (Γ:=Γ) x :=
  (MulAut.conj (flipWord (Γ:=Γ) x)).toMonoidHom.comp (halfWord x)

@[simp] lemma evaluation_rootWord (g : Γ) : evaluation (Γ:=Γ) x (rootWord x g)=embedding g := by
  rfl
@[simp] lemma evaluation_halfWord (g : Γ) :
    evaluation (Γ:=Γ) x (halfWord x g)=localize (left x) (embedding g) := by
  rfl
@[simp] lemma evaluation_flipWord : evaluation (Γ:=Γ) x (flipWord (Γ:=Γ) x)=flip x := by
  rfl
@[simp] lemma evaluation_rightWord (g : Γ) :
    evaluation (Γ:=Γ) x (rightWord x g)=localize (right x) (embedding g) := by
  change evaluation (Γ:=Γ) x (flipWord x * halfWord x g * (flipWord x)⁻¹)=_
  rw [map_mul,map_mul,map_inv,evaluation_flipWord,evaluation_halfWord]
  exact localize_conj (flip x) (flip_left x) (embedding g)

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

def generatorWord (g : finiteSet (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  Monoid.Coprod.inr (FreeGroup.of g)

@[simp] lemma evaluation_generatorWord (g : finiteSet (Γ:=Γ) x) :
    evaluation (Γ:=Γ) x (generatorWord x g)=g.val := by rfl

def associatorWord : Seed (Γ:=Γ) x :=
  generatorWord x ⟨associator x,by simp [finiteSet]⟩

@[simp] lemma evaluation_associatorWord :
    evaluation (Γ:=Γ) x (associatorWord (Γ:=Γ) x)=associator x := by rfl

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.TreeRefinement
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tree prefixes, common refinements, and quotient refinement relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe v
attribute [local instance] Classical.propDecidable
namespace Tree
variable {X : Type v}

def brickSet (t : Tree X) : Set (Prefix X) := Set.range t.brick

@[simp] lemma brickSet_leaf : brickSet (.leaf : Tree X)={Prefix.empty} := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩; rfl
  · intro hp; exact ⟨PUnit.unit,hp.symm⟩

@[simp] lemma brickSet_split (x : X) (a b : Tree X) :
    brickSet (.split x a b)=
      (Prefix.oneBit x false).comp '' brickSet a ∪
      (Prefix.oneBit x true).comp '' brickSet b := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨a.brick i,⟨i,rfl⟩,rfl⟩
    | inr i => exact Or.inr ⟨b.brick i,⟨i,rfl⟩,rfl⟩
  · rintro (⟨q,⟨i,rfl⟩,rfl⟩|⟨q,⟨i,rfl⟩,rfl⟩)
    · exact ⟨Sum.inl i,rfl⟩
    · exact ⟨Sum.inr i,rfl⟩

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Tree
variable {X : Type v}

def mapColors (f : X → X) : Tree X → Tree X
  | .leaf => .leaf
  | .split x a b => .split (f x) (mapColors f a) (mapColors f b)

@[simp] lemma mapColors_id (t : Tree X) : mapColors id t=t := by
  induction t with
  | leaf => rfl
  | split x a b ha hb => simp [mapColors,ha,hb]

end Tree
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.EndpointCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Associators, symmetries, coordinate invariance, and coherence of endpoint quotient data.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

universe u v w
attribute [local instance] Classical.propDecidable

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma twistPrefix_comp (g : Γ) (p q : Prefix X) :
    twistPrefix g (p.comp q)=(twistPrefix g p).comp (twistPrefix g q) := by
  ext x; rfl

@[simp] lemma twistPrefix_empty (g : Γ) : twistPrefix g (Prefix.empty : Prefix X)=Prefix.empty := by
  ext x; rfl

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.TreeCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Decorated tree interpretation, grafting, leaf values, and common-refinement invariance.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

section
universe v
open BinaryGroupCategory
variable {X : Type v}

/-- Number of internal nodes, so that the number of leaves is `arity+1`. -/
abbrev arity : Tree X → ℕ
  | .leaf => 0
  | .split _ a b => arity a+arity b+1

/-- Left-to-right exact ordinal enumeration of the leaves. -/
def ordinal : (a : Tree X) → a.Leaves ≃ Fin (a.arity+1)
  | .leaf => {
      toFun := fun _=>0
      invFun := fun _=>PUnit.unit
      left_inv := by rintro ⟨⟩; rfl
      right_inv := by intro i; apply Fin.ext; have hi := i.isLt; change (i:ℕ)<1 at hi; change 0=(i:ℕ); omega }
  | .split _ a b => (Equiv.sumCongr (ordinal a) (ordinal b)).trans (sumIndex a.arity b.arity)

@[simp] lemma ordinal_leaf (i : (.leaf : Tree X).Leaves) : ordinal .leaf i=0 := rfl
@[simp] lemma ordinal_left (x:X) (a b:Tree X) (i:a.Leaves) :
    ordinal (.split x a b) (Sum.inl i)=sumIndex a.arity b.arity (Sum.inl (ordinal a i)) := rfl
@[simp] lemma ordinal_right (x:X) (a b:Tree X) (i:b.Leaves) :
    ordinal (.split x a b) (Sum.inr i)=sumIndex a.arity b.arity (Sum.inr (ordinal b i)) := rfl

def ordinalEquiv {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Fin (a.arity+1) ≃ Fin (b.arity+1) :=
  (ordinal a).symm.trans (e.trans (ordinal b))

@[simp] lemma ordinalEquiv_apply {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (i:a.Leaves) :
    ordinalEquiv e (ordinal a i)=ordinal b (e i) := by simp [ordinalEquiv]

lemma ordinalEquiv_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves) :
    ordinalEquiv (e.trans f)=(ordinalEquiv e).trans (ordinalEquiv f) := by
  apply Equiv.ext; intro i
  simp [ordinalEquiv]

lemma ordinalEquiv_sum {a b c e:Tree X} (x y:X) (f:a.Leaves ≃ c.Leaves) (g:b.Leaves ≃ e.Leaves) :
    ordinalEquiv (a:=.split x a b) (b:=.split y c e) (Equiv.sumCongr f g)=
      sumEquiv (ordinalEquiv f) (ordinalEquiv g) := by
  apply Equiv.ext; intro i
  obtain ⟨j,rfl⟩ := (ordinal (.split x a b)).surjective i
  cases j <;> simp only [ordinalEquiv,ordinal,Equiv.trans_apply,Equiv.sumCongr_symm,
    Equiv.symm_trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,sumEquiv_left,sumEquiv_right]

lemma ordinalEquiv_exchange {a b:Tree X} (x y:X) :
    ordinalEquiv (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _)=
      exchangeEquiv a.arity b.arity := by
  apply Equiv.ext; intro i
  obtain ⟨j,rfl⟩ := (ordinal (.split x a b)).surjective i
  cases j <;> simp only [ordinalEquiv,ordinal,Equiv.trans_apply,Equiv.sumCongr_symm,
    Equiv.symm_trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
    Equiv.sumComm_apply,Sum.swap_inl,Sum.swap_inr,exchangeEquiv_left,exchangeEquiv_right]

end

section
universe v w
open BinaryGroupCategory
variable {X : Type v} {H : Type w} [Group H] (d : Data H) (q : SymmetryData d) (B : X → H)

/-- Interpret the split tree as a map from its ordered comb of leaves. -/
def flatten : Tree X → H
  | .leaf => 1
  | .split x a b => B x*d.tensor (flatten a,flatten b)*(merge d a.arity)⁻¹

/-- The actual groupoid interpretation of a whole permutation of leaves. -/
def leafValue {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : H :=
  flatten d B b * equivVal d q (ordinalEquiv e) * (flatten d B a)⁻¹

lemma leafValue_refl (a:Tree X) : leafValue d q B (Equiv.refl a.Leaves)=1 := by
  have he : ordinalEquiv (Equiv.refl a.Leaves)=Equiv.refl (Fin (a.arity+1)) := by
    apply Equiv.ext; intro i; simp [ordinalEquiv]
  rw [leafValue,he,equivVal_refl,mul_one,mul_inv_cancel]

lemma leafValue_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves) :
    leafValue d q B (e.trans f)=leafValue d q B f*leafValue d q B e := by
  rw [leafValue,ordinalEquiv_trans,equivVal_trans]
  dsimp only [leafValue]
  group

lemma leafValue_symm {a b:Tree X} (e:a.Leaves ≃ b.Leaves) :
    leafValue d q B e.symm=(leafValue d q B e)⁻¹ := by
  have hh := leafValue_trans d q B e e.symm
  rw [Equiv.self_trans_symm,leafValue_refl] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

lemma leafValue_sum {a b c e:Tree X} (x y:X) (f:a.Leaves ≃ c.Leaves) (g:b.Leaves ≃ e.Leaves) :
    leafValue d q B (a:=.split x a b) (b:=.split y c e) (Equiv.sumCongr f g)=
      B y*d.tensor (leafValue d q B f,leafValue d q B g)*(B x)⁻¹ := by
  rw [leafValue,ordinalEquiv_sum,equivVal_sum]
  dsimp only [flatten,leafValue,blockMap]
  have ht : d.tensor (flatten d B c * equivVal d q (ordinalEquiv f) * (flatten d B a)⁻¹,
      flatten d B e * equivVal d q (ordinalEquiv g) * (flatten d B b)⁻¹)=
      d.tensor (flatten d B c,flatten d B e)*
        d.tensor (equivVal d q (ordinalEquiv f),equivVal d q (ordinalEquiv g))*
          (d.tensor (flatten d B a,flatten d B b))⁻¹ := by
    rw [← map_inv,← map_mul,← map_mul]; rfl
  rw [ht]; group

lemma leafValue_exchange {a b:Tree X} (x y:X) :
    leafValue d q B (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _)=
      B y*q.c*(B x)⁻¹ := by
  rw [leafValue,ordinalEquiv_exchange,equivVal_exchange]
  dsimp only [flatten]
  have hn := q.naturality (flatten d B a) (flatten d B b)
  calc
    _=B y*d.tensor (flatten d B b,flatten d B a)*q.c*
        (d.tensor (flatten d B a,flatten d B b))⁻¹*(B x)⁻¹ := by group
    _=_ := by rw [← hn]; group

lemma equivVal_ordinal_assoc (x y z w:X) (a b c:Tree X) :
    equivVal d q (ordinalEquiv (a:=.split x (.split y a b) c)
      (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _))=1 := by
  apply equivVal_order
  intro i
  obtain ⟨j,rfl⟩ := (ordinal (.split x (.split y a b) c)).surjective i
  rw [ordinalEquiv_apply]
  rcases j with (j|j)|j <;>
    simp only [Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,
      Equiv.sumAssoc_apply_inr,ordinal,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
      sumIndex_left_val,sumIndex_right_val,arity]
  omega

lemma flatten_assoc (x y z w:X) (a b c:Tree X) :
    flatten d B (.split z a (.split w b c)) =
      (B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹)*
        flatten d B (.split x (.split y a b) c) := by
  let fa := flatten d B a
  let fb := flatten d B b
  let fc := flatten d B c
  have hT (l m n r:H) : d.tensor (l*m,n*r)=d.tensor (l,n)*d.tensor (m,r) :=
    d.tensor.map_mul (l,n) (m,r)
  have hR : d.tensor (fa,B w*d.tensor (fb,fc)*(merge d b.arity)⁻¹)=
      d.tensor (1,B w)*d.tensor (fa,d.tensor (fb,fc))*(right d (merge d b.arity))⁻¹ := by
    dsimp only [right,left,MonoidHom.coe_mk,OneHom.coe_mk]
    rw [← map_inv,← map_mul,← map_mul]
    simp only [Prod.inv_mk,Prod.mk_mul_mk,inv_one,one_mul,mul_one]
  have hL : d.tensor (B y*d.tensor (fa,fb)*(merge d a.arity)⁻¹,fc)=
      d.tensor (B y,1)*d.tensor (d.tensor (fa,fb),fc)*(left d (merge d a.arity))⁻¹ := by
    dsimp only [right,left,MonoidHom.coe_mk,OneHom.coe_mk]
    rw [← map_inv,← map_mul,← map_mul]
    simp only [Prod.inv_mk,Prod.mk_mul_mk,inv_one,one_mul,mul_one]
  change B z*d.tensor (fa,B w*d.tensor (fb,fc)*(merge d b.arity)⁻¹)*(merge d a.arity)⁻¹ =
    (B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹)*
      (B x*d.tensor (B y*d.tensor (fa,fb)*(merge d a.arity)⁻¹,fc)*
        (merge d (a.arity+b.arity+1))⁻¹)
  rw [hR,hL,← d.naturality fa fb fc]
  have hm := merge_coherence d a.arity b.arity
  calc
    _ = B z*d.tensor (1,B w)*d.tensor (fa,d.tensor (fb,fc))*
      d.a⁻¹*(merge d a.arity*right d (merge d b.arity)*d.a⁻¹)⁻¹ := by group
    _ = _ := by rw [← hm]; group

lemma leafValue_assoc (x y z w:X) (a b c:Tree X) :
    leafValue d q B (a:=.split x (.split y a b) c)
      (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _)=
      B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹ := by
  rw [leafValue,equivVal_ordinal_assoc,mul_one,flatten_assoc d B x y z w a b c]
  group

end

section
universe v
open BinaryGroupCategory
variable {X : Type v}

/-- Structural routes made only from tensor, associativity and exchange.
The arbitrary-permutation completeness theorem below is proved, not a constructor. -/
inductive Route : {a b:Tree X} → (a.Leaves ≃ b.Leaves) → Prop
  | refl (a) : Route (a:=a) (b:=a) (Equiv.refl _)
  | trans {a b c:Tree X} {e:a.Leaves ≃ b.Leaves} {f:b.Leaves ≃ c.Leaves} :
      Route e → Route f → Route (e.trans f)
  | symm {a b:Tree X} {e:a.Leaves ≃ b.Leaves} : Route e → Route e.symm
  | sum {a b c d:Tree X} (x y) {e:a.Leaves ≃ c.Leaves} {f:b.Leaves ≃ d.Leaves} :
      Route e → Route f → Route (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f)
  | assoc (x y z w) (a b c) : Route (a:=.split x (.split y a b) c)
      (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _)
  | exchange (x y) (a b) : Route (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _)

def Ordered {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Prop :=
  ∀ i,(ordinal b (e i):ℕ)=ordinal a i

lemma Ordered.trans {a b c:Tree X} {e:a.Leaves ≃ b.Leaves} {f:b.Leaves ≃ c.Leaves}
    (he:Ordered e) (hf:Ordered f) : Ordered (e.trans f) := fun i=>(hf (e i)).trans (he i)

lemma Ordered.arity {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (_he:Ordered e) : a.arity=b.arity :=
  equiv_size (ordinalEquiv e)

lemma Ordered.sum {a b c d:Tree X} (x y:X) {e:a.Leaves ≃ c.Leaves} {f:b.Leaves ≃ d.Leaves}
    (he:Ordered e) (hf:Ordered f) :
    Ordered (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) := by
  rintro (i|i) <;> simp only [ordinal,Equiv.sumCongr_apply,Equiv.trans_apply,Sum.map_inl,Sum.map_inr,
    sumIndex_left_val,sumIndex_right_val]
  · exact he i
  · rw [hf i,he.arity]

lemma ordered_assoc (x y z w:X) (a b c:Tree X) :
    Ordered (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) := by
  rintro ((i|i)|i) <;> simp only [Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,
    Equiv.sumAssoc_apply_inr,ordinal,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
    sumIndex_left_val,sumIndex_right_val,arity]
  omega

abbrev comb (x:X) : ℕ → Tree X
  | 0 => .leaf
  | n+1 => .split x .leaf (comb x n)

@[simp] lemma arity_comb (x:X) (n:ℕ) : (comb x n).arity=n := by
  induction n with
  | zero => rfl
  | succ n ih => change 0+(comb x n).arity+1=n+1; rw [ih,Nat.zero_add]

lemma route_merge (x:X) (m n:ℕ) :
    ∃ e:(Tree.split x (comb x m) (comb x n)).Leaves ≃ (comb x (m+n+1)).Leaves,
      Route e ∧ Ordered e := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    exact ⟨Equiv.refl _,Route.refl _,fun _=>rfl⟩
  | succ m ih =>
    obtain ⟨e,he,hoe⟩ := ih
    have h : ∃ f:(Tree.split x (.split x .leaf (comb x m)) (comb x n)).Leaves ≃
        (Tree.split x .leaf (comb x (m+n+1))).Leaves,Route f ∧ Ordered f := by
      refine ⟨(Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) e),
        (Route.assoc x x x x .leaf _ _).trans (Route.sum x x (Route.refl .leaf) he),?_⟩
      exact (ordered_assoc x x x x .leaf _ _).trans (Ordered.sum x x (fun _=>rfl) hoe)
    rw [show (m+1)+n+1=(m+n+1)+1 by omega]
    exact h

lemma route_normal (x:X) (a:Tree X) :
    ∃ e:a.Leaves ≃ (comb x a.arity).Leaves,Route e ∧ Ordered e := by
  induction a with
  | leaf => exact ⟨Equiv.refl _,Route.refl _,fun _=>rfl⟩
  | split y a b ha hb =>
    obtain ⟨ea,hea,hoa⟩ := ha
    obtain ⟨eb,heb,hob⟩ := hb
    obtain ⟨em,hem,hom⟩ := route_merge x a.arity b.arity
    exact ⟨(Equiv.sumCongr ea eb).trans em,
      (Route.sum y x hea heb).trans hem,(Ordered.sum y x hoa hob).trans hom⟩

def combIndex (x:X) (n:ℕ) : (comb x n).Leaves ≃ Fin (n+1) :=
  (ordinal (comb x n)).trans (finCongr (congrArg (fun k=>k+1) (arity_comb x n)))

@[simp] lemma combIndex_left (x:X) (n:ℕ) (i:PUnit) :
    (combIndex x (n+1) (Sum.inl i):ℕ)=0 := rfl
@[simp] lemma combIndex_right (x:X) (n:ℕ) (i:(comb x n).Leaves) :
    (combIndex x (n+1) (Sum.inr i):ℕ)=1+(combIndex x n i:ℕ) := rfl

/-- Conjugate an ordinal permutation to the exact leaves of the comb. -/
def combPerm (x:X) (n:ℕ) (p:Equiv.Perm (Fin (n+1))) : Equiv.Perm (comb x n).Leaves :=
  (combIndex x n).trans (p.trans (combIndex x n).symm)

@[simp] lemma combIndex_perm (x:X) (n:ℕ) (p:Equiv.Perm (Fin (n+1))) (i:(comb x n).Leaves) :
    combIndex x n (combPerm x n p i)=p (combIndex x n i) := by simp [combPerm]

lemma combPerm_one (x:X) (n:ℕ) : combPerm x n 1=Equiv.refl _ := by
  apply Equiv.ext; intro i; simp [combPerm]
lemma combPerm_mul (x:X) (n:ℕ) (p r:Equiv.Perm (Fin (n+1))) :
    combPerm x n (p*r)=(combPerm x n r).trans (combPerm x n p) := by
  apply Equiv.ext; intro i; simp [combPerm]

lemma route_comb_adjacent (x:X) (n:ℕ) (i:Fin n) :
    Route (a:=comb x n) (b:=comb x n) (combPerm x n (Equiv.swap i.castSucc i.succ)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i=>?_) i
    · cases n with
      | zero =>
        have he : combPerm x 1 (Equiv.swap (0:Fin 1).castSucc (0:Fin 1).succ)=Equiv.sumComm PUnit PUnit := by
          apply Equiv.ext; intro j
          apply (combIndex x 1).injective
          apply Fin.ext
          rw [combIndex_perm]
          rcases j with ⟨⟩|⟨⟩ <;> rfl
        rw [he]
        exact Route.exchange x x .leaf .leaf
      | succ n =>
        let e : Equiv.Perm (comb x (n+2)).Leaves :=
          (Equiv.sumAssoc PUnit PUnit (comb x n).Leaves).symm.trans
            ((Equiv.sumCongr (Equiv.sumComm PUnit PUnit) (Equiv.refl _)).trans
              (Equiv.sumAssoc PUnit PUnit (comb x n).Leaves))
        have he : combPerm x (n+2) (Equiv.swap (0:Fin (n+2)).castSucc (0:Fin (n+2)).succ)=e := by
          apply Equiv.ext; intro j
          apply (combIndex x (n+2)).injective
          apply Fin.ext
          rw [combIndex_perm]
          rcases j with ⟨⟩|(⟨⟩|j)
          · rfl
          · rfl
          · have hj : combIndex x (n+2) (Sum.inr (Sum.inr j)) ≠ (0:Fin (n+2)).castSucc := by
              intro h; have h' := congrArg Fin.val h
              change 1+(1+(combIndex x n j:ℕ))=0 at h'; omega
            have hj' : combIndex x (n+2) (Sum.inr (Sum.inr j)) ≠ (0:Fin (n+2)).succ := by
              intro h; have h' := congrArg Fin.val h
              change 1+(1+(combIndex x n j:ℕ))=1 at h'; omega
            rw [Equiv.swap_apply_of_ne_of_ne hj hj']
            rfl
        rw [he]
        exact (Route.assoc x x x x .leaf .leaf (comb x n)).symm.trans
          ((Route.sum x x (Route.exchange x x .leaf .leaf) (Route.refl (comb x n))).trans
            (Route.assoc x x x x .leaf .leaf (comb x n)))
    · let e := Equiv.sumCongr (Equiv.refl PUnit) (combPerm x n (Equiv.swap i.castSucc i.succ))
      have he : combPerm x (n+1) (Equiv.swap i.succ.castSucc i.succ.succ)=e := by
        apply Equiv.ext; intro j
        apply (combIndex x (n+1)).injective
        apply Fin.ext
        rw [combIndex_perm]
        rcases j with ⟨⟩|j
        · have h₁ : combIndex x (n+1) (Sum.inl PUnit.unit) ≠ i.succ.castSucc := by
            intro h; have h' := congrArg Fin.val h
            change 0=(i:ℕ)+1 at h'; omega
          have h₂ : combIndex x (n+1) (Sum.inl PUnit.unit) ≠ i.succ.succ := by
            intro h; have h' := congrArg Fin.val h
            change 0=(i:ℕ)+1+1 at h'; omega
          rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]; rfl
        · change (Equiv.swap i.succ.castSucc i.succ.succ
              (combIndex x (n+1) (Sum.inr j)):ℕ)=
            1+(combIndex x n (combPerm x n (Equiv.swap i.castSucc i.succ) j):ℕ)
          rw [combIndex_perm]
          have h₁ (k:Fin (n+1)) :
              combIndex x (n+1) (Sum.inr j)=k.succ ↔ combIndex x n j=k := by
            constructor <;> intro h
            · apply Fin.ext; have hh := congrArg Fin.val h
              change 1+(combIndex x n j:ℕ)=(k:ℕ)+1 at hh; omega
            · apply Fin.ext; change 1+(combIndex x n j:ℕ)=(k:ℕ)+1; rw [h]; omega
          have hc : i.succ.castSucc=i.castSucc.succ := rfl
          rw [hc]
          simp only [Equiv.swap_apply_def,h₁]
          split_ifs
          · simp only [Fin.val_succ]; omega
          · simp only [Fin.val_succ]; omega
          · exact combIndex_right x n j
      rw [he]
      exact Route.sum x x (Route.refl .leaf) (ih i)

lemma route_comb_perm (x:X) (n:ℕ) (p:Equiv.Perm (Fin (n+1))) :
    Route (a:=comb x n) (b:=comb x n) (combPerm x n p) := by
  induction p using Adjacent.permutation_induction with
  | hone => rw [combPerm_one]; exact Route.refl _
  | hswap i => exact route_comb_adjacent x n i
  | hmul p r hp hr => rw [combPerm_mul]; exact hr.trans hp

lemma route_comb_equiv (x:X) (m n:ℕ) (e:(comb x m).Leaves ≃ (comb x n).Leaves) :
    Route e := by
  have h := equiv_size (((combIndex x m).symm.trans e).trans (combIndex x n))
  subst n
  let p : Equiv.Perm (Fin (m+1)) := (combIndex x m).symm.trans (e.trans (combIndex x m))
  have hp : combPerm x m p=e := by
    apply Equiv.ext; intro j; simp [combPerm,p]
  rw [← hp]
  exact route_comb_perm x m p

/-- Every bijection of leaves is generated by associativity, symmetries and tensor.
This is a finite-permutation coherence theorem, not an extra relation. -/
lemma route_complete (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Route e := by
  obtain ⟨ea,hea,_⟩ := route_normal x a
  obtain ⟨eb,heb,_⟩ := route_normal x b
  have h := hea.trans ((route_comb_equiv x a.arity b.arity (ea.symm.trans (e.trans eb))).trans heb.symm)
  have he : ea.trans ((ea.symm.trans (e.trans eb)).trans eb.symm)=e := by
    apply Equiv.ext; intro i; simp
  rw [he] at h
  exact h

end

section
universe v w
open BinaryGroupCategory
variable {X : Type v}

/-- Replace each leaf by the tree attached to its image. This is cabling of a
bijection, defined on the actual dependent leaf sets. -/
def graftLift {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X) :
    (a.graft (fun i=>F (e i))).Leaves ≃ (b.graft F).Leaves :=
  (a.graftLeaves (fun i=>F (e i))).trans
    ((Equiv.sigmaCongr e (fun _=>Equiv.refl _)).trans (b.graftLeaves F).symm)

lemma graftLift_apply {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X)
    (i:a.Leaves) (j:(F (e i)).Leaves) :
    graftLift e F ((a.graftLeaves (fun i=>F (e i))).symm ⟨i,j⟩)=
      (b.graftLeaves F).symm ⟨e i,j⟩ := by
  simp [graftLift,Equiv.sigmaCongr,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft]

lemma graftLift_refl (a:Tree X) (F:a.Leaves → Tree X) :
    graftLift (Equiv.refl a.Leaves) F=Equiv.refl (a.graft F).Leaves := by
  apply Equiv.ext; intro j
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves F).symm.surjective j
  erw [graftLift_apply]; rfl

lemma graftLift_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves)
    (F:c.Leaves → Tree X) :
    graftLift (e.trans f) F=(graftLift e (fun i=>F (f i))).trans (graftLift f F) := by
  apply Equiv.ext; intro j
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (f (e i)))).symm.surjective j
  calc
    _ = (c.graftLeaves F).symm ⟨f (e i),k⟩ := graftLift_apply (e.trans f) F i k
    _ = graftLift f F ((b.graftLeaves (fun i=>F (f i))).symm ⟨e i,k⟩) :=
      (graftLift_apply f F (e i) k).symm
    _ = _ := congrArg (graftLift f F) (graftLift_apply e (fun i=>F (f i)) i k).symm

lemma graftLift_sum {a b c d:Tree X} (x y:X) (e:a.Leaves ≃ c.Leaves) (f:b.Leaves ≃ d.Leaves)
    (F:(Tree.split y c d).Leaves → Tree X) :
    graftLift (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) F =
      Equiv.sumCongr (graftLift e (fun i=>F (Sum.inl i))) (graftLift f (fun i=>F (Sum.inr i))) := by
  apply Equiv.ext
  rintro (j|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inl (e i)))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) F
      (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumCongr e f) i))).symm ⟨Sum.inl i,k⟩)=_
    erw [graftLift_apply]
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inr (f i)))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y c d) (Equiv.sumCongr e f) F
      (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumCongr e f) i))).symm ⟨Sum.inr i,k⟩)=_
    erw [graftLift_apply]

lemma graftLift_assoc (x y z w:X) (a b c:Tree X)
    (F:(Tree.split z a (.split w b c)).Leaves → Tree X) :
    graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c))
      (Equiv.sumAssoc _ _ _) F=Equiv.sumAssoc _ _ _ := by
  apply Equiv.ext
  rintro ((j|j)|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inl i))).symm.surjective j
    change graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) F (((Tree.split x (.split y a b) c).graftLeaves (fun i=>F ((Equiv.sumAssoc _ _ _) i))).symm ⟨Sum.inl (Sum.inl i),k⟩)=_
    erw [graftLift_apply]; rfl
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inr (Sum.inl i)))).symm.surjective j
    change graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) F (((Tree.split x (.split y a b) c).graftLeaves (fun i=>F ((Equiv.sumAssoc _ _ _) i))).symm ⟨Sum.inl (Sum.inr i),k⟩)=_
    erw [graftLift_apply]; rfl
  · obtain ⟨⟨i,k⟩,rfl⟩ := (c.graftLeaves (fun i=>F (Sum.inr (Sum.inr i)))).symm.surjective j
    change graftLift (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c)) (Equiv.sumAssoc _ _ _) F (((Tree.split x (.split y a b) c).graftLeaves (fun i=>F ((Equiv.sumAssoc _ _ _) i))).symm ⟨Sum.inr i,k⟩)=_
    erw [graftLift_apply]; rfl

lemma graftLift_exchange (x y:X) (a b:Tree X)
    (F:(Tree.split y b a).Leaves → Tree X) :
    graftLift (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F=Equiv.sumComm _ _ := by
  apply Equiv.ext
  rintro (j|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inr i))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumComm _ _) i))).symm ⟨Sum.inl i,k⟩)=_
    erw [graftLift_apply]; rfl
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inl i))).symm.surjective j
    change graftLift (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F (((Tree.split x a b).graftLeaves (fun i=>F ((Equiv.sumComm _ _) i))).symm ⟨Sum.inr i,k⟩)=_
    erw [graftLift_apply]; rfl

end

universe v w
open BinaryGroupCategory
variable {X : Type v} {H : Type w} [Group H] (d:Data H) (q:SymmetryData d) (B:X → H)

def cableValue {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X) : H :=
  leafValue d q B (graftLift e F)

lemma cableValue_refl (a:Tree X) (F:a.Leaves → Tree X) :
    cableValue d q B (Equiv.refl a.Leaves) F=1 := by
  unfold cableValue
  rw [graftLift_refl]
  exact leafValue_refl d q B (a.graft F)

lemma cableValue_trans {a b c:Tree X} (e:a.Leaves ≃ b.Leaves) (f:b.Leaves ≃ c.Leaves)
    (F:c.Leaves → Tree X) :
    cableValue d q B (e.trans f) F=
      cableValue d q B f F*cableValue d q B e (fun i=>F (f i)) := by
  unfold cableValue
  rw [graftLift_trans]
  exact leafValue_trans d q B (graftLift e (fun i=>F (f i))) (graftLift f F)

lemma cableValue_sum {a b c f:Tree X} (x y:X) (e:a.Leaves ≃ c.Leaves) (g:b.Leaves ≃ f.Leaves)
    (F:(Tree.split y c f).Leaves → Tree X) :
    cableValue d q B (a:=.split x a b) (b:=.split y c f) (Equiv.sumCongr e g) F=
      B y*d.tensor (cableValue d q B e (fun i=>F (Sum.inl i)),
        cableValue d q B g (fun i=>F (Sum.inr i)))*(B x)⁻¹ := by
  unfold cableValue
  rw [graftLift_sum]
  exact leafValue_sum d q B x y (graftLift e (fun i=>F (Sum.inl i)))
    (graftLift g (fun i=>F (Sum.inr i)))

lemma cableValue_assoc (x y z w:X) (a b c:Tree X)
    (F:(Tree.split z a (.split w b c)).Leaves → Tree X) :
    cableValue d q B (a:=.split x (.split y a b) c) (b:=.split z a (.split w b c))
      (Equiv.sumAssoc _ _ _) F=B z*d.tensor (1,B w)*d.a⁻¹*(B x*d.tensor (B y,1))⁻¹ := by
  unfold cableValue
  rw [graftLift_assoc]
  exact leafValue_assoc d q B x y z w (a.graft (fun i=>F (Sum.inl i)))
    (b.graft (fun i=>F (Sum.inr (Sum.inl i)))) (c.graft (fun i=>F (Sum.inr (Sum.inr i))))

lemma cableValue_exchange (x y:X) (a b:Tree X)
    (F:(Tree.split y b a).Leaves → Tree X) :
    cableValue d q B (a:=.split x a b) (b:=.split y b a) (Equiv.sumComm _ _) F=B y*q.c*(B x)⁻¹ := by
  unfold cableValue
  rw [graftLift_exchange]
  exact leafValue_exchange d q B x y

/-- Structural routes are invariant under replacing their wires by arbitrary
(nonempty) trees. This is cabling coherence for whole leaf permutations. -/
lemma Route.cableValue_eq {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (h:Route e)
    (F:b.Leaves → Tree X) : cableValue d q B e F=leafValue d q B e := by
  induction h with
  | refl a => rw [cableValue_refl,leafValue_refl]
  | @trans a b c e f he hf ihe ihf =>
    rw [cableValue_trans,ihe,ihf,leafValue_trans]
  | @symm a b e he ih =>
    have hh := cableValue_trans d q B e e.symm F
    rw [Equiv.self_trans_symm,cableValue_refl,ih] at hh
    rw [leafValue_symm]
    exact eq_inv_of_mul_eq_one_left hh.symm
  | @sum a b c f x y e g he hg ihe ihg =>
    rw [cableValue_sum,ihe,ihg,leafValue_sum]
  | assoc x y z w a b c => rw [cableValue_assoc,leafValue_assoc]
  | exchange x y a b => rw [cableValue_exchange,leafValue_exchange]

lemma leafValue_graftLift (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:b.Leaves → Tree X) :
    leafValue d q B (graftLift e F)=leafValue d q B e :=
  (route_complete x e).cableValue_eq d q B F

abbrev quad (x y:X) : Tree X := .split x (.split y .leaf .leaf) (.split y .leaf .leaf)

lemma flatten_bit (x:X) : flatten d B (.split x .leaf .leaf)=B x := by
  have ht : d.tensor (1,1)=1 := d.tensor.map_one
  simp only [flatten,arity,merge_zero,ht,mul_one,inv_one]

/-- The only additional colour relation needed for all tree-partition coherence. -/
structure GridLaw : Prop where
  grid : ∀ x y:X,x≠y → B x*d.tensor (B y,B y)=B y*d.tensor (B x,B x)*middleSwap d q

def SameBricks {a b:Tree X} (e:a.Leaves ≃ b.Leaves) : Prop :=
  ∀ i,a.brick i=b.brick (e i)

lemma SameBricks.symm {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (he:SameBricks e) : SameBricks e.symm := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm
lemma SameBricks.trans {a b c:Tree X} {e:a.Leaves ≃ b.Leaves} {f:b.Leaves ≃ c.Leaves}
    (he:SameBricks e) (hf:SameBricks f) : SameBricks (e.trans f) :=
  fun i=>(he i).trans (hf (e i))

end FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

section
universe v w
open BinaryGroupCategory
variable {X:Type v} {H:Type w} [Group H] (d:Data H) (q:SymmetryData d) (B:X → H)

/-- Tensor leaf decorations along the literal coloured tree. -/
def fold : (a:Tree X) → (a.Leaves → H) → H
  | .leaf,F => F PUnit.unit
  | .split x a b,F => B x*d.tensor (fold a (fun i=>F (Sum.inl i)),
      fold b (fun i=>F (Sum.inr i)))*(B x)⁻¹

lemma fold_congr (a:Tree X) {F G:a.Leaves → H} (h:∀ i,F i=G i) : fold d B a F=fold d B a G :=
  congrArg (fold d B a) (funext h)

@[simp] lemma fold_one (a:Tree X) : fold d B a (fun _=>1)=1 := by
  induction a with
  | leaf => rfl
  | split x a b ha hb =>
    simp only [fold,ha,hb,show d.tensor (1,1)=1 from d.tensor.map_one,mul_one,mul_inv_cancel]

lemma fold_mul (a:Tree X) (F G:a.Leaves → H) :
    fold d B a (fun i=>F i*G i)=fold d B a F*fold d B a G := by
  induction a with
  | leaf => rfl
  | split x a b ha hb =>
    simp only [fold,ha,hb]
    rw [show d.tensor (fold d B a (fun i=>F (Sum.inl i))*fold d B a (fun i=>G (Sum.inl i)),
        fold d B b (fun i=>F (Sum.inr i))*fold d B b (fun i=>G (Sum.inr i)))=
      d.tensor (fold d B a (fun i=>F (Sum.inl i)),fold d B b (fun i=>F (Sum.inr i)))*
      d.tensor (fold d B a (fun i=>G (Sum.inl i)),fold d B b (fun i=>G (Sum.inr i))) from
      d.tensor.map_mul (fold d B a (fun i=>F (Sum.inl i)),fold d B b (fun i=>F (Sum.inr i)))
        (fold d B a (fun i=>G (Sum.inl i)),fold d B b (fun i=>G (Sum.inr i)))]
    group

lemma fold_inv (a:Tree X) (F:a.Leaves → H) : fold d B a (fun i=>(F i)⁻¹)=(fold d B a F)⁻¹ := by
  have h := fold_mul d B a F (fun i=>(F i)⁻¹)
  simp only [mul_inv_cancel,fold_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Substitution of arbitrary decorated trees at all leaves. -/
lemma fold_graft (a:Tree X) (F:a.Leaves → Tree X) (L:(a.graft F).Leaves → H) :
    fold d B (a.graft F) L=fold d B a
      (fun i=>fold d B (F i) (fun j=>L ((a.graftLeaves F).symm ⟨i,j⟩))) := by
  induction a with
  | leaf => rfl
  | split x a b ha hb =>
    change B x*d.tensor (fold d B (a.graft _) (fun i=>L (Sum.inl i)),
      fold d B (b.graft _) (fun i=>L (Sum.inr i)))*(B x)⁻¹=_
    rw [ha,hb]
    rfl

/-- Scalar naturality for a tensor square, preventing dependent tree rewrites. -/
lemma tensor_square (A C U V F G I J:H)
    (h₁:U*F=I*U) (h₂:V*G=J*V) :
    (C*d.tensor (U,V)*A⁻¹)*(A*d.tensor (F,G)*A⁻¹)=
      (C*d.tensor (I,J)*C⁻¹)*(C*d.tensor (U,V)*A⁻¹) := by
  have hh : d.tensor (U,V)*d.tensor (F,G)=d.tensor (I,J)*d.tensor (U,V) := by
    rw [← map_mul,← map_mul]; exact congrArg d.tensor (Prod.ext h₁ h₂)
  calc
    _=C*(d.tensor (U,V)*d.tensor (F,G))*A⁻¹ := by group
    _=_ := by rw [hh]; group

/-- Flatten nested conjugations in a left-associated tree. -/
lemma fold_left_algebra (x y:X) (A C E:H) :
    B x*d.tensor (B y*d.tensor (A,C)*(B y)⁻¹,E)*(B x)⁻¹=
      (B x*d.tensor (B y,1))*d.tensor (d.tensor (A,C),E)*(B x*d.tensor (B y,1))⁻¹ := by
  have h := tensor_conjugate d (B y) 1 (d.tensor (A,C)) E
  simp only [inv_one,one_mul,mul_one] at h
  rw [h]
  group
lemma fold_right_algebra (x y:X) (A C E:H) :
    B x*d.tensor (A,B y*d.tensor (C,E)*(B y)⁻¹)*(B x)⁻¹=
      (B x*d.tensor (1,B y))*d.tensor (A,d.tensor (C,E))*(B x*d.tensor (1,B y))⁻¹ := by
  have h := tensor_conjugate d 1 (B y) A (d.tensor (C,E))
  simp only [inv_one,one_mul,mul_one] at h
  rw [h]
  group

lemma leafValue_fold_route {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (r:Route e)
    (F:a.Leaves → H) (G:b.Leaves → H) (h:∀ i,F i=G (e i)) :
    leafValue d q B e*fold d B a F=fold d B b G*leafValue d q B e := by
  induction r with
  | refl a => rw [leafValue_refl,one_mul,mul_one]; exact fold_congr d B a h
  | @trans a b c e f r s ih ik =>
    let M := fun j=>F (e.symm j)
    have h₁ := ih F M (by intro i; simp [M])
    have h₂ := ik M G (by intro j; simpa [M] using h (e.symm j))
    rw [leafValue_trans]
    calc
      _=leafValue d q B f*(leafValue d q B e*fold d B a F) := by group
      _=_ := by rw [h₁,← mul_assoc,h₂]; group
  | @symm a b e r ih =>
    have hh := ih G F (by intro i; simpa using (h (e i)).symm)
    rw [leafValue_symm]
    calc
      _=(leafValue d q B e)⁻¹*(fold d B b F*leafValue d q B e)*(leafValue d q B e)⁻¹ := by group
      _=_ := by rw [← hh]; group
  | @sum a b c f x y e g r s ih ik =>
    rw [leafValue_sum]
    exact tensor_square d (B x) (B y) _ _ _ _ _ _
      (ih (fun i=>F (Sum.inl i)) (fun i=>G (Sum.inl i)) (fun i=>h (Sum.inl i)))
      (ik (fun i=>F (Sum.inr i)) (fun i=>G (Sum.inr i)) (fun i=>h (Sum.inr i)))
  | assoc x y z w a b c =>
    have h₁ := fold_congr d B a (fun i=>h (Sum.inl (Sum.inl i)))
    have h₂ := fold_congr d B b (fun i=>h (Sum.inl (Sum.inr i)))
    have h₃ := fold_congr d B c (fun i=>h (Sum.inr i))
    rw [leafValue_assoc]
    simp only [fold]
    rw [h₁,h₂,h₃,fold_left_algebra,fold_right_algebra]
    simp only [Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,Equiv.sumAssoc_apply_inr]
    have hn := d.naturality (fold d B a (fun i=>G (Sum.inl i)))
      (fold d B b (fun i=>G (Sum.inr (Sum.inl i))))
      (fold d B c (fun i=>G (Sum.inr (Sum.inr i))))
    rw [← hn]
    group
  | exchange x y a b =>
    have h₁ := fold_congr d B a (fun i=>h (Sum.inl i))
    have h₂ := fold_congr d B b (fun i=>h (Sum.inr i))
    rw [leafValue_exchange]
    simp only [fold]
    rw [h₁,h₂]
    simp only [Equiv.sumComm_apply,Sum.swap_inl,Sum.swap_inr]
    have hn := q.naturality (fold d B a (fun i=>G (Sum.inr i)))
      (fold d B b (fun i=>G (Sum.inl i)))
    rw [← hn]
    group

lemma leafValue_fold (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves)
    (F:a.Leaves → H) (G:b.Leaves → H) (h:∀ i,F i=G (e i)) :
    leafValue d q B e*fold d B a F=fold d B b G*leafValue d q B e :=
  leafValue_fold_route d q B (route_complete x e) F G h

/-- Whole dependent substitution of a bijection and bijections in every fibre. -/
def graftMap {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:a.Leaves → Tree X) (G:b.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) : (a.graft F).Leaves ≃ (b.graft G).Leaves :=
  (a.graftLeaves F).trans ((Equiv.sigmaCongr e h).trans (b.graftLeaves G).symm)
lemma graftMap_apply {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:a.Leaves → Tree X) (G:b.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) (i:a.Leaves) (j:(F i).Leaves) :
    graftMap e F G h ((a.graftLeaves F).symm ⟨i,j⟩)=(b.graftLeaves G).symm ⟨e i,h i j⟩ := by
  simp [graftMap,Equiv.sigmaCongr,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft]

lemma graftMap_leaf (F G:(Tree.leaf:Tree X).Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G i).Leaves) : graftMap (Equiv.refl _) F G h=h PUnit.unit := by
  apply Equiv.ext; intro j
  exact graftMap_apply (Equiv.refl _) F G h PUnit.unit j

lemma graftMap_sum (x:X) (a b:Tree X) (F G:(Tree.split x a b).Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G i).Leaves) :
    graftMap (Equiv.refl _) F G h=
      Equiv.sumCongr (graftMap (Equiv.refl a.Leaves) (fun i=>F (Sum.inl i))
        (fun i=>G (Sum.inl i)) (fun i=>h (Sum.inl i)))
      (graftMap (Equiv.refl b.Leaves) (fun i=>F (Sum.inr i))
        (fun i=>G (Sum.inr i)) (fun i=>h (Sum.inr i))) := by
  apply Equiv.ext
  rintro (j|j)
  · obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (fun i=>F (Sum.inl i))).symm.surjective j
    change graftMap (a:=.split x a b) (Equiv.refl _) F G h
      (((Tree.split x a b).graftLeaves F).symm ⟨Sum.inl i,k⟩)=_
    erw [graftMap_apply]
  · obtain ⟨⟨i,k⟩,rfl⟩ := (b.graftLeaves (fun i=>F (Sum.inr i))).symm.surjective j
    change graftMap (a:=.split x a b) (Equiv.refl _) F G h
      (((Tree.split x a b).graftLeaves F).symm ⟨Sum.inr i,k⟩)=_
    erw [graftMap_apply]

lemma leafValue_graftWithin (a:Tree X) (F G:a.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G i).Leaves) :
    leafValue d q B (graftMap (Equiv.refl _) F G h)=fold d B a (fun i=>leafValue d q B (h i)) := by
  induction a with
  | leaf => rw [graftMap_leaf]; rfl
  | split x a b ha hb =>
    rw [graftMap_sum]
    change leafValue d q B (a:=.split x (a.graft _) (b.graft _))
      (b:=.split x (a.graft _) (b.graft _)) (Equiv.sumCongr _ _)=_
    rw [leafValue_sum,ha,hb]; rfl

lemma graftMap_factor {a b:Tree X} (e:a.Leaves ≃ b.Leaves) (F:a.Leaves → Tree X) (G:b.Leaves → Tree X)
    (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) : graftMap e F G h=
      (graftMap (Equiv.refl _) F (fun i=>G (e i)) h).trans (graftLift e G) := by
  apply Equiv.ext; intro j
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves F).symm.surjective j
  calc
    _=(b.graftLeaves G).symm ⟨e i,h i k⟩ := graftMap_apply e F G h i k
    _=graftLift e G ((a.graftLeaves (fun i=>G (e i))).symm ⟨i,h i k⟩) :=
      (graftLift_apply e G i (h i k)).symm
    _=_ := congrArg (graftLift e G) (graftMap_apply (Equiv.refl _) F (fun i=>G (e i)) h i k).symm

lemma leafValue_graftMap (x:X) {a b:Tree X} (e:a.Leaves ≃ b.Leaves)
    (F:a.Leaves → Tree X) (G:b.Leaves → Tree X) (h:∀ i,(F i).Leaves ≃ (G (e i)).Leaves) :
    leafValue d q B (graftMap e F G h)=leafValue d q B e*fold d B a (fun i=>leafValue d q B (h i)) := by
  rw [graftMap_factor,leafValue_trans,leafValue_graftLift d q B x,leafValue_graftWithin]

end

universe u v w
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
variable (d:Data H) (q:SymmetryData d) (B:X → H)

/-- Leaf transport of a coordinate relabelling, with the same binary shape. -/
def colourLeaves (f:X → X) : (a:Tree X) → a.Leaves ≃ (mapColors f a).Leaves
  | .leaf => Equiv.refl _
  | .split _ a b => Equiv.sumCongr (colourLeaves f a) (colourLeaves f b)

lemma colour_brick (g:Γ) (a:Tree X) (i:a.Leaves) :
    (mapColors (fun x=>g • x) a).brick (colourLeaves (fun x=>g • x) a i)=twistPrefix g (a.brick i) := by
  induction a with
  | leaf => exact (twistPrefix_empty g).symm
  | split x a b ha hb =>
    cases i with
    | inl i =>
      change (Prefix.oneBit (g • x) false).comp ((mapColors (fun x=>g • x) a).brick _)=_
      rw [ha,brick,twistPrefix_comp,twistPrefix_oneBit]
    | inr i =>
      change (Prefix.oneBit (g • x) true).comp ((mapColors (fun x=>g • x) b).brick _)=_
      rw [hb,brick,twistPrefix_comp,twistPrefix_oneBit]

/-- Root-label splitting, derived solely from the proved baker covariance law. -/
lemma leafValue_colour (R:Γ →* H)
    (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g)) (g:Γ) (a:Tree X) :
    leafValue d q B (colourLeaves (fun x=>g • x) a)*fold d B a (fun _=>R g)=R g := by
  induction a with
  | leaf =>
    change leafValue d q B (a:=.leaf) (b:=.leaf) (Equiv.refl _)*R g=R g
    rw [leafValue_refl,one_mul]
  | split x a b ha hb =>
    change leafValue d q B (a:=.split x a b)
      (b:=.split (g • x) (mapColors (fun x=>g • x) a) (mapColors (fun x=>g • x) b))
      (Equiv.sumCongr _ _)*(B x*d.tensor (fold d B a (fun _=>R g),fold d B b (fun _=>R g))*(B x)⁻¹)=_
    rw [leafValue_sum]
    calc
      _=B (g • x)*(d.tensor (leafValue d q B (colourLeaves (fun x=>g • x) a),
          leafValue d q B (colourLeaves (fun x=>g • x) b))*
        d.tensor (fold d B a (fun _=>R g),fold d B b (fun _=>R g)))*(B x)⁻¹ := by group
      _=B (g • x)*d.tensor (R g,R g)*(B x)⁻¹ := by
        rw [← map_mul]; change B (g • x)*d.tensor (_*_,_*_)*(B x)⁻¹=_; rw [ha,hb]
      _=R g := by rw [← hR]; group

lemma leafValue_uncolour (x:X) (R:Γ →* H)
    (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g)) (g:Γ) (a:Tree X) :
    leafValue d q B (colourLeaves (fun x=>g⁻¹ • x) a).symm*
      fold d B (mapColors (fun x=>g⁻¹ • x) a) (fun _=>R g)=R g := by
  have hh := congrArg (fun z:H=>z⁻¹) (leafValue_colour d q B R hR g⁻¹ a)
  simp only [mul_inv_rev,map_inv] at hh
  rw [← fold_inv] at hh
  simp only [inv_inv] at hh
  calc
    _=fold d B a (fun _=>R g)*leafValue d q B (colourLeaves (fun x=>g⁻¹ • x) a).symm :=
      leafValue_fold d q B x _ _ _ (fun _=>rfl)
    _=R g := by rw [leafValue_symm]; exact hh

end FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

end

end OAI
end

section
-- module Solutions.OAIFAE.Diagrams
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Represented diagrams and actual endpoint evaluation injectivity and equivalence.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v w
open BinaryGroupCategory

/-- A full finite decorated tree pair, including the entire leaf bijection. -/
structure Diagram (Γ:Type u) (X:Type v) where
  source : Tree X
  target : Tree X
  wires : source.Leaves ≃ target.Leaves
  label : source.Leaves → Γ

namespace Diagram
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H)

def value (A:Diagram Γ X) : H :=
  Tree.leafValue d q B A.wires*Tree.fold d B A.source (fun i=>R (A.label i))

def Realizes (A:Diagram Γ X) (f:Equiv.Perm (Cube X)) : Prop :=
  ∀ i z,f ((A.source.brick i).attach z)=(A.target.brick (A.wires i)).attach (twist (A.label i) z)

def root (g:Γ) : Diagram Γ X := ⟨.leaf,.leaf,Equiv.refl _,fun _=>g⟩

def inverse (A:Diagram Γ X) : Diagram Γ X :=
  ⟨A.target,A.source,A.wires.symm,fun i=>(A.label (A.wires.symm i))⁻¹⟩

omit [MulAction Γ X] in
lemma value_inverse (x:X) (A:Diagram Γ X) : value d q B R A.inverse=(value d q B R A)⁻¹ := by
  change Tree.leafValue d q B A.wires.symm*
      Tree.fold d B A.target (fun i=>R ((A.label (A.wires.symm i))⁻¹))=_
  simp only [map_inv]
  rw [Tree.leafValue_fold d q B x A.wires.symm _ (fun i=>(R (A.label i))⁻¹) (fun _=>rfl)]
  rw [Tree.fold_inv,Tree.leafValue_symm]
  exact (mul_inv_rev _ _).symm

lemma Realizes.inverse {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (h:Realizes A f) :
    Realizes A.inverse f⁻¹ := by
  change ∀ (i:A.target.Leaves) z, _
  intro i z
  change f.symm ((A.target.brick i).attach z)=
    (A.source.brick (A.wires.symm i)).attach (twist (A.label (A.wires.symm i))⁻¹ z)
  apply f.injective
  rw [f.apply_symm_apply,h,Equiv.apply_symm_apply,twist_twist_inv]

/-- Compose after identifying the two intermediate partitions. -/
def compose (A C:Diagram Γ X) (e:A.target.Leaves ≃ C.source.Leaves) : Diagram Γ X where
  source := A.source
  target := C.target
  wires := (A.wires.trans e).trans C.wires
  label i := C.label (e (A.wires i))*A.label i

omit [MulAction Γ X] in
lemma value_compose (x:X) (A C:Diagram Γ X) (e:A.target.Leaves ≃ C.source.Leaves) :
    value d q B R (compose A C e)=value d q B R C*Tree.leafValue d q B e*value d q B R A := by
  change Tree.leafValue d q B ((A.wires.trans e).trans C.wires)*
    Tree.fold d B A.source (fun i=>R (C.label (e (A.wires i))*A.label i))=_
  simp only [map_mul]
  rw [Tree.leafValue_trans,Tree.fold_mul]
  have hn := Tree.leafValue_fold d q B x (A.wires.trans e)
    (fun i=>R (C.label (e (A.wires i)))) (fun i=>R (C.label i)) (fun _=>rfl)
  calc
    _=Tree.leafValue d q B C.wires*
        (Tree.leafValue d q B (A.wires.trans e)*Tree.fold d B A.source (fun i=>R (C.label (e (A.wires i)))))*
        Tree.fold d B A.source (fun i=>R (A.label i)) := by group
    _=_ := by rw [hn,Tree.leafValue_trans]; dsimp only [value]; group

lemma Realizes.compose {A C:Diagram Γ X} {f g:Equiv.Perm (Cube X)}
    (ha:Realizes A f) (hc:Realizes C g) (e:A.target.Leaves ≃ C.source.Leaves)
    (he:Tree.SameBricks e) : Realizes (compose A C e) (g*f) := by
  change ∀ (i:A.source.Leaves) z, _
  intro i z
  change g (f ((A.source.brick i).attach z))=(C.target.brick (C.wires (e (A.wires i)))).attach
    (twist (C.label (e (A.wires i))*A.label i) z)
  rw [ha,he,hc,twist_twist]

end Diagram
end

section
universe u v w
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Tree
lemma graft_brick_symm (a:Tree X) (F:a.Leaves → Tree X) (i:a.Leaves) (j:(F i).Leaves) :
    (a.graft F).brick ((a.graftLeaves F).symm ⟨i,j⟩)=(a.brick i).comp ((F i).brick j) := by
  rw [graft_prefix,Equiv.apply_symm_apply]
end Tree
namespace Diagram

abbrev expansionFamily (A:Diagram Γ X) (F:A.target.Leaves → Tree X) (i:A.source.Leaves) :=
  Tree.mapColors (fun x=>(A.label i)⁻¹ • x) (F (A.wires i))

/-- Expand the whole target and pull every fibre back through its true label. -/
def expand (A:Diagram Γ X) (F:A.target.Leaves → Tree X) : Diagram Γ X where
  source := A.source.graft (A.expansionFamily F)
  target := A.target.graft F
  wires := Tree.graftMap A.wires (A.expansionFamily F) F
    (fun i=>(Tree.colourLeaves (fun x=>(A.label i)⁻¹ • x) (F (A.wires i))).symm)
  label j := A.label ((A.source.graftLeaves (A.expansionFamily F)) j).1

lemma expand_label (A:Diagram Γ X) (F:A.target.Leaves → Tree X)
    (i:A.source.Leaves) (j:(A.expansionFamily F i).Leaves) :
    (A.expand F).label ((A.source.graftLeaves (A.expansionFamily F)).symm ⟨i,j⟩)=A.label i := by
  change A.label ((A.source.graftLeaves (A.expansionFamily F))
    ((A.source.graftLeaves (A.expansionFamily F)).symm ⟨i,j⟩)).1=A.label i
  rw [Equiv.apply_symm_apply]

lemma value_expand (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H) (x:X)
    (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g))
    (A:Diagram Γ X) (F:A.target.Leaves → Tree X) : value d q B R (A.expand F)=value d q B R A := by
  change Tree.leafValue d q B (Tree.graftMap A.wires (A.expansionFamily F) F _)*
    Tree.fold d B (A.source.graft (A.expansionFamily F)) (fun i=>R ((A.expand F).label i))=_
  rw [Tree.leafValue_graftMap d q B x,Tree.fold_graft]
  simp only [expand_label]
  rw [mul_assoc,← Tree.fold_mul]
  apply congrArg (Tree.leafValue d q B A.wires * ·)
  exact Tree.fold_congr d B A.source (fun i=>
    Tree.leafValue_uncolour d q B x R hR (A.label i) (F (A.wires i)))

lemma Realizes.expand {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (h:Realizes A f)
    (F:A.target.Leaves → Tree X) : Realizes (A.expand F) f := by
  change ∀ (j:(A.source.graft (A.expansionFamily F)).Leaves) z, _
  intro j z
  obtain ⟨⟨i,k⟩,rfl⟩ := (A.source.graftLeaves (A.expansionFamily F)).symm.surjective j
  change f (((A.source.graft (A.expansionFamily F)).brick _).attach z)=
    ((A.target.graft F).brick (Tree.graftMap A.wires (A.expansionFamily F) F _ _)).attach
      (twist ((A.expand F).label _) z)
  rw [Tree.graftMap_apply,Tree.graft_brick_symm,Tree.graft_brick_symm,expand_label,
    Prefix.comp_attach,h,Prefix.comp_attach]
  congr 1
  have hb := Tree.colour_brick (A.label i)⁻¹ (F (A.wires i))
    ((Tree.colourLeaves (fun x=>(A.label i)⁻¹ • x) (F (A.wires i))).symm k)
  rw [Equiv.apply_symm_apply] at hb
  change twist (A.label i) (((A.expansionFamily F i).brick k).attach z)=_
  rw [hb,untwist_attach]

end Diagram
end

section
universe u v w
open BinaryGroupCategory
attribute [local instance] Classical.propDecidable
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Tree

abbrev gridFill (a:Tree X) (l:List X) (i:a.Leaves) := grid (l.diff (a.brick i).schedule)

lemma gridFill_length (a:Tree X) (l:List X)
    (h:∀ i x,((a.brick i).word x).length≤l.count x)
    (j:(a.graft (a.gridFill l)).Leaves) (x:X) :
    (((a.graft (a.gridFill l)).brick j).word x).length=l.count x := by
  classical
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (a.gridFill l)).symm.surjective j
  rw [graft_brick_symm]
  change ((a.brick i).word x ++ ((grid (l.diff (a.brick i).schedule)).brick k).word x).length=_
  rw [List.length_append,grid_length,List.count_diff,Prefix.schedule_count]
  exact Nat.add_sub_of_le (h i x)

lemma gridFill_equiv (a:Tree X) (l:List X)
    (h:∀ i x,((a.brick i).word x).length≤l.count x) :
    ∃ e:(a.graft (a.gridFill l)).Leaves ≃ (grid l).Leaves,SameBricks e := by
  let P := (a.graft (a.gridFill l)).partition
  have hh := P.grid_bricks_of_lengths l (a.gridFill_length l h)
  exact ⟨P.indexEquivOfBricks (grid l).partition hh,P.indexEquivOfBricks_spec (grid l).partition hh⟩
end Tree
namespace Diagram
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H) (x:X)
variable (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g))
include x hR

lemma refine_target_grid {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (ha:Realizes A f)
    (l:List X) (h:∀ i x,((A.target.brick i).word x).length≤l.count x) :
    ∃ C:Diagram Γ X,Realizes C f ∧ value d q B R C=value d q B R A ∧
      ∃ e:C.target.Leaves ≃ (Tree.grid l).Leaves,Tree.SameBricks e := by
  refine ⟨A.expand (A.target.gridFill l),ha.expand _,value_expand d q B R x hR A _,?_⟩
  exact A.target.gridFill_equiv l h

lemma refine_source_grid {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (ha:Realizes A f)
    (l:List X) (h:∀ i x,((A.source.brick i).word x).length≤l.count x) :
    ∃ C:Diagram Γ X,Realizes C f ∧ value d q B R C=value d q B R A ∧
      ∃ e:C.source.Leaves ≃ (Tree.grid l).Leaves,Tree.SameBricks e := by
  obtain ⟨D,hd,hv,e,he⟩ := refine_target_grid d q B R x hR ha.inverse l h
  refine ⟨D.inverse,by simpa only [inv_inv] using hd.inverse,?_,e,he⟩
  rw [value_inverse d q B R x,hv,value_inverse d q B R x,inv_inv]

end Diagram
end

universe u v w
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Diagram
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H)

/-- Undecorated full tree wiring. -/
def plain (a b:Tree X) (e:a.Leaves ≃ b.Leaves) : Diagram Γ X := ⟨a,b,e,fun _=>1⟩

/-- Prefix-localize an entire diagram, including its bijection and labels. -/
def half (x:X) (A:Diagram Γ X) : Diagram Γ X where
  source := .split x A.source .leaf
  target := .split x A.target .leaf
  wires := Equiv.sumCongr A.wires (Equiv.refl _)
  label := Sum.elim A.label (fun _=>1)

lemma Realizes.half {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (ha:Realizes A f) (x:X) :
    Realizes (half x A) (localizePerm (Prefix.oneBit x false) f) := by
  change ∀ (i:A.source.Leaves ⊕ (Tree.leaf:Tree X).Leaves) z, _
  rintro (i|i) z
  · change localizePerm (Prefix.oneBit x false) f
      (((Prefix.oneBit x false).comp (A.source.brick i)).attach z)=
        (((Prefix.oneBit x false).comp (A.target.brick (A.wires i))).attach (twist (A.label i) z))
    rw [Prefix.comp_attach,localizePerm_attach,ha,Prefix.comp_attach]
  · change localizePerm (Prefix.oneBit x false) f
      (((Prefix.oneBit x true).comp Prefix.empty).attach z)=
        (((Prefix.oneBit x true).comp Prefix.empty).attach (twist (1:Γ) z))
    rw [Prefix.comp_empty,twist_one,Equiv.Perm.one_apply,localizePerm_outside _ _
      (oneBit_outside x (Ne.symm Bool.false_ne_true) z)]

abbrev exchange (x:X) : Diagram Γ X :=
  plain (.split x .leaf .leaf) (.split x .leaf .leaf) (Equiv.sumComm _ _)

end Diagram
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end



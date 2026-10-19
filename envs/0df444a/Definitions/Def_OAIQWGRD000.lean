-- Prove2me | Definitions.Def_OAIQWGRD000
-- name    : OAIQWGRD000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T20:02:46.639965+00:00
-- url     : https://prove2.me/theorems/006daf86-7c0e-4ff4-88b8-b5f1099b8e73
-- title:
--   OpenAI group-ring determinant counterexample split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.GroupRingDeterminant.main`. It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/GroupDeterminants` (OpenAI, *A Counterexample to the Group-Ring Determinant Conjecture*, OpenAI Math Release, September 23, 2026, result family 197, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them:
--   - the input proposition `CompanionInput`;
--   - the star structure on group rings (`groupStar`, `groupAlgebraStar`);
--   - the coefficient maps `toRat` and `toMod`;
--   - the regular representation on $\ell^2(G)^n$ (`regularOperator`, `complexRepresentation`) and the closed group algebra;
--   - the block matrices of the transfer construction (`transferMatrix`, shears, `projectionReweight`);
--   - the lamp group of a group $H$ (`LampGroup`, a subgroup of the wreath product `Multiplicative (ZMod 3) ≀ᵣ H`) with its rational projections (`projection`), their integral numerators and the denominators $3^{|S|+1}$.
--
--   It also contains the lemmas these definitions use in their bodies.
--
--   The definitions of the published statement (`Hilbert`, `identityVector`, `groupTrace`, `fkDet`, `IsRegularOperator`, `rationalMatrix`, `MainStatement`) are not repeated: the bundle imports them from the published bundle `Def_GroupRingDeterminant`. It imports no other bundle.
--
--   Modules: `ClosedAlgebra`, `ClosedTrace`, `ComplexRepresentation`, `CyclicAverage`, `DefectProjections`, `Defects`, `FiniteFields`, `GroupAlgebraStar`, `IndexedRepresentation`, `IntegralTransfer`, `LampCoefficients`, `LampDenominators`, `LampProjections`, `Lamps`, `ModularLifting`, `ProductSupport`, `RationalRepresentation`, `RegularAdjoint`, `RegularOperators`, `TraceLog`, `TransferAlgebra`, `TransferTrace`, `WeightedProjections`, `WeightedTrace`.
--
--   OpenAI's proof also re-proves the counterexample to Kaplansky's direct-finiteness conjecture in characteristic two. This split does not: the proof imports the published statement `OAI.KaplanskyCounterexample.finitelyPresented_counterexample` instead.
-- source:
--   OpenAI, A Counterexample to the Group-Ring Determinant Conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 197; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-the-Group-Ring-Determinant-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/GroupDeterminants at commit adc7f12

import Mathlib
import Definitions.Def_GroupRingDeterminant

section
-- module Solutions.OAIQW_GroupRingDeterminant.Defects
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR ud ul um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

def CompanionInput : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
    (H : Type) (_ : Group H) (_ : Group.FG H)
    (a b : MonoidAlgebra K H), a * b = 1 ∧ b * a ≠ 1

section CornerLifting
variable {R : Type uR} [Ring R]

def cornerSeries (e z : R) (k : ℕ) : R :=
  e * ∑ i ∈ Finset.range k, (e - z) ^ i

end CornerLifting

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ModularLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uA um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ModularKernel
variable (k : ℕ) (hk : 0 < k)

def reduceTwo : ZMod (2 ^ k) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt hk)) (ZMod 2)

variable {G : Type uG} [Group G]

def reduceGroupTwo : MonoidAlgebra (ZMod (2 ^ k)) G →+* MonoidAlgebra (ZMod 2) G :=
  MonoidAlgebra.mapRingHom G (reduceTwo k hk)

def halfGroup (a : MonoidAlgebra (ZMod (2 ^ k)) G) :
    MonoidAlgebra (ZMod (2 ^ k)) G :=
  MonoidAlgebra.ofCoeff (a.coeff.mapRange
    (fun c => (c.val / 2 : ℕ)) (by simp))

end ModularKernel

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularAction
open scoped ENNReal
variable {G : Type} [Group G] {n : ℕ}

def reindex (e : (Fin n × G) ≃ (Fin n × G)) : Hilbert G n →ₗᵢ[ℂ] Hilbert G n where
  toFun ξ := ⟨fun a => ξ (e a), memℓp_gen
    (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩
  map_add' ξ η := by ext a; rfl
  map_smul' z ξ := by ext a; rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun a => ‖ξ a‖ ^ (2 : ℝ≥0∞).toReal)

def cutComponent (i : Fin n) : Hilbert G n →L[ℂ] Hilbert G n := by
  classical
  let f : Hilbert G n →ₗ[ℂ] Hilbert G n := {
    toFun ξ := ⟨fun a => if a.1 = i then ξ a else 0,
      (lp.memℓp ξ).mono' (fun a => by split_ifs <;> simp)⟩
    map_add' ξ η := by
      ext a
      change (if a.1 = i then ξ a + η a else 0) =
        (if a.1 = i then ξ a else 0) + (if a.1 = i then η a else 0)
      split_ifs <;> simp
    map_smul' z ξ := by
      ext a
      change (if a.1 = i then z • ξ a else 0) = z • (if a.1 = i then ξ a else 0)
      split_ifs <;> simp }
  exact f.mkContinuous 1 (fun ξ => by
    simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (x := f ξ) (y := ξ) (fun a => by
        change ‖ite (a.1 = i) (ξ a) 0‖ ≤ ‖ξ a‖
        split_ifs <;> simp))

omit [Group G] in
@[simp] theorem cutComponent_apply (i : Fin n) (ξ : Hilbert G n) (a : Fin n × G) :
    cutComponent i ξ a = if a.1 = i then ξ a else 0 := rfl

def elementaryOperator (i j : Fin n) (g : G) : Hilbert G n →L[ℂ] Hilbert G n :=
  (cutComponent i).comp (reindex
    (Equiv.prodCongr (Equiv.swap i j) (Equiv.mulLeft g⁻¹))).toContinuousLinearMap

theorem elementaryOperator_apply (i j : Fin n) (g : G) (ξ : Hilbert G n)
    (a : Fin n) (h : G) :
    elementaryOperator i j g ξ (a, h) = if a = i then ξ (j, g⁻¹ * h) else 0 := by
  classical
  by_cases hi : a = i
  · subst a
    simp [elementaryOperator, reindex, cutComponent_apply]
  · simp [elementaryOperator, cutComponent_apply, hi]

def regularOperator (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)) :
    Hilbert G n →L[ℂ] Hilbert G n :=
  ∑ i : Fin n, ∑ j : Fin n, (A i j).coeff.sum
    (fun g z => (z : ℂ) • elementaryOperator i j g)

end RegularAction

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.TransferAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uF uR ur um

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ProjectionScalars
variable {F : Type uF} {R : Type uR} [Field F] [Ring R] [Algebra F R]

def projectionReweight (P : R) (a b : F) : R := a • P + b • (1 - P)

theorem projectionReweight_mul (P : R) (hP : P * P = P) (a b c d : F) :
    projectionReweight P a b * projectionReweight P c d =
      projectionReweight P (a * c) (b * d) := by
  have h₁ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have h₂ : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have h₃ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  simp only [projectionReweight, add_mul, mul_add, smul_mul_smul_comm, hP,
    h₁, h₂, h₃, smul_zero, add_zero, zero_add]

@[simp] theorem projectionReweight_one (P : R) : projectionReweight P (1 : F) 1 = 1 := by
  simp [projectionReweight]

def projectionReweightUnit (P : R) (hP : P * P = P) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Rˣ where
  val := projectionReweight P a b
  inv := projectionReweight P a⁻¹ b⁻¹
  val_inv := by rw [projectionReweight_mul P hP]; simp [ha, hb]
  inv_val := by rw [projectionReweight_mul P hP]; simp [ha, hb]

end ProjectionScalars

section ShearAlgebra
variable {R : Type uR} {r : Type ur} {m : Type um} [Ring R] [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

def lowerShear (S : Matrix m r R) : Matrix (r ⊕ m) (r ⊕ m) R :=
  Matrix.fromBlocks 1 0 S 1

def upperShear (T : Matrix r m R) : Matrix (r ⊕ m) (r ⊕ m) R :=
  Matrix.fromBlocks 1 T 0 1

theorem lowerShear_neg (S : Matrix m r R) : lowerShear S * lowerShear (-S) = 1 := by
  simp [lowerShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem upperShear_neg (T : Matrix r m R) : upperShear T * upperShear (-T) = 1 := by
  simp [upperShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

def lowerShearUnit (S : Matrix m r R) : (Matrix (r ⊕ m) (r ⊕ m) R)ˣ where
  val := lowerShear S
  inv := lowerShear (-S)
  val_inv := lowerShear_neg S
  inv_val := by simpa using lowerShear_neg (-S)

def upperShearUnit (T : Matrix r m R) : (Matrix (r ⊕ m) (r ⊕ m) R)ˣ where
  val := upperShear T
  inv := upperShear (-T)
  val_inv := upperShear_neg T
  inv_val := by simpa using upperShear_neg (-T)

def blockDiagonalUnit (a : (Matrix r r R)ˣ) (b : (Matrix m m R)ˣ) :
    (Matrix (r ⊕ m) (r ⊕ m) R)ˣ where
  val := Matrix.fromBlocks ↑a 0 0 ↑b
  inv := Matrix.fromBlocks ↑a⁻¹ 0 0 ↑b⁻¹
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

end ShearAlgebra

section TransferAlgebra
variable {F : Type uF} {R : Type uR} {r : Type ur} {m : Type um} [Field F] [Ring R] [Algebra F R]
variable [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

def transferMatrix (q : F) (P : Matrix m m R) (U : Matrix m r R) (V : Matrix r m R) :
    Matrix (r ⊕ m) (r ⊕ m) R :=
  Matrix.fromBlocks (q • 1) V U (q⁻¹ • (U * V - P - q • (1 - P)))

end TransferAlgebra

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.IntegralTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section IntegralTransfer
variable {G : Type uG} {m : Type um} {r : Type ur} [Group G] [Fintype m] [DecidableEq m]
  [Fintype r] [DecidableEq r]

def divideGroup (q : ℕ) (a : MonoidAlgebra ℤ G) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.ofCoeff (a.coeff.mapRange (fun z => z / (q : ℤ)) (by simp))

def toRat : MonoidAlgebra ℤ G →+* MonoidAlgebra ℚ G :=
  MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ)

def toMod (q : ℕ) : MonoidAlgebra ℤ G →+* MonoidAlgebra (ZMod q) G :=
  MonoidAlgebra.mapRingHom G (Int.castRingHom (ZMod q))

end IntegralTransfer

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ComplexRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ComplexRegular
variable {G : Type} [Group G] {n : ℕ}

def shiftFunctions : G →* Module.End ℂ (G → ℂ) where
  toFun g := {
    toFun f h := f (g⁻¹ * h)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by ext f h; simp
  map_mul' g h := by ext f a; simp [mul_assoc]

def convolutionHom : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ (G → ℂ) :=
  MonoidAlgebra.lift ℂ (Module.End ℂ (G → ℂ)) G shiftFunctions

theorem convolutionHom_apply (a : MonoidAlgebra ℂ G) (f : G → ℂ) (h : G) :
    convolutionHom a f h = a.coeff.sum fun g z => z * f (g⁻¹ * h) := by
  simp only [convolutionHom, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl

local instance functionModule : Module (MonoidAlgebra ℂ G) (G → ℂ) :=
  Module.compHom (G → ℂ) convolutionHom.toRingHom

open scoped Matrix.Module

def complexOperator (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    Hilbert G n →L[ℂ] Hilbert G n :=
  ∑ i : Fin n, ∑ j : Fin n, (A i j).coeff.sum
    (fun g z => z • elementaryOperator i j g)

theorem complexOperator_apply (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G))
    (ξ : Hilbert G n) (i : Fin n) (h : G) :
    complexOperator A ξ (i, h) = ∑ j : Fin n,
      (A i j).coeff.sum fun g z => z * ξ (j, g⁻¹ * h) := by
  classical
  simp only [complexOperator, Finsupp.sum, sum_apply,
    smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, elementaryOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [Ne.symm hbi]
  · simp

theorem complexOperator_curry (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G))
    (ξ : Hilbert G n) :
    Function.curry (complexOperator A ξ) = A • Function.curry (ξ : Fin n × G → ℂ) := by
  funext i h
  rw [Matrix.Module.smul_apply]
  simp only [Finset.sum_apply]
  rw [Function.curry_apply, complexOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact (convolutionHom_apply (A i j) (fun g => ξ (j, g)) h).symm

theorem complexOperator_mul (A B : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (A * B) = complexOperator A * complexOperator B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext a
  obtain ⟨i, h⟩ := a
  have he : Function.curry (complexOperator (A * B) ξ) =
      Function.curry (complexOperator A (complexOperator B ξ)) := by
    rw [complexOperator_curry, mul_smul, complexOperator_curry, complexOperator_curry]
  exact congrFun (congrFun he i) h

theorem complexOperator_one : complexOperator (1 : Matrix (Fin n) (Fin n)
    (MonoidAlgebra ℂ G)) = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext a
  obtain ⟨i, h⟩ := a
  have he := complexOperator_curry (1 : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) ξ
  rw [one_smul] at he
  exact congrFun (congrFun he i) h

theorem complexOperator_add (A B : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (A + B) = complexOperator A + complexOperator B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext a
  obtain ⟨i, h⟩ := a
  have he : Function.curry (complexOperator (A + B) ξ) =
      Function.curry (complexOperator A ξ) + Function.curry (complexOperator B ξ) := by
    rw [complexOperator_curry, add_smul, complexOperator_curry, complexOperator_curry]
  exact congrFun (congrFun he i) h

theorem complexOperator_zero : complexOperator (0 : Matrix (Fin n) (Fin n)
    (MonoidAlgebra ℂ G)) = 0 := by
  simp [complexOperator, MonoidAlgebra.coeff_zero]

def complexRepresentation : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G) →+*
    (Hilbert G n →L[ℂ] Hilbert G n) where
  toFun := complexOperator
  map_one' := complexOperator_one
  map_mul' := complexOperator_mul
  map_zero' := complexOperator_zero
  map_add' := complexOperator_add

def groupTraceCLM : (Hilbert G n →L[ℂ] Hilbert G n) →L[ℂ] ℂ :=
  ∑ i : Fin n, (innerSL ℂ (identityVector i)).comp
    (ContinuousLinearMap.apply ℂ (Hilbert G n) (identityVector i))

end ComplexRegular

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.RegularAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularStar
variable {G : Type} [Group G] {n : ℕ}

theorem complexOperator_smul (z : ℂ)
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (z • A) = z • complexOperator A := by
  classical
  unfold complexOperator
  simp only [Matrix.smul_apply, MonoidAlgebra.coeff_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.sum_smul_index (fun g => zero_smul ℂ (elementaryOperator i j g)),
    Finsupp.smul_sum]
  simp only [smul_smul]

def complexAlgebraRepresentation : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G) →ₐ[ℂ]
    (Hilbert G n →L[ℂ] Hilbert G n) :=
  AlgHom.ofLinearMap
    { toFun := complexOperator
      map_add' := complexOperator_add
      map_smul' := complexOperator_smul }
    complexOperator_one complexOperator_mul

theorem elementaryOperator_star (i j : Fin n) (g : G) :
    star (elementaryOperator i j g) = elementaryOperator j i g⁻¹ := by
  classical
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  let e : Fin n × G ≃ Fin n × G :=
    Equiv.prodCongr (Equiv.swap i j) (Equiv.mulLeft g)
  rw [← e.tsum_eq (fun a => inner ℂ (ξ a) (elementaryOperator i j g η a))]
  apply tsum_congr
  rintro ⟨a, h⟩
  simp only [elementaryOperator_apply, e, Equiv.prodCongr_apply]
  by_cases ha : a = j
  · subst a
    simp [elementaryOperator_apply]
  · have hs : Equiv.swap i j a ≠ i := by
      intro hsi
      have := (Equiv.swap i j).injective (hsi.trans (Equiv.swap_apply_right i j).symm)
      exact ha this
    simp [elementaryOperator_apply, ha, hs]

end RegularStar

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ClosedAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section GroupAlgebraClosure
variable {G : Type} [Group G] {n : ℕ}

theorem complexOperator_single (i j : Fin n) (g : G) (z : ℂ) :
    complexOperator (Matrix.single i j (MonoidAlgebra.single g z)) =
      z • elementaryOperator i j g := by
  classical
  unfold complexOperator
  simp only [Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index
          (h := fun groupElement coefficient => coefficient • elementaryOperator i j groupElement)
          (zero_smul ℂ (elementaryOperator i j g))]
    · intro b _ hbj
      simp [Ne.symm hbj]
    · simp
  · intro a _ hai
    simp [Ne.symm hai]
  · simp

def finiteGroupAlgebra : Subalgebra ℂ (Hilbert G n →L[ℂ] Hilbert G n) :=
  complexAlgebraRepresentation.range

theorem elementaryOperator_mem (i j : Fin n) (g : G) :
    elementaryOperator i j g ∈ finiteGroupAlgebra := by
  refine ⟨Matrix.single i j (MonoidAlgebra.single g 1), ?_⟩
  exact (complexOperator_single i j g 1).trans (one_smul _ _)

theorem finiteGroupAlgebra_star {T : Hilbert G n →L[ℂ] Hilbert G n}
    (hT : T ∈ finiteGroupAlgebra) : star T ∈ finiteGroupAlgebra := by
  classical
  obtain ⟨A, rfl⟩ := hT
  change star (complexOperator A) ∈ finiteGroupAlgebra
  rw [complexOperator, star_sum (R := Hilbert G n →L[ℂ] Hilbert G n)]
  apply Subalgebra.sum_mem
  intro i _
  rw [star_sum (R := Hilbert G n →L[ℂ] Hilbert G n)]
  apply Subalgebra.sum_mem
  intro j _
  rw [Finsupp.sum, star_sum (R := Hilbert G n →L[ℂ] Hilbert G n)]
  apply Subalgebra.sum_mem
  intro g _
  rw [star_smul, elementaryOperator_star]
  exact Subalgebra.smul_mem _ (elementaryOperator_mem j i g⁻¹) _

def finiteGroupStarAlgebra : StarSubalgebra ℂ (Hilbert G n →L[ℂ] Hilbert G n) :=
  { finiteGroupAlgebra with star_mem' := finiteGroupAlgebra_star }

def closedGroupAlgebra : StarSubalgebra ℂ (Hilbert G n →L[ℂ] Hilbert G n) :=
  finiteGroupStarAlgebra.topologicalClosure

end GroupAlgebraClosure

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.FiniteFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uF uG ud

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section FiniteFieldPassage

variable {K : Type uK} {F : Type uF} {G : Type uG} {d : Type ud} [Semiring K] [Semiring F] [Monoid G]
variable [Fintype d] [DecidableEq d]

def coeffMatrix (φ : K →+* Matrix d d F) (a : MonoidAlgebra K G) :
    Matrix d d (MonoidAlgebra F G) := fun i j =>
  MonoidAlgebra.ofCoeff (a.coeff.mapRange (fun k => φ k i j) (by simp))

omit [Monoid G] in
@[simp] theorem coeffMatrix_coeff (φ : K →+* Matrix d d F) (a : MonoidAlgebra K G)
    (i j : d) (g : G) : (coeffMatrix φ a i j).coeff g = φ (a.coeff g) i j := rfl

omit [Monoid G] in
@[simp] theorem coeffMatrix_single (φ : K →+* Matrix d d F) (g : G) (k : K) :
    coeffMatrix φ (MonoidAlgebra.single g k) = Matrix.of (fun i j => MonoidAlgebra.single g (φ k i j)) := by
  ext i j h
  classical
  by_cases h = g <;> simp_all [coeffMatrix_coeff, MonoidAlgebra.coeff_single]

@[simp] theorem coeffMatrix_zero (φ : K →+* Matrix d d F) : coeffMatrix (G := G) φ 0 = 0 := by
  ext i j h
  simp

@[simp] theorem coeffMatrix_add (φ : K →+* Matrix d d F) (a b : MonoidAlgebra K G) :
    coeffMatrix φ (a + b) = coeffMatrix φ a + coeffMatrix φ b := by
  ext i j h
  simp

theorem coeffMatrix_mul_single (φ : K →+* Matrix d d F) (g h : G) (k l : K) :
    coeffMatrix φ (MonoidAlgebra.single g k * MonoidAlgebra.single h l) =
      coeffMatrix φ (MonoidAlgebra.single g k) * coeffMatrix φ (MonoidAlgebra.single h l) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [MonoidAlgebra.single_mul_single, coeffMatrix_single, map_mul, Matrix.mul_apply, Matrix.of_apply]
  ext t
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single]
  by_cases ht : g * h = t <;> simp [ht]

theorem coeffMatrix_mul (φ : K →+* Matrix d d F) (a b : MonoidAlgebra K G) :
    coeffMatrix φ (a * b) = coeffMatrix φ a * coeffMatrix φ b := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | single g k =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | single h l => exact coeffMatrix_mul_single φ g h k l
    | add x y hx hy => simp_all [mul_add]
  | add x y hx hy => simp_all [add_mul]

@[simp] theorem coeffMatrix_one (φ : K →+* Matrix d d F) : coeffMatrix (G := G) φ 1 = 1 := by
  classical
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;> simp [MonoidAlgebra.one_def, Matrix.one_apply, hij]

def coeffMatrixHom (φ : K →+* Matrix d d F) :
    MonoidAlgebra K G →+* Matrix d d (MonoidAlgebra F G) where
  toFun := coeffMatrix φ
  map_one' := coeffMatrix_one φ
  map_mul' := coeffMatrix_mul φ
  map_zero' := coeffMatrix_zero φ
  map_add' := coeffMatrix_add φ

end FiniteFieldPassage

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.TraceLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section TraceCFC
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
def nilpotentShearUnit (S : A) (hS : S * S = 0) (x : ℝ) : Aˣ where
  val := 1 + x • S
  inv := 1 - x • S
  val_inv := by
    simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, hS, smul_zero]
    abel
  inv_val := by
    simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hS, smul_zero]
    abel

end TraceCFC

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ClosedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section SubTrace
variable {A : Type uA} [CStarAlgebra A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]

def subTrace (τ : A →L[ℝ] ℂ) : D →L[ℝ] ℂ :=
  τ.comp (D.toSubalgebra.toSubmodule.subtypeL.restrictScalars ℝ)

@[simp] lemma subTrace_apply (τ : A →L[ℝ] ℂ) (a : D) : subTrace D τ a = τ a := rfl

end SubTrace

section ClosedTraceCalculus
variable {G : Type} [Group G] {n : ℕ}

instance closedGroupAlgebra_isClosed :
    IsClosed (closedGroupAlgebra (G := G) (n := n) : Set (Hilbert G n →L[ℂ] Hilbert G n)) :=
  StarSubalgebra.isClosed_topologicalClosure _

def closedRepresentation : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G) →+*
    closedGroupAlgebra (G := G) (n := n) :=
  complexRepresentation.codRestrict closedGroupAlgebra (fun A =>
    StarSubalgebra.le_topologicalClosure _ ⟨A, rfl⟩)

@[simp] theorem closedRepresentation_coe (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    (closedRepresentation A : Hilbert G n →L[ℂ] Hilbert G n) = complexOperator A := rfl

end ClosedTraceCalculus

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.WeightedProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section WeightedPair
variable {A : Type uA} [Ring A] [Algebra ℝ A]
def weightedPair (Q R : A) (a b c : ℝ) : A := a • Q + b • R + c • (1 - Q - R)
end WeightedPair

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.GroupAlgebraStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR uG uF uS uH

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section GroupStar
variable {R : Type uR} {G : Type uG} [Semiring R] [StarRing R] [Group G]

def groupStar (a : MonoidAlgebra R G) : MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainAddEquiv R (Equiv.inv G)
    (MonoidAlgebra.map (starAddEquiv : R ≃+ R).toAddMonoidHom a)

@[simp] lemma groupStar_coeff (a : MonoidAlgebra R G) (g : G) :
    (groupStar a).coeff g = star (a.coeff g⁻¹) := by
  simp [groupStar, MonoidAlgebra.coeff_mapDomainAddEquiv]

@[simp] lemma groupStar_single (g : G) (r : R) :
    groupStar (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ (star r) := by
  classical
  ext h
  simp only [groupStar_coeff, MonoidAlgebra.coeff_single]
  by_cases hh : g = h⁻¹
  · have he : g⁻¹ = h := by rw [hh, inv_inv]
    simp [hh]
  · have he : g⁻¹ ≠ h := fun he => hh (by rw [← he, inv_inv])
    simp [hh, he]

@[simp] lemma groupStar_zero : groupStar (0 : MonoidAlgebra R G) = 0 := by ext; simp

@[simp] lemma groupStar_add (a b : MonoidAlgebra R G) :
    groupStar (a + b) = groupStar a + groupStar b := by ext; simp

@[simp] lemma groupStar_star (a : MonoidAlgebra R G) : groupStar (groupStar a) = a := by ext; simp

lemma groupStar_mul (a b : MonoidAlgebra R G) : groupStar (a * b) = groupStar b * groupStar a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, groupStar_add, ha, hb, mul_add]
  | single g r =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [mul_add, groupStar_add, ha, hb, add_mul]
    | single h s => simp [MonoidAlgebra.single_mul_single]

instance groupAlgebraStar : StarRing (MonoidAlgebra R G) where
  star := groupStar
  star_involutive := groupStar_star
  star_mul := groupStar_mul
  star_add := groupStar_add

@[simp] lemma star_groupAlgebra_coeff (a : MonoidAlgebra R G) (g : G) :
    (star a).coeff g = star (a.coeff g⁻¹) := groupStar_coeff a g

@[simp] lemma star_groupAlgebra_single (g : G) (r : R) :
    star (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ (star r) := groupStar_single g r

instance groupAlgebraStarModule {F : Type uF} [CommSemiring F] [StarRing F]
    [Algebra F R] [StarModule F R] : StarModule F (MonoidAlgebra R G) where
  star_smul c a := by ext; simp

end GroupStar

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.CyclicAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace AverageDraft
section Algebra
variable {A : Type uA} [Ring A] [Algebra ℚ A]
def thirdAverage (z : A) : A := (1 / 3 : ℚ) • (1 + z + z * z)
end Algebra
end AverageDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.ProductSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uB uC uI

noncomputable section
open scoped BigOperators Pointwise

namespace SupportDraft
variable {B : Type uB} {C : Type uC} {I : Type uI} [CommGroup B] [Group C]
variable (coord : I → B →* C)

def SupportedOn (s : Set I) (a : MonoidAlgebra ℚ B) : Prop :=
  ∀ b, a.coeff b ≠ 0 → ∀ i, i ∉ s → coord i b = 1

end SupportDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.Lamps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampDraft
variable (H : Type uH) [Group H]
local instance instDecidableEq_solutions : DecidableEq H := Classical.decEq H
abbrev FullLamp := Multiplicative (ZMod 3) ≀ᵣ H

def coordinate (h : H) : FullLamp H := by
  classical
  exact ⟨fun t => if t = h then Multiplicative.ofAdd 1 else 1, 1⟩

def lampSubgroup : Subgroup (FullLamp H) :=
  (RegularWreathProduct.inl : H →* FullLamp H).range ⊔
    Subgroup.closure {coordinate H 1}

abbrev LampGroup := lampSubgroup H

instance lampGroup_fg [Group.FG H] : Group.FG (LampGroup H) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  apply Subgroup.FG.sup
  · exact (Group.fg_iff_subgroup_fg _).mp inferInstance
  · exact ⟨{coordinate H 1}, by simp⟩

def shift : H →* LampGroup H :=
  (RegularWreathProduct.inl : H →* FullLamp H).codRestrict (lampSubgroup H)
    (fun h => (show (RegularWreathProduct.inl : H →* FullLamp H).range ≤ lampSubgroup H from le_sup_left) (show RegularWreathProduct.inl h ∈
      (RegularWreathProduct.inl : H →* FullLamp H).range from ⟨h, rfl⟩))

def lampSeed : LampGroup H := ⟨coordinate H 1,
  (show Subgroup.closure {coordinate H 1} ≤ lampSubgroup H from le_sup_right)
    (Subgroup.subset_closure (Set.mem_singleton _))⟩

def lamp (h : H) : LampGroup H := shift H h * lampSeed H * (shift H h)⁻¹

@[simp] theorem shift_coe (h : H) : (shift H h : FullLamp H) = RegularWreathProduct.inl h := rfl

@[simp] theorem lamp_coe (h : H) : (lamp H h : FullLamp H) = coordinate H h := by
  classical
  apply RegularWreathProduct.ext
  · funext t
    simp only [lamp, Subgroup.coe_mul, Subgroup.coe_inv, shift_coe, lampSeed,
      RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      RegularWreathProduct.left_inl, RegularWreathProduct.right_inl,
      RegularWreathProduct.inv_left, Pi.mul_apply, Pi.one_apply,
      Pi.inv_apply, inv_one, mul_one, one_mul, coordinate, inv_mul_eq_one, eq_comm]
  · simp [lamp, lampSeed, coordinate]

def lampRight : LampGroup H →* H :=
  (RegularWreathProduct.rightHom : FullLamp H →* H).comp (lampSubgroup H).subtype

abbrev BaseGroup := (lampRight H).ker

instance baseGroup_commGroup : CommGroup (BaseGroup H) :=
  { (inferInstance : Group (BaseGroup H)) with
    mul_comm := by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      apply RegularWreathProduct.ext
      · funext t
        have ha : ((a : LampGroup H) : FullLamp H).right = 1 := a.property
        have hb : ((b : LampGroup H) : FullLamp H).right = 1 := b.property
        simp [RegularWreathProduct.mul_left, ha, hb, mul_comm]
      · change ((a : LampGroup H) : FullLamp H).right * ((b : LampGroup H) : FullLamp H).right =
          ((b : LampGroup H) : FullLamp H).right * ((a : LampGroup H) : FullLamp H).right
        have ha : ((a : LampGroup H) : FullLamp H).right = 1 := a.property
        have hb : ((b : LampGroup H) : FullLamp H).right = 1 := b.property
        rw [ha, hb] }

def baseLamp (h : H) : BaseGroup H := ⟨lamp H h, by
  change ((lamp H h : LampGroup H) : FullLamp H).right = 1
  rw [lamp_coe]; rfl⟩

def baseCoordinate (h : H) : BaseGroup H →* Multiplicative (ZMod 3) where
  toFun a := ((a : LampGroup H) : FullLamp H).left h
  map_one' := rfl
  map_mul' a b := by
    have ha : ((a : LampGroup H) : FullLamp H).right = 1 := a.property
    change (((a : LampGroup H) : FullLamp H).left h *
      ((b : LampGroup H) : FullLamp H).left (((a : LampGroup H) : FullLamp H).right⁻¹ * h)) = _
    simp [ha]

@[simp] lemma baseCoordinate_baseLamp (h t : H) :
    baseCoordinate H t (baseLamp H h) = if t = h then Multiplicative.ofAdd 1 else 1 := by
  classical
  change (lamp H h : FullLamp H).left t = _
  rw [lamp_coe]; rfl

end LampDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.LampProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft AverageDraft SupportDraft GroupRingDeterminant
variable (H : Type uH) [Group H]
local instance instDecidableEq_solutions : DecidableEq H := Classical.decEq H

def baseAverage (h : H) : MonoidAlgebra ℚ (BaseGroup H) :=
  thirdAverage (MonoidAlgebra.single (baseLamp H h) 1)

def baseProjection (S : Finset H) : MonoidAlgebra ℚ (BaseGroup H) :=
  baseAverage H 1 * ∏ s ∈ S, (1 - baseAverage H s)

end LampProjectionDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.LampCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH uR

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft AverageDraft SupportDraft GroupRingDeterminant
variable (H : Type uH) [Group H]
local instance instDecidableEq_solutions_1 : DecidableEq H := Classical.decEq H

variable (R : Type uR) [CommRing R]
def baseEmbedding : MonoidAlgebra R (BaseGroup H) →+* MonoidAlgebra R (LampGroup H) :=
  MonoidAlgebra.mapDomainRingHom R (BaseGroup H).subtype

@[simp] lemma baseEmbedding_coeff_one (a : MonoidAlgebra R (BaseGroup H)) :
    (baseEmbedding H R a).coeff 1 = a.coeff 1 := by
  exact Finsupp.mapDomain_apply (Subgroup.subtype_injective (BaseGroup H)) a.coeff 1

variable {R}
def fullLampSymbol (h : H) : MonoidAlgebra R (LampGroup H) := MonoidAlgebra.single (lamp H h) 1

def shiftSymbol (h : H) : MonoidAlgebra R (LampGroup H) := MonoidAlgebra.single (shift H h) 1

def projection (S : Finset H) : MonoidAlgebra ℚ (LampGroup H) :=
  baseEmbedding H ℚ (baseProjection H S)

def average (h : H) : MonoidAlgebra ℚ (LampGroup H) := baseEmbedding H ℚ (baseAverage H h)

def baseSum (h : H) : MonoidAlgebra ℤ (BaseGroup H) :=
  1 + MonoidAlgebra.single (baseLamp H h) 1 + MonoidAlgebra.single (baseLamp H h) 1 ^ 2

def baseNumerator (S : Finset H) : MonoidAlgebra ℤ (BaseGroup H) :=
  baseSum H 1 * ∏ s ∈ S, (3 - baseSum H s)

def denominator (S : Finset H) : ℕ := 3 ^ (S.card + 1)

def numerator (S : Finset H) : MonoidAlgebra ℤ (LampGroup H) :=
  baseEmbedding H ℤ (baseNumerator H S)

def intToRat : MonoidAlgebra ℤ (BaseGroup H) →+* MonoidAlgebra ℚ (BaseGroup H) :=
  MonoidAlgebra.mapRingHom _ (Int.castRingHom ℚ)

end LampProjectionDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.LampDenominators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft GroupRingDeterminant
variable (H : Type uH) [Group H]

local instance instDecidableEq_solutions_2_r089032_1 : DecidableEq H := Classical.decEq H
def fullIntToRat : MonoidAlgebra ℤ (LampGroup H) →+* MonoidAlgebra ℚ (LampGroup H) :=
  MonoidAlgebra.mapRingHom _ (Int.castRingHom ℚ)
def fullIntToBin : MonoidAlgebra ℤ (LampGroup H) →+* MonoidAlgebra (ZMod 2) (LampGroup H) :=
  MonoidAlgebra.mapRingHom _ (Int.castRingHom (ZMod 2))

def binaryProjection (S : Finset H) : MonoidAlgebra (ZMod 2) (LampGroup H) :=
  fullIntToBin H (numerator H S)

end LampProjectionDraft

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.DefectProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
open LampDraft LampProjectionDraft
variable {H : Type} [Group H]

def lampRingEmbedding (R : Type) [Semiring R] :
    MonoidAlgebra R H →+* MonoidAlgebra R (LampGroup H) :=
  MonoidAlgebra.mapDomainRingHom R (shift H)

end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.IndexedRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant

section IndexedRepresentation
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]

def indexedComplexRepresentation : Matrix I I (MonoidAlgebra ℂ G) →ₐ[ℂ]
    (Hilbert G (Fintype.card I) →L[ℂ] Hilbert G (Fintype.card I)) :=
  complexAlgebraRepresentation.comp (Matrix.reindexAlgEquiv ℂ (MonoidAlgebra ℂ G)
    (Fintype.equivFin I)).toAlgHom

lemma indexedComplexRepresentation_mem (A : Matrix I I (MonoidAlgebra ℂ G)) :
    indexedComplexRepresentation A ∈ closedGroupAlgebra :=
  StarSubalgebra.le_topologicalClosure _ ⟨_, rfl⟩

end IndexedRepresentation
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.WeightedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant

section IndexedTraceCalculus
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]

def indexedClosedRepresentation : Matrix I I (MonoidAlgebra ℂ G) →ₐ[ℂ]
    closedGroupAlgebra (G := G) (n := Fintype.card I) :=
  indexedComplexRepresentation.codRestrict closedGroupAlgebra.toSubalgebra indexedComplexRepresentation_mem

@[simp] lemma indexedClosedRepresentation_coe (A : Matrix I I (MonoidAlgebra ℂ G)) :
    (indexedClosedRepresentation A : Hilbert G (Fintype.card I) →L[ℂ] Hilbert G (Fintype.card I)) =
    indexedComplexRepresentation A := rfl

end IndexedTraceCalculus
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.TransferTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section TransferTrace
variable {G r m : Type} [Group G] [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

def topBlockIdentity : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) :=
  Matrix.fromBlocks 1 0 0 0

def bottomBlock (P : Matrix m m (MonoidAlgebra ℂ G)) :
    Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := Matrix.fromBlocks 0 0 0 P

def lowerNil (U : Matrix m r (MonoidAlgebra ℂ G)) :
    Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := Matrix.fromBlocks 0 0 U 0

def upperNil (V : Matrix r m (MonoidAlgebra ℂ G)) :
    Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℂ G) := Matrix.fromBlocks 0 V 0 0

end TransferTrace
end GroupRingDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_GroupRingDeterminant.RationalRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section RationalMap
variable {G I J : Type} [Group G]

def rationalComplexMap : MonoidAlgebra ℚ G →+* MonoidAlgebra ℂ G :=
  MonoidAlgebra.mapRingHom G (Rat.castHom ℂ)

end RationalMap
end GroupRingDeterminant

end

end OAI
end



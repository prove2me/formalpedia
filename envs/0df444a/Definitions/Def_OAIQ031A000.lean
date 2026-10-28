-- Prove2me | Definitions.Def_OAIQ031A000
-- name    : OAIQ031A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:17.375065+00:00
-- url     : https://prove2.me/theorems/63cf789a-0fb7-4991-9489-2409aaabfa6a
-- title:
--   Definitions bundle OAIQ031A000 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 29 definitions, 6 inductive types or structures, 13 instances and 29 theorems. The definitions and types are `OAI.ArExplicit.BaseAlgebra`, `OAI.ArExplicit.BaseAlgebra.basisVector`, `OAI.ArExplicit.BaseAlgebra.coordinateAddEquiv`, `OAI.ArExplicit.BaseAlgebra.coordinates`, `OAI.ArExplicit.BaseAlgebra.product`, `OAI.ArExplicit.CocycleData.MulMonomial`, `OAI.ArExplicit.CocycleData.QuadMonomial`, `OAI.ArExplicit.CocycleData.QuadMonomial.number`, `OAI.ArExplicit.CocycleData.TripleMonomial`, `OAI.ArExplicit.CocycleData.certificate`, `OAI.ArExplicit.CocycleData.cochain`, `OAI.ArExplicit.CocycleData.contributions`, `OAI.ArExplicit.CocycleData.differentialBlock`, `OAI.ArExplicit.CocycleData.multiplication`, `OAI.ArExplicit.Letter`, `OAI.ArExplicit.SparseParity.insert`, `OAI.ArExplicit.SparseParity.paired`, `OAI.ArExplicit.SparseParity.sort`, `OAI.ArExplicit.T`, `OAI.ArExplicit.T.coefficient`, `OAI.ArExplicit.T.coordinateFunctional`, `OAI.ArExplicit.T.lower`, `OAI.ArExplicit.T.upper`, `OAI.ArExplicit.T.vector`, `OAI.ArExplicit.TIndex`, `OAI.ArExplicit.TIndex.number`, `OAI.ArExplicit.TrivialExtension`, `OAI.ArExplicit.TrivialExtension.coordinates`, `OAI.ArExplicit.TrivialExtension.inl`, `OAI.ArExplicit.TrivialExtension.inr`, `OAI.ArExplicit.TrivialExtension.leftDual`, `OAI.ArExplicit.TrivialExtension.product`, `OAI.ArExplicit.TrivialExtension.rightDual`, `OAI.ArExplicit.TrivialExtension.trace`, `OAI.ArExplicit.TrivialExtension.traceForm`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_BaseAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/BaseAlgebra.lean), [`AuslanderReiten_Algebras_TCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TCoordinates.lean), [`AuslanderReiten_Algebras_TrivialExtension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TrivialExtension.lean), [`AuslanderReiten_Cocycles_CocycleCertificate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCertificate.lean), [`AuslanderReiten_Cocycles_CocycleData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleData.lean), [`AuslanderReiten_Cocycles_CocycleDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleDifferential.lean), [`AuslanderReiten_Cocycles_SparseParity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/SparseParity.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A001`, `OAIQ031A002`, `OAIQ031A005`, `OAIQ031A006`, `OAIQ031A008`, `OAIQ031A009`, `OAIQ031A012` and `OAIQ031A013`; the statement `OAI.ArExplicit.CocycleData.certificate_valid`; the proof of `OAI.ArExplicit.CocycleData.certificate_valid`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

inductive Letter
  | e | x | y | z | u | v | t | j | f | n
  deriving DecidableEq

instance instFintypeLetter : Fintype Letter where
  elems := {.e, .x, .y, .z, .u, .v, .t, .j, .f, .n}
  complete i := by cases i <;> simp

@[simp] theorem Letter.card : Fintype.card Letter = 10 := by decide

@[ext]
structure BaseAlgebra (k : Type*) (q : k) where
  coeff : Letter → k

namespace BaseAlgebra

variable {k : Type*} (q : k)

def coordinates : BaseAlgebra k q ≃ (Letter → k) where
  toFun := coeff
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup [AddCommGroup k] : AddCommGroup (BaseAlgebra k q) :=
  (coordinates q).addCommGroup

variable [CommRing k]

def coordinateAddEquiv : BaseAlgebra k q ≃+ (Letter → k) where
  __ := coordinates q
  map_add' _ _ := rfl

instance instModule : Module k (BaseAlgebra k q) := (coordinateAddEquiv q).module k

@[simp] theorem coeff_zero (i : Letter) : (0 : BaseAlgebra k q).coeff i = 0 := rfl
@[simp] theorem coeff_add (a b : BaseAlgebra k q) (i : Letter) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl
@[simp] theorem coeff_neg (a : BaseAlgebra k q) (i : Letter) :
    (-a).coeff i = -a.coeff i := rfl
@[simp] theorem coeff_smul (r : k) (a : BaseAlgebra k q) (i : Letter) :
    (r • a).coeff i = r * a.coeff i := rfl

open Letter

def product (a b : BaseAlgebra k q) : BaseAlgebra k q := ⟨fun
  | e => a.coeff e * b.coeff e
  | x => a.coeff e * b.coeff x + a.coeff x * b.coeff e + q * a.coeff u * b.coeff t
  | y => a.coeff e * b.coeff y + a.coeff y * b.coeff e + a.coeff u * b.coeff t
  | z => a.coeff e * b.coeff z + a.coeff z * b.coeff e + q * a.coeff x * b.coeff y +
      a.coeff y * b.coeff x + q * a.coeff v * b.coeff t + a.coeff u * b.coeff j
  | u => a.coeff e * b.coeff u + a.coeff u * b.coeff f
  | v => a.coeff e * b.coeff v + a.coeff v * b.coeff f + a.coeff x * b.coeff u +
      a.coeff y * b.coeff u + a.coeff u * b.coeff n
  | t => a.coeff f * b.coeff t + a.coeff t * b.coeff e
  | j => a.coeff f * b.coeff j + a.coeff j * b.coeff e + a.coeff t * b.coeff x +
      q ^ 2 * a.coeff t * b.coeff y + q * a.coeff n * b.coeff t
  | f => a.coeff f * b.coeff f
  | n => a.coeff f * b.coeff n + a.coeff n * b.coeff f +
      (1 + q) * a.coeff t * b.coeff u⟩

instance instMul : Mul (BaseAlgebra k q) := ⟨product q⟩
instance instOne : One (BaseAlgebra k q) := ⟨⟨fun i => if i = e ∨ i = f then 1 else 0⟩⟩

@[simp] theorem coeff_mul (a b : BaseAlgebra k q) :
    (a * b).coeff = (product q a b).coeff := rfl
@[simp] theorem coeff_one (i : Letter) :
    (1 : BaseAlgebra k q).coeff i = if i = e ∨ i = f then 1 else 0 := rfl

theorem product_assoc (a b c : BaseAlgebra k q) : (a * b) * c = a * (b * c) := by
  ext i
  cases i <;> simp only [coeff_mul, product] <;> ring

instance instRing : Ring (BaseAlgebra k q) where
  __ := (inferInstance : AddCommGroup (BaseAlgebra k q))
  mul_assoc := product_assoc q
  one_mul a := by ext i; cases i <;> simp [product]
  mul_one a := by ext i; cases i <;> simp [product]
  left_distrib a b c := by
    ext i
    cases i <;> simp only [coeff_mul, product, coeff_add] <;> ring
  right_distrib a b c := by
    ext i
    cases i <;> simp only [coeff_mul, product, coeff_add] <;> ring
  zero_mul a := by ext i; cases i <;> simp [product]
  mul_zero a := by ext i; cases i <;> simp [product]

instance instAlgebra : Algebra k (BaseAlgebra k q) :=
  Algebra.ofModule
    (by intro r a b; ext i; cases i <;> simp only [coeff_smul, coeff_mul, product] <;> ring)
    (by intro r a b; ext i; cases i <;> simp only [coeff_smul, coeff_mul, product] <;> ring)

def basisVector (i : Letter) : BaseAlgebra k q := ⟨Pi.single i 1⟩

@[simp] theorem coeff_basisVector (i l : Letter) :
    (basisVector q i).coeff l = if l = i then 1 else 0 := by
  simp [basisVector, Pi.single_apply, eq_comm]

end BaseAlgebra
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TrivialExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

@[ext]
structure TrivialExtension where
  base : A
  dual : Module.Dual k A

namespace TrivialExtension

variable {k A}

def coordinates : TrivialExtension k A ≃ A × Module.Dual k A where
  toFun a := (a.base, a.dual)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (TrivialExtension k A) := coordinates.addCommGroup
instance instModule : Module k (TrivialExtension k A) := coordinates.addEquiv.module k

@[simp] theorem base_zero : (0 : TrivialExtension k A).base = 0 := rfl
@[simp] theorem dual_zero : (0 : TrivialExtension k A).dual = 0 := rfl
@[simp] theorem base_add (a b : TrivialExtension k A) : (a + b).base = a.base + b.base := rfl
@[simp] theorem dual_add (a b : TrivialExtension k A) : (a + b).dual = a.dual + b.dual := rfl
@[simp] theorem base_smul (r : k) (a : TrivialExtension k A) : (r • a).base = r • a.base := rfl
@[simp] theorem dual_smul (r : k) (a : TrivialExtension k A) : (r • a).dual = r • a.dual := rfl

def leftDual (a : A) (φ : Module.Dual k A) : Module.Dual k A where
  toFun c := φ (c * a)
  map_add' c d := by simp [add_mul]
  map_smul' r c := by simp

def rightDual (a : A) (φ : Module.Dual k A) : Module.Dual k A where
  toFun c := φ (a * c)
  map_add' c d := by simp [mul_add]
  map_smul' r c := by simp

@[simp] theorem leftDual_apply (a : A) (φ : Module.Dual k A) (c : A) :
    leftDual a φ c = φ (c * a) := rfl
@[simp] theorem rightDual_apply (a : A) (φ : Module.Dual k A) (c : A) :
    rightDual a φ c = φ (a * c) := rfl

def product (a b : TrivialExtension k A) : TrivialExtension k A :=
  ⟨a.base * b.base, leftDual a.base b.dual + rightDual b.base a.dual⟩

instance instMul : Mul (TrivialExtension k A) := ⟨product⟩
instance instOne : One (TrivialExtension k A) := ⟨⟨1, 0⟩⟩

@[simp] theorem base_one : (1 : TrivialExtension k A).base = 1 := rfl
@[simp] theorem dual_one : (1 : TrivialExtension k A).dual = 0 := rfl
@[simp] theorem base_mul (a b : TrivialExtension k A) : (a * b).base = a.base * b.base := rfl
@[simp] theorem dual_mul_apply (a b : TrivialExtension k A) (c : A) :
    (a * b).dual c = b.dual (c * a.base) + a.dual (b.base * c) := rfl

instance instRing : Ring (TrivialExtension k A) where
  __ := (inferInstance : AddCommGroup (TrivialExtension k A))
  mul_assoc a b c := by
    apply TrivialExtension.ext
    · simp only [base_mul, mul_assoc]
    · ext d
      simp [mul_assoc, add_assoc]
  one_mul a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp
  mul_one a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp
  left_distrib a b c := by
    apply TrivialExtension.ext
    · simp [mul_add]
    · ext d; simp [add_mul]; abel
  right_distrib a b c := by
    apply TrivialExtension.ext
    · simp [add_mul]
    · ext d; simp [mul_add]; abel
  zero_mul a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp
  mul_zero a := by
    apply TrivialExtension.ext
    · simp
    · ext d; simp

instance instAlgebra : Algebra k (TrivialExtension k A) :=
  Algebra.ofModule
    (by
      intro r a b
      apply TrivialExtension.ext
      · simp
      · ext d; simp [mul_add])
    (by
      intro r a b
      apply TrivialExtension.ext
      · simp
      · ext d; simp [mul_add])

def inl (a : A) : TrivialExtension k A := ⟨a, 0⟩

def inr (φ : Module.Dual k A) : TrivialExtension k A := ⟨0, φ⟩

@[simp] theorem inr_mul_inr (φ ψ : Module.Dual k A) :
    inr φ * inr ψ = (0 : TrivialExtension k A) := by
  apply TrivialExtension.ext
  · simp [inr]
  · ext d; simp [inr]

def trace : TrivialExtension k A →ₗ[k] k where
  toFun a := a.dual 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem trace_apply (a : TrivialExtension k A) : trace a = a.dual 1 := rfl

def traceForm : LinearMap.BilinForm k (TrivialExtension k A) where
  toFun a :=
    { toFun := fun b => trace (a * b)
      map_add' b c := by simp [mul_add]
      map_smul' r b := by simp }
  map_add' a b := by ext c; simp [add_mul]
  map_smul' r a := by ext b; simp

@[simp] theorem traceForm_apply (a b : TrivialExtension k A) :
    traceForm a b = trace (a * b) := rfl

end TrivialExtension

abbrev T (k : Type*) [Field k] (q : k) := TrivialExtension k (BaseAlgebra k q)

namespace T

variable {k : Type*} [Field k] (q : k)

def coordinateFunctional (i : Letter) : Module.Dual k (BaseAlgebra k q) where
  toFun a := a.coeff i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lower (i : Letter) : T k q := TrivialExtension.inl (BaseAlgebra.basisVector q i)

def upper (i : Letter) : T k q := TrivialExtension.inr (coordinateFunctional q i)

end T

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

abbrev TIndex := Bool × Letter

namespace TIndex

def number : TIndex → ℕ
  | (upper, i) => (if upper then 10 else 0) + match i with
    | .e => 0 | .x => 1 | .y => 2 | .z => 3 | .u => 4
    | .v => 5 | .t => 6 | .j => 7 | .f => 8 | .n => 9

end TIndex

namespace T

open BaseAlgebra TrivialExtension

variable {k : Type*} [Field k] (q : k)

def vector : TIndex → T k q
  | (false, i) => lower q i
  | (true, i) => upper q i

def coefficient (i : TIndex) : T k q →ₗ[k] k where
  toFun a := if i.1 then a.dual (basisVector q i.2) else a.base.coeff i.2
  map_add' a b := by cases i with | mk b i => cases b <;> rfl
  map_smul' r a := by cases i with | mk b i => cases b <;> rfl

@[simp] theorem coefficient_lower (i bidx : Letter) :
    coefficient q (false, i) (lower q bidx) = if i = bidx then 1 else 0 := by
  simp [coefficient, lower, inl]

@[simp] theorem coefficient_upper (i bidx : Letter) :
    coefficient q (true, i) (upper q bidx) = if i = bidx then 1 else 0 := by
  change (basisVector q i).coeff bidx = if i = bidx then 1 else 0
  simp [eq_comm]

@[simp] theorem coefficient_lower_upper (i bidx : Letter) :
    coefficient q (false, i) (upper q bidx) = 0 := rfl

@[simp] theorem coefficient_upper_lower (i bidx : Letter) :
    coefficient q (true, i) (lower q bidx) = 0 := rfl

@[simp] theorem coefficient_vector (i bidx : TIndex) :
    coefficient q i (vector q bidx) = if i = bidx then 1 else 0 := by
  obtain ⟨b, i⟩ := i
  obtain ⟨c, bidx⟩ := bidx
  cases b <;> cases c <;> simp [vector]

end T
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

structure MulMonomial where
  first : TIndex
  second : TIndex
  output : TIndex
  degree : ℕ
  deriving DecidableEq

structure TripleMonomial where
  first : TIndex
  second : TIndex
  third : TIndex
  output : TIndex
  degree : ℕ
  deriving DecidableEq

def multiplication : List MulMonomial := [
  ⟨(false, .e), (false, .e), (false, .e), 0⟩,
  ⟨(false, .e), (false, .x), (false, .x), 0⟩,
  ⟨(false, .x), (false, .e), (false, .x), 0⟩,
  ⟨(false, .e), (false, .y), (false, .y), 0⟩,
  ⟨(false, .y), (false, .e), (false, .y), 0⟩,
  ⟨(false, .e), (false, .z), (false, .z), 0⟩,
  ⟨(false, .z), (false, .e), (false, .z), 0⟩,
  ⟨(false, .e), (false, .u), (false, .u), 0⟩,
  ⟨(false, .u), (false, .f), (false, .u), 0⟩,
  ⟨(false, .e), (false, .v), (false, .v), 0⟩,
  ⟨(false, .v), (false, .f), (false, .v), 0⟩,
  ⟨(false, .f), (false, .t), (false, .t), 0⟩,
  ⟨(false, .t), (false, .e), (false, .t), 0⟩,
  ⟨(false, .f), (false, .j), (false, .j), 0⟩,
  ⟨(false, .j), (false, .e), (false, .j), 0⟩,
  ⟨(false, .f), (false, .f), (false, .f), 0⟩,
  ⟨(false, .f), (false, .n), (false, .n), 0⟩,
  ⟨(false, .n), (false, .f), (false, .n), 0⟩,
  ⟨(false, .x), (false, .y), (false, .z), 1⟩,
  ⟨(false, .y), (false, .x), (false, .z), 0⟩,
  ⟨(false, .x), (false, .u), (false, .v), 0⟩,
  ⟨(false, .y), (false, .u), (false, .v), 0⟩,
  ⟨(false, .t), (false, .x), (false, .j), 0⟩,
  ⟨(false, .t), (false, .y), (false, .j), 2⟩,
  ⟨(false, .u), (false, .t), (false, .y), 0⟩,
  ⟨(false, .u), (false, .t), (false, .x), 1⟩,
  ⟨(false, .v), (false, .t), (false, .z), 1⟩,
  ⟨(false, .u), (false, .j), (false, .z), 0⟩,
  ⟨(false, .t), (false, .u), (false, .n), 0⟩,
  ⟨(false, .t), (false, .u), (false, .n), 1⟩,
  ⟨(false, .n), (false, .t), (false, .j), 1⟩,
  ⟨(false, .u), (false, .n), (false, .v), 0⟩,
  ⟨(false, .e), (true, .e), (true, .e), 0⟩,
  ⟨(true, .e), (false, .e), (true, .e), 0⟩,
  ⟨(false, .e), (true, .x), (true, .x), 0⟩,
  ⟨(true, .x), (false, .e), (true, .x), 0⟩,
  ⟨(false, .e), (true, .y), (true, .y), 0⟩,
  ⟨(true, .y), (false, .e), (true, .y), 0⟩,
  ⟨(false, .e), (true, .z), (true, .z), 0⟩,
  ⟨(true, .z), (false, .e), (true, .z), 0⟩,
  ⟨(true, .u), (false, .e), (true, .u), 0⟩,
  ⟨(true, .v), (false, .e), (true, .v), 0⟩,
  ⟨(false, .e), (true, .t), (true, .t), 0⟩,
  ⟨(false, .e), (true, .j), (true, .j), 0⟩,
  ⟨(false, .x), (true, .x), (true, .e), 0⟩,
  ⟨(true, .x), (false, .x), (true, .e), 0⟩,
  ⟨(false, .x), (true, .z), (true, .y), 0⟩,
  ⟨(true, .z), (false, .x), (true, .y), 1⟩,
  ⟨(true, .v), (false, .x), (true, .u), 0⟩,
  ⟨(false, .x), (true, .j), (true, .t), 0⟩,
  ⟨(false, .y), (true, .y), (true, .e), 0⟩,
  ⟨(true, .y), (false, .y), (true, .e), 0⟩,
  ⟨(false, .y), (true, .z), (true, .x), 1⟩,
  ⟨(true, .z), (false, .y), (true, .x), 0⟩,
  ⟨(true, .v), (false, .y), (true, .u), 0⟩,
  ⟨(false, .y), (true, .j), (true, .t), 2⟩,
  ⟨(false, .z), (true, .z), (true, .e), 0⟩,
  ⟨(true, .z), (false, .z), (true, .e), 0⟩,
  ⟨(true, .x), (false, .u), (true, .t), 1⟩,
  ⟨(true, .y), (false, .u), (true, .t), 0⟩,
  ⟨(true, .z), (false, .u), (true, .j), 0⟩,
  ⟨(false, .u), (true, .u), (true, .e), 0⟩,
  ⟨(true, .u), (false, .u), (true, .f), 0⟩,
  ⟨(false, .u), (true, .v), (true, .x), 0⟩,
  ⟨(false, .u), (true, .v), (true, .y), 0⟩,
  ⟨(true, .v), (false, .u), (true, .n), 0⟩,
  ⟨(false, .u), (true, .n), (true, .t), 0⟩,
  ⟨(false, .u), (true, .n), (true, .t), 1⟩,
  ⟨(true, .z), (false, .v), (true, .t), 1⟩,
  ⟨(false, .v), (true, .v), (true, .e), 0⟩,
  ⟨(true, .v), (false, .v), (true, .f), 0⟩,
  ⟨(false, .t), (true, .x), (true, .u), 1⟩,
  ⟨(false, .t), (true, .y), (true, .u), 0⟩,
  ⟨(false, .t), (true, .z), (true, .v), 1⟩,
  ⟨(true, .t), (false, .t), (true, .e), 0⟩,
  ⟨(false, .t), (true, .t), (true, .f), 0⟩,
  ⟨(true, .j), (false, .t), (true, .x), 0⟩,
  ⟨(true, .j), (false, .t), (true, .y), 2⟩,
  ⟨(false, .t), (true, .j), (true, .n), 1⟩,
  ⟨(true, .n), (false, .t), (true, .u), 0⟩,
  ⟨(true, .n), (false, .t), (true, .u), 1⟩,
  ⟨(false, .j), (true, .z), (true, .u), 0⟩,
  ⟨(true, .j), (false, .j), (true, .e), 0⟩,
  ⟨(false, .j), (true, .j), (true, .f), 0⟩,
  ⟨(false, .f), (true, .u), (true, .u), 0⟩,
  ⟨(false, .f), (true, .v), (true, .v), 0⟩,
  ⟨(true, .t), (false, .f), (true, .t), 0⟩,
  ⟨(true, .j), (false, .f), (true, .j), 0⟩,
  ⟨(false, .f), (true, .f), (true, .f), 0⟩,
  ⟨(true, .f), (false, .f), (true, .f), 0⟩,
  ⟨(false, .f), (true, .n), (true, .n), 0⟩,
  ⟨(true, .n), (false, .f), (true, .n), 0⟩,
  ⟨(false, .n), (true, .v), (true, .u), 0⟩,
  ⟨(true, .j), (false, .n), (true, .t), 1⟩,
  ⟨(false, .n), (true, .n), (true, .f), 0⟩,
  ⟨(true, .n), (false, .n), (true, .f), 0⟩]

def cochain : List TripleMonomial := [
  ⟨(true, .e), (false, .u), (true, .n), (true, .t), 2⟩,
  ⟨(true, .e), (false, .y), (true, .z), (true, .x), 2⟩,
  ⟨(true, .f), (true, .n), (false, .t), (true, .u), 2⟩,
  ⟨(true, .j), (false, .t), (true, .x), (true, .z), 2⟩,
  ⟨(true, .n), (false, .t), (true, .e), (true, .u), 2⟩,
  ⟨(true, .n), (false, .t), (true, .x), (true, .v), 2⟩,
  ⟨(true, .x), (false, .z), (true, .j), (true, .t), 2⟩,
  ⟨(true, .z), (false, .x), (true, .e), (true, .y), 2⟩,
  ⟨(false, .t), (true, .e), (false, .u), (false, .n), 2⟩,
  ⟨(false, .t), (true, .x), (false, .u), (false, .f), 2⟩,
  ⟨(false, .t), (true, .x), (false, .v), (false, .n), 2⟩,
  ⟨(false, .t), (true, .x), (false, .z), (false, .j), 2⟩,
  ⟨(false, .t), (false, .u), (true, .f), (false, .n), 2⟩,
  ⟨(false, .t), (false, .u), (true, .n), (false, .f), 2⟩,
  ⟨(false, .t), (false, .v), (true, .n), (false, .n), 2⟩,
  ⟨(false, .u), (true, .f), (true, .n), (true, .t), 2⟩,
  ⟨(false, .v), (true, .n), (true, .n), (true, .t), 2⟩,
  ⟨(false, .v), (false, .t), (true, .j), (false, .u), 2⟩,
  ⟨(false, .x), (true, .e), (false, .y), (false, .z), 2⟩,
  ⟨(false, .z), (true, .j), (false, .t), (false, .x), 2⟩,
  ⟨(true, .e), (false, .u), (true, .u), (true, .e), 1⟩,
  ⟨(true, .e), (false, .u), (true, .v), (true, .x), 1⟩,
  ⟨(true, .e), (false, .v), (true, .v), (true, .e), 1⟩,
  ⟨(true, .e), (false, .x), (true, .x), (true, .e), 1⟩,
  ⟨(true, .e), (false, .y), (true, .y), (true, .e), 1⟩,
  ⟨(true, .e), (false, .z), (true, .z), (true, .e), 1⟩,
  ⟨(true, .f), (true, .n), (false, .n), (true, .f), 1⟩,
  ⟨(true, .f), (true, .v), (false, .v), (true, .f), 1⟩,
  ⟨(true, .f), (true, .v), (false, .x), (true, .u), 1⟩,
  ⟨(true, .f), (false, .t), (true, .t), (true, .f), 1⟩,
  ⟨(true, .f), (false, .t), (true, .y), (true, .u), 1⟩,
  ⟨(true, .f), (false, .t), (false, .u), (false, .n), 1⟩,
  ⟨(true, .f), (false, .t), (false, .x), (false, .j), 1⟩,
  ⟨(true, .j), (true, .f), (false, .t), (true, .x), 1⟩,
  ⟨(true, .j), (true, .n), (false, .t), (true, .z), 1⟩,
  ⟨(true, .j), (true, .u), (false, .y), (true, .x), 1⟩,
  ⟨(true, .j), (true, .v), (false, .y), (true, .z), 1⟩,
  ⟨(true, .j), (false, .j), (true, .e), (true, .e), 1⟩,
  ⟨(true, .j), (false, .j), (true, .t), (true, .t), 1⟩,
  ⟨(true, .j), (false, .j), (true, .x), (true, .x), 1⟩,
  ⟨(true, .n), (true, .f), (false, .t), (true, .u), 1⟩,
  ⟨(true, .n), (true, .n), (false, .t), (true, .v), 1⟩,
  ⟨(true, .n), (true, .u), (false, .y), (true, .u), 1⟩,
  ⟨(true, .n), (true, .v), (false, .y), (true, .v), 1⟩,
  ⟨(true, .n), (false, .j), (true, .j), (true, .n), 1⟩,
  ⟨(true, .n), (false, .j), (true, .z), (true, .v), 1⟩,
  ⟨(true, .n), (false, .n), (true, .n), (true, .n), 1⟩,
  ⟨(true, .n), (false, .n), (true, .v), (true, .v), 1⟩,
  ⟨(true, .n), (false, .t), (false, .u), (false, .f), 1⟩,
  ⟨(true, .n), (false, .t), (false, .v), (false, .n), 1⟩,
  ⟨(true, .n), (false, .t), (false, .z), (false, .j), 1⟩,
  ⟨(true, .t), (false, .t), (true, .e), (true, .e), 1⟩,
  ⟨(true, .t), (false, .t), (true, .x), (true, .x), 1⟩,
  ⟨(true, .u), (false, .u), (true, .f), (true, .f), 1⟩,
  ⟨(true, .u), (false, .u), (true, .u), (true, .u), 1⟩,
  ⟨(true, .u), (false, .v), (true, .n), (true, .f), 1⟩,
  ⟨(true, .u), (false, .v), (true, .v), (true, .u), 1⟩,
  ⟨(true, .u), (false, .x), (true, .x), (true, .u), 1⟩,
  ⟨(true, .u), (false, .y), (false, .u), (false, .n), 1⟩,
  ⟨(true, .u), (false, .y), (false, .x), (false, .j), 1⟩,
  ⟨(true, .u), (false, .z), (true, .z), (true, .u), 1⟩,
  ⟨(true, .v), (false, .v), (true, .n), (true, .n), 1⟩,
  ⟨(true, .v), (false, .v), (true, .v), (true, .v), 1⟩,
  ⟨(true, .v), (false, .x), (true, .e), (true, .u), 1⟩,
  ⟨(true, .v), (false, .x), (true, .x), (true, .v), 1⟩,
  ⟨(true, .v), (false, .y), (false, .u), (false, .f), 1⟩,
  ⟨(true, .v), (false, .y), (false, .v), (false, .n), 1⟩,
  ⟨(true, .v), (false, .y), (false, .z), (false, .j), 1⟩,
  ⟨(true, .v), (false, .z), (true, .z), (true, .v), 1⟩,
  ⟨(true, .x), (false, .x), (true, .e), (true, .e), 1⟩,
  ⟨(true, .x), (false, .x), (true, .x), (true, .x), 1⟩,
  ⟨(true, .y), (false, .u), (true, .f), (true, .t), 1⟩,
  ⟨(true, .y), (false, .u), (true, .u), (true, .y), 1⟩,
  ⟨(true, .y), (false, .v), (true, .n), (true, .t), 1⟩,
  ⟨(true, .y), (false, .v), (true, .v), (true, .y), 1⟩,
  ⟨(true, .y), (false, .x), (true, .x), (true, .y), 1⟩,
  ⟨(true, .y), (false, .y), (true, .e), (true, .e), 1⟩,
  ⟨(true, .y), (false, .y), (true, .j), (true, .j), 1⟩,
  ⟨(true, .y), (false, .y), (true, .t), (true, .t), 1⟩,
  ⟨(true, .y), (false, .y), (true, .x), (true, .x), 1⟩,
  ⟨(true, .y), (false, .y), (true, .y), (true, .y), 1⟩,
  ⟨(true, .y), (false, .y), (true, .z), (true, .z), 1⟩,
  ⟨(true, .y), (false, .z), (true, .z), (true, .y), 1⟩,
  ⟨(true, .z), (false, .x), (true, .x), (true, .z), 1⟩,
  ⟨(true, .z), (false, .z), (true, .e), (true, .e), 1⟩,
  ⟨(true, .z), (false, .z), (true, .j), (true, .j), 1⟩,
  ⟨(true, .z), (false, .z), (true, .t), (true, .t), 1⟩,
  ⟨(true, .z), (false, .z), (true, .x), (true, .x), 1⟩,
  ⟨(false, .j), (true, .j), (true, .f), (true, .f), 1⟩,
  ⟨(false, .j), (true, .j), (true, .u), (true, .u), 1⟩,
  ⟨(false, .j), (true, .j), (false, .j), (false, .j), 1⟩,
  ⟨(false, .j), (true, .j), (false, .n), (false, .n), 1⟩,
  ⟨(false, .j), (true, .y), (false, .y), (false, .j), 1⟩,
  ⟨(false, .j), (true, .z), (false, .v), (false, .n), 1⟩,
  ⟨(false, .j), (true, .z), (false, .z), (false, .j), 1⟩,
  ⟨(false, .n), (true, .n), (true, .f), (true, .f), 1⟩,
  ⟨(false, .n), (true, .n), (true, .u), (true, .u), 1⟩,
  ⟨(false, .n), (false, .t), (true, .t), (false, .n), 1⟩,
  ⟨(false, .t), (true, .j), (false, .j), (false, .t), 1⟩,
  ⟨(false, .t), (true, .t), (true, .n), (true, .n), 1⟩,
  ⟨(false, .t), (true, .t), (true, .v), (true, .v), 1⟩,
  ⟨(false, .t), (true, .t), (false, .t), (false, .t), 1⟩,
  ⟨(false, .t), (true, .y), (false, .y), (false, .t), 1⟩,
  ⟨(false, .t), (true, .z), (false, .z), (false, .t), 1⟩,
  ⟨(false, .t), (false, .z), (true, .j), (false, .n), 1⟩,
  ⟨(false, .u), (true, .f), (true, .v), (true, .x), 1⟩,
  ⟨(false, .u), (true, .f), (false, .t), (false, .y), 1⟩,
  ⟨(false, .u), (true, .n), (true, .f), (true, .t), 1⟩,
  ⟨(false, .u), (true, .n), (true, .u), (true, .y), 1⟩,
  ⟨(false, .u), (true, .n), (false, .t), (false, .e), 1⟩,
  ⟨(false, .u), (true, .u), (false, .y), (false, .y), 1⟩,
  ⟨(false, .u), (true, .v), (false, .y), (false, .e), 1⟩,
  ⟨(false, .u), (false, .j), (true, .j), (false, .u), 1⟩,
  ⟨(false, .v), (true, .n), (true, .u), (true, .e), 1⟩,
  ⟨(false, .v), (true, .n), (true, .v), (true, .x), 1⟩,
  ⟨(false, .v), (true, .n), (false, .t), (false, .y), 1⟩,
  ⟨(false, .v), (true, .v), (false, .y), (false, .y), 1⟩,
  ⟨(false, .v), (false, .t), (true, .t), (false, .v), 1⟩,
  ⟨(false, .x), (true, .e), (false, .u), (false, .v), 1⟩,
  ⟨(false, .x), (true, .j), (true, .f), (true, .t), 1⟩,
  ⟨(false, .x), (true, .j), (true, .u), (true, .y), 1⟩,
  ⟨(false, .x), (true, .j), (false, .j), (false, .x), 1⟩,
  ⟨(false, .x), (true, .j), (false, .t), (false, .e), 1⟩,
  ⟨(false, .x), (true, .t), (false, .t), (false, .x), 1⟩,
  ⟨(false, .x), (true, .x), (false, .u), (false, .u), 1⟩,
  ⟨(false, .x), (true, .x), (false, .v), (false, .v), 1⟩,
  ⟨(false, .x), (true, .x), (false, .y), (false, .y), 1⟩,
  ⟨(false, .x), (true, .x), (false, .z), (false, .z), 1⟩,
  ⟨(false, .x), (true, .y), (false, .y), (false, .x), 1⟩,
  ⟨(false, .x), (true, .z), (false, .y), (false, .e), 1⟩,
  ⟨(false, .x), (true, .z), (false, .z), (false, .x), 1⟩,
  ⟨(false, .x), (false, .u), (true, .f), (false, .v), 1⟩,
  ⟨(false, .x), (false, .u), (true, .n), (false, .u), 1⟩,
  ⟨(false, .x), (false, .v), (true, .n), (false, .v), 1⟩,
  ⟨(false, .y), (false, .x), (true, .j), (false, .u), 1⟩,
  ⟨(false, .y), (false, .z), (true, .j), (false, .v), 1⟩,
  ⟨(false, .z), (true, .j), (true, .n), (true, .t), 1⟩,
  ⟨(false, .z), (true, .j), (true, .v), (true, .y), 1⟩,
  ⟨(false, .z), (true, .y), (false, .y), (false, .z), 1⟩,
  ⟨(false, .z), (true, .z), (false, .u), (false, .u), 1⟩,
  ⟨(false, .z), (true, .z), (false, .v), (false, .v), 1⟩,
  ⟨(false, .z), (true, .z), (false, .y), (false, .y), 1⟩,
  ⟨(false, .z), (true, .z), (false, .z), (false, .z), 1⟩,
  ⟨(true, .e), (false, .y), (true, .j), (true, .t), 3⟩,
  ⟨(true, .j), (false, .t), (true, .e), (true, .y), 3⟩,
  ⟨(false, .t), (true, .e), (false, .y), (false, .j), 3⟩,
  ⟨(false, .t), (false, .y), (true, .j), (false, .f), 3⟩,
  ⟨(true, .j), (true, .n), (false, .j), (true, .x), 0⟩,
  ⟨(true, .j), (true, .v), (false, .z), (true, .x), 0⟩,
  ⟨(true, .n), (true, .n), (false, .j), (true, .u), 0⟩,
  ⟨(true, .n), (true, .v), (false, .z), (true, .u), 0⟩,
  ⟨(true, .n), (false, .j), (true, .y), (true, .u), 0⟩,
  ⟨(true, .n), (false, .j), (false, .u), (false, .n), 0⟩,
  ⟨(true, .n), (false, .j), (false, .x), (false, .j), 0⟩,
  ⟨(true, .n), (false, .t), (false, .x), (false, .t), 0⟩,
  ⟨(true, .t), (true, .n), (false, .t), (true, .x), 0⟩,
  ⟨(true, .t), (true, .v), (false, .y), (true, .x), 0⟩,
  ⟨(true, .v), (false, .y), (false, .x), (false, .t), 0⟩,
  ⟨(true, .v), (false, .z), (true, .y), (true, .u), 0⟩,
  ⟨(true, .v), (false, .z), (false, .u), (false, .n), 0⟩,
  ⟨(true, .v), (false, .z), (false, .x), (false, .j), 0⟩,
  ⟨(true, .y), (false, .u), (true, .n), (true, .j), 0⟩,
  ⟨(true, .y), (false, .u), (true, .v), (true, .z), 0⟩,
  ⟨(false, .j), (true, .y), (false, .u), (false, .n), 0⟩,
  ⟨(false, .j), (false, .u), (true, .n), (false, .n), 0⟩,
  ⟨(false, .j), (false, .x), (true, .j), (false, .n), 0⟩,
  ⟨(false, .t), (false, .x), (true, .t), (false, .n), 0⟩,
  ⟨(false, .u), (true, .n), (true, .n), (true, .j), 0⟩,
  ⟨(false, .u), (true, .n), (true, .v), (true, .z), 0⟩,
  ⟨(false, .u), (true, .n), (false, .j), (false, .y), 0⟩,
  ⟨(false, .u), (true, .v), (false, .z), (false, .y), 0⟩,
  ⟨(false, .x), (true, .j), (true, .n), (true, .j), 0⟩,
  ⟨(false, .x), (true, .j), (true, .v), (true, .z), 0⟩,
  ⟨(false, .x), (true, .t), (true, .n), (true, .t), 0⟩,
  ⟨(false, .x), (true, .t), (true, .v), (true, .y), 0⟩,
  ⟨(false, .y), (false, .x), (true, .t), (false, .v), 0⟩,
  ⟨(false, .z), (true, .y), (false, .u), (false, .v), 0⟩,
  ⟨(false, .z), (false, .u), (true, .n), (false, .v), 0⟩,
  ⟨(false, .z), (false, .x), (true, .j), (false, .v), 0⟩]

end ArExplicit.CocycleData

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

structure QuadMonomial where
  first : TIndex
  second : TIndex
  third : TIndex
  fourth : TIndex
  output : TIndex
  degree : ℕ
  deriving DecidableEq

def QuadMonomial.number (a : QuadMonomial) : ℕ :=
  a.first.number + 20 * (a.second.number + 20 * (a.third.number +
    20 * (a.fourth.number + 20 * (a.output.number + 20 * a.degree))))

def contributions (p : TripleMonomial) (m : MulMonomial) : List QuadMonomial :=
  (if m.second = p.output then
    [⟨m.first, p.first, p.second, p.third, m.output, p.degree + m.degree⟩] else []) ++
  (if m.output = p.first then
    [⟨m.first, m.second, p.second, p.third, p.output, p.degree + m.degree⟩] else []) ++
  (if m.output = p.second then
    [⟨p.first, m.first, m.second, p.third, p.output, p.degree + m.degree⟩] else []) ++
  (if m.output = p.third then
    [⟨p.first, p.second, m.first, m.second, p.output, p.degree + m.degree⟩] else []) ++
  (if m.first = p.output then
    [⟨p.first, p.second, p.third, m.second, m.output, p.degree + m.degree⟩] else [])

def differentialBlock (a : TIndex) : List QuadMonomial :=
  cochain.flatMap fun p => multiplication.flatMap fun m =>
    (contributions p m).filter fun x => decide (x.first = a)

end ArExplicit.CocycleData

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.SparseParity

variable {α : Type*}

def paired [DecidableEq α] : List α → Bool
  | [] => true
  | a :: b :: rest => decide (a = b) && paired rest
  | [_] => false

def insert (cmp : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if cmp a b then a :: b :: l else b :: insert cmp a l

def sort (cmp : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insert cmp a (sort cmp l)

end ArExplicit.SparseParity

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

def certificate (a : TIndex) : Bool :=
  SparseParity.paired (SparseParity.sort (fun x y => decide (x.number ≤ y.number)) (differentialBlock a))

end ArExplicit.CocycleData

end OAI
end



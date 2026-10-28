-- Prove2me | Definitions.Def_OAIQ031A001
-- name    : OAIQ031A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:00:49.607969+00:00
-- url     : https://prove2.me/theorems/da0b7a5c-ca62-42cc-8e9a-0c8ca6e69716
-- title:
--   Definitions bundle OAIQ031A001 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 41 definitions, 2 instances and 48 theorems. The definitions and types are `OAI.ArExplicit.A`, `OAI.ArExplicit.A.originalProjection`, `OAI.ArExplicit.A.radicalT`, `OAI.ArExplicit.A.radicalU`, `OAI.ArExplicit.BaseAlgebra.coordinateLinearEquiv`, `OAI.ArExplicit.BaseAlgebra.diagonal`, `OAI.ArExplicit.BaseAlgebra.diagonalAlg`, `OAI.ArExplicit.BaseAlgebra.eCharacter`, `OAI.ArExplicit.BaseAlgebra.fCharacter`, `OAI.ArExplicit.BaseAlgebra.multiplicationTable`, `OAI.ArExplicit.BaseField`, `OAI.ArExplicit.CocycleData.simpleGenerator`, `OAI.ArExplicit.ExternalTensor.left`, `OAI.ArExplicit.ExternalTensor.map`, `OAI.ArExplicit.ExternalTensor.module`, `OAI.ArExplicit.ExternalTensor.moduleObject`, `OAI.ArExplicit.ExternalTensor.representation`, `OAI.ArExplicit.ExternalTensor.right`, `OAI.ArExplicit.ParameterRing`, `OAI.ArExplicit.Resolution.E`, `OAI.ArExplicit.Resolution.F`, `OAI.ArExplicit.Resolution.Simple`, `OAI.ArExplicit.Resolution.augmentation`, `OAI.ArExplicit.Resolution.complex`, `OAI.ArExplicit.Resolution.dEll`, `OAI.ArExplicit.Resolution.dU`, `OAI.ArExplicit.Resolution.differential`, `OAI.ArExplicit.Resolution.ell`, `OAI.ArExplicit.Resolution.fCoordinate`, `OAI.ArExplicit.Resolution.fixedRight`, `OAI.ArExplicit.Resolution.objects`, `OAI.ArExplicit.Resolution.rightBetween`, `OAI.ArExplicit.Resolution.simpleCoordinate`, `OAI.ArExplicit.Resolution.toSimple`, `OAI.ArExplicit.Resolution.vertexF`, `OAI.ArExplicit.T.diagonalAlg`, `OAI.ArExplicit.TIndex.star`, `OAI.ArExplicit.TrivialExtension.baseProjection`, `OAI.ArExplicit.TrivialExtension.projection`, `OAI.ArExplicit.parameter` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_BaseAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/BaseAlgebra.lean), [`AuslanderReiten_Algebras_BaseRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/BaseRadical.lean), [`AuslanderReiten_Algebras_SimpleModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleModule.lean), [`AuslanderReiten_Algebras_TCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TCoordinates.lean), [`AuslanderReiten_Algebras_TSimple`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TSimple.lean), [`AuslanderReiten_Algebras_TensorStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorStructure.lean), [`AuslanderReiten_Algebras_TrivialExtensionRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TrivialExtensionRadical.lean), [`AuslanderReiten_Cocycles_CocycleDetector`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleDetector.lean), [`AuslanderReiten_Parameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Parameters.lean), [`AuslanderReiten_Resolutions_CProjectiveResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CProjectiveResolution.lean), [`AuslanderReiten_Resolutions_Resolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/Resolution.lean), [`AuslanderReiten_Tensor_ExternalTensorModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorModule.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A025`, `OAIQ031A026`, `OAIQ031A028`, `OAIQ031A029`, `OAIQ031A030`, `OAIQ031A031`, `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A035`, `OAIQ031A037`, `OAIQ031A038`, `OAIQ031A039`, `OAIQ031A040` and `OAIQ031A043`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace BaseAlgebra

variable {k : Type*} (q : k)

variable [CommRing k]

open Letter

def multiplicationTable (left right : Letter) : BaseAlgebra k q :=
  let b := basisVector q
  match left, right with
  | e, e => b e
  | e, x => b x
  | e, y => b y
  | e, z => b z
  | e, u => b u
  | e, v => b v
  | x, e => b x
  | x, y => q • b z
  | x, u => b v
  | y, e => b y
  | y, x => b z
  | y, u => b v
  | z, e => b z
  | u, f => b u
  | u, t => b y + q • b x
  | u, j => b z
  | u, n => b v
  | v, f => b v
  | v, t => q • b z
  | t, e => b t
  | t, x => b j
  | t, y => q ^ 2 • b j
  | t, u => (1 + q) • b n
  | j, e => b j
  | f, t => b t
  | f, j => b j
  | f, f => b f
  | f, n => b n
  | n, f => b n
  | n, t => q • b j
  | _, _ => 0

theorem basis_e_mul (right : Letter) :
    basisVector q e * basisVector q right = multiplicationTable q e right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_x_mul (right : Letter) :
    basisVector q x * basisVector q right = multiplicationTable q x right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_y_mul (right : Letter) :
    basisVector q y * basisVector q right = multiplicationTable q y right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_z_mul (right : Letter) :
    basisVector q z * basisVector q right = multiplicationTable q z right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_u_mul (right : Letter) :
    basisVector q u * basisVector q right = multiplicationTable q u right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_v_mul (right : Letter) :
    basisVector q v * basisVector q right = multiplicationTable q v right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_t_mul (right : Letter) :
    basisVector q t * basisVector q right = multiplicationTable q t right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_j_mul (right : Letter) :
    basisVector q j * basisVector q right = multiplicationTable q j right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_f_mul (right : Letter) :
    basisVector q f * basisVector q right = multiplicationTable q f right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_n_mul (right : Letter) :
    basisVector q n * basisVector q right = multiplicationTable q n right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_mul (left right : Letter) :
    basisVector q left * basisVector q right = multiplicationTable q left right := by
  cases left
  · exact basis_e_mul q right
  · exact basis_x_mul q right
  · exact basis_y_mul q right
  · exact basis_z_mul q right
  · exact basis_u_mul q right
  · exact basis_v_mul q right
  · exact basis_t_mul q right
  · exact basis_j_mul q right
  · exact basis_f_mul q right
  · exact basis_n_mul q right

def coordinateLinearEquiv : BaseAlgebra k q ≃ₗ[k] (Letter → k) :=
  (coordinateAddEquiv q).linearEquiv k

end BaseAlgebra
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BaseAlgebra

open ArExplicit.Letter

variable {k : Type*} [Field k] (q : k)

def eCharacter : BaseAlgebra k q →+* k where
  toFun a := a.coeff e
  map_one' := by simp
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def fCharacter : BaseAlgebra k q →+* k where
  toFun a := a.coeff f
  map_one' := by simp
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def diagonal : BaseAlgebra k q →+* k × k := (eCharacter q).prod (fCharacter q)

def diagonalAlg : BaseAlgebra k q →ₐ[k] k × k where
  __ := diagonal q
  commutes' c := by
    apply Prod.ext
    · change (algebraMap k (BaseAlgebra k q) c).coeff e = c
      rw [Algebra.algebraMap_eq_smul_one]
      simp
    · change (algebraMap k (BaseAlgebra k q) c).coeff f = c
      rw [Algebra.algebraMap_eq_smul_one]
      simp

end ArExplicit.BaseAlgebra

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

abbrev ParameterRing := MvPolynomial (Fin 3) (ZMod 2)

abbrev BaseField := FractionRing ParameterRing

noncomputable def parameter (i : Fin 3) : BaseField :=
  algebraMap ParameterRing BaseField (MvPolynomial.X i)

noncomputable abbrev q : BaseField := parameter 0

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_Resolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

def fixedRight (p : C) : Submodule C C where
  carrier := {a | a * p = a}
  zero_mem' := zero_mul p
  add_mem' {a b} ha hb := by
    change a * p = a at ha
    change b * p = b at hb
    change (a + b) * p = a + b
    rw [add_mul, ha, hb]
  smul_mem' c a ha := by
    change (c * a) * p = c * a
    rw [mul_assoc, ha]

abbrev E : Submodule C C := fixedRight q (basisVector q e)

abbrev F : Submodule C C := fixedRight q (basisVector q f)

def rightBetween (p r z : C) (hz : z * r = z) :
    fixedRight q p →ₗ[C] fixedRight q r where
  toFun a := ⟨(a : C) * z, by change ((a : C) * z) * r = (a : C) * z; rw [mul_assoc, hz]⟩
  map_add' a b := Subtype.ext (add_mul (a : C) (b : C) z)
  map_smul' c a := Subtype.ext (mul_assoc c (a : C) z)

def ell (r : k) : C := basisVector q x + r • basisVector q y

@[simp] theorem ell_right_e (r : k) : ell q r * basisVector q e = ell q r := by
  simp [ell, add_mul, basis_mul, multiplicationTable]

def dU : E q →ₗ[C] F q :=
  rightBetween q _ _ (basisVector q u)
    (by simpa [multiplicationTable] using basis_mul q u f)

def dEll (r : k) : E q →ₗ[C] E q := rightBetween q _ _ (ell q r) (ell_right_e q r)

@[simp] theorem coe_dU (a : E q) : (dU q a : C) = (a : C) * basisVector q u := rfl
@[simp] theorem coe_dEll (r : k) (a : E q) : (dEll q r a : C) = (a : C) * ell q r := rfl

theorem E_coeff_zero (a : E q) (i : Letter)
    (hi : i = u ∨ i = v ∨ i = f ∨ i = n) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem E_coeff_u (a : E q) : (a : C).coeff u = 0 := E_coeff_zero q a u (by simp)
@[simp] theorem E_coeff_v (a : E q) : (a : C).coeff v = 0 := E_coeff_zero q a v (by simp)
@[simp] theorem E_coeff_f (a : E q) : (a : C).coeff f = 0 := E_coeff_zero q a f (by simp)
@[simp] theorem E_coeff_n (a : E q) : (a : C).coeff n = 0 := E_coeff_zero q a n (by simp)

theorem mul_u_formula (a : E q) : (a : C) * basisVector q u =
    (a : C).coeff e • basisVector q u +
    ((a : C).coeff x + (a : C).coeff y) • basisVector q v +
    ((1 + q) * (a : C).coeff t) • basisVector q n := by
  ext i
  cases i <;> simp [product]

section Exactness

variable [CharP k 2]

@[simp] theorem ell_one_mul_u : ell q 1 * basisVector q u = 0 := by
  ext i
  cases i <;> simp [ell, product, CharTwo.add_self_eq_zero]

@[simp] theorem ell_successor_mul (r : k) : ell q (q * r) * ell q r = 0 := by
  ext i
  cases i <;> simp [ell, product, CharTwo.add_self_eq_zero]

theorem dU_comp_dEll_one : (dU q).comp (dEll q 1) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change ((a : C) * ell q 1) * basisVector q u = 0
  rw [mul_assoc, ell_one_mul_u, mul_zero]

theorem dEll_comp_successor (r : k) : (dEll q r).comp (dEll q (q * r)) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change ((a : C) * ell q (q * r)) * ell q r = 0
  rw [mul_assoc, ell_successor_mul, mul_zero]

end Exactness

end ArExplicit.Resolution

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CProjectiveResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

variable {k : Type*} [Field k] [CharP k 2] (q : k)

local notation "C" => BaseAlgebra k q

abbrev Simple := (F q) ⧸ LinearMap.range (dU q)

def objects : ℕ → ModuleCat C
  | 0 => ModuleCat.of C (F q)
  | _ + 1 => ModuleCat.of C (E q)

def differential : (n : ℕ) → objects q (n + 1) ⟶ objects q n
  | 0 => ModuleCat.ofHom (dU q)
  | n + 1 => ModuleCat.ofHom (dEll q (q ^ n))

theorem differential_comp (n : ℕ) : differential q (n + 1) ≫ differential q n = 0 := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    change (dU q).comp (dEll q (q ^ 0)) = 0
    simpa only [pow_zero] using dU_comp_dEll_one q
  | succ n =>
    apply ModuleCat.hom_ext
    change (dEll q (q ^ n)).comp (dEll q (q ^ (n + 1))) = 0
    simpa only [pow_succ'] using dEll_comp_successor q (q ^ n)

def complex : ChainComplex (ModuleCat C) ℕ :=
  ChainComplex.of (objects q) (differential q) (differential_comp q)

def augmentation : (complex q).X 0 ⟶ ModuleCat.of C (Simple q) :=
  ModuleCat.ofHom (LinearMap.range (dU q)).mkQ

theorem differential_augmentation : (complex q).d 1 0 ≫ augmentation q = 0 := by
  apply ModuleCat.hom_ext
  change (LinearMap.range (dU q)).mkQ.comp (dU q) = 0
  exact LinearMap.range_mkQ_comp (dU q)

def toSimple : complex q ⟶ (ChainComplex.single₀ (ModuleCat C)).obj (ModuleCat.of C (Simple q)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation q, differential_augmentation q⟩

@[simp] theorem toSimple_zero : (toSimple q).f 0 = augmentation q :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem F_coeff_zero (a : F q) (i : Letter)
    (hi : i = e ∨ i = x ∨ i = y ∨ i = z ∨ i = t ∨ i = j) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem F_coeff_e (a : F q) : (a : C).coeff e = 0 := F_coeff_zero q a e (by simp)
@[simp] theorem F_coeff_x (a : F q) : (a : C).coeff x = 0 := F_coeff_zero q a x (by simp)
@[simp] theorem F_coeff_y (a : F q) : (a : C).coeff y = 0 := F_coeff_zero q a y (by simp)
@[simp] theorem F_coeff_z (a : F q) : (a : C).coeff z = 0 := F_coeff_zero q a z (by simp)
@[simp] theorem F_coeff_t (a : F q) : (a : C).coeff t = 0 := F_coeff_zero q a t (by simp)
@[simp] theorem F_coeff_j (a : F q) : (a : C).coeff j = 0 := F_coeff_zero q a j (by simp)

def fCoordinate : F q →ₗ[k] k where
  toFun a := (a : C).coeff f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def simpleCoordinate : Simple q →ₗ[k] k :=
  ((LinearMap.range (dU q)).restrictScalars k).liftQ (fCoordinate q) (by
    rintro a ⟨b, rfl⟩
    change (dU q b : C).coeff f = 0
    simp [product])

@[simp] theorem simpleCoordinate_mk (a : F q) :
    simpleCoordinate q (Submodule.Quotient.mk a) = (a : C).coeff f := rfl

def vertexF : F q := ⟨basisVector q f, by
  change basisVector q f * basisVector q f = basisVector q f
  simpa [multiplicationTable] using basis_mul q f f⟩

theorem simpleCoordinate_smul (c : C) (a : Simple q) :
    simpleCoordinate q (c • a) = c.coeff f * simpleCoordinate q a := by
  refine Submodule.Quotient.induction_on _ a ?_
  intro b
  rfl

end ArExplicit.Resolution

end

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

namespace TIndex

def star (i : TIndex) : TIndex := (!i.1, i.2)

end TIndex

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TSimple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit
namespace TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def baseProjection : TrivialExtension k A →ₐ[k] A where
  toFun a := a.base
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

end TrivialExtension

namespace Resolution

variable {k : Type*} [Field k] (q : k)

instance instModuleTSimple : Module (T k q) (Simple q) :=
  Module.compHom (Simple q) TrivialExtension.baseProjection.toRingHom

@[simp] theorem t_smul_simple (a : T k q) (s : Simple q) :
    a • s = a.base • s := rfl

instance instIsScalarTowerTSimple : IsScalarTower k (T k q) (Simple q) where
  smul_assoc r a s := by
    change (r • a.base) • s = r • (a.base • s)
    exact smul_assoc r a.base s

theorem t_simple_character (a : T k q) (s : Simple q) :
    simpleCoordinate q (a • s) = a.base.coeff .f * simpleCoordinate q s :=
  simpleCoordinate_smul q a.base s

end Resolution
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TrivialExtensionRadical
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def projection : TrivialExtension k A →ₐ[k] A where
  toFun := base
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by simp only [Algebra.algebraMap_eq_smul_one, base_smul, base_one]

@[simp] theorem projection_apply (a : TrivialExtension k A) : projection a = a.base := rfl

end ArExplicit.TrivialExtension

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

def diagonalAlg : T k q →ₐ[k] k × k :=
  (BaseAlgebra.diagonalAlg q).comp TrivialExtension.projection

end ArExplicit.T

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

abbrev A (k : Type*) [Field k] (q : k) := T k q ⊗[k] T k q

namespace A

variable {k : Type*} [Field k] (q : k)

def radicalU : A k q := T.lower q Letter.u ⊗ₜ[k] 1
def radicalT : A k q := T.lower q Letter.t ⊗ₜ[k] 1

noncomputable def originalProjection : A k q →ₐ[k] BaseAlgebra k q :=
  TrivialExtension.projection.comp
    ((Algebra.TensorProduct.rid k k (T k q)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k (T k q))
        ((AlgHom.snd k k k).comp (T.diagonalAlg q))))

@[simp] theorem originalProjection_radicalU :
    originalProjection q (radicalU q) = BaseAlgebra.basisVector q Letter.u := by
  simp [originalProjection, radicalU, T.lower, TrivialExtension.inl]

@[simp] theorem originalProjection_radicalT :
    originalProjection q (radicalT q) = BaseAlgebra.basisVector q Letter.t := by
  simp [originalProjection, radicalT, T.lower, TrivialExtension.inl]

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)
local notation "S" => Resolution.Simple q

def simpleGenerator : S := Submodule.Quotient.mk (Resolution.vertexF q)

@[simp] theorem simpleGenerator_coordinate : Resolution.simpleCoordinate q (simpleGenerator q) = 1 := by
  simp [simpleGenerator, Resolution.vertexF]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module k M] [Module k N] [Module A M] [Module B N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

def left : A →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M)

def right : B →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)

@[simp] theorem left_tmul (a : A) (m : M) (n : N) :
    left k A M N a (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] n := rfl

@[simp] theorem right_tmul (b : B) (m : M) (n : N) :
    right k B M N b (m ⊗ₜ[k] n) = m ⊗ₜ[k] (b • n) := rfl

theorem left_right (a : A) (b : B) (z : M ⊗[k] N) :
    left k A M N a (right k B M N b z) =
      right k B M N b (left k A M N a z) := by
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => rfl

def representation : (A ⊗[k] B) →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift (left k A M N) (right k B M N) fun a b => by
    apply LinearMap.ext
    exact left_right k A B M N a b

@[instance_reducible] def module : Module (A ⊗[k] B) (M ⊗[k] N) :=
  Module.compHom (M ⊗[k] N) (representation k A B M N).toRingHom

def moduleObject : ModuleCat.{u} (A ⊗[k] B) :=
  letI := module k A B M N
  ModuleCat.of (A ⊗[k] B) (M ⊗[k] N)

@[simp] theorem smul_tmul (a : A) (b : B) (m : M) (n : N) :
    @SMul.smul (A ⊗[k] B) (moduleObject k A B M N)
      (moduleObject k A B M N).isModule.toSMul (a ⊗ₜ[k] b) (m ⊗ₜ[k] n) =
      ((a • m) ⊗ₜ[k] (b • n) : moduleObject k A B M N) := rfl

variable {M N}
variable {M' N' : Type u} [AddCommGroup M'] [AddCommGroup N']
variable [Module k M'] [Module k N'] [Module A M'] [Module B N']
variable [IsScalarTower k A M'] [IsScalarTower k B N']

def map (f : M →ₗ[A] M') (g : N →ₗ[B] N') :
    moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B M' N' where
  toAddHom := (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)).toAddHom
  map_smul' a z := by
    let F := TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
    let w : M ⊗[k] N := z
    change F (representation k A B M N a w) = representation k A B M' N' a (F w)
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      induction w using OAI.tensorInductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul m n =>
        change (f (a • m)) ⊗ₜ[k] (g (b • n)) = (a • f m) ⊗ₜ[k] (b • g n)
        rw [map_smul, map_smul]

@[simp] theorem map_tmul (f : M →ₗ[A] M') (g : N →ₗ[B] N') (m : M) (n : N) :
    map k A B f g (m ⊗ₜ[k] n) = (f m) ⊗ₜ[k] (g n) := rfl

end ArExplicit.ExternalTensor

end

end OAI
end



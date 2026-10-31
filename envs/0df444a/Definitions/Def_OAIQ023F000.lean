-- Prove2me | Definitions.Def_OAIQ023F000
-- name    : OAIQ023F000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:41:01.138514+00:00
-- url     : https://prove2.me/theorems/30574c99-a48e-4cdd-bd2c-c82f594d8514
-- title:
--   Definitions bundle OAIQ023F000 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 174 declarations of OpenAI's Lean: 73 definitions, 9 instances and 92 theorems. The definitions and types are `OAI.DerivedBar.Balanced.collapse`, `OAI.DerivedBar.Balanced.descend`, `OAI.DerivedBar.Balanced.freeEquiv`, `OAI.DerivedBar.Balanced.insert`, `OAI.DerivedBar.Balanced.instModuleCarrier_solutions`, `OAI.DerivedBar.Balanced.map`, `OAI.DerivedBar.Balanced.quotient`, `OAI.DerivedBar.Balanced.relations`, `OAI.DerivedBar.Balanced.resolvedTensorIso`, `OAI.DerivedBar.Balanced.tensor`, `OAI.DerivedBar.Balanced.tensorBarHomologyIso`, `OAI.DerivedBar.Balanced.tensorFunctor`, `OAI.DerivedBar.Balanced.tensorFunctorObjIso`, `OAI.DerivedBar.BimoduleTensor.barComplex`, `OAI.DerivedBar.BimoduleTensor.barDifferential`, `OAI.DerivedBar.BimoduleTensor.barTermMap`, `OAI.DerivedBar.BimoduleTensor.collapse`, `OAI.DerivedBar.BimoduleTensor.congrLeft`, `OAI.DerivedBar.BimoduleTensor.descend`, `OAI.DerivedBar.BimoduleTensor.freeMap`, `OAI.DerivedBar.BimoduleTensor.insert`, `OAI.DerivedBar.BimoduleTensor.instModuleCarrier_solutions`, `OAI.DerivedBar.BimoduleTensor.instModuleCarrier_solutions_2`, `OAI.DerivedBar.BimoduleTensor.instModuleCarrier_solutions_4`, `OAI.DerivedBar.BimoduleTensor.leftMap`, `OAI.DerivedBar.BimoduleTensor.map`, `OAI.DerivedBar.BimoduleTensor.quotient`, `OAI.DerivedBar.BimoduleTensor.relations`, `OAI.DerivedBar.BimoduleTensor.rightAction`, `OAI.DerivedBar.BimoduleTensor.rightMul`, `OAI.DerivedBar.BimoduleTensor.scalarModule`, `OAI.DerivedBar.BimoduleTensor.tensor`, `OAI.DerivedBar.BimoduleTensor.tensorFunctor`, `OAI.DerivedBar.BimoduleTensor.tensorFunctorCongr`, `OAI.DerivedBar.FreeBaseChange.coefficient`, `OAI.DerivedBar.FreeBaseChange.map`, `OAI.DerivedBar.SquareZero.baseProjection`, `OAI.DerivedBar.SquareZero.idealProjection`, `OAI.DerivedBar.SquareZero.projection`, `OAI.DerivedBar.SquareZero.twoSidedProjection` and 33 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_Balanced`, `Finitistic_Bar_BalancedTensorFunctor`, `Finitistic_Bar_Bar`, `Finitistic_Bar_BarBimoduleCongruence`, `Finitistic_Bar_BarFunctor`, `Finitistic_Bar_Projection`, `Finitistic_Bar_Splitting`, `Finitistic_Bar_TensorModel`, `Finitistic_Bar_TotalAdditive`, `Finitistic_Bar_TotalBar`, `Finitistic_Bar_TotalBarContraction`, `Finitistic_Bar_TotalBarDerived`, `Finitistic_Bar_TotalBarFunctor`, `Finitistic_Bar_TotalBarTensor`, `Finitistic_Bar_TwoSided`, `Finitistic_Bar_TwoSidedBarFunctor`, `Finitistic_Bimodule_BimoduleBar`, `Finitistic_Bimodule_BimoduleBarIteration`, `Finitistic_Bimodule_BimoduleComparison`, `Finitistic_Bimodule_BimoduleDerived`, `Finitistic_Bimodule_BimoduleTensor`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F005`, `OAIQ023F006`, `OAIQ023F007`, `OAIQ023F008` and `OAIQ023F009`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ023_Fin.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

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
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Bar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace DerivedBar
universe u
variable (k A N : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The augmented bar terms: term 0 is N; term (n+1) is A ⊗ term n. -/
@[reducible] def term : ℕ → ModuleCat k
  | 0 => ModuleCat.of k N
  | n+1 => ModuleCat.of k (A ⊗[k] term n)

@[reducible] instance termModule : (n : ℕ) → Module A (term k A N n)
  | 0 => inferInstanceAs (Module A N)
  | n+1 => inferInstanceAs (Module A (A ⊗[k] term k A N n))

instance termTower : (n : ℕ) → IsScalarTower k A (term k A N n)
  | 0 => inferInstanceAs (IsScalarTower k A N)
  | n+1 => inferInstanceAs (IsScalarTower k A (A ⊗[k] term k A N n))


/-- Multiplication/action on the first two positions of an augmented bar word. -/
def action (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] : A ⊗[k] M →ₗ[A] M :=
  { (TensorProduct.lift (Algebra.lsmul k k M).toLinearMap).toAddHom with
    map_smul' := by
      intro a z
      induction z using OAI.tensorInductionOn with
      | tmul b m => simp [TensorProduct.smul_tmul']
      | add x y hx hy => simp_all [smul_add] }

@[simp] theorem action_tmul (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] (a : A) (m : M) :
    action k A M (a ⊗ₜ[k] m) = a • m := rfl

/-- Recursive alternating face differential. No A-flatness of N is required. -/
def differential : (n : ℕ) → term k A N (n+1) →ₗ[A] term k A N n
  | 0 => action k A N
  | n+1 => action k A (term k A N (n+1)) -
      AlgebraTensorModule.lTensor A A ((differential n).restrictScalars k)

@[simp] theorem differential_zero_tmul (a : A) (z : N) :
    differential k A N 0 (a ⊗ₜ[k] z) = a • z := rfl

@[simp] theorem differential_succ_tmul (n : ℕ) (a : A) (z : term k A N (n+1)) :
    differential k A N (n+1) (a ⊗ₜ[k] z) =
      a • z - a ⊗ₜ[k] differential k A N n z := rfl

/-- The actual bar differential squares to zero in every degree. -/
theorem differential_sq (n : ℕ) :
    (differential k A N n).comp (differential k A N (n+1)) = 0 := by
  induction n with
  | zero =>
    apply AlgebraTensorModule.ext
    intro a z
    change differential k A N 0 (differential k A N 1 (a ⊗ₜ[k] z)) = 0
    rw [differential_succ_tmul k A N 0 a z, map_sub, map_smul,
      differential_zero_tmul k A N a (differential k A N 0 z), sub_self]
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a z
    have hz := LinearMap.congr_fun ih z
    change differential k A N n (differential k A N (n+1) z) = 0 at hz
    change differential k A N (n+1) (differential k A N (n+2) (a ⊗ₜ[k] z)) = 0
    rw [differential_succ_tmul k A N (n+1) a z, map_sub, map_smul,
      differential_succ_tmul k A N n a (differential k A N (n+1) z), hz,
      TensorProduct.tmul_zero, sub_zero, sub_self]

/-- Unit insertion; this is k-linear, generally not A-linear. -/
def contraction (n : ℕ) : term k A N n →ₗ[k] term k A N (n+1) :=
  TensorProduct.mk k A (term k A N n) 1

omit [Module A N] [IsScalarTower k A N] in
@[simp] theorem contraction_apply (n : ℕ) (z : term k A N n) :
    contraction k A N n z = 1 ⊗ₜ[k] z := rfl

/-- The augmented degree-zero contraction identity. -/
theorem contraction_zero (z : N) :
    differential k A N 0 (contraction k A N 0 z) = z := by
  change (1 : A) • z = z
  exact one_smul A z

/-- Contracting homotopy in every positive augmented degree. -/
theorem contraction_identity (n : ℕ) (z : term k A N (n+1)) :
    differential k A N (n+1) (contraction k A N (n+1) z) +
      contraction k A N n (differential k A N n z) = z := by
  change differential k A N (n+1) (1 ⊗ₜ[k] z) + 1 ⊗ₜ[k] differential k A N n z = z
  rw [differential_succ_tmul k A N n 1 z, one_smul, sub_add_cancel]

/-- Exactness of the augmented absolute bar complex as actual A-linear maps. -/
theorem differential_exact (n : ℕ) :
    LinearMap.range (differential k A N (n+1)) =
      LinearMap.ker (differential k A N n) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact LinearMap.congr_fun (differential_sq k A N n) z
  · intro z hz
    refine ⟨contraction k A N (n+1) z, ?_⟩
    have h := contraction_identity k A N n z
    have hz' : differential k A N n z = 0 := hz
    simpa [hz'] using h

/-- The unaugmented absolute bar complex, degree n = A ⊗ A^⊗n ⊗ N. -/
def complex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (term k A N (n+1)))
    (fun n => ModuleCat.ofHom (differential k A N (n+1)))
    (fun n => by exact ModuleCat.hom_ext (differential_sq k A N (n+1)))


open CategoryTheory CategoryTheory.Limits

instance complex_projective (n : ℕ) : Projective ((complex k A N).X n) := by
  change Projective (ModuleCat.of A (term k A N (n+1)))
  exact inferInstance

/-- Surjectivity of the bar augmentation, witnessed by insertion of 1. -/
theorem augmentation_surjective : Function.Surjective (differential k A N 0) := by
  intro z
  exact ⟨contraction k A N 0 z, contraction_zero k A N z⟩

/-- The bar augmentation as a chain map to N concentrated in degree zero. -/
def augmentation : complex k A N ⟶ (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A N) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (differential k A N 0), by
      change ModuleCat.ofHom (differential k A N 1) ≫
        ModuleCat.ofHom (differential k A N 0) = 0
      exact ModuleCat.hom_ext (differential_sq k A N 0)⟩

/-- All positive-degree homology of the unaugmented bar complex vanishes. -/
theorem complex_exactAt_succ (n : ℕ) : (complex k A N).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    complex, ChainComplex.of_d, ModuleCat.hom_ofHom] using! differential_exact k A N (n+1)

/-- Exactness at the augmentation term, stated in the abelian category of A-modules. -/
theorem augmentation_exact :
    (ShortComplex.mk ((complex k A N).d 1 0) (ModuleCat.ofHom (differential k A N 0))
      (ModuleCat.hom_ext (differential_sq k A N 0))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact differential_exact k A N 0

instance augmentation_epi : Epi (ModuleCat.ofHom (differential k A N 0)) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective k A N)

/-- The absolute algebra bar augmentation is a genuine quasi-isomorphism. -/
instance augmentation_quasiIso : QuasiIso (augmentation k A N) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp [augmentation]
      exact ⟨augmentation_exact k A N, augmentation_epi k A N⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact complex_exactAt_succ k A N n
    · apply ChainComplex.exactAt_succ_single_obj

/-- Explicit free absolute bar resolution, packaged for derived functor computations. -/
def projectiveResolution : ProjectiveResolution (ModuleCat.of A N) where
  complex := complex k A N
  π := augmentation k A N
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSided
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar
namespace FreeBaseChange
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V W U : Type u) [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- Replace only the free leading algebra coefficient along f. -/
def coefficient : A ⊗[k] V →ₗ[k] D ⊗[k] V :=
  TensorProduct.map f.toLinearMap LinearMap.id

@[simp] theorem coefficient_tmul (a : A) (v : V) :
    coefficient f V (a ⊗ₜ[k] v) = f a ⊗ₜ[k] v := rfl

/-- Coefficient change intertwines the two regular left actions. -/
theorem coefficient_smul (a : A) (z : A ⊗[k] V) :
    coefficient f V (a • z) = f a • coefficient f V z := by
  induction z using OAI.tensorInductionOn with
  | tmul b v => simp [TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => simp_all [smul_add]

/-- Scalar extension of a morphism between explicitly free A-modules. -/
def map (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) : D ⊗[k] V →ₗ[D] D ⊗[k] W :=
  (action k D (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D
      ((coefficient f W).comp ((h.restrictScalars k).comp (TensorProduct.mk k A V 1))))

@[simp] theorem map_tmul (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) (d : D) (v : V) :
    map f V W h (d ⊗ₜ[k] v) = d • coefficient f W (h (1 ⊗ₜ[k] v)) := rfl

end FreeBaseChange

universe u
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Balanced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar.Balanced
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The balancing relations for the right A-action d·a = d*f(a). -/
def relations : Submodule D (D ⊗[k] V) :=
  Submodule.span D {z | ∃ (d : D) (a : A) (v : V),
    z = (d * f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v)}

/-- Noncommutative balanced tensor D ⊗_A V, presented using tensors over the field. -/
abbrev tensor := (D ⊗[k] V) ⧸ relations f V

/-- Its canonical D-linear quotient map. -/
def quotient : D ⊗[k] V →ₗ[D] tensor f V := (relations f V).mkQ

omit [IsScalarTower k A V] in
/-- The defining balanced relation, as an equality in the actual quotient module. -/
theorem balanced (d : D) (a : A) (v : V) :
    quotient f V ((d*f a) ⊗ₜ[k] v) = quotient f V (d ⊗ₜ[k] (a • v)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨d, a, v, rfl⟩)

section Maps
variable (W U : Type u) [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup U] [Module k U] [Module A U] [IsScalarTower k A U]

/-- Balanced tensor acts on all A-linear maps. -/
theorem map_relations (h : V →ₗ[A] W) : relations f V ≤
    ((quotient f W).comp (AlgebraTensorModule.lTensor D D (h.restrictScalars k))).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨d, a, v, rfl⟩
  change quotient f W ((AlgebraTensorModule.lTensor D D (h.restrictScalars k))
    ((d*f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v))) = 0
  simp only [map_sub, AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
    LinearMap.map_smul]
  rw [balanced, sub_self]

def map (h : V →ₗ[A] W) : tensor f V →ₗ[D] tensor f W :=
  (relations f V).liftQ
    ((quotient f W).comp (AlgebraTensorModule.lTensor D D (h.restrictScalars k)))
    (map_relations f V W h)

@[simp] theorem map_quotient_tmul (h : V →ₗ[A] W) (d : D) (v : V) :
    map f V W h (quotient f V (d ⊗ₜ[k] v)) = quotient f W (d ⊗ₜ[k] h v) := rfl

/-- Composition preservation for the actual balanced tensor, proved from its quotient presentation. -/
theorem map_comp (h : V →ₗ[A] W) (g : W →ₗ[A] U) :
    map f V U (g.comp h) = (map f W U g).comp (map f V W h) := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  rfl

@[simp] theorem map_zero : map f V W 0 = 0 := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  change quotient f W (d ⊗ₜ[k] (0 : W)) = 0
  rw [TensorProduct.tmul_zero, _root_.map_zero]

@[simp] theorem map_id : map f V V LinearMap.id = LinearMap.id := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  rfl
end Maps

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- Evaluation of D ⊗_k (A ⊗_k W) on the two leading coefficients. -/
def collapse : D ⊗[k] (A ⊗[k] W) →ₗ[D] D ⊗[k] W :=
  (DerivedBar.action k D (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D (FreeBaseChange.coefficient f W))

@[simp] theorem collapse_tmul (d : D) (z : A ⊗[k] W) :
    collapse f W (d ⊗ₜ[k] z) = d • FreeBaseChange.coefficient f W z := rfl

/-- The evaluation kills all balancing relations, without commutativity of A or D. -/
theorem relations_le_ker_collapse : relations f (A ⊗[k] W) ≤ (collapse f W).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨d, a, v, rfl⟩
  change collapse f W ((d*f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v)) = 0
  rw [map_sub, collapse_tmul, collapse_tmul, FreeBaseChange.coefficient_smul,
    mul_smul, sub_self]

/-- Descent of coefficient evaluation to the balanced tensor. -/
def descend : tensor f (A ⊗[k] W) →ₗ[D] D ⊗[k] W :=
  (relations f (A ⊗[k] W)).liftQ (collapse f W) (relations_le_ker_collapse f W)

/-- The inverse inserts a unit A coefficient before taking the balanced quotient. -/
def insert : D ⊗[k] W →ₗ[D] tensor f (A ⊗[k] W) :=
  (quotient f (A ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D (TensorProduct.mk k A W 1))

@[simp] theorem descend_quotient (z : D ⊗[k] (A ⊗[k] W)) :
    descend f W (quotient f (A ⊗[k] W) z) = collapse f W z := rfl

@[simp] theorem insert_tmul (d : D) (w : W) :
    insert f W (d ⊗ₜ[k] w) = quotient f (A ⊗[k] W) (d ⊗ₜ[k] (1 ⊗ₜ[k] w)) := rfl

/-- One inverse identity of the actual balanced free-module tensor equivalence. -/
theorem descend_insert : (descend f W).comp (insert f W) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro d w
  simp [LinearMap.comp_apply, TensorProduct.smul_tmul']

/-- The other inverse identity follows from balancing, not from flatness. -/
theorem insert_descend : (insert f W).comp (descend f W) = LinearMap.id := by
  apply (relations f (A ⊗[k] W)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d z
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => simp_all [TensorProduct.tmul_add]
  | tmul a w =>
    change insert f W (collapse f W (d ⊗ₜ[k] (a ⊗ₜ[k] w))) =
      quotient f (A ⊗[k] W) (d ⊗ₜ[k] (a ⊗ₜ[k] w))
    rw [collapse_tmul, FreeBaseChange.coefficient_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, insert_tmul, balanced]
    simp [TensorProduct.smul_tmul']

/-- The standard identification D ⊗_A (A ⊗_k W) ≅ D ⊗_k W for arbitrary algebras. -/
def freeEquiv : tensor f (A ⊗[k] W) ≃ₗ[D] D ⊗[k] W :=
  LinearEquiv.ofLinearMap (descend f W) (insert f W) (descend_insert f W) (insert_descend f W)

end DerivedBar.Balanced

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

def baseProjection : Module.End k (TrivSqZeroExt D X) :=
  (inlAlgHom k D X).toLinearMap.comp (fstHom k D X).toLinearMap

def idealProjection : Module.End k (TrivSqZeroExt D X) :=
  LinearMap.id - baseProjection k D X

@[simp] theorem baseProjection_inl (d : D) :
    baseProjection k D X (inl d) = inl d := rfl
@[simp] theorem baseProjection_inr (x : X) :
    baseProjection k D X (inr x) = 0 := rfl
@[simp] theorem idealProjection_inl (d : D) :
    idealProjection k D X (inl d) = 0 := by simp [idealProjection]
@[simp] theorem idealProjection_inr (x : X) :
    idealProjection k D X (inr x) = inr x := by simp [idealProjection]

/-- The actual linear projection onto words with a prescribed X-count. -/
def projection : (n r : ℕ) → Module.End k (term k (TrivSqZeroExt D X) N n)
  | 0, 0 => LinearMap.id
  | 0, _+1 => 0
  | n+1, 0 => TensorProduct.map (baseProjection k D X) (projection n 0)
  | n+1, r+1 => TensorProduct.map (baseProjection k D X) (projection n (r+1)) +
      TensorProduct.map (idealProjection k D X) (projection n r)

@[simp] theorem projection_base (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) r ((inl d : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inl d : TrivSqZeroExt D X) ⊗ₜ[k] projection k D X N n r v := by
  cases r <;> simp [projection]

@[simp] theorem projection_ideal_zero (n : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) 0 ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) = 0 := by
  simp [projection]

@[simp] theorem projection_ideal_succ (n r : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) (r+1) ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inr x : TrivSqZeroExt D X) ⊗ₜ[k] projection k D X N n r v := by
  simp [projection]

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Splitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Actual D-linear count projection on the two-sided bar term. -/
def twoSidedProjection (n r : ℕ) : Module.End D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  AlgebraTensorModule.lTensor D D (projection k D X N n r)

@[simp] theorem twoSidedProjection_tmul (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    twoSidedProjection k D X N n r (d ⊗ₜ[k] v) = d ⊗ₜ[k] projection k D X N n r v := rfl

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TensorModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

variable (k A D N : Type u) [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (f : A →ₐ[k] D)

/-- The actual balanced tensor of D with every term and differential of the verified bar resolution. -/
def tensorBarComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (Balanced.tensor f (term k A N (n+1))))
    (fun n => ModuleCat.ofHom (Balanced.map f _ _ (differential k A N (n+1))))
    (fun n => by
      apply ModuleCat.hom_ext
      change (Balanced.map f _ _ (differential k A N (n+1))).comp
        (Balanced.map f _ _ (differential k A N (n+1+1))) = 0
      rw [← Balanced.map_comp, differential_sq, Balanced.map_zero])

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

/-- Noncommutative balancing relations for an arbitrary (D,D)-bimodule X. -/
def relations : Submodule D (X ⊗[k] V) :=
  Submodule.span D {z | ∃ (x : X) (d : D) (v : V),
    z = (MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v)}

/-- Genuine balanced X ⊗_D V, with its exterior left D-action. -/
abbrev tensor := (X ⊗[k] V) ⧸ relations k D X V

def quotient : X ⊗[k] V →ₗ[D] tensor k D X V := (relations k D X V).mkQ

omit [IsScalarTower k D V] in
theorem balanced (x : X) (d : D) (v : V) :
    quotient k D X V ((MulOpposite.op d • x) ⊗ₜ[k] v) =
      quotient k D X V (x ⊗ₜ[k] (d • v)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x, d, v, rfl⟩)

section Maps
variable (W U : Type u) [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]
  [AddCommGroup U] [Module k U] [Module D U] [IsScalarTower k D U]

theorem map_relations (h : V →ₗ[D] W) : relations k D X V ≤
    ((quotient k D X W).comp (AlgebraTensorModule.lTensor D X (h.restrictScalars k))).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, d, v, rfl⟩
  change quotient k D X W ((AlgebraTensorModule.lTensor D X (h.restrictScalars k))
    ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v))) = 0
  simp only [map_sub, AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
    LinearMap.map_smul]
  rw [balanced, sub_self]

def map (h : V →ₗ[D] W) : tensor k D X V →ₗ[D] tensor k D X W :=
  (relations k D X V).liftQ
    ((quotient k D X W).comp (AlgebraTensorModule.lTensor D X (h.restrictScalars k)))
    (map_relations k D X V W h)

@[simp] theorem map_quotient (h : V →ₗ[D] W) (x : X) (v : V) :
    map k D X V W h (quotient k D X V (x ⊗ₜ[k] v)) =
      quotient k D X W (x ⊗ₜ[k] h v) := rfl

theorem map_comp (h : V →ₗ[D] W) (g : W →ₗ[D] U) :
    map k D X V U (g.comp h) = (map k D X W U g).comp (map k D X V W h) := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  rfl

@[simp] theorem map_zero : map k D X V W 0 = 0 := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  change quotient k D X W (x ⊗ₜ[k] (0 : W)) = 0
  rw [TensorProduct.tmul_zero, _root_.map_zero]

@[simp] theorem map_id : map k D X V V LinearMap.id = LinearMap.id := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  rfl

theorem map_add (h g : V →ₗ[D] W) :
    map k D X V W (h+g) = map k D X V W h + map k D X V W g := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  change quotient k D X W (x ⊗ₜ[k] (h v + g v)) =
    quotient k D X W (x ⊗ₜ[k] h v) + quotient k D X W (x ⊗ₜ[k] g v)
  rw [TensorProduct.tmul_add, _root_.map_add]
end Maps

variable [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The bimodule right action, bilinear over the field. -/
def rightMul : X →ₗ[k] D →ₗ[k] X where
  toFun x :=
    { toFun := fun d => MulOpposite.op d • x
      map_add' := by intro a b; simp [add_smul]
      map_smul' := by intro c d; simp [MulOpposite.op_smul, smul_assoc] }
  map_add' := by intro x y; ext d; simp [smul_add]
  map_smul' := by intro c x; ext d; simp [smul_comm (MulOpposite.op d) c]

/-- Multiplication X ⊗_k D → X respects the arbitrary exterior D-action. -/
def rightAction : X ⊗[k] D →ₗ[D] X :=
  { (TensorProduct.lift (rightMul k D X)).toAddHom with
    map_smul' := by
      intro a z
      induction z using OAI.tensorInductionOn with
      | tmul x d =>
        change (TensorProduct.lift (rightMul k D X)) (a • (x ⊗ₜ[k] d)) =
          a • ((TensorProduct.lift (rightMul k D X)) (x ⊗ₜ[k] d))
        rw [TensorProduct.smul_tmul']
        exact (smul_comm a (MulOpposite.op d) x).symm
      | add v w hv hw => simp_all [smul_add] }

@[simp] theorem rightAction_tmul (x : X) (d : D) :
    rightAction k D X (x ⊗ₜ[k] d) = MulOpposite.op d • x := rfl

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- Collapse the first two slots using the right D-action on X. -/
def collapse : X ⊗[k] (D ⊗[k] W) →ₗ[D] X ⊗[k] W :=
  { ((TensorProduct.map ((rightAction k D X).restrictScalars k) LinearMap.id).comp
      (TensorProduct.assoc k X D W).symm.toLinearMap).toAddHom with
    map_smul' := by
      intro a z
      induction z using OAI.tensorInductionOn with
      | tmul x v =>
        induction v using OAI.tensorInductionOn with
        | tmul d w =>
          rw [TensorProduct.smul_tmul']
          change (MulOpposite.op d • (a • x)) ⊗ₜ[k] w =
            a • ((MulOpposite.op d • x) ⊗ₜ[k] w)
          rw [TensorProduct.smul_tmul', ← smul_comm a (MulOpposite.op d) x]
        | add v w hv hw => simp_all [TensorProduct.tmul_add, smul_add]
      | add v w hv hw => simp_all [smul_add] }

@[simp] theorem collapse_tmul (x : X) (d : D) (w : W) :
    collapse k D X W (x ⊗ₜ[k] (d ⊗ₜ[k] w)) = (MulOpposite.op d • x) ⊗ₜ[k] w := rfl

/-- The collapse descends through the actual balancing relations. -/
theorem relations_le_ker_collapse : relations k D X (D ⊗[k] W) ≤ (collapse k D X W).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, d, v, rfl⟩
  change collapse k D X W ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v)) = 0
  induction v using OAI.tensorInductionOn with
  | tmul a w =>
    rw [_root_.map_sub, collapse_tmul, TensorProduct.smul_tmul', smul_eq_mul, collapse_tmul]
    simp [← mul_smul, ← MulOpposite.op_mul]
  | add v w hv hw =>
    simp only [TensorProduct.tmul_add, smul_add, _root_.map_sub, _root_.map_add] at *
    rw [sub_eq_zero.mp hv, sub_eq_zero.mp hw, sub_self]

def descend : tensor k D X (D ⊗[k] W) →ₗ[D] X ⊗[k] W :=
  (relations k D X (D ⊗[k] W)).liftQ (collapse k D X W) (relations_le_ker_collapse k D X W)

def insert : X ⊗[k] W →ₗ[D] tensor k D X (D ⊗[k] W) :=
  (quotient k D X (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D X (TensorProduct.mk k D W 1))

@[simp] theorem descend_quotient (z : X ⊗[k] (D ⊗[k] W)) :
    descend k D X W (quotient k D X (D ⊗[k] W) z) = collapse k D X W z := rfl

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
@[simp] theorem insert_tmul (x : X) (w : W) :
    insert k D X W (x ⊗ₜ[k] w) = quotient k D X (D ⊗[k] W) (x ⊗ₜ[k] (1 ⊗ₜ[k] w)) := rfl

theorem insert_descend : (insert k D X W).comp (descend k D X W) = LinearMap.id := by
  apply (relations k D X (D ⊗[k] W)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  induction v using OAI.tensorInductionOn with
  | tmul d w =>
    change insert k D X W (collapse k D X W (x ⊗ₜ[k] (d ⊗ₜ[k] w))) =
      quotient k D X (D ⊗[k] W) (x ⊗ₜ[k] (d ⊗ₜ[k] w))
    rw [collapse_tmul, insert_tmul, balanced]
    simp [TensorProduct.smul_tmul']
  | add v w hv hw => simp_all [TensorProduct.tmul_add]

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

section FreeMaps
variable (V W U : Type u) [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- Balanced tensor on a map of free modules, in the explicit field-tensor coordinates. -/
def freeMap (h : D ⊗[k] V →ₗ[D] D ⊗[k] W) : X ⊗[k] V →ₗ[D] X ⊗[k] W :=
  (descend k D X W).comp ((map k D X _ _ h).comp (insert k D X V))

/-- Coordinate change commutes with every free-module differential. -/
theorem freeMap_descend (h : D ⊗[k] V →ₗ[D] D ⊗[k] W)
    (z : tensor k D X (D ⊗[k] V)) :
    freeMap k D X V W h (descend k D X V z) =
      descend k D X W (map k D X _ _ h z) := by
  change descend k D X W (map k D X _ _ h (insert k D X V (descend k D X V z))) = _
  rw [show insert k D X V (descend k D X V z) = z from
    LinearMap.congr_fun (insert_descend k D X V) z]

theorem freeMap_comp (h : D ⊗[k] V →ₗ[D] D ⊗[k] W)
    (g : D ⊗[k] W →ₗ[D] D ⊗[k] U) :
    freeMap k D X V U (g.comp h) =
      (freeMap k D X W U g).comp (freeMap k D X V W h) := by
  apply LinearMap.ext
  intro z
  change descend k D X U (map k D X _ _ (g.comp h) (insert k D X V z)) =
    freeMap k D X W U g (descend k D X W (map k D X _ _ h (insert k D X V z)))
  rw [freeMap_descend, map_comp]
  rfl

@[simp] theorem freeMap_zero : freeMap k D X V W 0 = 0 := by
  apply LinearMap.ext
  intro z
  simp only [freeMap, LinearMap.comp_apply, map_zero, LinearMap.zero_apply, _root_.map_zero]
end FreeMaps

variable (N : Type u) [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- The two-sided bar differential for arbitrary bimodule coefficients X. -/
def barDifferential (n : ℕ) : X ⊗[k] DerivedBar.term k D N (n+1) →ₗ[D]
    X ⊗[k] DerivedBar.term k D N n :=
  freeMap k D X _ _ (DerivedBar.differential k D N (n+1))

/-- Independent endpoint-minus-tail formula, including the noncommutative right action. -/
theorem barDifferential_tmul (n : ℕ) (x : X) (z : DerivedBar.term k D N (n+1)) :
    barDifferential k D X N n (x ⊗ₜ[k] z) =
      collapse k D X (DerivedBar.term k D N n) (x ⊗ₜ[k] z) -
        x ⊗ₜ[k] DerivedBar.differential k D N n z := by
  change descend k D X (DerivedBar.term k D N n)
    (map k D X _ _ (DerivedBar.differential k D N (n+1))
      (insert k D X (DerivedBar.term k D N (n+1)) (x ⊗ₜ[k] z))) = _
  rw [insert_tmul, map_quotient, DerivedBar.differential_succ_tmul, one_smul,
    TensorProduct.tmul_sub, _root_.map_sub, _root_.map_sub,
    descend_quotient, descend_quotient, collapse_tmul, MulOpposite.op_one, one_smul]

theorem barDifferential_sq (n : ℕ) :
    (barDifferential k D X N n).comp (barDifferential k D X N (n+1)) = 0 := by
  unfold barDifferential
  rw [← freeMap_comp, DerivedBar.differential_sq, freeMap_zero]

/-- The explicit two-sided X,D,N bar complex, with no D-flatness assumption. -/
def barComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (X ⊗[k] DerivedBar.term k D N n))
    (fun n => ModuleCat.ofHom (barDifferential k D X N n))
    (fun n => ModuleCat.hom_ext (barDifferential_sq k D X N n))

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleDerived
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The canonical field action on a left D-module. -/
@[instance_reducible] def scalarModule (V : ModuleCat.{u} D) : Module k V := Module.compHom V (algebraMap k D)

local instance instModuleCarrier_solutions (V : ModuleCat.{u} D) : Module k V := scalarModule k D V
local instance instIsScalarTowerCarrier_solutions (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Actual balanced tensor by the arbitrary bimodule X, as an additive endofunctor. -/
def tensorFunctor : ModuleCat.{u} D ⥤ ModuleCat.{u} D where
  obj V := ModuleCat.of D (tensor k D X V)
  map h := ModuleCat.ofHom (map k D X _ _ h.hom)
  map_id V := ModuleCat.hom_ext (map_id k D X V)
  map_comp h g := ModuleCat.hom_ext (map_comp k D X _ _ _ h.hom g.hom)

instance tensorFunctor_additive : (tensorFunctor k D X).Additive where
  map_add := by
    intro V W h g
    exact ModuleCat.hom_ext (map_add k D X _ _ h.hom g.hom)

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Canonical scalar restriction agrees with every supplied compatible field action. -/
theorem scalarModule_eq (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] :
    scalarModule k D (ModuleCat.of D V) = (inferInstance : Module k V) := by
  apply Module.ext
  funext c v
  exact IsScalarTower.algebraMap_smul D c v

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BalancedTensorFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Balanced
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  (f : A →ₐ[k] D)

local instance instModuleCarrier_solutions (V : ModuleCat.{u} A) : Module k V := BimoduleTensor.scalarModule k A V
local instance instIsScalarTowerCarrier_solutions (V : ModuleCat.{u} A) : IsScalarTower k A V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def tensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} D where
  obj V := ModuleCat.of D (tensor f V)
  map h := ModuleCat.ofHom (map f _ _ h.hom)
  map_id V := ModuleCat.hom_ext (map_id f V)
  map_comp h g := ModuleCat.hom_ext (map_comp f _ _ _ h.hom g.hom)

instance tensorFunctor_additive : (tensorFunctor f).Additive where
  map_add := by
    intro V W h g
    apply ModuleCat.hom_ext
    apply (relations f V).linearMap_qext
    apply AlgebraTensorModule.ext
    intro d v
    change quotient f W (d ⊗ₜ[k] (h.hom v + g.hom v)) =
      quotient f W (d ⊗ₜ[k] h.hom v) + quotient f W (d ⊗ₜ[k] g.hom v)
    rw [TensorProduct.tmul_add, map_add]

def tensorFunctorObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    (tensorFunctor f).obj (ModuleCat.of A V) ≅ ModuleCat.of D (tensor f V) := by
  have h := BimoduleTensor.scalarModule_eq k A V
  cases h
  exact Iso.refl _

theorem tensorFunctorObjIso_natural (V W : Type u)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (h : V →ₗ[A] W) :
    (tensorFunctor f).map (ModuleCat.ofHom h) ≫ (tensorFunctorObjIso f W).hom =
      (tensorFunctorObjIso f V).hom ≫ ModuleCat.ofHom (map f V W h) := by
  have hV := BimoduleTensor.scalarModule_eq k A V
  have hW := BimoduleTensor.scalarModule_eq k A W
  cases hV
  cases hW
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def resolvedTensorIso :
    ((tensorFunctor f).mapHomologicalComplex (.down ℕ)).obj
      (DerivedBar.projectiveResolution k A N).complex ≅ tensorBarComplex k A D N f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tensorFunctorObjIso f (DerivedBar.term k A N (n+1)))
    (by
      intro i j hij
      change j+1=i at hij
      subst i
      simpa only [tensorBarComplex, DerivedBar.projectiveResolution,
        DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
        using (tensorFunctorObjIso_natural f (DerivedBar.term k A N (j+1+1))
          (DerivedBar.term k A N (j+1)) (DerivedBar.differential k A N (j+1))).symm)

def tensorBarHomologyIso (i : ℕ) :
    ((tensorFunctor f).leftDerived i).obj (ModuleCat.of A N) ≅
      (tensorBarComplex k A D N f).homology i :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj (tensorFunctor f) i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.down ℕ) i).mapIso (resolvedTensorIso f N)
end DerivedBar.Balanced

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BarFunctor
attribute [-simp] _root_.OAI.DerivedBar.SquareZero.projection_base _root_.OAI.DerivedBar.SquareZero.projection_ideal_succ _root_.OAI.DerivedBar.SquareZero.projection_ideal_zero _root_.OAI.DerivedBar.SquareZero.twoSidedProjection_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (V W U : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup U] [Module k U] [Module A U] [IsScalarTower k A U]

/-- Functorial map on every augmented bar term. -/
def termMap (h : V →ₗ[A] W) : (n : ℕ) → term k A V n →ₗ[A] term k A W n
  | 0 => h
  | n+1 => AlgebraTensorModule.lTensor A A ((termMap h n).restrictScalars k)

@[simp] theorem termMap_tmul (h : V →ₗ[A] W) (n : ℕ) (a : A) (v : term k A V n) :
    termMap k A V W h (n+1) (a ⊗ₜ[k] v) = a ⊗ₜ[k] termMap k A V W h n v := rfl

theorem termMap_comp (h : V →ₗ[A] W) (g : W →ₗ[A] U) (n : ℕ) :
    termMap k A V U (g.comp h) n = (termMap k A W U g n).comp (termMap k A V W h n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    change a ⊗ₜ[k] termMap k A V U (g.comp h) n v =
      a ⊗ₜ[k] termMap k A W U g n (termMap k A V W h n v)
    rw [ih]
    rfl

theorem termMap_id (n : ℕ) : termMap k A V V LinearMap.id n = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    change a ⊗ₜ[k] termMap k A V V LinearMap.id n v = a ⊗ₜ[k] v
    rw [ih]
    rfl

theorem termMap_zero (n : ℕ) : termMap k A V W 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    change a ⊗ₜ[k] termMap k A V W 0 n v = 0
    rw [ih, LinearMap.zero_apply, TensorProduct.tmul_zero]

/-- The bar differential is natural for all module maps. -/
theorem differential_natural (h : V →ₗ[A] W) (n : ℕ) :
    (differential k A W n).comp (termMap k A V W h (n+1)) =
      (termMap k A V W h n).comp (differential k A V n) := by
  induction n with
  | zero =>
    apply AlgebraTensorModule.ext
    intro a v
    exact (h.map_smul a v).symm
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    have hn : differential k A W n (termMap k A V W h (n+1) v) =
        termMap k A V W h n (differential k A V n v) := LinearMap.congr_fun ih v
    change a • termMap k A V W h (n+1) v -
        a ⊗ₜ[k] differential k A W n (termMap k A V W h (n+1) v) =
      termMap k A V W h (n+1) (a • v - a ⊗ₜ[k] differential k A V n v)
    rw [map_sub, map_smul]
    change a • termMap k A V W h (n+1) v -
        a ⊗ₜ[k] differential k A W n (termMap k A V W h (n+1) v) =
      a • termMap k A V W h (n+1) v -
        a ⊗ₜ[k] termMap k A V W h n (differential k A V n v)
    rw [hn]

/-- Unit insertion is natural over k, the key homotopy for the total bar augmentation. -/
theorem contraction_natural (h : V →ₗ[A] W) (n : ℕ) (v : term k A V n) :
    termMap k A V W h (n+1) (contraction k A V n v) =
      contraction k A W n (termMap k A V W h n v) := rfl

/-- An actual chain map between unaugmented free bar resolutions. -/
def complexMap (h : V →ₗ[A] W) : complex k A V ⟶ complex k A W where
  f n := ModuleCat.ofHom (termMap k A V W h (n+1))
  comm' i j hij := by
    change j+1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    simpa only [complex, ChainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom] using!
      differential_natural k A V W h (j+1)

local instance instModuleCarrier_solutions (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance instIsScalarTowerCarrier_solutions (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The explicit free bar resolution is functorial, not just an objectwise choice. -/
def barFunctor : ModuleCat.{u} A ⥤ ChainComplex (ModuleCat.{u} A) ℕ where
  obj N := complex k A N
  map h := complexMap k A _ _ h.hom
  map_id N := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_id k A N (n+1)
  map_comp h g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_comp k A _ _ _ h.hom g.hom (n+1)

instance barFunctor_preservesZero : (barFunctor k A).PreservesZeroMorphisms where
  map_zero V W := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_zero k A V W (n+1)

/-- The bicomplex for the left-module bar resolution of a nonnegative chain complex.
Outer degree is the bar length; inner degree is the input complex degree.
The two differentials commute by the proved naturality of the absolute bar differential. -/
def barBicomplex (Z : ChainComplex (ModuleCat.{u} A) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip (((barFunctor k A).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z)

/-- Each entry in the bar bicomplex is genuinely projective over A. -/
instance barBicomplex_projective (Z : ChainComplex (ModuleCat.{u} A) ℕ) (i q : ℕ) :
    Projective (((barBicomplex k A Z).X i).X q) := by
  change Projective ((complex k A (Z.X q)).X i)
  exact complex_projective k A (Z.X q) i

/-- The ordinary direct-sum total bar complex, with standard totalization signs.
The total augmentation quasi-isomorphism must still be proved. -/
def barTotal (Z : ChainComplex (ModuleCat.{u} A) ℕ) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  (barBicomplex k A Z).total (ComplexShape.down ℕ)

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace DerivedBar
universe u
abbrev moduleForgetAdd (A : Type u) [Ring A] : ModuleCat.{u} A ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} A) AddCommGrpCat
variable {A : Type u} [Ring A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
local notation "c" => ComplexShape.down ℕ

local notation "F" => moduleForgetAdd A

/-- Additive maps out of a module totalization, using its preserved coproduct.
This permits unit insertion, which need not be A-linear. -/
def totalAddDesc {n : ℕ} {Y : AddCommGrpCat.{u}}
    (f : ∀ i q (_ : i+q=n), (F).obj ((K.X i).X q) ⟶ Y) :
    (F).obj ((K.total c).X n) ⟶ Y :=
  (isColimitOfPreserves F (K.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π c c c) n)).desc
    { pt := Y
      ι := Discrete.natTrans (fun j => f j.as.val.1 j.as.val.2 j.as.property) }

@[reassoc (attr := simp)]
theorem ι_totalAddDesc {n : ℕ} {Y : AddCommGrpCat.{u}}
    (f : ∀ i q (_ : i+q=n), (F).obj ((K.X i).X q) ⟶ Y)
    (i q : ℕ) (h : i+q=n) :
    (F).map (K.ιTotal c i q n h) ≫ totalAddDesc K f = f i q h := by
  exact (isColimitOfPreserves F (K.toGradedObject.isColimitCofanMapObj
    (ComplexShape.π c c c) n)).fac _ ⟨⟨⟨i,q⟩,h⟩⟩

theorem totalAdd_hom_ext {n : ℕ} {Y : AddCommGrpCat.{u}}
    {f g : (F).obj ((K.total c).X n) ⟶ Y}
    (h : ∀ i q (hi : i+q=n),
      (F).map (K.ιTotal c i q n hi) ≫ f = (F).map (K.ιTotal c i q n hi) ≫ g) : f=g := by
  apply IsColimit.hom_ext
    (isColimitOfPreserves F (K.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π c c c) n))
  rintro ⟨⟨⟨i,q⟩,hi⟩⟩
  exact h i q hi
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBar
attribute [-simp] _root_.OAI.DerivedBar.SquareZero.projection_base _root_.OAI.DerivedBar.SquareZero.projection_ideal_succ _root_.OAI.DerivedBar.SquareZero.projection_ideal_zero _root_.OAI.DerivedBar.SquareZero.twoSidedProjection_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
local instance instModuleCarrier_solutions_1 (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance instIsScalarTowerCarrier_solutions_1 (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

variable (Z : ChainComplex (ModuleCat.{u} A) ℕ)
local notation "B" => barBicomplex k A Z
local notation "T" => barTotal k A Z
local notation "c" => ComplexShape.down ℕ

/-- The augmentation is the action in bar length zero and zero elsewhere. -/
def barTotalAugmentationF (n : ℕ) : (T).X n ⟶ Z.X n :=
  (B).totalDesc (fun i q h => match i with
    | 0 => ModuleCat.ofHom (differential k A (Z.X q) 0) ≫
        (Z.XIsoOfEq (by simpa using h)).hom
    | _+1 => 0)

@[reassoc (attr := simp)]
theorem ι_barTotalAugmentationF_zero (q n : ℕ) (h : 0 + q = n) :
    (B).ιTotal c 0 q n h ≫ barTotalAugmentationF k A Z n =
      ModuleCat.ofHom (differential k A (Z.X q) 0) ≫
        (Z.XIsoOfEq (by omega : q = n)).hom := by
  apply HomologicalComplex₂.ι_totalDesc

@[reassoc (attr := simp)]
theorem ι_barTotalAugmentationF_succ (i q n : ℕ) (h : i+1+q=n) :
    (B).ιTotal c (i+1) q n h ≫ barTotalAugmentationF k A Z n = 0 := by
  apply HomologicalComplex₂.ι_totalDesc

/-- Horizontal face formula in positive bar length. -/
theorem barTotal_d₁_succ (i q n : ℕ) (h : i+q=n) :
    (B).d₁ c (i+1) q n =
      ModuleCat.ofHom (differential k A (Z.X q) (i+1)) ≫ (B).ιTotal c i q n h := by
  rw [HomologicalComplex₂.d₁_eq _ _ (by rfl : (c).Rel (i+1) i) q n h]
  change (1 : ℤˣ) • ((complex k A (Z.X q)).d (i+1) i ≫ _) = _
  erw [one_smul]
  simp only [complex, ChainComplex.of_d]

/-- The horizontal differential is absent in bar length zero. -/
@[simp] theorem barTotal_d₁_zero (q n : ℕ) : (B).d₁ c 0 q n = 0 := by
  apply HomologicalComplex₂.d₁_eq_zero
  simp

/-- The vertical differential is absent in input degree zero. -/
@[simp] theorem barTotal_d₂_zero (i n : ℕ) : (B).d₂ c i 0 n = 0 := by
  apply HomologicalComplex₂.d₂_eq_zero
  simp

/-- Vertical face formula, with the standard totalization sign. -/
theorem barTotal_d₂_succ (i q n : ℕ) (h : i+q=n) :
    (B).d₂ c i (q+1) n =
      ((-1 : ℤˣ)^i) • (ModuleCat.ofHom
        (termMap k A (Z.X (q+1)) (Z.X q) (Z.d (q+1) q).hom (i+1)) ≫
          (B).ιTotal c i q n h) := by
  rw [HomologicalComplex₂.d₂_eq _ _ i (by rfl : (c).Rel (q+1) q) n h]
  rfl

/-- The total augmentation is a chain map. -/
theorem barTotalAugmentation_comm (n : ℕ) :
    (T).d (n+1) n ≫ barTotalAugmentationF k A Z n =
      barTotalAugmentationF k A Z (n+1) ≫ Z.d (n+1) n := by
  apply HomologicalComplex₂.total.hom_ext
  intro i q h
  change i+q=n+1 at h
  simp only [barTotal, HomologicalComplex₂.total_d]
  erw [add_comp, comp_add, HomologicalComplex₂.ι_D₁_assoc,
    HomologicalComplex₂.ι_D₂_assoc]
  cases i with
  | zero =>
    have hq : q=n+1 := by omega
    subst q
    erw [barTotal_d₁_zero, zero_comp, zero_add,
      barTotal_d₂_succ k A Z 0 n n (by omega)]
    erw [pow_zero, one_smul, Category.assoc, ι_barTotalAugmentationF_zero,
      ι_barTotalAugmentationF_zero_assoc]
    simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.comp_id]
    apply ModuleCat.hom_ext
    exact differential_natural k A (Z.X (n+1)) (Z.X n) (Z.d (n+1) n).hom 0
  | succ i =>
    erw [barTotal_d₁_succ k A Z i q n (by omega)]
    erw [Category.assoc]
    erw [ι_barTotalAugmentationF_succ_assoc k A Z i q (n+1) h]
    erw [zero_comp]
    have hhor : ModuleCat.ofHom (differential k A (Z.X q) (i+1)) ≫
        (B).ιTotal c i q n (show i+q=n by omega) ≫ barTotalAugmentationF k A Z n = 0 := by
      cases i with
      | zero =>
        have hn : q=n := by omega
        subst n
        erw [ι_barTotalAugmentationF_zero]
        simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl,
          Iso.refl_hom, Category.comp_id]
        exact ModuleCat.hom_ext (differential_sq k A (Z.X q) 0)
      | succ i => erw [ι_barTotalAugmentationF_succ, comp_zero]
    erw [hhor, zero_add]
    cases q with
    | zero => erw [barTotal_d₂_zero, zero_comp]
    | succ q =>
      erw [barTotal_d₂_succ k A Z (i+1) q n (by omega)]
      erw [CategoryTheory.Linear.units_smul_comp, Category.assoc,
        ι_barTotalAugmentationF_succ, comp_zero, smul_zero]

def barTotalAugmentation : T ⟶ Z where
  f := barTotalAugmentationF k A Z
  comm' i j h := by
    change j+1=i at h
    subst i
    exact (barTotalAugmentation_comm k A Z j).symm
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarContraction
attribute [-simp] _root_.OAI.DerivedBar.SquareZero.projection_base _root_.OAI.DerivedBar.SquareZero.projection_ideal_succ _root_.OAI.DerivedBar.SquareZero.projection_ideal_zero _root_.OAI.DerivedBar.SquareZero.twoSidedProjection_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
local instance instModuleCarrier_solutions_2 (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance instIsScalarTowerCarrier_solutions_2 (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (Z : ChainComplex (ModuleCat.{u} A) ℕ)
local notation "B" => barBicomplex k A Z
local notation "T" => barTotal k A Z
local notation "c" => ComplexShape.down ℕ
local notation "F" => moduleForgetAdd A

/-- Horizontal contribution with the declared total object as codomain. -/
def barTotalDH (i q n : ℕ) : (F).obj (((B).X i).X q) ⟶ (F).obj ((T).X n) :=
  (F).map ((B).d₁ c i q n)

/-- Vertical contribution with the declared total object as codomain. -/
def barTotalDV (i q n : ℕ) : (F).obj (((B).X i).X q) ⟶ (F).obj ((T).X n) :=
  (F).map ((B).d₂ c i q n)

/-- Unit insertion on an individual bar term, viewed as an additive map. -/
def barUnit (i q : ℕ) :
    AddCommGrpCat.of (term k A (Z.X q) i) ⟶ AddCommGrpCat.of (term k A (Z.X q) (i+1)) :=
  AddCommGrpCat.ofHom (contraction k A (Z.X q) i).toAddMonoidHom

/-- Unit insertion with the exact bicomplex source and target objects. -/
def barRaise (i q : ℕ) :
    (F).obj (((B).X i).X q) ⟶ (F).obj (((B).X (i+1)).X q) :=
  barUnit k A Z (i+1) q

/-- Natural unit insertion in the total bar, increasing bar length by one. -/
def barTotalH (n : ℕ) : (F).obj ((T).X n) ⟶ (F).obj ((T).X (n+1)) :=
  totalAddDesc B (fun i q h => barRaise k A Z i q ≫
    (F).map ((B).ιTotal c (i+1) q (n+1) (show i+1+q=n+1 by omega)))

@[reassoc (attr := simp)]
theorem ι_barTotalH (i q n : ℕ) (h : i+q=n) :
    (F).map ((B).ιTotal c i q n h) ≫ barTotalH k A Z n =
      barRaise k A Z i q ≫
        (F).map ((B).ιTotal c (i+1) q (n+1) (show i+1+q=n+1 by omega)) := by
  exact ι_totalAddDesc _ _ _ _ _

/-- Unit insertion in bar length zero gives the additive section. -/
def barTotalSectionF (n : ℕ) : (F).obj (Z.X n) ⟶ (F).obj ((T).X n) :=
  barUnit k A Z 0 n ≫ (F).map ((B).ιTotal c 0 n n (Nat.zero_add n))

@[reassoc (attr := simp)]
theorem barTotalSectionF_augmentation (n : ℕ) :
    barTotalSectionF k A Z n ≫ (F).map ((barTotalAugmentation k A Z).f n) = 𝟙 _ := by
  dsimp only [barTotal]
  dsimp only [barTotalSectionF, barTotalAugmentation]
  erw [Category.assoc, ← Functor.map_comp, ι_barTotalAugmentationF_zero]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  ext x
  exact contraction_zero k A (Z.X n) x

/-- Naturality of unit insertion under the input differential. -/
@[reassoc]
theorem barUnit_natural (i p q : ℕ) :
    (F).map (ModuleCat.ofHom (termMap k A (Z.X p) (Z.X q) (Z.d p q).hom i)) ≫
      barUnit k A Z i q =
    barUnit k A Z i p ≫
      (F).map (ModuleCat.ofHom (termMap k A (Z.X p) (Z.X q) (Z.d p q).hom (i+1))) := by
  ext x
  exact (contraction_natural k A (Z.X p) (Z.X q) (Z.d p q).hom i x).symm

@[reassoc]
theorem ι_barTotal_d (i q n m : ℕ) (h : i+q=n) :
    (F).map ((B).ιTotal c i q n h) ≫ (F).map ((T).d n m) =
      barTotalDH k A Z i q m + barTotalDV k A Z i q m := by
  dsimp only [barTotal, barTotalDH, barTotalDV]
  erw [← Functor.map_comp]
  simp only [HomologicalComplex₂.total_d, comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Functor.map_add]
  rfl

theorem add_interleave {M : Type*} [AddCommMonoid M] (aa bb cc dd ee : M) :
    aa + bb + (cc + dd) + ee = (aa + cc + ee) + (bb + dd) := by
  abel

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
local instance instModuleCarrier_solutions_3 (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance instIsScalarTowerCarrier_solutions_3 (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local notation "c" => ComplexShape.down ℕ

/-- The total bar resolution is a functor on nonnegative chain complexes. -/
def barTotalFunctor : ChainComplex (ModuleCat.{u} A) ℕ ⥤ ChainComplex (ModuleCat.{u} A) ℕ :=
  (barFunctor k A).mapHomologicalComplex c ⋙
    HomologicalComplex₂.flipFunctor _ c c ⋙ HomologicalComplex₂.totalFunctor _ c c c

@[reassoc]
theorem ι_barTotalFunctor_map {Z W : ChainComplex (ModuleCat.{u} A) ℕ} (f : Z ⟶ W)
    (i q n : ℕ) (h : i+q=n) :
    (barBicomplex k A Z).ιTotal c i q n h ≫ ((barTotalFunctor k A).map f).f n =
      ModuleCat.ofHom (termMap k A (Z.X q) (W.X q) (f.f q).hom (i+1)) ≫
        (barBicomplex k A W).ιTotal c i q n h := by
  dsimp only [barTotalFunctor, Functor.comp_map, HomologicalComplex₂.totalFunctor]
  erw [HomologicalComplex₂.ιTotal_map]
  rfl

theorem augmentation_zero_diagonal (Z : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ)
    (h : 0 + n = n) :
    (barBicomplex k A Z).ιTotal c 0 n n h ≫ barTotalAugmentationF k A Z n =
      ModuleCat.ofHom (differential k A (Z.X n) 0) := by
  erw [ι_barTotalAugmentationF_zero, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id]

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]

/-- Additive functors preserve quasi-isomorphisms between nonnegative projective complexes.
This uses the proved homotopy-equivalence criterion, not a flatness hypothesis. -/
theorem additive_map_quasiIso_of_projective (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D)
    [G.Additive] {P Q : ChainComplex (ModuleCat.{u} D) ℕ}
    [∀ n, Projective (P.X n)] [∀ n, Projective (Q.X n)]
    (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map f) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  rw [← he]
  exact (G.mapHomotopyEquiv e).quasiIso_hom

variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Resolve the entire input complex before applying the actual balanced tensor functor. -/
def tensorTotalFunctor : ChainComplex (ModuleCat.{u} D) ℕ ⥤ ChainComplex (ModuleCat.{u} D) ℕ :=
  barTotalFunctor k D ⋙
    (BimoduleTensor.tensorFunctor k D X).mapHomologicalComplex (ComplexShape.down ℕ)

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSidedBarFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_2 (N : ModuleCat.{u} D) : Module k N := scalarModule k D N
local instance instIsScalarTowerCarrier_solutions_2 (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The map on the explicit field-tensor bar terms. -/
def barTermMap {V W : ModuleCat.{u} D} (f : V ⟶ W) (n : ℕ) :
    X ⊗[k] term k D V n →ₗ[D] X ⊗[k] term k D W n :=
  AlgebraTensorModule.lTensor D X ((termMap k D V W f.hom n).restrictScalars k)

theorem freeMap_termMap {V W : ModuleCat.{u} D} (f : V ⟶ W) (n : ℕ) :
    freeMap k D X _ _ (termMap k D V W f.hom (n+1)) =
      barTermMap k D X f n := by
  apply AlgebraTensorModule.ext
  intro x v
  change descend k D X _ (map k D X _ _ (termMap k D V W f.hom (n+1))
    (insert k D X _ (x ⊗ₜ[k] v))) = x ⊗ₜ[k] termMap k D V W f.hom n v
  rw [insert_tmul, map_quotient, termMap_tmul, descend_quotient,
    collapse_tmul, MulOpposite.op_one, one_smul]

theorem barDifferential_natural {V W : ModuleCat.{u} D} (f : V ⟶ W) (n : ℕ) :
    (barDifferential k D X W n).comp (barTermMap k D X f (n+1)) =
      (barTermMap k D X f n).comp (barDifferential k D X V n) := by
  rw [← freeMap_termMap, ← freeMap_termMap]
  unfold barDifferential
  rw [← freeMap_comp, ← freeMap_comp, differential_natural]

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarDerived
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Functor HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
local notation "c" => ComplexShape.down ℕ

abbrev chainQuasiIso := HomologicalComplex.quasiIso (ModuleCat.{u} D) c
abbrev chainDerived := (chainQuasiIso D).Localization
abbrev chainQ : ChainComplex (ModuleCat.{u} D) ℕ ⥤ chainDerived D := (chainQuasiIso D).Q

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BarBimoduleCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor TensorProduct
open scoped TensorProduct
namespace DerivedBar.BimoduleTensor
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
variable {X Y : Type u}
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [Module D Y] [Module Dᵐᵒᵖ Y]
  [SMulCommClass D Dᵐᵒᵖ Y] [IsScalarTower k D Y] [IsScalarTower k Dᵐᵒᵖ Y]
variable (e : X ≃ₗ[D] Y) (he : ∀ d : Dᵐᵒᵖ, ∀ x, e (d • x) = d • e x)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

include he in
omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ Y] [IsScalarTower k Dᵐᵒᵖ Y] [IsScalarTower k D V] in
theorem leftMap_relations : relations k D X V ≤
    ((quotient k D Y V).comp (AlgebraTensorModule.rTensor k V e.toLinearMap)).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x,d,v,rfl⟩
  change quotient k D Y V (AlgebraTensorModule.rTensor k V e.toLinearMap
    ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v))) = 0
  simp only [_root_.map_sub, AlgebraTensorModule.rTensor_tmul, LinearEquiv.coe_coe, he]
  rw [balanced, sub_self]

/-- The actual left-factor map on the bar's balanced quotient. -/
def leftMap : tensor k D X V →ₗ[D] tensor k D Y V :=
  (relations k D X V).liftQ
    ((quotient k D Y V).comp (AlgebraTensorModule.rTensor k V e.toLinearMap))
      (leftMap_relations k D e he V)

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ Y] [IsScalarTower k Dᵐᵒᵖ Y] [IsScalarTower k D V] in
@[simp] theorem leftMap_quotient (x : X) (v : V) :
    leftMap k D e he V (quotient k D X V (x ⊗ₜ[k] v)) =
      quotient k D Y V (e x ⊗ₜ[k] v) := rfl

include he in
omit [SMulCommClass D Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ Y] in
theorem symm_right (d : Dᵐᵒᵖ) (y : Y) : e.symm (d • y) = d • e.symm y := by
  apply e.injective
  simp only [LinearEquiv.apply_symm_apply, he]

/-- A genuine bimodule equivalence induces an equivalence of the actual balanced tensors. -/
def congrLeft : tensor k D X V ≃ₗ[D] tensor k D Y V :=
  LinearEquiv.ofLinearMap (leftMap k D e he V)
    (leftMap k D e.symm (symm_right D e he) V)
    (by
      apply (relations k D Y V).linearMap_qext
      apply AlgebraTensorModule.ext
      intro y v
      change quotient k D Y V (e (e.symm y) ⊗ₜ[k] v) = quotient k D Y V (y ⊗ₜ[k] v)
      rw [e.apply_symm_apply])
    (by
      apply (relations k D X V).linearMap_qext
      apply AlgebraTensorModule.ext
      intro x v
      change quotient k D X V (e.symm (e x) ⊗ₜ[k] v) = quotient k D X V (x ⊗ₜ[k] v)
      rw [e.symm_apply_apply])

local instance instModuleCarrier_solutions_4 (N : ModuleCat.{u} D) : Module k N := scalarModule k D N
local instance instIsScalarTowerCarrier_solutions_4 (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Naturality in every input module retains the exterior D-action. -/
def tensorFunctorCongr : tensorFunctor k D X ≅ tensorFunctor k D Y :=
  NatIso.ofComponents (fun N => (congrLeft k D e he N).toModuleIso) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply (relations k D X N).linearMap_qext
    apply AlgebraTensorModule.ext
    intro x n
    rfl)

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotal
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
local instance instHasDerivedCategoryModuleCat_solutions_3 : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
end LittleFinitistic.BimoduleTotal

end

end OAI
end



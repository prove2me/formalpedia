-- Prove2me | Definitions.Def_OAIQ023F004
-- name    : OAIQ023F004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:39:47.427014+00:00
-- url     : https://prove2.me/theorems/d6c77604-14ee-4acb-bf46-67eeecb5de98
-- title:
--   Definitions bundle OAIQ023F004 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 141 declarations of OpenAI's Lean: 56 definitions, 2 inductive types or structures, 41 instances and 42 theorems. The definitions and types are `OAI.LittleFinitistic.OrdinarySimulation.Compression`, `OAI.LittleFinitistic.OrdinarySimulation.Compression.insert`, `OAI.LittleFinitistic.OrdinarySimulation.Compression.project`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.congr`, `OAI.LittleFinitistic.OrdinarySimulation.OffDiagonal.map`, `OAI.LittleFinitistic.OrdinarySimulation.TensorDirected.bIndex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorDirected.cIndex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.coefficient`, `OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.vertex`, `OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.degreeEmbedding`, `OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple`, `OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor`, `OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.value`, `OAI.LittleFinitistic.OrdinarySimulation.intervalDifferential`, `OAI.LittleFinitistic.OrdinarySimulation.intervalTerms`, `OAI.LittleFinitistic.OrdinarySimulation.underlyingComplex`, `OAI.LittleFinitistic.OrdinarySimulation.unsignedShift`, `OAI.LittleFinitistic.PDBarQuotient.RightBase`, `OAI.LittleFinitistic.PDBarQuotient.restrictHomologyIso`, `OAI.LittleFinitistic.PDCovers.RightMinimal`, `OAI.LittleFinitistic.PDMinimal.Cover`, `OAI.LittleFinitistic.PDMinimal.FiniteModule`, `OAI.LittleFinitistic.PDMinimal.FiniteModule.cat`, `OAI.LittleFinitistic.PDMinimal.FiniteModule.of`, `OAI.LittleFinitistic.PDMinimal.augment`, `OAI.LittleFinitistic.PDMinimal.complex`, `OAI.LittleFinitistic.PDMinimal.cover`, `OAI.LittleFinitistic.PDMinimal.differential`, `OAI.LittleFinitistic.PDMinimal.next`, `OAI.LittleFinitistic.PDMinimal.resolution`, `OAI.LittleFinitistic.PDMinimal.syzygy`, `OAI.LittleFinitistic.PDMinimal.term`, `OAI.LittleFinitistic.PDSquareZero.residueQuotientEquiv`, `OAI.LittleFinitistic.PDTensor.Residue`, `OAI.LittleFinitistic.PDTensor.ScalarModule`, `OAI.LittleFinitistic.PDTensor.Top`, `OAI.LittleFinitistic.PDTensor.radicalProduct`, `OAI.LittleFinitistic.PDTensor.residuePair`, `OAI.LittleFinitistic.PDTensor.rightRadical` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Dimension_PDBalancedRight`, `Finitistic_Dimension_PDBarQuotient`, `Finitistic_Dimension_PDBaseBarConsumer`, `Finitistic_Dimension_PDCoverRadical`, `Finitistic_Dimension_PDCovers`, `Finitistic_Dimension_PDMinimalData`, `Finitistic_Dimension_PDMinimalResolution`, `Finitistic_Dimension_PDRadical`, `Finitistic_Dimension_PDResidueTensor`, `Finitistic_Dimension_PDSquareZero`, `Finitistic_Dimension_PDSquareZeroResidue`, `Finitistic_Dimension_PDTensorFunctor`, `Finitistic_Iteration_FunctorObjectIteration`, `Finitistic_Ordinary_OrdinaryBlockBimodule`, `Finitistic_Ordinary_OrdinaryCochain`, `Finitistic_Ordinary_OrdinaryCompression`, `Finitistic_Ordinary_OrdinaryIntegerResolution`, `Finitistic_Ordinary_OrdinaryOffDiagonalMaps`, `Finitistic_Ordinary_OrdinaryPairComplex`, `Finitistic_Ordinary_OrdinaryPairQuasiIso`, `Finitistic_Ordinary_OrdinaryProductOpposite`, `Finitistic_Ordinary_OrdinaryProductSplitting`, `Finitistic_Ordinary_OrdinaryResolutionQuasiIso`, `Finitistic_Ordinary_OrdinaryRetainedBimodule`, `Finitistic_Ordinary_OrdinaryRetainedCongruence`, `Finitistic_Ordinary_OrdinaryRetainedRestriction`, `Finitistic_Ordinary_OrdinaryRightProjective`, `Finitistic_Ordinary_OrdinaryShiftSign`, `Finitistic_Ordinary_OrdinarySingleTensorTerms`, `Finitistic_Ordinary_OrdinaryTensorDirected`, `Finitistic_Ordinary_OrdinaryTensorIdeal`, `Finitistic_Ordinary_OrdinaryTensorIdealActions`, `Finitistic_Ordinary_OrdinaryTerminal`, `Finitistic_Ordinary_OrdinaryTerminalResolution`, `Finitistic_Ordinary_OrdinaryVertexCompression`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F008` and `OAIQ023F009`.
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
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBalancedRight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
variable {M N : Type u} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The actual right radical quotient of the regular module. -/
def rightRadical : Submodule Aᵐᵒᵖ A where
  carrier := Ring.jacobson A
  zero_mem' := (Ring.jacobson A).zero_mem
  add_mem' := (Ring.jacobson A).add_mem
  smul_mem' b _ ha := (Ring.jacobson A).mul_mem_right b.unop ha

abbrev Residue := A ⧸ (rightRadical (A := A))

theorem residue_annihilated (a : A) (ha : a ∈ Ring.jacobson A) (s : Residue (A := A)) :
    MulOpposite.op a • s = 0 := by
  induction s using Submodule.Quotient.induction_on with
  | _ b =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (Ring.jacobson A).mul_mem_left b ha
end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDTensorFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

abbrev ScalarModule (M : ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (algebraMap k A)).obj M

instance scalarModuleTower (M : ModuleCat.{u} A) :
    IsScalarTower k A (ScalarModule k A M) where
  smul_assoc c a m := by
    change (c • a) • (m : M) = algebraMap k A c • (a • (m : M))
    rw [Algebra.smul_def, mul_smul]

end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBarQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

/-- D with the actual right A action through f. -/
def RightBase (_f : A →ₐ[k] D) := D
instance instRingRightBase : Ring (RightBase f) := inferInstanceAs (Ring D)
instance instAlgebraRightBase : Algebra k (RightBase f) := inferInstanceAs (Algebra k D)
instance instModuleMulOppositeRightBase : Module Aᵐᵒᵖ (RightBase f) := Module.compHom D f.toRingHom.op

@[simp] theorem right_smul (a : A) (d : RightBase f) :
    MulOpposite.op a • d = (show RightBase f from (show D from d) * f a) := rfl

end LittleFinitistic.PDBarQuotient

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDCovers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDCovers
open Module LinearMap Submodule
universe u v
variable {A : Type u} [Ring A]
variable {E N : Type v} [AddCommGroup E] [Module A E]
  [AddCommGroup N] [Module A N]

/-- An epimorphism is right minimal if every endomorphism over it is surjective. -/
def RightMinimal (p : E →ₗ[A] N) : Prop :=
  ∀ f : Module.End A E, p.comp f = p → Function.Surjective f

lemma comp_pow_eq {p : E →ₗ[A] N} {f : Module.End A E}
    (h : p.comp f = p) (n : ℕ) : p.comp (f ^ n) = p := by
  induction n with
  | zero => ext x; rfl
  | succ n ih => rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, h]

/-- Fitting decomposition upgrades minimality among projective submodules to
right minimality of an actual epimorphism. -/
theorem rightMinimal_of_minimal [IsArtinian A E] [IsNoetherian A E]
    (p : E →ₗ[A] N) (S : Submodule A E)
    (hS : Minimal (fun T : Submodule A E =>
      Module.Projective A T ∧ Function.Surjective (p.comp T.subtype)) S) :
    RightMinimal (p.comp S.subtype) := by
  have : Module.Projective A S := hS.1.1
  intro f hf
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
  let r := f ^ (n+1)
  have hc : IsCompl (LinearMap.range r) (LinearMap.ker r) :=
    (hn (n+1) (by omega)).symm
  let R := LinearMap.range r
  have : Module.Projective A R := Module.Projective.of_split R.subtype
    (R.projectionOnto (LinearMap.ker r) hc) (Submodule.projectionOnto_comp_subtype hc)
  let T := R.map S.subtype
  let i : R →ₗ[A] E := S.subtype.comp R.subtype
  have hi : Function.Injective i := S.injective_subtype.comp R.injective_subtype
  have he : LinearMap.range i = T := by simp [i, T, LinearMap.range_comp]
  let e : R ≃ₗ[A] T := (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ he)
  have : Module.Projective A T := Module.Projective.of_equiv e
  have hpr : (p.comp S.subtype).comp r = p.comp S.subtype := comp_pow_eq hf _
  have hTsurj : Function.Surjective (p.comp T.subtype) := by
    intro y
    obtain ⟨x, hx⟩ := hS.1.2 y
    refine ⟨⟨S.subtype (r x), ⟨r x, mem_range_self r x, rfl⟩⟩, ?_⟩
    exact (DFunLike.congr_fun hpr x).trans hx
  have hTS : T ≤ S := by
    rintro x ⟨z, hz, rfl⟩
    exact z.property
  have hST : S ≤ T := hS.2 ⟨inferInstance, hTsurj⟩ hTS
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨z, ⟨w, hw⟩, hz⟩ := hST x.property
    refine ⟨w, ?_⟩
    exact hw.trans (Subtype.ext hz)
  intro x
  obtain ⟨y, hy⟩ := hr x
  refine ⟨(f ^ n) y, ?_⟩
  simpa [r, pow_succ', Module.End.mul_eq_comp] using hy

/-- Every projective epimorphism from a finite-length module contains a
projective cover. This proves existence rather than assuming covers. -/
theorem exists_rightMinimal [IsArtinian A E] [IsNoetherian A E]
    [Module.Projective A E] (p : E →ₗ[A] N) (hp : Function.Surjective p) :
    ∃ S : Submodule A E, Module.Projective A S ∧
      Function.Surjective (p.comp S.subtype) ∧ RightMinimal (p.comp S.subtype) := by
  have : Module.Projective A (⊤ : Submodule A E) :=
    Module.Projective.of_equiv (Submodule.topEquiv : (⊤ : Submodule A E) ≃ₗ[A] E).symm
  obtain ⟨S, hS⟩ := WellFoundedLT.exists_minimal (inferInstance : WellFoundedLT (Submodule A E))
    {T : Submodule A E | Module.Projective A T ∧ Function.Surjective (p.comp T.subtype)}
    ⟨⊤, inferInstance, fun y => by obtain ⟨x, hx⟩ := hp y; exact ⟨⟨x, mem_top⟩, hx⟩⟩
  exact ⟨S, hS.1.1, hS.1.2, rightMinimal_of_minimal p S hS⟩
end LittleFinitistic.PDCovers

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDCoverRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDCovers
open Module LinearMap Submodule
universe u
variable {A : Type u} [Ring A]
variable {E N : Type u} [AddCommGroup E] [Module A E]
  [AddCommGroup N] [Module A N]

/-- A projective right-minimal epimorphism has a superfluous kernel. -/
theorem eq_top_of_sup_ker [Module.Projective A E]
    (p : E →ₗ[A] N) (hp : Function.Surjective p) (hm : RightMinimal p)
    (L : Submodule A E) (hL : L ⊔ LinearMap.ker p = ⊤) : L = ⊤ := by
  have hsurj : Function.Surjective (p.comp L.subtype) := by
    intro y
    obtain ⟨x, hx⟩ := hp y
    have hm : x ∈ L ⊔ LinearMap.ker p := hL.symm ▸ mem_top
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hm
    refine ⟨⟨z, hz⟩, ?_⟩
    have hw0 : p w = 0 := hw
    change p z = y
    rw [← hx, ← hzw, map_add, hw0, add_zero]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (p.comp L.subtype) p hsurj
  have hfg : p.comp (L.subtype.comp g) = p := by rwa [← LinearMap.comp_assoc]
  have hfgsurj := hm (L.subtype.comp g) hfg
  apply top_unique
  intro x _
  obtain ⟨z, hz⟩ := hfgsurj x
  rw [← hz]
  exact (g z).property

/-- Projective-cover kernels lie in the actual module Jacobson radical. -/
theorem ker_le_jacobson [Module.Projective A E]
    (p : E →ₗ[A] N) (hp : Function.Surjective p) (hm : RightMinimal p) :
    LinearMap.ker p ≤ Module.jacobson A E := by
  apply le_sInf
  intro L hL
  by_contra h
  have hlt : L < L ⊔ LinearMap.ker p := lt_of_le_of_ne le_sup_left (fun he => h (he ▸ le_sup_right))
  have htop : L ⊔ LinearMap.ker p = ⊤ := hL.2 _ hlt
  exact hL.1 (eq_top_of_sup_ker p hp hm L htop)

/-- Over a finite-dimensional algebra every finite-dimensional module has an
actual finitely generated projective cover, constructed inside a finite free module. -/
theorem exists_finite_projective_cover
    {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
    [Module k N] [IsScalarTower k A N] [FiniteDimensional k N] :
    ∃ (n : ℕ) (S : Submodule A (Fin n → A)) (p : S →ₗ[A] N),
      Module.Projective A S ∧ Function.Surjective p ∧
      RightMinimal p ∧ LinearMap.ker p ≤ Module.jacobson A S := by
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A N
  have : IsArtinian A (Fin n → A) := isArtinian_of_tower k inferInstance
  have : IsNoetherian A (Fin n → A) := isNoetherian_of_tower k inferInstance
  obtain ⟨S, hS, hs, hm⟩ := exists_rightMinimal p hp
  have := hS
  exact ⟨n, S, p.comp S.subtype, hS, hs, hm, ker_le_jacobson _ hs hm⟩
end LittleFinitistic.PDCovers

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDRadical
open Module LinearMap Submodule
universe u v
variable {A : Type u} [Ring A]
variable (P : Type v) [AddCommGroup P] [Module A P]

/-- For a finitely generated projective module the module radical is exactly
multiplication by the ring Jacobson radical. No commutativity is assumed. -/
theorem jacobson_eq_smul [Module.Finite A P] [Module.Projective A P] :
    Module.jacobson A P = Ring.jacobson A • (⊤ : Submodule A P) := by
  apply le_antisymm _ (Ring.jacobson_smul_top_le A P)
  intro x hx
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hcoord (i : Fin n) : g x i ∈ Ring.jacobson A :=
    Module.le_comap_jacobson ((LinearMap.proj i).comp g) hx
  have hsum : g x = ∑ i : Fin n, Pi.single i (g x i) := by
    classical
    ext j
    simp
  have hxsum : x = ∑ i : Fin n, (g x i) • f (Pi.single i 1) := by
    classical
    calc
      x = f (g x) := (DFunLike.congr_fun hfg x).symm
      _ = ∑ i : Fin n, f (Pi.single i (g x i)) := by conv_lhs => rw [hsum, map_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have he : Pi.single i (g x i) = (g x i) • (Pi.single i 1 : Fin n → A) := by
          ext j
          by_cases hj : i = j
          · subst j; simp
          · simp [Ne.symm hj]
        rw [he, map_smul]
  rw [hxsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) mem_top

end LittleFinitistic.PDRadical

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDMinimalData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open Module LinearMap Submodule
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- Finite-dimensional actual left modules, retaining the scalar compatibility. -/
structure FiniteModule where
  carrier : Type u
  [add : AddCommGroup carrier]
  [moduleA : Module A carrier]
  [moduleK : Module k carrier]
  [tower : IsScalarTower k A carrier]
  [finite : FiniteDimensional k carrier]
attribute [instance] FiniteModule.add FiniteModule.moduleA FiniteModule.moduleK
  FiniteModule.tower FiniteModule.finite
instance instCoeSortFiniteModuleType : CoeSort (FiniteModule k A) (Type u) := ⟨FiniteModule.carrier⟩

namespace FiniteModule
variable {k A}
abbrev of (M : Type u) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] : FiniteModule k A := ⟨M⟩
def cat (M : FiniteModule k A) : ModuleCat A := ModuleCat.of A M
instance instFiniteCarrier (M : FiniteModule k A) : Module.Finite A M :=
  Module.Finite.of_restrictScalars_finite k A M
end FiniteModule

variable [FiniteDimensional k A]
/-- Projective covers with their actual maps and radical-kernel property. -/
structure Cover (M : FiniteModule k A) where
  source : FiniteModule k A
  [projective : Module.Projective A source]
  π : source →ₗ[A] M
  surjective : Function.Surjective π
  minimal : PDCovers.RightMinimal π
  radical : LinearMap.ker π ≤ Ring.jacobson A • (⊤ : Submodule A source)
attribute [instance] Cover.projective

variable {k A}
theorem cover_nonempty (M : FiniteModule k A) : Nonempty (Cover k A M) := by
  obtain ⟨n, S, p, hP, hp, hm, hr⟩ := PDCovers.exists_finite_projective_cover (k := k) (A := A) (N := M)
  have := hP
  have : FiniteDimensional k S := Module.Finite.of_injective
    (S.subtype.restrictScalars k) S.injective_subtype
  have : Module.Finite A S := Module.Finite.of_restrictScalars_finite k A S
  refine ⟨⟨FiniteModule.of S, p, hp, hm, ?_⟩⟩
  exact hr.trans (PDRadical.jacobson_eq_smul S).le

def cover (M : FiniteModule k A) : Cover k A M := Classical.choice (cover_nonempty M)

abbrev next (M : FiniteModule k A) : FiniteModule k A := by
  have : FiniteDimensional k (LinearMap.ker (cover M).π) :=
    Module.Finite.of_injective ((LinearMap.ker (cover M).π).subtype.restrictScalars k)
      (Submodule.injective_subtype _)
  exact FiniteModule.of (LinearMap.ker (cover M).π)

@[reducible] def syzygy (M : FiniteModule k A) : ℕ → FiniteModule k A
  | 0 => M
  | n+1 => next (syzygy M n)

abbrev term (M : FiniteModule k A) (n : ℕ) := (cover (syzygy M n)).source
abbrev augment (M : FiniteModule k A) (n : ℕ) := (cover (syzygy M n)).π

def differential (M : FiniteModule k A) (n : ℕ) : term M (n+1) →ₗ[A] term M n :=
  (LinearMap.ker (augment M n)).subtype.comp (augment M (n+1))

@[simp] theorem augment_differential (M : FiniteModule k A) (n : ℕ) :
    (augment M n).comp (differential M n) = 0 := by
  ext x
  exact (augment M (n+1) x).property

@[simp] theorem differential_comp (M : FiniteModule k A) (n : ℕ) :
    (differential M n).comp (differential M (n+1)) = 0 := by
  rw [differential, LinearMap.comp_assoc, augment_differential, LinearMap.comp_zero]

theorem range_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M n) = LinearMap.ker (augment M n) := by
  rw [differential, LinearMap.range_comp, LinearMap.range_eq_top.mpr (cover _).surjective,
    Submodule.map_top, Submodule.range_subtype]

theorem ker_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.ker (differential M n) = LinearMap.ker (augment M (n+1)) := by
  ext x
  change ((augment M (n+1) x : LinearMap.ker (augment M n)) : term M n) = 0 ↔
    augment M (n+1) x = 0
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg (fun z : LinearMap.ker (augment M n) => z.val) h

theorem exact_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M (n+1)) = LinearMap.ker (differential M n) := by
  rw [range_differential, ker_differential]

theorem differential_radical (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M n) ≤
      Ring.jacobson A • (⊤ : Submodule A (term M n)) := by
  rw [range_differential]
  exact (cover _).radical
end LittleFinitistic.PDMinimal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDMinimalResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (M : FiniteModule k A)

/-- The actual chain complex of the successive projective covers. -/
def complex : ChainComplex (ModuleCat A) ℕ := ChainComplex.of
  (fun n => (term M n).cat)
  (fun n => ModuleCat.ofHom (differential M n))
  (fun n => ModuleCat.hom_ext (differential_comp M n))

@[simp] theorem complex_d (n : ℕ) :
    (complex M).d (n+1) n = ModuleCat.ofHom (differential M n) := by
  exact ChainComplex.of_d (fun n => (term M n).cat)
    (fun n => ModuleCat.ofHom (differential M n)) n

instance term_projective (n : ℕ) : Projective ((complex M).X n) := by
  exact (IsProjective.iff_projective _).mp (cover (syzygy M n)).projective

lemma complex_exactAt (n : ℕ) : (complex M).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((complex M).d (n+2) (n+1)).hom =
    LinearMap.ker ((complex M).d (n+1) n).hom
  rw [complex_d, complex_d]
  exact exact_differential M n

lemma complex_d_augment : (complex M).d 1 0 ≫ ModuleCat.ofHom (augment M 0) = 0 := by
  rw [complex_d]
  exact ModuleCat.hom_ext (augment_differential M 0)

lemma complex_exact_augment :
    (ShortComplex.mk _ _ (complex_d_augment M)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((complex M).d 1 0).hom = LinearMap.ker (augment M 0)
  rw [complex_d]
  exact range_differential M 0

instance augment_epi : Epi (ModuleCat.ofHom (augment M 0)) :=
  (ModuleCat.epi_iff_surjective _).mpr (cover _).surjective

/-- A projective resolution, including its augmentation quasi-isomorphism. -/
def resolution : ProjectiveResolution M.cat where
  complex := complex M
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (augment M 0),
    complex_d_augment M⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      ·
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨complex_exact_augment M, augment_epi M⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by erw [Category.id_comp])
          (by erw [Category.id_comp])
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt M n
      · apply ChainComplex.exactAt_succ_single_obj⟩
end LittleFinitistic.PDMinimal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

abbrev radicalProduct := Ring.jacobson A • (⊤ : Submodule A N)
abbrev Top := N ⧸ radicalProduct (A := A) N

def residuePair : Residue (A := A) →ₗ[k] N →ₗ[k] Top (A := A) N := by
  let f : A →ₗ[k] N →ₗ[k] Top (A := A) N :=
    { toFun := fun a =>
        { toFun := fun n => (radicalProduct N).mkQ (a • n)
          map_add' := fun x y => by simp [smul_add]
          map_smul' := fun c n => by simp [smul_comm a c] }
      map_add' := fun a b => by ext n; simp [add_smul]
      map_smul' := fun c a => by ext n; simp [smul_assoc] }
  exact ((rightRadical (A := A)).restrictScalars k).liftQ f (by
    intro a ha
    ext n
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul ha mem_top)

@[simp] theorem residuePair_mk (a : A) (n : N) :
    residuePair (k := k) N (Submodule.Quotient.mk a) n =
      (radicalProduct N).mkQ (a • n) := rfl

end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDSquareZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDSquareZero
open Submodule
universe u
variable {A D : Type u} [Ring A] [Ring D]

/-- A square-zero ideal lies in the actual noncommutative Jacobson radical. -/
theorem squareZero_le_jacobson (I : Ideal A)
    (hI : ∀ a ∈ I, ∀ b ∈ I, a*b=0) : I ≤ Ring.jacobson A := by
  apply le_sInf
  intro L hL
  by_contra hn
  have hlt : L < L ⊔ I := lt_of_le_of_ne le_sup_left (fun he => hn (he ▸ le_sup_right))
  have htop : L ⊔ I = ⊤ := hL.2 _ hlt
  have hone : (1 : A) ∈ L ⊔ I := htop.symm ▸ mem_top
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp hone
  have hxx : x*x=0 := hI x hx x hx
  have hleq : l=1-x := eq_sub_iff_add_eq.mpr hlx
  have heq : (1+x)*l=1 := by
    simp [hleq, mul_sub, add_mul, hxx]
  have h1 : (1 : A) ∈ L := heq ▸ L.smul_mem (1+x) hl
  exact hL.1 (Ideal.eq_top_of_isUnit_mem L h1 isUnit_one)

/-- A surjection with square-zero kernel pulls back the ring radical exactly. -/
theorem comap_jacobson (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) :
    Ideal.comap f (Ring.jacobson D) = Ring.jacobson A := by
  let : RingHomSurjective f := ⟨hf⟩
  exact Module.comap_jacobson_of_ker_le (f := f.toSemilinearMap) hf
    (squareZero_le_jacobson (RingHom.ker f) hsq)

end LittleFinitistic.PDSquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBaseBarConsumer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [FiniteDimensional k A] [FiniteDimensional k N]

/-- Restriction of scalars preserves the actual homology of a D-complex. -/
def restrictHomologyIso (C : ChainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj C).homology n ≅
      (ModuleCat.restrictScalars (algebraMap k D)).obj (C.homology n) :=
  by
    let F : ModuleCat.{u} D ⥤ ModuleCat.{u} k := ModuleCat.restrictScalars (algebraMap k D)
    letI : F.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels F
    exact (C.sc n).mapHomologyIso F

end LittleFinitistic.PDBarQuotient

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDSquareZeroResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDSquareZero
universe u
variable {A D : Type u} [Ring A] [Ring D]

/-- The radical quotient is unchanged by a square-zero kernel. -/
def residueQuotientEquiv (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) :
    A ⧸ Ring.jacobson A ≃+* D ⧸ Ring.jacobson D := by
  let g := (Ideal.Quotient.mk (Ring.jacobson D)).comp f
  have hk : RingHom.ker g = Ring.jacobson A := by
    ext a
    change Ideal.Quotient.mk (Ring.jacobson D) (f a) = 0 ↔ a ∈ Ring.jacobson A
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change a ∈ Ideal.comap f (Ring.jacobson D) ↔ _
    rw [comap_jacobson f hf hsq]
  exact (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := g) (Ideal.Quotient.mk_surjective.comp hf))

@[simp] theorem residueQuotientEquiv_mk (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) (a : A) :
    residueQuotientEquiv f hf hsq (Ideal.Quotient.mk (Ring.jacobson A) a) =
      Ideal.Quotient.mk (Ring.jacobson D) (f a) := by
  simp [residueQuotientEquiv]

end LittleFinitistic.PDSquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_FunctorObjectIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u v
variable {C : Type u} [Category.{v} C] {F G : C ⥤ C}

/-- An actual natural isomorphism identifies every objectwise iterate. -/
def functorObjectIteration (e : F ≅ G) (r : ℕ) (Y : C) :
    (F.obj^[r]) Y ≅ (G.obj^[r]) Y := by
  induction r with
  | zero => exact Iso.refl _
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact F.mapIso ih ≪≫ e.app _

/-- Transport an object isomorphism through an actual repeated functor. -/
def mapObjectIteration (F : C ⥤ C) {X Y : C} (e : X ≅ Y) (r : ℕ) :
    (F.obj^[r]) X ≅ (F.obj^[r]) Y := by
  induction r with
  | zero => exact e
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact F.mapIso ih
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k : Type u} [Field k]

/-- The genuine cochain differential on the selected finite interval. -/
abbrev intervalTerms (P : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ) (l : ℕ)
    (i : Fin (l+1)) : Type u := P.X (a + (i.val : ℤ))

def intervalDifferential (P : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ) (l : ℕ)
    (i j : Fin (l+1)) : intervalTerms P a l i →ₗ[k] intervalTerms P a l j :=
  (P.d (a + (i.val : ℤ)) (a + (j.val : ℤ))).hom

theorem intervalDifferential_square (P : CochainComplex (ModuleCat.{u} k) ℤ)
    (a : ℤ) (l : ℕ) (i j h : Fin (l+1)) :
    (intervalDifferential P a l j h).comp (intervalDifferential P a l i j) = 0 := by
  have h := P.d_comp_d (a + (i.val : ℤ)) (a + (j.val : ℤ)) (a + (h.val : ℤ))
  exact congrArg (fun f => f.hom) h

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Forgetting to k uses the actual restriction-of-scalars functor on complexes. -/
abbrev underlyingComplex (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (.up ℤ)).obj P

/-- Ordinary finite compression of the actual dg A-module P on [a,a+l].
Take A=B tensor Bᵐᵒᵖ for a genuine dg B-bimodule. -/
def Compression (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ) :=
  ∀ i : Fin (l+1), P.X (a + (i.val : ℤ))

namespace Compression
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)
instance instAddCommGroup : AddCommGroup (Compression P a l) :=
  inferInstanceAs (AddCommGroup (∀ i : Fin (l+1), P.X (a + (i.val : ℤ))))
instance instModule_1 : Module A (Compression P a l) :=
  inferInstanceAs (Module A (∀ i : Fin (l+1), P.X (a + (i.val : ℤ))))
end Compression
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- Coordinate model for B tensor_k W, with its specified terminal right action. -/
def TerminalTensor := B
namespace TerminalTensor
instance instAddCommGroup : AddCommGroup (TerminalTensor B) := inferInstanceAs (AddCommGroup B)
instance instModule : Module k (TerminalTensor B) := inferInstanceAs (Module k B)
instance instModule_1 : Module B (TerminalTensor B) := inferInstanceAs (Module B B)

def value (t : TerminalTensor B) : B := t

end TerminalTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockBimodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k L R O T : Type u} [Field k] [Ring L] [Ring R]
  [AddCommGroup O] [AddCommGroup T]

/-- The off-diagonal ordinary bimodule O ⊕ T over L × R. -/
def OffDiagonal (O T : Type u) := O × T
namespace OffDiagonal
instance instAddCommGroup : AddCommGroup (OffDiagonal O T) := inferInstanceAs (AddCommGroup (O × T))
instance instModule [Module k O] [Module k T] : Module k (OffDiagonal O T) :=
  inferInstanceAs (Module k (O × T))

instance leftModule [Module R O] [Module L T] : Module (L × R) (OffDiagonal O T) := by
  let : Module (L × R) O := Module.compHom O (RingHom.snd L R)
  let : Module (L × R) T := Module.compHom T (RingHom.fst L R)
  exact inferInstanceAs (Module (L × R) (O × T))

instance rightModule [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T] :
    Module (L × R)ᵐᵒᵖ (OffDiagonal O T) := by
  let : Module (L × R)ᵐᵒᵖ O := Module.compHom O (RingHom.fst L R).op
  let : Module (L × R)ᵐᵒᵖ T := Module.compHom T (RingHom.snd L R).op
  exact inferInstanceAs (Module (L × R)ᵐᵒᵖ (O × T))

instance commuteActions [Module R O] [Module L T] [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T]
    [SMulCommClass R Lᵐᵒᵖ O] [SMulCommClass L Rᵐᵒᵖ T] :
    SMulCommClass (L × R) (L × R)ᵐᵒᵖ (OffDiagonal O T) where
  smul_comm x y z := by
    apply Prod.ext
    · change x.2 • (MulOpposite.op y.unop.1 • z.1) = MulOpposite.op y.unop.1 • (x.2 • z.1)
      exact smul_comm _ _ _
    · change x.1 • (MulOpposite.op y.unop.2 • z.2) = MulOpposite.op y.unop.2 • (x.1 • z.2)
      exact smul_comm _ _ _

instance towerLeft [Algebra k L] [Algebra k R] [Module k O] [Module k T]
    [Module R O] [Module L T] [IsScalarTower k R O] [IsScalarTower k L T] :
    IsScalarTower k (L × R) (OffDiagonal O T) where
  smul_assoc c x z := Prod.ext (smul_assoc c x.2 z.1) (smul_assoc c x.1 z.2)

instance towerRight [Algebra k L] [Algebra k R] [Module k O] [Module k T]
    [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T] [IsScalarTower k Lᵐᵒᵖ O] [IsScalarTower k Rᵐᵒᵖ T] :
    IsScalarTower k (L × R)ᵐᵒᵖ (OffDiagonal O T) where
  smul_assoc c x z := Prod.ext (smul_assoc c (MulOpposite.op x.unop.1) z.1)
    (smul_assoc c (MulOpposite.op x.unop.2) z.2)

instance finiteDimensional [Module k O] [Module k T]
    [FiniteDimensional k O] [FiniteDimensional k T] : FiniteDimensional k (OffDiagonal O T) :=
  inferInstanceAs (FiniteDimensional k (O × T))

end OffDiagonal

open CategoryTheory
open scoped TensorProduct
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTerminalResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- W is the genuine terminal right simple, via the terminal character. -/
def TerminalSimple := k
namespace TerminalSimple
instance instAddCommGroup : AddCommGroup (TerminalSimple k) := inferInstanceAs (AddCommGroup k)
instance instModule : Module k (TerminalSimple k) := inferInstanceAs (Module k k)
end TerminalSimple

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryResolutionQuasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- Postcomposing a short complex's second map by an isomorphism preserves exactness. -/
theorem exact_post_iso {R : Type u} [Ring R] {X Y Z Z' : ModuleCat.{u} R}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) (e : Z ≅ Z')
    (h : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk f (g ≫ e.hom) (by rw [← Category.assoc, hfg, zero_comp])).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at h ⊢
  intro x hx
  apply h x
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  exact hx.trans (map_zero _).symm

end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorIdeal
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable (e : C) (he : e*e=e)

def vertex : B ⊗[k] C := (1:B) ⊗ₜ[k] e

include he in
theorem vertex_idempotent : vertex (k := k) (B := B) e * vertex e = vertex e := by
  simp only [vertex, Algebra.TensorProduct.tmul_mul_tmul, one_mul, he]

end LittleFinitistic.OrdinarySimulation.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorIdealActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorIdeal
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable (e : C)

abbrev coefficient : B →ₐ[k] B ⊗[k] C := Algebra.TensorProduct.includeLeft

end LittleFinitistic.OrdinarySimulation.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryIntegerResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

def degreeEmbedding : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntGE (-(l:ℤ))

instance degreeEmbedding_rel : (degreeEmbedding l).IsRelIff :=
  inferInstanceAs ((ComplexShape.embeddingUpIntGE (-(l:ℤ))).IsRelIff)

@[simp] theorem degreeEmbedding_apply (n : ℕ) : (degreeEmbedding l).f n = -(l:ℤ)+n := rfl

end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRetainedBimodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic
universe u
/-- An ordinary bimodule packaged as a module over its actual tensor algebra. -/
def RetainedBimodule (_k _S _A M : Type u) := M
namespace RetainedBimodule
variable (k S A M : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]
instance instAddCommGroup : AddCommGroup (RetainedBimodule k S A M) := inferInstanceAs (AddCommGroup M)
instance instModule : Module k (RetainedBimodule k S A M) := inferInstanceAs (Module k M)
instance instModule_1 : Module S (RetainedBimodule k S A M) := inferInstanceAs (Module S M)
instance instModuleMulOpposite : Module Aᵐᵒᵖ (RetainedBimodule k S A M) := inferInstanceAs (Module Aᵐᵒᵖ M)
instance instIsScalarTower : IsScalarTower k S (RetainedBimodule k S A M) := inferInstanceAs (IsScalarTower k S M)
instance instIsScalarTowerMulOpposite : IsScalarTower k Aᵐᵒᵖ (RetainedBimodule k S A M) := inferInstanceAs (IsScalarTower k Aᵐᵒᵖ M)
instance instSMulCommClassMulOpposite : SMulCommClass S Aᵐᵒᵖ (RetainedBimodule k S A M) := inferInstanceAs (SMulCommClass S Aᵐᵒᵖ M)


def action : (S ⊗[k] Aᵐᵒᵖ) →ₐ[k] Module.End k (RetainedBimodule k S A M) :=
  show (S ⊗[k] Aᵐᵒᵖ) →ₐ[k] Module.End k M from
  Algebra.TensorProduct.lift (Algebra.lsmul k k M) (Algebra.lsmul k k M) (by
    intro s a
    ext m
    exact smul_comm s a (m : M))
instance instModuleTensorProductMulOpposite : Module (S ⊗[k] Aᵐᵒᵖ) (RetainedBimodule k S A M) := Module.compHom _ (action k S A M).toRingHom
instance tower : IsScalarTower k (S ⊗[k] Aᵐᵒᵖ) (RetainedBimodule k S A M) where
  smul_assoc r x m := by
    change action k S A M (r • x) m = r • action k S A M x m
    rw [map_smul]
    rfl

end RetainedBimodule
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable {L R O O' T T' : Type u} [Ring L] [Ring R]
variable [AddCommGroup O] [AddCommGroup O'] [AddCommGroup T] [AddCommGroup T']
variable [Module R O] [Module R O'] [Module L T] [Module L T']
variable [Module Lᵐᵒᵖ O] [Module Lᵐᵒᵖ O'] [Module Rᵐᵒᵖ T] [Module Rᵐᵒᵖ T']

/-- Actual component maps of the off-diagonal right product-ring module. -/
def map (f : O →ₗ[Lᵐᵒᵖ] O') (g : T →ₗ[Rᵐᵒᵖ] T') :
    OffDiagonal O T →ₗ[(L × R)ᵐᵒᵖ] OffDiagonal O' T' where
  toFun x := (f x.1,g x.2)
  map_add' left right := Prod.ext (f.map_add left.1 right.1) (g.map_add left.2 right.2)
  map_smul' d x := Prod.ext (f.map_smul (MulOpposite.op d.unop.1) x.1)
    (g.map_smul (MulOpposite.op d.unop.2) x.2)

/-- The same map retains the two prescribed left product-ring actions. -/
theorem map_left (f : O →ₗ[Lᵐᵒᵖ] O') (hf : ∀ (r : R) x, f (r • x) = r • f x)
    (g : T →ₗ[Rᵐᵒᵖ] T') (hg : ∀ (s : L) x, g (s • x) = s • g x)
    (d : L × R) (x : OffDiagonal O T) :
    map f g (d • x) = d • map f g x :=
  Prod.ext (hf d.2 x.1) (hg d.1 x.2)
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryPairComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.PairComplex
universe u
variable {k : Type u} [Ring k]
variable (O T : CochainComplex (ModuleCat.{u} k) ℤ)

def complex : CochainComplex (ModuleCat.{u} k) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of k (O.X n × T.X n))
    (fun n => ModuleCat.ofHom ((O.d n (n+1)).hom.prodMap (T.d n (n+1)).hom)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Prod.ext (congrArg (fun h => h.hom x.1) (O.d_comp_d n (n+1) ((n+1)+1)))
        (congrArg (fun h => h.hom x.2) (T.d_comp_d n (n+1) ((n+1)+1))))

theorem complex_d (n : ℤ) : (complex O T).d n (n+1) =
    ModuleCat.ofHom ((O.d n (n+1)).hom.prodMap (T.d n (n+1)).hom) :=
  CochainComplex.of_d (fun n => ModuleCat.of k (O.X n × T.X n))
    (fun n => ModuleCat.ofHom ((O.d n (n+1)).hom.prodMap (T.d n (n+1)).hom)) n

def fst : complex O T ⟶ O where
  f n := ModuleCat.ofHom (LinearMap.fst k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    rfl

def snd : complex O T ⟶ T where
  f n := ModuleCat.ofHom (LinearMap.snd k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    rfl

def inl : O ⟶ complex O T where
  f n := ModuleCat.ofHom (LinearMap.inl k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext rfl ((T.d n (n+1)).hom.map_zero)

def inr : T ⟶ complex O T where
  f n := ModuleCat.ofHom (LinearMap.inr k (O.X n) (T.X n))
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext ((O.d n (n+1)).hom.map_zero) rfl

@[simp] theorem inl_fst : inl O T ≫ fst O T = 𝟙 O := by ext degree element; rfl
@[simp] theorem inl_snd : inl O T ≫ snd O T = 0 := by ext degree element; rfl
@[simp] theorem inr_fst : inr O T ≫ fst O T = 0 := by ext degree element; rfl
@[simp] theorem inr_snd : inr O T ≫ snd O T = 𝟙 T := by ext degree element; rfl

/-- The actual coordinate complex is the native binary biproduct. -/
def biprodIso : complex O T ≅ O ⊞ T where
  hom := biprod.lift (fst O T) (snd O T)
  inv := biprod.desc (inl O T) (inr O T)
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext n x
    exact Prod.ext (add_zero _) (zero_add _)
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [Category.assoc]
end LittleFinitistic.PairComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryPairQuasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.PairComplex
universe u
variable {k : Type u} [Ring k]
variable {O O' T T' : CochainComplex (ModuleCat.{u} k) ℤ}

def map (f : O ⟶ O') (g : T ⟶ T') : complex O T ⟶ complex O' T' where
  f n := ModuleCat.ofHom ((f.f n).hom.prodMap (g.f n).hom)
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun h => h.hom x.1) (f.comm n (n+1)))
      (congrArg (fun h => h.hom x.2) (g.comm n (n+1)))

theorem biprodIso_natural (f : O ⟶ O') (g : T ⟶ T') :
    map f g ≫ (biprodIso O' T').hom = (biprodIso O T).hom ≫ biprod.map f g := by
  apply biprod.hom_ext
  · simp only [biprodIso,Category.assoc,biprod.lift_fst,biprod.map_fst,biprod.lift_fst_assoc]
    ext n x
    rfl
  · simp only [biprodIso,Category.assoc,biprod.lift_snd,biprod.map_snd,biprod.lift_snd_assoc]
    ext n x
    rfl

/-- Native binary biproducts preserve actual quasi-isomorphisms. -/
theorem biprodMap_quasiIso (f : O ⟶ O') (g : T ⟶ T') [QuasiIso f] [QuasiIso g] :
    QuasiIso (biprod.map f g) := by
  constructor
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap _ i).mpr
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) i
  let : H.Additive := inferInstanceAs ((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) i).Additive)
  let : PreservesFiniteBiproducts H := Functor.preservesFiniteBiproductsOfAdditive H
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have : IsIso (H.map f) := (quasiIsoAt_iff_isIso_homologyMap f i).mp inferInstance
  have : IsIso (H.map g) := (quasiIsoAt_iff_isIso_homologyMap g i).mp inferInstance
  change IsIso (H.map (biprod.map f g))
  have he : H.map (biprod.map f g) ≫ (H.mapBiprod O' T').hom =
      (H.mapBiprod O T).hom ≫ biprod.map (H.map f) (H.map g) := by
    apply biprod.hom_ext
    · simp only [Functor.mapBiprod_hom,Category.assoc,biprod.lift_fst,biprod.map_fst,biprod.lift_fst_assoc,← H.map_comp]
    · simp only [Functor.mapBiprod_hom,Category.assoc,biprod.lift_snd,biprod.map_snd,biprod.lift_snd_assoc,← H.map_comp]
  have : IsIso (biprod.map (H.map f) (H.map g)) := by
    refine ⟨⟨biprod.map (inv (H.map f)) (inv (H.map g)), ?_, ?_⟩⟩
    · apply biprod.hom_ext <;> simp [Category.assoc]
    · apply biprod.hom_ext <;> simp [Category.assoc]
  have h : IsIso (H.map (biprod.map f g) ≫ (H.mapBiprod O' T').hom) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ (H.mapBiprod O' T').hom).mp h

/-- Coordinatewise quasi-isomorphisms give a quasi-isomorphism of the actual direct sum. -/
theorem map_quasiIso (f : O ⟶ O') (g : T ⟶ T') [QuasiIso f] [QuasiIso g] :
    QuasiIso (map f g) := by
  have := biprodMap_quasiIso f g
  have h : QuasiIso (map f g ≫ (biprodIso O' T').hom) := by
    rw [biprodIso_natural]
    infer_instance
  exact (quasiIso_iff_comp_right (map f g) (biprodIso O' T').hom).mp h
end LittleFinitistic.PairComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

abbrev swapModule (M : ModuleCat.{v} (L × R)) : ModuleCat.{v} (R × L) :=
  (ModuleCat.restrictScalars (RingEquiv.prodComm : R × L ≃+* L × R).toRingHom).obj M

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductOpposite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

/-- The opposite of the actual product ring is the product of the two opposite rings. -/
def oppositeEquiv : (L × R)ᵐᵒᵖ ≃+* Lᵐᵒᵖ × Rᵐᵒᵖ where
  toFun x := (MulOpposite.op x.unop.1,MulOpposite.op x.unop.2)
  invFun x := MulOpposite.op (x.1.unop,x.2.unop)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

abbrev oppositeModule (M : ModuleCat.{v} (L × R)ᵐᵒᵖ) : ModuleCat.{v} (Lᵐᵒᵖ × Rᵐᵒᵖ) :=
  (ModuleCat.restrictScalars (oppositeEquiv L R).symm.toRingHom).obj M

attribute [local instance] RingHomInvPair.of_ringEquiv

def oppositeModuleEquiv (M : ModuleCat.{v} (L × R)ᵐᵒᵖ) :
    M ≃ₛₗ[RingHomClass.toRingHom (oppositeEquiv L R)] oppositeModule L R M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRetainedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.RetainedBimodule
universe u
variable (k S A M : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]

abbrev object : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ) := ModuleCat.of _ (RetainedBimodule k S A M)

end LittleFinitistic.RetainedBimodule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRetainedCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable {L R O O' T T' : Type u} [Ring L] [Ring R]
variable [AddCommGroup O] [AddCommGroup O'] [AddCommGroup T] [AddCommGroup T']
variable [Module Lᵐᵒᵖ O] [Module Lᵐᵒᵖ O'] [Module Rᵐᵒᵖ T] [Module Rᵐᵒᵖ T']

def congr (f : O ≃ₗ[Lᵐᵒᵖ] O') (g : T ≃ₗ[Rᵐᵒᵖ] T') :
    OffDiagonal O T ≃ₗ[(L × R)ᵐᵒᵖ] OffDiagonal O' T' where
  toFun x := (f x.1,g x.2)
  invFun x := (f.symm x.1,g.symm x.2)
  left_inv x := Prod.ext (f.left_inv x.1) (g.left_inv x.2)
  right_inv x := Prod.ext (f.right_inv x.1) (g.right_inv x.2)
  map_add' left right := Prod.ext (f.map_add left.1 right.1) (g.map_add left.2 right.2)
  map_smul' d x := Prod.ext (f.map_smul (MulOpposite.op d.unop.1) x.1)
    (g.map_smul (MulOpposite.op d.unop.2) x.2)
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRightProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u v w

/-- The finite direct sum of actual projective terms is projective. -/
theorem finitePi_projective {R : Type u} [Ring R] {ι : Type v} [Fintype ι]
    (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, Module.Projective R (V i)] : Module.Projective R (∀ i, V i) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := V))

open CategoryTheory
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryShiftSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Reindex P by b, retaining the original differential. This is what the resolution computes. -/
def unsignedShift (P : CochainComplex C ℤ) (b : ℤ) : CochainComplex C ℤ where
  X n := P.X (n+b)
  d n m := P.d (n+b) (m+b)
  shape n m h := P.shape _ _ (by
    change ¬ (n+b)+1 = m+b
    change ¬ n+1=m at h
    omega)
  d_comp_d' n m q _ _ := P.d_comp_d _ _ _

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySingleTensorTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.SingleBimoduleTensor
universe u
variable (k S A N : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable [AddCommGroup N] [Module k N] [Module S N] [Module Aᵐᵒᵖ N]
  [IsScalarTower k S N] [IsScalarTower k Aᵐᵒᵖ N] [SMulCommClass S Aᵐᵒᵖ N]

abbrev complex : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (RetainedBimodule.object k S A N)

end LittleFinitistic.SingleBimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorDirected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorDirected
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable {n : ℕ}

def bIndex (i : Fin (n*3)) : Fin 3 := (finProdFinEquiv.symm i).2
def cIndex (i : Fin (n*3)) : Fin n := (finProdFinEquiv.symm i).1

theorem index_value (i : Fin (n*3)) : (bIndex i).val + 3 * (cIndex i).val = i.val :=
  congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)

end LittleFinitistic.OrdinarySimulation.TensorDirected

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryVertexCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.Compression
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)

/-- Coordinate insertion is linear over the full coefficient algebra A. -/
def insert (i : Fin (l+1)) : P.X (a+(i.val:ℤ)) →ₗ[A] Compression P a l :=
  LinearMap.single A (fun i : Fin (l+1) => P.X (a+(i.val:ℤ))) i

def project (i : Fin (l+1)) : Compression P a l →ₗ[A] P.X (a+(i.val:ℤ)) := LinearMap.proj i

end LittleFinitistic.OrdinarySimulation.Compression

end

end OAI
end



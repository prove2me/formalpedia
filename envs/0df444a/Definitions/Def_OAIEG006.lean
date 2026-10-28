-- Prove2me | Definitions.Def_OAIEG006
-- name    : OAIEG006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T23:49:51.104004+00:00
-- url     : https://prove2.me/theorems/bfc99ae2-63a3-4a70-b1a0-fcd6ba8fbce4
-- title:
--   Definitions bundle OAIEG006 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 49 definitions and 27 theorems. The definitions and types are `OAI.EilenbergGanea.SeedChainCertificate.h1CodeData_17`, `OAI.EilenbergGanea.SeedChainCertificate.h1CodeData_18`, `OAI.EilenbergGanea.SeedChainCertificate.h1CodeData_19`, `OAI.EilenbergGanea.alignmentIndexEquiv`, `OAI.EilenbergGanea.complexRadialTorus`, `OAI.EilenbergGanea.coordinateBasis`, `OAI.EilenbergGanea.coordinateVolumeForm`, `OAI.EilenbergGanea.cosetConjugate`, `OAI.EilenbergGanea.cosetMap`, `OAI.EilenbergGanea.cosetSemidirectLift`, `OAI.EilenbergGanea.equivariantBumpOperator`, `OAI.EilenbergGanea.eraseCoefficients`, `OAI.EilenbergGanea.eraseExtra`, `OAI.EilenbergGanea.exponentCup`, `OAI.EilenbergGanea.exponentMatrix`, `OAI.EilenbergGanea.familySize`, `OAI.EilenbergGanea.finiteTranslation`, `OAI.EilenbergGanea.finiteWordAction`, `OAI.EilenbergGanea.fixedRestriction`, `OAI.EilenbergGanea.formFlux`, `OAI.EilenbergGanea.freeAction`, `OAI.EilenbergGanea.freeGroupCongr`, `OAI.EilenbergGanea.invariantSubtypeAction`, `OAI.EilenbergGanea.jacobianIntegral`, `OAI.EilenbergGanea.linearPerturbation`, `OAI.EilenbergGanea.linearPerturbationDerivative`, `OAI.EilenbergGanea.linearSolvedParameter`, `OAI.EilenbergGanea.mergeLabels`, `OAI.EilenbergGanea.nielsenEquiv`, `OAI.EilenbergGanea.nielsenHom`, `OAI.EilenbergGanea.normalProjection`, `OAI.EilenbergGanea.normalShift`, `OAI.EilenbergGanea.normalizeCircle`, `OAI.EilenbergGanea.orbitObservation`, `OAI.EilenbergGanea.quaternionCoordinates`, `OAI.EilenbergGanea.quaternionTupleCoordinates`, `OAI.EilenbergGanea.radialAngularLinear`, `OAI.EilenbergGanea.radialCutoff`, `OAI.EilenbergGanea.scalarRotation`, `OAI.EilenbergGanea.scalarRotationRepresentation` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: [`CliqueCohomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/CliqueCohomology.lean), [`IntegralDegree`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/IntegralDegree.lean), [`PresentationAlignment`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/PresentationAlignment.lean), [`Regularization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/Regularization.lean), [`RightAngledArtin_ResidualFiniteness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/RightAngledArtin/ResidualFiniteness.lean), [`Seed`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/Seed.lean), [`SeedContraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean), [`SmallHolonomy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SmallHolonomy.lean), [`UnitaryWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/UnitaryWords.lean), [`WordEquations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/WordEquations.lean).
--
--   **Imports.** It imports the published bundle `Def_EilenbergGanea`.
--
--   **Imported by** (directly, in this split): the bundles `OAIEG018` and `OAIEG035`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_EilenbergGanea

section
-- module Solutions.OAIEG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
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
-- module Solutions.OAIEG.RightAngledArtin_ResidualFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u
/-! Finite permutation separation for free groups. -/
section FreeGroupResidualFiniteness

variable {A : Type*} [Group A]

/-- Left translation, restricted wherever both endpoints lie in a finite set,
extends to a permutation of that finite set. -/
theorem finite_translation_extension (s : Finset A) (a : A) :
    ∃ σ : Equiv.Perm s, ∀ (x : s), a * x.val ∈ s → (σ x).val = a * x.val := by
  classical
  let D := {x : s // a * x.val ∈ s}
  let f : D → s := fun x => x.val
  let g : D → s := fun x => ⟨a * x.val.val, x.property⟩
  have hf : Function.Injective f := fun _ _ h => Subtype.ext h
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨σ, fun x hx => congrArg Subtype.val (hσ ⟨x, hx⟩)⟩

noncomputable def finiteTranslation (s : Finset A) (a : A) : Equiv.Perm s :=
  (finite_translation_extension s a).choose

variable {X : Type*}

/-- The finite set of suffix vertices of a free word, including both endpoints. -/
def wordVertices (w : List (X × Bool)) : Finset (FreeGroup X) := by
  classical
  exact (w.tails.map FreeGroup.mk).toFinset

noncomputable def finiteWordAction (s : Finset (FreeGroup X)) :
    FreeGroup X →* Equiv.Perm s :=
  FreeGroup.lift (fun a => finiteTranslation s (FreeGroup.of a))

end FreeGroupResidualFiniteness


section FiniteSemidirectSeparation

variable {N D K : Type*} [Group N] [Group D] [Group K]

/-- All translates of a finite observation of the normal factor, simultaneously. -/
def orbitObservation (φ : D →* MulAut N) (f : N →* K) : N →* (D → K) where
  toFun n d := f (φ d n)
  map_one' := by ext d; simp
  map_mul' n m := by ext d; simp

end FiniteSemidirectSeparation


section FreeAction

variable (A X : Type*) [Group A] [MulAction A X]

def freeAction : A →* MulAut (FreeGroup X) where
  toFun a := FreeGroup.freeGroupCongr (MulAction.toPermHom A X a)
  map_one' := by
    apply MulEquiv.ext
    intro w
    change FreeGroup.map (fun x : X => (1 : A) • x) w = w
    simpa only [one_smul] using FreeGroup.map.id' w
  map_mul' a b := by
    apply MulEquiv.ext
    intro w
    change FreeGroup.map (fun x : X => (a * b) • x) w =
      FreeGroup.map (fun x => a • x) (FreeGroup.map (fun x => b • x) w)
    rw [FreeGroup.map.comp]
    simp only [Function.comp_def, mul_smul]

@[simp] theorem freeAction_of (a : A) (x : X) :
    freeAction A X a (FreeGroup.of x) = FreeGroup.of (a • x) := rfl

end FreeAction


section RetractCosetSeparation

variable {A : Type u} {D : Type*} [Group A] [Group D]

/-- A homomorphism induces a map on left cosets of a subgroup, without a
normality hypothesis on that subgroup. -/
def cosetMap (q : A →* D) (C : Subgroup A) : A ⧸ C → D ⧸ C.map q :=
  Quotient.map' q (by
    intro a b h
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map.mpr ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp h, rfl⟩)

@[simp] theorem cosetMap_mk (q : A →* D) (C : Subgroup A) (a : A) :
    cosetMap q C (QuotientGroup.mk a) = QuotientGroup.mk (q a) := rfl

end RetractCosetSeparation

section CosetConjugation

variable {A P : Type*} [Group A] [Group P]

/-- The formal inverse to the graph-group splitting, on its free generators. -/
def cosetConjugate (C : Subgroup A) (i : A →* P) (t : P)
    (ht : ∀ c ∈ C, Commute (i c) t) : A ⧸ C → P :=
  Quotient.lift (fun a => i a * t * (i a)⁻¹) (by
    intro a b hab
    have hd := QuotientGroup.leftRel_apply.mp hab
    have hc : i (a⁻¹ * b) * t * (i (a⁻¹ * b))⁻¹ = t := by
      rw [(ht _ hd).eq]
      group
    calc
      i a * t * (i a)⁻¹ = i a * (i (a⁻¹ * b) * t * (i (a⁻¹ * b))⁻¹) * (i a)⁻¹ := by rw [hc]
      _ = i b * t * (i b)⁻¹ := by simp only [map_mul, map_inv]; group)

@[simp] theorem cosetConjugate_mk (C : Subgroup A) (i : A →* P) (t : P)
    (ht : ∀ c ∈ C, Commute (i c) t) (a : A) :
    cosetConjugate C i t ht (QuotientGroup.mk a) = i a * t * (i a)⁻¹ := rfl

theorem cosetConjugate_equivariant (C : Subgroup A) (i : A →* P) (t : P)
    (ht : ∀ c ∈ C, Commute (i c) t) (a : A) (x : A ⧸ C) :
    cosetConjugate C i t ht (a • x) = i a * cosetConjugate C i t ht x * (i a)⁻¹ := by
  induction x using QuotientGroup.induction_on with
  | H b =>
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, cosetConjugate_mk, map_mul]
    group

def cosetSemidirectLift (C : Subgroup A) (i : A →* P) (t : P)
    (ht : ∀ c ∈ C, Commute (i c) t) :
    (FreeGroup (A ⧸ C) ⋊[freeAction A (A ⧸ C)] A) →* P :=
  SemidirectProduct.lift (FreeGroup.lift (cosetConjugate C i t ht)) i (by
    intro a
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, freeAction_of,
      FreeGroup.lift_apply_of, MulAut.conj_apply, cosetConjugate_equivariant])

@[simp] theorem cosetSemidirectLift_inr (C : Subgroup A) (i : A →* P) (t : P)
    (ht : ∀ c ∈ C, Commute (i c) t) (a : A) :
    cosetSemidirectLift C i t ht (SemidirectProduct.inr a) = i a := by
  simp [cosetSemidirectLift]

@[simp] theorem cosetSemidirectLift_base (C : Subgroup A) (i : A →* P) (t : P)
    (ht : ∀ c ∈ C, Commute (i c) t) :
    cosetSemidirectLift C i t ht
      (SemidirectProduct.inl (FreeGroup.of (QuotientGroup.mk (1 : A)))) = t := by
  simp [cosetSemidirectLift]

end CosetConjugation


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Seed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea

/-- The vertex of the rose common to its two circles. -/
def seedBase : SeedCell := .inl (.inl none)


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.CliqueCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea

 def seedCliqueVertex : SeedCell := .inl (.inl none)
 def seedCliqueEdge : SeedCell := .inr (.inl (.inl (false, 0)))
 def seedCliqueFace : SeedCell := .inr (.inr ⟨false, ⟨0, by decide⟩⟩)

section CupCocycle
open groupCohomology
variable {G : Type} [Group G]

/-- The cup product of two integral exponent homomorphisms. -/
def exponentCup (a b : G →* Multiplicative ℤ) : cocycles₂ (Rep.trivial ℤ G ℤ) :=
  ⟨fun p => (a p.1).toAdd * (b p.2).toAdd, by
    rw [mem_cocycles₂_iff]
    intro g h j
    simp only [map_mul, toAdd_mul]
    change ((a g).toAdd + (a h).toAdd) * (b j).toAdd + (a g).toAdd * (b h).toAdd =
      (a h).toAdd * (b j).toAdd + (a g).toAdd * ((b h).toAdd + (b j).toAdd)
    ring⟩

end CupCocycle


open CategoryTheory CategoryTheory.Limits

open CategoryTheory CategoryTheory.Limits

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.Regularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology

/-! Localized regularization for finite SU(2) systems. -/

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff

section FixedRegularization
variable {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The complement of the fixed subspace. -/
def normalProjection : (A × V) →L[ℝ] (A × V) :=
  (ContinuousLinearMap.inr ℝ A V).comp (ContinuousLinearMap.snd ℝ A V)

@[simp] theorem normalProjection_apply (x : A × V) : normalProjection x = (0, x.2) := rfl

def normalShift (f : A × V → A × V) (s : ℝ) (x : A × V) := f x + s • normalProjection x

@[simp] theorem normalShift_fixed (f : A × V → A × V) (s : ℝ) (a : A) :
    normalShift f s (a, 0) = f (a, 0) := by simp [normalShift]

variable [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

def scalarRotation (z : ℂˣ) : (A × V) ≃L[ℝ] (A × V) :=
  (ContinuousLinearEquiv.refl ℝ A).prodCongr
    ((ContinuousLinearEquiv.smulLeft z : V ≃L[ℂ] V).restrictScalars ℝ)

@[simp] theorem scalarRotation_apply (z : ℂˣ) (q : A × V) :
    scalarRotation z q = (q.1, (z : ℂ) • q.2) := rfl

variable [FiniteDimensional ℝ A] [FiniteDimensional ℂ V]


def fixedRestriction (f : A × V → A × V) (a : A) : A := (f (a, 0)).1

end FixedRegularization
end EilenbergGanea

open Set Filter Topology
namespace EilenbergGanea
section LinearParameters
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearPerturbation (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (x : E) (p : ι → E) : E := f x + ∑ j, T j x (p j)

def linearPerturbationDerivative (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (x : E) (p : ι → E) : E →L[ℝ] E :=
  fderiv ℝ f x + ∑ j, (fderiv ℝ (T j) x).flip (p j)

def linearSolvedParameter (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) : ι → E :=
  Function.update q i (-(Ring.inverse (T i (q i))
    (f (q i) + ∑ j ∈ Finset.univ.erase i, T j (q i) (q j))))

end LinearParameters
end EilenbergGanea
open scoped ContDiff
open Set Filter Topology
namespace EilenbergGanea
section EquivariantBumps
variable {G E : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def equivariantBumpOperator (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ) (x : E) : E →L[ℝ] E :=
  ∑ g, b (ρ g⁻¹ x) • (ρ g : E →L[ℝ] E)

end EquivariantBumps
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section MixedRegularization
variable {G A V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

def scalarRotationRepresentation (χ : G →* ℂˣ) : G →* (A × V) ≃L[ℝ] (A × V) where
  toFun g := scalarRotation (χ g)
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext q
    change scalarRotation (χ 1) q = q
    simp [scalarRotation_apply]
  map_mul' g h := by
    apply ContinuousLinearEquiv.ext
    funext q
    change scalarRotation (χ (g * h)) q = scalarRotation (χ g) (scalarRotation (χ h) q)
    simp [mul_smul]

omit [Fintype G] [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
@[simp] theorem scalarRotationRepresentation_apply (χ : G →* ℂˣ) (g : G) (q : A × V) :
    scalarRotationRepresentation χ g q = (q.1, (χ g : ℂ) • q.2) := rfl

end MixedRegularization
end EilenbergGanea


namespace EilenbergGanea
section SignedAction
variable {G X : Type*} [Group G] [MulAction G X]

@[instance_reducible] def invariantSubtypeAction (P : X → Prop) (hP : ∀ (g : G) x, P x → P (g • x)) :
    MulAction G {x // P x} where
  smul g x := ⟨g • x.1, hP g x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

end SignedAction
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.UnitaryWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology
open scoped Quaternion ContDiff

open scoped Quaternion
namespace EilenbergGanea

def exponentMatrix {m : ℕ} (w : Fin m → FreeGroup (Fin m)) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => Multiplicative.toAdd
    (FreeGroup.lift (fun k => Multiplicative.ofAdd (if j = k then (1 : ℤ) else 0)) (w i))

open Set Filter Topology
open scoped ContDiff


/-- A conjugation-invariant smooth cutoff, zero near coordinate hyperplanes
and one near the unit quaternion locus. -/
def radialCutoff {m : ℕ} (x : Fin m → ℍ) : ℝ :=
  ∏ i, Real.smoothTransition (4 * ‖x i‖ ^ 2 - 1)

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {n : Type*} [Fintype n] [DecidableEq n]

def splitComplex : (n → ℂ) ≃ₗ[ℝ] ((n → ℝ) × (n → ℝ)) where
  toFun z := (fun i => (z i).re, fun i => (z i).im)
  invFun p i := (p.1 i : ℂ) + (p.2 i : ℂ) * Complex.I
  left_inv z := by funext i; exact Complex.re_add_im (z i)
  right_inv p := by ext i <;> simp
  map_add' a b := by ext i <;> simp
  map_smul' a b := by ext i <;> simp

def radialAngularLinear (B : Matrix n n ℝ) : (n → ℂ) →L[ℝ] (n → ℂ) :=
  ((splitComplex (n := n)).symm.toLinearMap.comp
    (((LinearMap.id : (n → ℝ) →ₗ[ℝ] (n → ℝ)).prodMap B.toLin').comp
      (splitComplex (n := n)).toLinearMap)).toContinuousLinearMap

@[simp] theorem radialAngularLinear_apply (B : Matrix n n ℝ) (z : n → ℂ) (i : n) :
    radialAngularLinear B z i = ((z i).re : ℂ) + (∑ j, B i j * (z j).im : ℝ) * Complex.I := rfl

def complexRadialTorus (B : Matrix n n ℤ) (z : n → ℂ) : n → ℂ :=
  fun i => ‖z i‖ • ∏ j, (‖z j‖⁻¹ • z j) ^ B i j

end EilenbergGanea
namespace EilenbergGanea
section CommutativeWords
variable {n A : Type*} [Fintype n] [DecidableEq n] [CommGroup A]
def wordExponents {ι : Type*} [DecidableEq ι] (w : FreeGroup ι) (j : ι) : ℤ :=
  Multiplicative.toAdd
    (FreeGroup.lift (fun k => Multiplicative.ofAdd (if j = k then (1 : ℤ) else 0)) w)

@[simp] theorem wordExponents_one {ι : Type*} [DecidableEq ι] (j : ι) : wordExponents (1 : FreeGroup ι) j = 0 := by
  simp [wordExponents]

@[simp] theorem wordExponents_of {ι : Type*} [DecidableEq ι] (j k : ι) :
    wordExponents (FreeGroup.of k) j = if j = k then 1 else 0 := by
  simp [wordExponents]

@[simp] theorem wordExponents_inv {ι : Type*} [DecidableEq ι] (w : FreeGroup ι) (j : ι) :
    wordExponents w⁻¹ j = -wordExponents w j := by
  simp [wordExponents]

@[simp] theorem wordExponents_mul {ι : Type*} [DecidableEq ι] (w v : FreeGroup ι) (j : ι) :
    wordExponents (w * v) j = wordExponents w j + wordExponents v j := by
  simp [wordExponents]

end CommutativeWords
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def quaternionCoordinates : ℍ ≃ₗ[ℝ] ℂ × ℂ where
  toFun q := (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩)
  invFun z := ⟨z.1.re, z.1.im, z.2.re, z.2.im⟩
  left_inv q := by cases q; rfl
  right_inv z := by rcases z with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
  map_add' q r := by ext <;> rfl
  map_smul' r q := by apply Prod.ext <;> apply Complex.ext <;> simp

@[simp] theorem quaternionCoordinates_apply (q : ℍ) :
    quaternionCoordinates q = (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩) := rfl

@[simp] theorem quaternionCoordinates_ofComplex (z : ℂ) :
    quaternionCoordinates (Quaternion.ofComplex z) = (z, 0) := by
  ext <;> rfl

@[simp] theorem norm_quaternion_ofComplex (z : ℂ) : ‖Quaternion.ofComplex z‖ = ‖z‖ := by
  have h : ‖Quaternion.ofComplex z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, ← Complex.normSq_eq_norm_sq]
    simp [Quaternion.normSq_def', Complex.normSq_apply, sq]
  nlinarith [norm_nonneg (Quaternion.ofComplex z), norm_nonneg z]

def quaternionTupleCoordinates {m : ℕ} :
    (Fin m → ℍ) ≃L[ℝ] ((Fin m → ℂ) × (Fin m → ℂ)) :=
  (show (Fin m → ℍ) ≃ₗ[ℝ] ((Fin m → ℂ) × (Fin m → ℂ)) from
    { toFun := fun q => (fun i => (quaternionCoordinates (q i)).1,
        fun i => (quaternionCoordinates (q i)).2)
      invFun := fun z i => quaternionCoordinates.symm (z.1 i, z.2 i)
      left_inv := by intro q; funext i; exact quaternionCoordinates.symm_apply_apply _
      right_inv := by intro z; ext i <;> simp
      map_add' := by intro q r; ext i <;> rfl
      map_smul' := by intro r q; ext i <;> simp [quaternionCoordinates] }).toContinuousLinearEquiv

@[simp] theorem quaternionTupleCoordinates_fixed {m : ℕ} (z : Fin m → ℂ) :
    quaternionTupleCoordinates (fun i => Quaternion.ofComplex (z i)) = (z, 0) := by
  apply Prod.ext
  · funext i; exact congrArg Prod.fst (quaternionCoordinates_ofComplex (z i))
  · funext i; exact congrArg Prod.snd (quaternionCoordinates_ofComplex (z i))

@[simp] theorem quaternionTupleCoordinates_symm_fixed {m : ℕ} (z : Fin m → ℂ) :
    quaternionTupleCoordinates.symm (z, 0) = fun i => Quaternion.ofComplex (z i) := by
  exact quaternionTupleCoordinates.injective (by rw [ContinuousLinearEquiv.apply_symm_apply, quaternionTupleCoordinates_fixed])

/-- Circle normalization chosen compatibly with quaternion normalization. -/
def normalizeCircle (z : ℂ) : Circle := by
  classical
  exact if hz : z = 0 then 1 else ⟨‖z‖⁻¹ • z, by apply mem_sphere_zero_iff_norm.mpr; simp [hz]⟩

end EilenbergGanea


namespace EilenbergGanea
open Set
section Torus
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Type*} [CommGroup A]

def torusMap (B : Matrix n n ℤ) (x : n → A) : n → A :=
  fun i => ∏ j, x j ^ B i j

end Torus
end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.IntegralDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

open scoped ContDiff
open Set Filter Topology

open Set MeasureTheory
namespace EilenbergGanea
section SignedIntegralDegree
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/- The integral representative of local degree against a target bump. -/
def jacobianIntegral (f : E → E) (U : Set E) (ρ : E → ℝ) : ℝ :=
  ∫ x in U, (fderiv ℝ f x).det * ρ (f x) ∂μ

/- The signed change-of-variables formula on one regular inverse patch. -/

end SignedIntegralDegree
end EilenbergGanea

open Set MeasureTheory Filter Topology
namespace EilenbergGanea

/-- Standard coordinate basis as a tuple of vectors. -/
def coordinateBasis (n : ℕ) : Fin n → (Fin n → ℝ) := fun i => Pi.single i 1

/-- The signed coordinate coefficient of an n-form in dimension n+1. -/
def formFlux {n : ℕ} (form : (Fin (n + 1) → ℝ) →
    (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (-1 : ℝ) ^ i.val * form x (i.removeNth (coordinateBasis (n + 1)))

/-- Determinant form with the standard coordinate orientation. -/
def coordinateVolumeForm (n : ℕ) : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.WordEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def eraseCoefficients {ι : Type*} {m : ℕ} : FreeGroup (ι ⊕ Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.SmallHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
variable {Γ S H : Type*} [Group Γ] [Group H]


section CompactLabeling
variable {T I : Type*}

 def mergeLabels (a : Γ → S → H) (b : Γ → T → H) : Γ → S ⊕ T → H :=
  fun g => Sum.elim (a g) (b g)

end CompactLabeling
end EilenbergGanea

open scoped Quaternion

namespace EilenbergGanea

/-- A uniform size for an arbitrary family, normalized to zero for an empty
index set. This is a real supremum, not an attained maximum. -/
def familySize {I : Type*} (f : I → ℝ) : ℝ := sSup (Set.range f ∪ {0})

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.PresentationAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Actual word and cycle-basis alignment. -/

namespace EilenbergGanea
section TrivialPresentationExtension
variable {Γ S T R : Type*} [Group Γ]

def eraseExtra : FreeGroup (S ⊕ T) →* FreeGroup S :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))

def unitExtendedRelators (r : R → FreeGroup S) : R ⊕ T → FreeGroup (S ⊕ T) :=
  Sum.elim (fun i => FreeGroup.map Sum.inl (r i)) (fun t => FreeGroup.of (.inr t))

end TrivialPresentationExtension
end EilenbergGanea

namespace EilenbergGanea
section Nielsen
variable {Γ S T A R : Type*} [Group Γ]

def nielsenHom (a : T → FreeGroup S) : FreeGroup (S ⊕ T) →* FreeGroup (S ⊕ T) :=
  FreeGroup.lift (Sum.elim (fun s => FreeGroup.of (.inl s))
    (fun t => FreeGroup.of (.inr t) * FreeGroup.map Sum.inl (a t)))

@[simp] theorem nielsenHom_of_left (a : T → FreeGroup S) (s : S) :
    nielsenHom a (FreeGroup.of (.inl s)) = FreeGroup.of (.inl s) := by
  simp [nielsenHom]

@[simp] theorem nielsenHom_of_right (a : T → FreeGroup S) (t : T) :
    nielsenHom a (FreeGroup.of (.inr t)) =
      FreeGroup.of (.inr t) * FreeGroup.map Sum.inl (a t) := by
  simp [nielsenHom]

@[simp] theorem nielsenHom_left (a : T → FreeGroup S) (w : FreeGroup S) :
    nielsenHom a (FreeGroup.map Sum.inl w) = FreeGroup.map Sum.inl w := by
  have h : (nielsenHom a).comp (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
    apply FreeGroup.ext_hom
    intro s
    simp [nielsenHom]
  exact DFunLike.congr_fun h w

def nielsenEquiv (a : T → FreeGroup S) : FreeGroup (S ⊕ T) ≃* FreeGroup (S ⊕ T) where
  __ := nielsenHom a
  invFun := nielsenHom (fun t => (a t)⁻¹)
  left_inv w := by
    have h : (nielsenHom (fun t => (a t)⁻¹)).comp (nielsenHom a) = MonoidHom.id _ := by
      apply FreeGroup.ext_hom
      intro s
      rcases s with s | t <;> simp [mul_assoc]
    exact DFunLike.congr_fun h w
  right_inv w := by
    have h : (nielsenHom a).comp (nielsenHom (fun t => (a t)⁻¹)) = MonoidHom.id _ := by
      apply FreeGroup.ext_hom
      intro s
      rcases s with s | t <;> simp [mul_assoc]
    exact DFunLike.congr_fun h w

@[simp] theorem nielsenEquiv_apply (a : T → FreeGroup S) (w : FreeGroup (S ⊕ T)) :
    nielsenEquiv a w = nielsenHom a w := rfl

end Nielsen
end EilenbergGanea

namespace EilenbergGanea
section GeneratorAlignment
variable {Γ S T A R : Type*} [Group Γ]

def freeGroupCongr (e : S ≃ T) : FreeGroup S ≃* FreeGroup T where
  __ := FreeGroup.map e
  invFun := FreeGroup.map e.symm
  left_inv w := by simpa [Function.comp_def] using FreeGroup.map.comp e e.symm w
  right_inv w := by simpa [Function.comp_def] using FreeGroup.map.comp e.symm e w

@[simp] theorem freeGroupCongr_apply (e : S ≃ T) (w : FreeGroup S) :
    freeGroupCongr e w = FreeGroup.map e w := rfl

end GeneratorAlignment
end EilenbergGanea

namespace EilenbergGanea
section Reindexing
variable {Γ S T U R I : Type*} [Group Γ]

/-- Permutation of the stabilized relator indices into distinguished and
ordinary blocks, in exactly the order of source (ordinary-diagonal). -/
def alignmentIndexEquiv : I ⊕ (T ⊕ R) ≃ R ⊕ (I ⊕ T) where
  toFun
    | .inl i => .inr (.inl i)
    | .inr (.inl t) => .inr (.inr t)
    | .inr (.inr r) => .inl r
  invFun
    | .inl r => .inr (.inr r)
    | .inr (.inl i) => .inl i
    | .inr (.inr t) => .inr (.inl t)
  left_inv := by rintro (i | (t | r)) <;> rfl
  right_inv := by rintro (r | (i | t)) <;> rfl

end Reindexing
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.SeedContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

def h1CodeData_17 : List (ℕ) := [
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643267678582306417573723147527693866912298954138737954511314173894072363613501027320944644794287413171424191315148723422979633036694731951992907366347118799459159439445314406953013957046235590455476752,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643412508697272216538743692879145216960116364784472052797750479781360558204408899575901888490569871809138764536623827603845303538937407293896723898828052061426351310764257299203589387804594266645742096,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669404065936256338779090195354015515152,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669444306236909983693211306700566970896,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830670731995857826620945086869790213554704,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830711938063727159013005104888658904236560,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911832030532235545795558925681492457006055952,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911874225545733742165028384132813996264276496,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403913224465977676025988051054575103252527333904,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403956432159799829108324776508728359452945170960,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927405339078362108727743099991041632557866315956752,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927449583756835993484055906856094566907094181102096,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300937291704371755672804111132820519355629991396375497659751048917996116021060158169337623057091098044108481860485647,
  8960398908465065285194385145529814865131561316688344088366879287077187266704144446968499216757201154660315097893421471351046172841839609630003338937122754501682145693782416653467136646900445911869935907422332147268002814888941585855489359172920225886703277800036751703350360976748782465901223762232164435311196755893685482386050872578709374477737727947821313601413829266305610599090656044221152909338193325,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128]

def h1CodeData_18 : List (ℕ) := [
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621928865413468000305686065726537788466082385865753104,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621974171964225258296150379956351993239691719774585360,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635377204126574138486584608690802899556757443646887886095563648127739642087154066535318877382250746188663900169533145584,
  8960398908465065285194385145529814865131561316688344088366879287077187266704144446968499216757201154660315097893421471351046172841839609630003338937122754501682145693782416653467136646900445911869935907422332147268002814888941585855489359172920225780402824579472380442560627886570663656882401367799354156945748263235231718316249130218104481872026267567957947768283950676461503480385385135588817289293966765,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155623423981588457513991008435310406545995190404857217552,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155669817889563889696226466206640152234171148327501447696,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  11194493006286113734317918171090867901209939875540933901284090476616535925135964069750907553869167108505258650611032314838375170032013004217008668764142665949173410349817165020065231600757420723810031139712161788823481232683428840166309915161978500230750925330711016814357450744798698518839953735488450667222715638729876965144764130204817507586446721411670159160515480609602004007433135482119206982312737263,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057494956968918135832264780823039073604418626307209070222989523072779924359285458055184092215232686580867897713919979455835748672428524289970294497324768107698415373798285984679082753481697865948069380624,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397157154422944777719527761114889192014255801801852116812304,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397204661784711620274136869872730851598947982714639808479760,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  11194493006286113734317918171090867901209939875540933901284090476616535925135964069750907553869167108505258650611032314838375170032013004217008668764142666170908166201037197278513870687453642951162859567274150519295146522327792369662444202874324933529652711887075897776033971191995667703249833146465737676410485140307115629291397649840449547623696831934646204568273104141892654123025037100562754473956948463]

def h1CodeData_19 : List (ℕ) := [
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469865905777880376265498427062456942150307443854318441172192495809424489682253418763134227588819509227599378531096527708579508017433021949929555247483376176444724458784790040924214734828086389846622229232108048,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544398724897361250582021628350123663958309097771923845941838352,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544447372435810497357941355718153523373033891026618442209313296,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  11194493006286113734317918171090867901209939875540933901284090476616535925135964069750907553869167108505258650611032314838375170032013004217008668764142893227298157850154674452930802301847947539062317518671959046556613065275213238977317697380329431825992457703420773911259221594306500831771086310289207441223161261624618485791134143798804233256886797010248506471579786313904726919924209281925654958127397359,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469710547491449499964795499882681217581661411432960762232977524342268031919249356439518173755953059610840568559014302115585976524294610147454113515823900562459727057655679750802004723386093543830042103534600720,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263546004093666186394187372631495109024644227275176845522768511504,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263595819173038215092729173456357685065322415567984112100662854160,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  11194493006286113734317918171090867901209939875540933901284090476616535925135964069750907553869167108505258650611032314838375170032013004217008668764375398970649606540193525792204994240423646463407999843511043739137071351247516706155388137553153294347022160799190620492901632684260049807285888404132562018578117689951088192625700343430664321293868299967223394961628253858630612730017799642984360044608829935,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905310623662186232168044998067788445036181000545719406098831331892495419578668338578208147968145012639010983410341453851067906830337366629325655041958235440454924467680283774612225765977572913931875608226714632720,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097263544397155621927403911830669402767862041705072183062729933210128,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097265189901712943133446066799851960118367024440937816642593281819152,
  12683889071500146033733606854798236591928858914775993776562231269642768363950015768399122090766032505751393829060148867137189812710059670150665532016266182340220725967964038919746916023463509482905469866057643263006643113972445819258967969629813982263472746531985945260800934034755729805635300862739568624183110817985423720062306546891461097316200542989900520752870844511237984021489252772457618357088698896]

end EilenbergGanea.SeedChainCertificate


end

end OAI
end



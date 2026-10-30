-- Prove2me | Definitions.Def_OAIQ113B000
-- name    : OAIQ113B000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:02:29.19085+00:00
-- url     : https://prove2.me/theorems/cba5ef94-c1f0-4efa-9a0c-4576d9107386
-- title:
--   Definitions bundle OAIQ113B000 of the split of OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TorsionFreeBass.torsion_free_corollary`, carved from OpenAI's openai/math development (OpenAI, *The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture*, OpenAI Math Release, September 24, 2026, result family 207, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 563 declarations of OpenAI's Lean: 213 definitions, 16 inductive types or structures, 24 instances and 310 theorems. The definitions and types are `OAI.BassTrace.BarycentricChains.ActualFlags.level`, `OAI.BassTrace.BarycentricChains.coneLeft`, `OAI.BassTrace.BarycentricChains.filteredCount`, `OAI.BassTrace.BarycentricChains.filteredLabel`, `OAI.BassTrace.BarycentricChains.labelMap`, `OAI.BassTrace.BarycentricChains.stepValues`, `OAI.BassTrace.ChainHomotopy.Complex`, `OAI.BassTrace.ChainHomotopy.Complex.IsInvariant`, `OAI.BassTrace.ChainHomotopy.Complex.chains`, `OAI.BassTrace.ChainHomotopy.Complex.projection`, `OAI.BassTrace.ChainHomotopy.Complex.projectionValues`, `OAI.BassTrace.ChainHomotopy.Complex.relations`, `OAI.BassTrace.ChainHomotopy.average`, `OAI.BassTrace.ChainHomotopy.cone`, `OAI.BassTrace.ChainHomotopy.coneFunction`, `OAI.BassTrace.ChainHomotopy.coneLift`, `OAI.BassTrace.ChainHomotopy.d`, `OAI.BassTrace.ChainHomotopy.homotopy`, `OAI.BassTrace.ChainHomotopy.relabel`, `OAI.BassTrace.ChainHomotopy.vertexMap`, `OAI.BassTrace.Chains.Algebra`, `OAI.BassTrace.Chains.Vectors`, `OAI.BassTrace.Chains.augmentation`, `OAI.BassTrace.Chains.boundary`, `OAI.BassTrace.Chains.contraction`, `OAI.BassTrace.Detector.ActingGroup`, `OAI.BassTrace.Detector.Centralizer`, `OAI.BassTrace.Detector.CoordinateAlgebra`, `OAI.BassTrace.Detector.CoordinateSpace`, `OAI.BassTrace.Detector.Vertex`, `OAI.BassTrace.Detector.centralizerAct`, `OAI.BassTrace.Detector.centralizerPerm`, `OAI.BassTrace.Detector.cocycle`, `OAI.BassTrace.Detector.coordinate`, `OAI.BassTrace.Detector.coordinateBasis`, `OAI.BassTrace.Detector.coordinateMap`, `OAI.BassTrace.Detector.coordinateVector`, `OAI.BassTrace.Detector.cosetCocycle`, `OAI.BassTrace.Detector.cyclic`, `OAI.BassTrace.Detector.detector` and 189 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `BassTrace_AdmissibleCuts`, `BassTrace_AffinePotentials`, `BassTrace_AveragedChains`, `BassTrace_BallGeometry`, `BassTrace_BarycentricBounds`, `BassTrace_BarycentricChains`, `BassTrace_CanonicalCells`, `BassTrace_CellTriangulation`, `BassTrace_CentralizerGeometry`, `BassTrace_ChainMaps`, `BassTrace_ClosedPaths`, `BassTrace_Coning`, `BassTrace_CutNaturality`, `BassTrace_Definitions`, `BassTrace_ExteriorChains`, `BassTrace_ExteriorDetector`, `BassTrace_FaceFiltration`, `BassTrace_FacetGeometry`, `BassTrace_FiniteAverages`, `BassTrace_FiniteCells`, `BassTrace_FreeParameters`, `BassTrace_FundamentalChains`, `BassTrace_GeometricSubcomplexes`, `BassTrace_GraphRealization`, `BassTrace_Incidence`, `BassTrace_LocalCuts`, `BassTrace_MarkedArea`, `BassTrace_MarkedSubdivisions`, `BassTrace_NormedVectors`, `BassTrace_OrbitForms`, `BassTrace_PathComplex`, `BassTrace_PathWeights`, `BassTrace_PfaffianDetector`, `BassTrace_ProbabilityGeometry`, `BassTrace_RelativeExponents`, `BassTrace_SparseChains`, `BassTrace_SubdivisionWeights`, `BassTrace_Subdivisions`, `BassTrace_TransportMetric`, `BassTrace_TwistedPaths`, `BassTrace_ZeroStrata`.
--
--   **Imports.** It imports the published bundle `Def_BassTorsionFree`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ113B002`.
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_BassTorsionFree

section
-- module Solutions.OAIQ113_TFB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ExteriorChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Chains

open scoped BigOperators

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

abbrev contraction (α : M →ₗ[R] R) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) α

@[simp] lemma contraction_one (α : M →ₗ[R] R) :
    contraction α (1 : ExteriorAlgebra R M) = 0 :=
  CliffordAlgebra.contractLeft_one _ α

@[simp] lemma contraction_ι (α : M →ₗ[R] R) (v : M) :
    contraction α (ExteriorAlgebra.ι R v) = algebraMap R _ (α v) :=
  CliffordAlgebra.contractLeft_ι _ α v

lemma contraction_ι_mul (α : M →ₗ[R] R) (v : M) (x : ExteriorAlgebra R M) :
    contraction α (ExteriorAlgebra.ι R v * x) =
      α v • x - ExteriorAlgebra.ι R v * contraction α x :=
  CliffordAlgebra.contractLeft_ι_mul α v x

lemma contraction_map (α : M →ₗ[R] R) (β : N →ₗ[R] R) (f : M →ₗ[R] N)
    (hf : ∀ v, β (f v) = α v) (x : ExteriorAlgebra R M) :
    contraction β (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (contraction α x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contraction, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    change contraction β (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v * x)) = _
    rw [map_mul, ExteriorAlgebra.map_apply_ι, contraction_ι_mul, contraction_ι_mul,
      hf, hx, map_sub, map_smul, map_mul, ExteriorAlgebra.map_apply_ι]

lemma contraction_ιMulti_succ (α : M →ₗ[R] R) {n : ℕ} (v : Fin (n+1) → M) :
    contraction α (ExteriorAlgebra.ιMulti R (n+1) v) =
      α (v 0) • ExteriorAlgebra.ιMulti R n (fun i => v i.succ) -
        ExteriorAlgebra.ι R (v 0) *
          contraction α (ExteriorAlgebra.ιMulti R n (fun i => v i.succ)) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, contraction_ι_mul]
  rfl

lemma contraction_ιMulti (α : M →ₗ[R] R) (n : ℕ) (v : Fin (n+1) → M) :
    contraction α (ExteriorAlgebra.ιMulti R (n+1) v) =
      ∑ i : Fin (n+1), ((-1 : R)^i.val * α (v i)) •
        ExteriorAlgebra.ιMulti R n (fun j => v (i.succAbove j)) := by
  induction n with
  | zero =>
    rw [contraction_ιMulti_succ]
    simp
  | succ n ih =>
    rw [contraction_ιMulti_succ, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    simp only [Fin.val_succ, pow_succ, Matrix.vecTail, Function.comp_def, Fin.succ_succAbove_succ,
      Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i), mul_smul_comm,
      mul_neg, mul_one, neg_mul, neg_smul]

lemma contraction_mem_exteriorPower (α : M →ₗ[R] R) (n : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n+1) M) :
    contraction α x ∈ ⋀[R]^n M := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R (n+1)] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction n with
    | zero =>
      rw [contraction_ιMulti_succ]
      simp only [ExteriorAlgebra.ιMulti_zero_apply, contraction_one, mul_zero, sub_zero]
      exact Submodule.smul_mem _ _ (by simp [ExteriorAlgebra.exteriorPower])
    | succ n ih =>
      rw [contraction_ιMulti_succ]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range R (n+1) ⟨_, rfl⟩)
      · have ht := ih (fun i => v i.succ)
        rw [ExteriorAlgebra.exteriorPower, pow_succ' ]
        exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v 0, rfl⟩) ht
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

variable (Y : Type*)

abbrev Vectors := Y →₀ ℂ

abbrev Algebra := ExteriorAlgebra ℂ (Vectors Y)

noncomputable def augmentation : Vectors Y →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun _ : Y => (1 : ℂ))

noncomputable def boundary : Algebra Y →ₗ[ℂ] Algebra Y :=
  contraction (augmentation Y)

@[simp] lemma augmentation_single (y : Y) (c : ℂ) :
    augmentation Y (Finsupp.single y c) = c := by
  simp [augmentation]

end Chains

/-! Alternating functions on vertex labels extend to genuine linear maps on exterior chains. -/

namespace Oriented

open scoped BigOperators

variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]

abbrev Degree (Y : Type*) (n : ℕ) := ⋀[ℂ]^n (Y →₀ ℂ)

def wedge (n : ℕ) (v : Fin n → Y) : Degree Y n :=
  exteriorPower.ιMulti ℂ n (fun i => Finsupp.single (v i) 1)

lemma wedge_perm (n : ℕ) (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    wedge n (v ∘ σ) = Equiv.Perm.sign σ • wedge n v :=
  by simpa only [wedge, Function.comp_def] using
    (exteriorPower.ιMulti ℂ n).map_perm (fun i => Finsupp.single (v i) 1) σ

lemma wedge_eq_zero_of_not_injective (n : ℕ) {v : Fin n → Y}
    (hv : ¬ Function.Injective v) : wedge n v = 0 := by
  apply (exteriorPower.ιMulti ℂ n).map_eq_zero_of_not_injective
  intro h
  exact hv fun i j hij => h (by simpa only using congrArg (fun y => Finsupp.single y (1 : ℂ)) hij)

structure AltFunction (Y : Type*) (n : ℕ) (A : Type*) [AddCommGroup A] where
  toFun : (Fin n → Y) → A
  perm : ∀ v (σ : Equiv.Perm (Fin n)), toFun (v ∘ σ) = Equiv.Perm.sign σ • toFun v
  zero : ∀ v, ¬ Function.Injective v → toFun v = 0

instance instCoeFunAltFunctionForallForallFin {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩

variable [LinearOrder Y]

abbrev basis (n : ℕ) : Module.Basis (Set.powersetCard Y n) ℂ (Degree Y n) :=
  (Finsupp.basisSingleOne : Module.Basis Y ℂ (Y →₀ ℂ)).exteriorPower n

lemma basis_eq_wedge (n : ℕ) (s : Set.powersetCard Y n) :
    basis n s = wedge n (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  rw [exteriorPower.basis_apply]
  rfl

lemma exists_sorted_perm {n : ℕ} (v : Fin n → Y) (hv : Function.Injective v) :
    ∃ (s : Set.powersetCard Y n) (σ : Equiv.Perm (Fin n)),
      v = (Set.powersetCard.ofFinEmbEquiv.symm s) ∘ σ := by
  classical
  let s : Set.powersetCard Y n :=
    ⟨Finset.univ.image v, by simpa using Finset.card_image_of_injective Finset.univ hv⟩
  let w : Fin n ↪o Y := Set.powersetCard.ofFinEmbEquiv.symm s
  have hs (i : Fin n) : v i ∈ s := by simp [s]
  have hw (i : Fin n) : ∃ j, w j = v i :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (v i)).mpr (hs i)
  let f : Fin n → Fin n := fun i => (hw i).choose
  have hf (i : Fin n) : w (f i) = v i := (hw i).choose_spec
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hv
    rw [← hf i, ← hf j, hij]
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, rfl⟩)
  refine ⟨s, σ, ?_⟩
  funext i
  exact (hf i).symm

def AltFunction.lift {n : ℕ} (f : AltFunction Y n A) : Degree Y n →ₗ[ℂ] A :=
  (basis n).constr ℂ fun s => f (Set.powersetCard.ofFinEmbEquiv.symm s)

@[simp] lemma AltFunction.lift_wedge {n : ℕ} (f : AltFunction Y n A)
    (v : Fin n → Y) : f.lift (wedge n v) = f v := by
  classical
  by_cases hv : Function.Injective v
  · obtain ⟨s, σ, rfl⟩ := exists_sorted_perm v hv
    rw [wedge_perm, f.perm, ← basis_eq_wedge]
    simp only [Units.smul_def, map_zsmul, AltFunction.lift, Module.Basis.constr_basis]
  · rw [wedge_eq_zero_of_not_injective n hv, map_zero, f.zero v hv]

lemma linearMap_ext_wedge {n : ℕ} {f g : Degree Y n →ₗ[ℂ] A}
    (h : ∀ v, f (wedge n v) = g (wedge n v)) : f = g := by
  apply (basis n).ext
  intro s
  rw [basis_eq_wedge]
  exact h _

lemma span_wedges (n : ℕ) :
    Submodule.span ℂ (Set.range (wedge (Y := Y) n)) = ⊤ := by
  apply top_unique
  rw [← (basis n).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨s, rfl⟩
  exact ⟨_, (basis_eq_wedge n s).symm⟩

end Oriented

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y : Type*}

def average (n : ℕ) (v : Fin n → Y) : Y →₀ ℂ :=
  (n : ℂ)⁻¹ • ∑ i, Finsupp.single (v i) 1

lemma average_perm (n : ℕ) (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    average n (v ∘ σ) = average n v := by
  unfold average
  congr 1
  exact Equiv.sum_comp σ (fun y => Finsupp.single (v y) (1 : ℂ))

def cone (n : ℕ) (v : Y →₀ ℂ) : Degree Y n →ₗ[ℂ] Degree Y (n+1) where
  toFun x := ⟨ExteriorAlgebra.ι ℂ v * x, by
    change _ ∈ (ExteriorAlgebra.ι ℂ).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v, rfl⟩) x.property⟩
  map_add' a b := by ext; exact mul_add _ _ _
  map_smul' a x := by ext; exact mul_smul_comm _ _ _

@[simp] lemma cone_coe (n : ℕ) (v : Y →₀ ℂ) (x : Degree Y n) :
    (cone n v x : Chains.Algebra Y) = ExteriorAlgebra.ι ℂ v * x := rfl

def d (n : ℕ) : Degree Y (n+1) →ₗ[ℂ] Degree Y n :=
  ((Chains.boundary Y).comp (Degree Y (n+1)).subtype).codRestrict _ fun x =>
    Chains.contraction_mem_exteriorPower (Chains.augmentation Y) n x.property

@[simp] lemma d_coe (n : ℕ) (x : Degree Y (n+1)) :
    (d n x : Chains.Algebra Y) = Chains.boundary Y x := rfl

def coneFunction {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n) :
    AltFunction Y n (Degree Y (n+1)) where
  toFun v := cone n (average n v) (r (wedge n v))
  perm v σ := by
    rw [average_perm, wedge_perm]
    simp only [Units.smul_def, map_zsmul]
  zero v hv := by
    rw [wedge_eq_zero_of_not_injective n hv, map_zero, map_zero]

variable [LinearOrder Y]

def coneLift {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n) :
    Degree Y n →ₗ[ℂ] Degree Y (n+1) := (coneFunction r).lift

@[simp] lemma coneLift_wedge {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n)
    (v : Fin n → Y) :
    coneLift r (wedge n v) = cone n (average n v) (r (wedge n v)) :=
  (coneFunction r).lift_wedge v

omit [LinearOrder Y] in
lemma d_wedge (n : ℕ) (v : Fin (n+1) → Y) :
    d n (wedge (n+1) v) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val • wedge n (fun j => v (i.succAbove j)) := by
  apply Subtype.ext
  change Chains.boundary Y (ExteriorAlgebra.ιMulti ℂ (n+1)
      (fun i => Finsupp.single (v i) 1)) = _
  rw [Chains.boundary, Chains.contraction_ιMulti]
  simp only [Chains.augmentation_single, mul_one, Submodule.coe_sum,
    Submodule.coe_smul, wedge, exteriorPower.ιMulti_apply_coe]

end ChainHomotopy

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Incidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace OrientedIncidence

section

open scoped BigOperators

open Oriented ChainHomotopy

variable {V : Type*} [LinearOrder V]

abbrev vertices {n : ℕ} (s : Set.powersetCard V n) : Fin n ↪o V :=
  Set.powersetCard.ofFinEmbEquiv.symm s

lemma vertices_mem {n : ℕ} (s : Set.powersetCard V n) (i : Fin n) : vertices s i ∈ s.val :=
  Finset.orderEmbOfFin_mem s.val s.property i

def eraseFace {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    Set.powersetCard V n :=
  ⟨s.val.erase (vertices s i), by simp [Finset.card_erase_of_mem (vertices_mem s i)]⟩

@[simp] lemma eraseFace_val {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    (eraseFace s i).val = s.val.erase (vertices s i) := rfl

end

open scoped BigOperators

open Oriented ChainHomotopy

variable {V : Type*} [LinearOrder V] {n : ℕ}

def incidencePairs (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) :
    Finset (Set.powersetCard V (n+1) × Fin (n+1)) :=
  (F ×ˢ Finset.univ).filter fun p => eraseFace p.1 p.2 = t

def apexes (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) : Finset V :=
  (incidencePairs F t).image fun p => vertices p.1 p.2

end OrientedIncidence

namespace Fundamental

open scoped BigOperators

open OrientedIncidence Oriented ChainHomotopy

variable {V : Type*} [LinearOrder V] {n : ℕ}

def chain (F : Finset (Set.powersetCard V (n+1))) (p : V → (Fin (n+1) → ℝ)) :
    Oriented.Degree V (n+1) :=
  ∑ s ∈ F, (Real.sign (Matrix.det (fun i => p (vertices s i))) : ℂ) • basis (n+1) s

end Fundamental

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FacetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Two-sided facet incidence inside a single affine carrier, without a manifold hypothesis. -/

namespace BassTrace.Sparse

section

open Set Finset

open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma sum_weights_mem_convexHull (s : Finset E) {w : E → ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1) :
    ∑ x ∈ s, w x • x ∈ convexHull ℝ (s : Set E) :=
  (convex_convexHull ℝ (s : Set E)).sum_mem hw hsum
    (fun _ hx => subset_convexHull ℝ (s : Set E) hx)

end

section

open Set Finset

open scoped Topology Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positiveCombination_carrier {F T : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hTF : T ⊆ F)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  obtain ⟨a,_,has,hap⟩ := Finset.mem_convexHull'.mp hq
  let a' : E → ℝ := fun x => if x ∈ T then a x else 0
  have hs : ∑ x ∈ F, a' x = 1 := by
    calc
      _ = ∑ x ∈ T, a' x := (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = 1 := has
  have hp : ∑ x ∈ F, a' x • x = ∑ x ∈ F, w x • x := by
    calc
      _ = ∑ x ∈ T, a' x • x :=
        (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x • x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = _ := hap
  have he := hF.eq_of_sum_eq_sum_subtype (hs.trans hws.symm) hp
  intro x hx
  by_contra hxt
  have hzero : w x = 0 := by simpa [a',hxt] using (he x hx).symm
  exact (ne_of_gt (hw x hx)) hzero

end

end

open Set Finset

open scoped Classical

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FundamentalChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Fundamental

section

open scoped BigOperators

open OrientedIncidence Oriented ChainHomotopy

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

def faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (k : ℕ) :
    Finset (Set.powersetCard E k) := by
  classical
  exact hK.toFinset.subtype fun s : Finset E => s ∈ Set.powersetCard E k

omit [LinearOrder E] in
@[simp] lemma mem_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (k : ℕ) (s : Set.powersetCard E k) : s ∈ faces K hK k ↔ s.val ∈ K.faces := by
  classical
  simp only [faces,Finset.mem_subtype,Set.Finite.mem_toFinset]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

def faceChain (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) : Degree E (n+1) := by
  classical
  exact chain ((faces K hK (n+1)).filter fun t => ∀ x ∈ t.val, p x i = 0)
    (fun x j => p x (i.succAbove j))

open scoped Classical

end

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy

section

variable {V : Type*}

def term (n : ℕ) (p : V → (Fin n → ℝ)) (v : Fin n → V) : Degree V n :=
  (Real.sign (Matrix.det (fun j => p (v j))) : ℂ) • wedge n v

end

end Fundamental

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ChainMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y Z W : Type*}

def vertexMap (f : Y → Z) : (Y →₀ ℂ) →ₗ[ℂ] (Z →₀ ℂ) := Finsupp.lmapDomain ℂ ℂ f

def relabel (n : ℕ) (f : Y → Z) : Degree Y n →ₗ[ℂ] Degree Z n :=
  exteriorPower.map n (vertexMap f)

@[simp] lemma vertexMap_single (f : Y → Z) (y : Y) (a : ℂ) :
    vertexMap f (Finsupp.single y a) = Finsupp.single (f y) a :=
  Finsupp.mapDomain_single

@[simp] lemma relabel_wedge (n : ℕ) (f : Y → Z) (v : Fin n → Y) :
    relabel n f (wedge n v) = wedge n (f ∘ v) := by
  simp only [relabel, wedge, exteriorPower.map_apply_ιMulti, Function.comp_def,
    vertexMap_single]

end ChainHomotopy

namespace Fundamental

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy

variable {V W : Type*} [LinearOrder V] [LinearOrder W]

def simplexMap (f : V ↪ W) (n : ℕ) : Set.powersetCard V n ↪ Set.powersetCard W n where
  toFun s := ⟨s.val.map f,by simp⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    exact Finset.map_injective f (congrArg Subtype.val h)

end Fundamental

/-! Alternating functions on vertex labels act on oriented exterior chains. -/

namespace Oriented

open scoped BigOperators

variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]

instance instCoeFunAltFunctionForallForallFin_1 {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩

end Oriented

namespace ChainHomotopy

section

open scoped BigOperators

open Oriented

variable {Y : Type*}

variable [LinearOrder Y]

structure Complex (Y : Type*) where
  faces : Set (Finset Y)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

def Complex.chains (K : Complex Y) (n : ℕ) : Submodule ℂ (Degree Y n) :=
  Submodule.span ℂ {x | ∃ v : Fin n → Y,
    (Finset.univ.image v) ∈ K.faces ∧ wedge n v = x}

lemma Complex.wedge_mem (K : Complex Y) {n : ℕ} (v : Fin n → Y)
    (hv : Finset.univ.image v ∈ K.faces) : wedge n v ∈ K.chains n :=
  Submodule.subset_span ⟨v, hv, rfl⟩

lemma Complex.d_mem (K : Complex Y) (n : ℕ) {x : Degree Y (n+1)}
    (hx : x ∈ K.chains (n+1)) : d n x ∈ K.chains n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [d_wedge]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply K.wedge_mem
    apply K.down_closed hv
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

def homotopy (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n) :
    ∀ n, Degree Y n →ₗ[ℂ] Degree Y (n+1)
  | 0 => 0
  | n+1 => coneLift (F (n+1) - LinearMap.id - (homotopy F n).comp (d n))

end

section

open scoped BigOperators

open Oriented

variable {Y Z W : Type*}

lemma augmentation_vertexMap (f : Y → Z) (x : Y →₀ ℂ) :
    Chains.augmentation Z (vertexMap f x) = Chains.augmentation Y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single y c => simp

variable [LinearOrder Y]

lemma relabel_coe (n : ℕ) (f : Y → Z) (x : Degree Y n) :
    (relabel n f x : Chains.Algebra Z) =
      ExteriorAlgebra.map (vertexMap f) (x : Chains.Algebra Y) := by
  have he : (Degree Z n).subtype.comp (relabel n f) =
      (ExteriorAlgebra.map (vertexMap f)).toLinearMap.comp (Degree Y n).subtype := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [relabel_wedge]
    simp only [wedge, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
      Function.comp_def, vertexMap_single]
  exact LinearMap.congr_fun he x

lemma d_relabel (n : ℕ) (f : Y → Z) (x : Degree Y (n+1)) :
    d n (relabel (n+1) f x) = relabel n f (d n x) := by
  apply Subtype.ext
  simp only [d_coe, relabel_coe]
  exact Chains.contraction_map (Chains.augmentation Y) (Chains.augmentation Z)
    (vertexMap f) (augmentation_vertexMap f) x

@[simp] lemma relabel_id (n : ℕ) : relabel n (id : Y → Y) = LinearMap.id := by
  apply linearMap_ext_wedge
  intro v
  simp only [relabel_wedge, Function.id_comp, LinearMap.id_apply]

end

open scoped BigOperators

open Oriented

variable {Y H : Type*} [LinearOrder Y] [Monoid H] [MulAction H Y]

def Complex.IsInvariant (K : Complex Y) : Prop :=
  ∀ h : H, ∀ s ∈ K.faces, s.image (fun y => h • y) ∈ K.faces

lemma Complex.relabel_mem (K : Complex Y) (hK : K.IsInvariant (H := H))
    (n : ℕ) (h : H) {x : Degree Y n} (hx : x ∈ K.chains n) :
    relabel n (fun y => h • y) x ∈ K.chains n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [relabel_wedge]
    apply K.wedge_mem
    simpa only [Finset.image_image] using hK h (Finset.univ.image v) hv
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

def Complex.relations (K : Complex Y) (hK : K.IsInvariant (H := H)) (n : ℕ) :
    Submodule ℂ (K.chains n) :=
  Submodule.span ℂ (Set.range fun p : H × K.chains n =>
    (⟨relabel n (fun y => p.1 • y) p.2, K.relabel_mem hK n p.1 p.2.property⟩ : K.chains n) - p.2)

end ChainHomotopy

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BarycentricChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y H : Type*} [LinearOrder Y]

lemma tuple_image_perm {n : ℕ} (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.image (v ∘ σ) = Finset.univ.image v := by
  classical
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩,
    fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩⟩

def Complex.projectionValues (K : Complex Y) (n : ℕ) : AltFunction Y n (K.chains n) := by
  classical
  refine {
  toFun := ?_, perm := ?_, zero := ?_ }
  · exact fun v => if hv : Finset.univ.image v ∈ K.faces then ⟨wedge n v, K.wedge_mem v hv⟩ else 0
  · intro v σ
    have he := tuple_image_perm v σ
    by_cases hv : Finset.univ.image v ∈ K.faces
    · simp only [he, dite_eq_left hv]
      apply Subtype.ext
      exact wedge_perm n v σ
    · simp only [he, dite_eq_right hv, smul_zero]
  · intro v hv
    split_ifs
    · apply Subtype.ext
      exact wedge_eq_zero_of_not_injective n hv
    · rfl

def Complex.projection (K : Complex Y) (n : ℕ) : Degree Y n →ₗ[ℂ] K.chains n :=
  (K.projectionValues n).lift

end ChainHomotopy

namespace BarycentricChains

open scoped BigOperators

open Oriented ChainHomotopy

variable {V Y : Type*} [LinearOrder V]

def stepValues {n : ℕ} (b : Finset V → Y →₀ ℂ)
    (F : Degree V n →ₗ[ℂ] Degree Y n) : AltFunction V (n+1) (Degree Y (n+1)) where
  toFun v := cone n (b (Finset.univ.image v)) (F (d n (wedge (n+1) v)))
  perm v σ := by
    rw [tuple_image_perm, wedge_perm]
    simp only [Units.smul_def,map_zsmul]
  zero v hv := by
    rw [wedge_eq_zero_of_not_injective _ hv,map_zero,map_zero,map_zero]

def labelMap (b : Finset V → Y →₀ ℂ) : ∀ n, Degree V n →ₗ[ℂ] Degree Y n
  | 0 => exteriorPower.map 0 (0 : (V →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
  | n+1 => (stepValues b (labelMap b n)).lift

@[simp] lemma labelMap_wedge_succ (b : Finset V → Y →₀ ℂ) (n : ℕ) (v : Fin (n+1) → V) :
    labelMap b (n+1) (wedge (n+1) v) =
      cone n (b (Finset.univ.image v)) (labelMap b n (d n (wedge (n+1) v))) := by
  rw [labelMap,AltFunction.lift_wedge]
  rfl

@[simp] lemma labelMap_wedge_zero (b : Finset V → Y →₀ ℂ) (v : Fin 0 → V) :
    labelMap b 0 (wedge 0 v) = wedge 0 (fun i => Fin.elim0 i) := by
  rw [labelMap,wedge,exteriorPower.map_apply_ιMulti]
  congr 1
  exact funext fun i => Fin.elim0 i

lemma labelMap_wedge_recursion (b : Finset V → Y →₀ ℂ) (n : ℕ) (v : Fin (n+1) → V) :
    labelMap b (n+1) (wedge (n+1) v) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val •
        cone n (b (Finset.univ.image v))
          (labelMap b n (wedge n (fun j => v (i.succAbove j)))) := by
  rw [labelMap_wedge_succ,d_wedge,map_sum,map_sum]
  simp only [map_smul]

lemma labelMap_local (b c : Finset V → Y →₀ ℂ) (s : Finset V)
    (hbc : ∀ t : Finset V, t ⊆ s → t.Nonempty → b t = c t)
    (n : ℕ) (v : Fin n → V) (hv : ∀ i, v i ∈ s) :
    labelMap b n (wedge n v) = labelMap c n (wedge n v) := by
  induction n with
  | zero => simp only [labelMap_wedge_zero]
  | succ n ih =>
    rw [labelMap_wedge_recursion,labelMap_wedge_recursion]
    have him : Finset.univ.image v ⊆ s := by
      intro y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      exact hv i
    rw [hbc _ him (Finset.image_nonempty.mpr Finset.univ_nonempty)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih (fun j => v (i.succAbove j)) (fun j => hv (i.succAbove j))]

end BarycentricChains

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Coning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset

open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def vertexMean (s : Finset E) : E :=
  (s.card : ℝ)⁻¹ • ∑ x ∈ s, x

lemma vertexMean_mem_convexHull {s : Finset E} (hs : s.Nonempty) :
    vertexMean s ∈ convexHull ℝ (s : Set E) := by
  have h := s.centerMass_id_mem_convexHull (R := ℝ) (w := fun _ => 1)
    (fun _ _ => zero_le_one) (by simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card))
  simpa [Finset.centerMass, vertexMean] using h

lemma linear_vertexMean (f : E →ₗ[ℝ] ℝ) (s : Finset E) :
    f (vertexMean s) = (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x := by
  simp [vertexMean]

lemma linear_vertexMean_eq_iff (f : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : s.Nonempty)
    {b : ℝ} (hb : ∀ x ∈ s, f x ≤ b) :
    f (vertexMean s) = b ↔ ∀ x ∈ s, f x = b := by
  have hn : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  rw [linear_vertexMean]
  constructor
  · intro h
    have he : ∑ x ∈ s, f x = ∑ _x ∈ s, b := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ = (s.card : ℝ) * ((s.card : ℝ)⁻¹ * ∑ x ∈ s, f x) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul]
        _ = _ := by rw [h]
    exact (Finset.sum_eq_sum_iff_of_le hb).mp he
  · intro h
    rw [Finset.sum_congr rfl h]
    simp [ne_of_gt hn]

def cell {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

lemma exists_ray_boundary {I : Type*} [Fintype I]
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {c x : E}
    (hc : c ∈ cell a b) (hx : x ∈ cell a b)
    (hp : ∃ i, 0 < a i (x - c)) :
    ∃ (i : I) (t : ℝ), 1 ≤ t ∧
      c + t • (x - c) ∈ cell a b ∧
      a i (c + t • (x - c)) = b i ∧ a i c < b i ∧
      x ∈ segment ℝ c (c + t • (x - c)) := by
  classical
  let S : Finset I := Finset.univ.filter (fun i => 0 < a i (x - c))
  have hs : S.Nonempty := by
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun i => (b i - a i c) / a i (x - c)) hs
  have hip : 0 < a i (x - c) := (Finset.mem_filter.mp hi).2
  let t := (b i - a i c) / a i (x - c)
  have ht : 1 ≤ t := by
    rw [le_div_iff₀ hip]
    simp only [one_mul, map_sub]
    linarith [hx i]
  have hteq : t * a i (x - c) = b i - a i c := by
    exact div_mul_cancel₀ _ (ne_of_gt hip)
  have hmem : c + t • (x - c) ∈ cell a b := by
    intro j
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hj : 0 < a j (x - c)
    · have hbound : t ≤ (b j - a j c) / a j (x - c) :=
        hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hmul := (le_div_iff₀ hj).mp hbound
      linarith
    · have hmul : t * a j (x - c) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_gt hj)
      linarith [hc j]
  refine ⟨i, t, ht, hmem, ?_, ?_, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul]
    linarith
  · have : 0 < a i x - a i c := by simpa using hip
    linarith [hx i]
  · have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    refine ⟨1 - t⁻¹, t⁻¹, ?_, inv_nonneg.mpr ht0.le, by ring, ?_⟩
    · have := inv_le_one_of_one_le₀ ht
      linarith
    · simp only [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul,
        sub_smul, one_smul, smul_sub]
      module

section BoundedRay

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma bounded_cell_positive_direction {I : Type*}
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c v : V} (hc : c ∈ cell a b) (hv : v ≠ 0) : ∃ i, 0 < a i v := by
  by_contra! h
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg c).trans (hR c hc)
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := (R + ‖c‖ + 1) / ‖v‖
  have ht : 0 < t := div_pos (by positivity) hv0
  have hmem : c + t • v ∈ cell a b := by
    intro i
    simp only [map_add, map_smul, smul_eq_mul]
    have := mul_nonpos_of_nonneg_of_nonpos ht.le (h i)
    linarith [hc i]
  have hn : ‖t • v‖ ≤ R + ‖c‖ := by
    calc
      ‖t • v‖ = ‖(c + t • v) - c‖ := by congr 1; abel
      _ ≤ ‖c + t • v‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ R + ‖c‖ := add_le_add (hR _ hmem) le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hn
  have hteq : t * ‖v‖ = R + ‖c‖ + 1 := div_mul_cancel₀ _ (ne_of_gt hv0)
  linarith

lemma bounded_exists_ray_boundary {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c x : V} (hc : c ∈ cell a b) (hx : x ∈ cell a b) (hxc : x ≠ c) :
    ∃ (i : I) (t : ℝ), 1 ≤ t ∧
      c + t • (x - c) ∈ cell a b ∧
      a i (c + t • (x - c)) = b i ∧ a i c < b i ∧
      x ∈ segment ℝ c (c + t • (x - c)) :=
  exists_ray_boundary a b hc hx
    (bounded_cell_positive_direction a b hbounded hc (sub_ne_zero.mpr hxc))

end BoundedRay

lemma boundary_ray_unique {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {c y z : E}
    (hy : y ∈ cell a b) (hz : z ∈ cell a b)
    (hyi : ∃ i, a i y = b i ∧ a i c < b i)
    (hzi : ∃ i, a i z = b i ∧ a i c < b i)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (he : t • (y - c) = u • (z - c)) : t = u ∧ y = z := by
  obtain ⟨i, hiy, hic⟩ := hyi
  obtain ⟨j, hjz, hjc⟩ := hzi
  have he1 := congrArg (a i) he
  have he2 := congrArg (a j) he
  simp only [map_smul, map_sub, smul_eq_mul, hiy] at he1
  simp only [map_smul, map_sub, smul_eq_mul, hjz] at he2
  have htu : t ≤ u := by
    have hi := hz i
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hi (a i c)) hu.le
    nlinarith
  have hut : u ≤ t := by
    have hj := hy j
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hj (a j c)) ht.le
    nlinarith
  have h : t = u := le_antisymm htu hut
  refine ⟨h, ?_⟩
  rw [← h] at he
  have hdiff : y - c = z - c := by
    have hh := congrArg ((t⁻¹ : ℝ) • ·) he
    simpa [smul_smul, ne_of_gt ht] using hh
  exact sub_left_injective hdiff

lemma linear_eq_on_affineSpan (f : E →ₗ[ℝ] ℝ) {S : Set E} {b : ℝ}
    (hS : ∀ x ∈ S, f x = b) {x : E} (hx : x ∈ affineSpan ℝ S) : f x = b := by
  refine affineSpan_induction hx hS ?_
  intro t u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, hu, hv, hw,
    sub_self, smul_zero, zero_add]

lemma convexHull_inter_supporting (S : Set E) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hS : ∀ x ∈ S, f x ≤ b) :
    convexHull ℝ S ∩ {x | f x = b} = convexHull ℝ (S ∩ {x | f x = b}) := by
  let T := convexHull ℝ (S ∩ {x | f x = b})
  let C := {x : E | f x ≤ b ∧ (f x = b → x ∈ T)}
  have hSC : S ⊆ C := by
    intro x hx
    exact ⟨hS x hx, fun he => subset_convexHull ℝ _ ⟨hx, he⟩⟩
  have hC : Convex ℝ C := by
    intro x hx y hy u v hu hv huv
    change f (u • x + v • y) ≤ b ∧ (f (u • x + v • y) = b → _)
    simp only [map_add, map_smul, smul_eq_mul]
    have hew : u*b + v*b = b := by rw [← add_mul, huv, one_mul]
    have hux : 0 ≤ u*(b-f x) := mul_nonneg hu (sub_nonneg.mpr hx.1)
    have hvy : 0 ≤ v*(b-f y) := mul_nonneg hv (sub_nonneg.mpr hy.1)
    refine ⟨?_, ?_⟩
    · nlinarith only [hew, hux, hvy]
    · intro he
      by_cases hu0 : u = 0
      · have hv1 : v = 1 := by linarith
        have hyb : f y = b := by simpa [hu0, hv1] using he
        simpa [hu0, hv1] using hy.2 hyb
      by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        have hxb : f x = b := by simpa [hv0, hu1] using he
        simpa [hv0, hu1] using hx.2 hxb
      have hux0 : u*(b-f x) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hvy0 : v*(b-f y) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hxb : f x = b := (sub_eq_zero.mp ((mul_eq_zero.mp hux0).resolve_left hu0)).symm
      have hyb : f y = b := (sub_eq_zero.mp ((mul_eq_zero.mp hvy0).resolve_left hv0)).symm
      exact (convex_convexHull ℝ _) (hx.2 hxb) (hy.2 hyb) hu hv huv
  apply subset_antisymm
  · intro x hx
    exact (convexHull_min hSC hC hx.1).2 hx.2
  · intro x hx
    refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
    exact linear_eq_on_affineSpan f (fun _ hy => hy.2)
      (convexHull_subset_affineSpan _ hx)

lemma exists_positive_ray_of_mem_convexHull_insert {S : Set E} {c x : E}
    (hx : x ∈ convexHull ℝ (insert c S)) (hxc : x ≠ c) :
    ∃ y ∈ convexHull ℝ S, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      x = c + t • (y-c) ∧ x ∈ segment ℝ c y := by
  have hS : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hx
    have : x = c := by simpa using hx
    exact hxc this
  rw [convexHull_insert hS, convexJoin_singleton_left] at hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  have hseg := hxy
  obtain ⟨u, t, hu, ht, hut, he⟩ := hxy
  have ht0 : t ≠ 0 := by
    intro ht0
    have hu1 : u = 1 := by linarith
    apply hxc
    simpa [ht0, hu1] using he.symm
  refine ⟨y, hy, t, lt_of_le_of_ne ht (Ne.symm ht0), by linarith, ?_, hseg⟩
  rw [← he, show u = 1-t by linarith, sub_smul, one_smul, smul_sub]
  abel

def radialBoundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (c : E) : Set E :=
  {y | y ∈ cell a b ∧ ∃ i, a i y = b i ∧ a i c < b i}

lemma center_notMem_radialBoundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : I → ℝ) (c : E) : c ∉ radialBoundary a b c := by
  rintro ⟨_, i, he, hi⟩
  exact (ne_of_lt hi) he

lemma cone_hull_inter {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    {c : E} {S T : Set E}
    (hS : convexHull ℝ S ⊆ radialBoundary a b c)
    (hT : convexHull ℝ T ⊆ radialBoundary a b c)
    (hST : convexHull ℝ S ∩ convexHull ℝ T ⊆ convexHull ℝ (S ∩ T)) :
    convexHull ℝ (insert c S) ∩ convexHull ℝ (insert c T) =
      convexHull ℝ (insert c (S ∩ T)) := by
  apply subset_antisymm
  · intro x hx
    by_cases hxc : x = c
    · subst x
      exact subset_convexHull ℝ _ (Set.mem_insert c _)
    obtain ⟨y, hy, t, ht, _, hxy, hseg⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.1 hxc
    obtain ⟨z, hz, u, hu, _, hxz, _⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.2 hxc
    have hray : t • (y-c) = u • (z-c) := by
      exact add_left_cancel (hxy.symm.trans hxz)
    have hyz := (boundary_ray_unique a b (hS hy).1 (hT hz).1
      (hS hy).2 (hT hz).2 ht hu hray).2
    have hyST : y ∈ convexHull ℝ (S ∩ T) := hST ⟨hy, hyz ▸ hz⟩
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (Set.mem_insert c _))
      (convexHull_mono (Set.subset_insert c _) hyST) hseg
  · exact Set.subset_inter
      (convexHull_mono (Set.insert_subset_insert Set.inter_subset_left))
      (convexHull_mono (Set.insert_subset_insert Set.inter_subset_right))

lemma cone_hull_inter_boundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    {c : E} {S T : Set E}
    (hS : convexHull ℝ S ⊆ radialBoundary a b c)
    (hT : convexHull ℝ T ⊆ radialBoundary a b c)
    (hST : convexHull ℝ S ∩ convexHull ℝ T ⊆ convexHull ℝ (S ∩ T)) :
    convexHull ℝ (insert c S) ∩ convexHull ℝ T = convexHull ℝ (S ∩ T) := by
  apply subset_antisymm
  · intro x hx
    have hxc : x ≠ c := by
      intro hh
      exact center_notMem_radialBoundary a b c (hh ▸ hT hx.2)
    obtain ⟨y, hy, t, ht, _, hxy, _⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.1 hxc
    have hray : t • (y-c) = (1 : ℝ) • (x-c) := by
      rw [one_smul, hxy]
      abel
    have hyx := (boundary_ray_unique a b (hS hy).1 (hT hx.2).1
      (hS hy).2 (hT hx.2).2 ht zero_lt_one hray).2
    exact hST ⟨hyx ▸ hy, hx.2⟩
  · exact Set.subset_inter
      (convexHull_mono (Set.inter_subset_left.trans (Set.subset_insert c S)))
      (convexHull_mono Set.inter_subset_right)

lemma affineIndependent_insert {S : Set E} {c : E}
    (hS : AffineIndependent ℝ ((↑) : S → E)) (hc : c ∉ affineSpan ℝ S) :
    AffineIndependent ℝ (fun x : (insert c S : Set E) => (x : E)) := by
  let i : (insert c S : Set E) := ⟨c, Set.mem_insert c S⟩
  let f : {j : (insert c S : Set E) // j ≠ i} → S := fun j =>
    ⟨j.val.val, by
      rcases j.val.property with he | hm
      · exact False.elim (j.property (Subtype.ext he))
      · exact hm⟩
  have hf : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : E)) hjk
  have hi : AffineIndependent ℝ (fun j : {j : (insert c S : Set E) // j ≠ i} =>
      (j.val : E)) := hS.comp_embedding ⟨f, hf⟩
  apply hi.affineIndependent_of_notMem_span
  intro hmem
  apply hc
  apply affineSpan_mono ℝ (s₁ := (fun x : (insert c S : Set E) => (x : E)) '' {j | j ≠ i})
    (s₂ := S) ?_ hmem
  rintro x ⟨j, hj, rfl⟩
  exact (f ⟨j, hj⟩).property

variable [DecidableEq E]

def coneFaces (B : Geometry.SimplicialComplex ℝ E) (c : E) : Set (Finset E) :=
  {{c}} ∪ B.faces ∪ (fun s => insert c s) '' B.faces

lemma mem_coneFaces_iff (B : Geometry.SimplicialComplex ℝ E) (c : E) (s : Finset E) :
    s ∈ coneFaces B c ↔ s = {c} ∨ s ∈ B.faces ∨ ∃ t ∈ B.faces, s = insert c t := by
  simp only [coneFaces, Set.mem_union, Set.mem_singleton_iff, Set.mem_image]
  aesop

lemma coneFaces_down_closed (B : Geometry.SimplicialComplex ℝ E) (c : E) :
    IsRelLowerSet (coneFaces B c) Finset.Nonempty := by
  intro s hs
  rw [mem_coneFaces_iff] at hs
  have hpos : s.Nonempty := by
    rcases hs with rfl | hs | ⟨t, _, rfl⟩
    · exact Finset.singleton_nonempty _
    · exact B.nonempty_of_mem_faces hs
    · exact Finset.insert_nonempty _ _
  refine ⟨hpos, ?_⟩
  intro t hts ht
  rw [mem_coneFaces_iff]
  rcases hs with rfl | hs | ⟨u, hu, rfl⟩
  · left
    exact Finset.Subset.antisymm hts (Finset.singleton_subset_iff.mpr
      (by obtain ⟨x, hx⟩ := ht; simpa only [Finset.mem_singleton.mp (hts hx)] using hx))
  · exact Or.inr (Or.inl (B.down_closed hs hts ht))
  · by_cases hct : c ∈ t
    · by_cases he : t.erase c = ∅
      · exact Or.inl ((Finset.erase_eq_empty_iff t c).mp he |>.resolve_left ht.ne_empty)
      · right; right
        refine ⟨t.erase c, B.down_closed hu ?_ (Finset.nonempty_iff_ne_empty.mpr he),
          (Finset.insert_erase hct).symm⟩
        intro x hx
        exact (Finset.mem_insert.mp (hts (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.ne_of_mem_erase hx)
    · right; left
      apply B.down_closed hu _ ht
      intro x hx
      rcases Finset.mem_insert.mp (hts hx) with rfl | hu'
      · exact False.elim (hct hx)
      · exact hu'

lemma center_mem_hull_coneFace_iff {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c) {s : Finset E} (hs : s ∈ coneFaces B c) :
    c ∈ convexHull ℝ (s : Set E) ↔ c ∈ s := by
  constructor
  · intro hc
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, _, rfl⟩
    · exact Finset.mem_singleton_self _
    · exact False.elim (center_notMem_radialBoundary a b c
        (hB (B.convexHull_subset_space hs hc)))
    · exact Finset.mem_insert_self _ _
  · intro hc
    exact subset_convexHull ℝ (s : Set E) hc

lemma coneFaces_inter_subset {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    {s t : Finset E} (hs : s ∈ coneFaces B c) (ht : t ∈ coneFaces B c) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  intro x hx
  by_cases hxc : x = c
  · subst x
    exact subset_convexHull ℝ _
      ⟨(center_mem_hull_coneFace_iff a b B c hB hs).mp hx.1,
       (center_mem_hull_coneFace_iff a b B c hB ht).mp hx.2⟩
  have hnotS : s ≠ {c} := by
    intro hh
    apply hxc
    simpa [hh] using hx.1
  have hnotT : t ≠ {c} := by
    intro hh
    apply hxc
    simpa [hh] using hx.2
  have hs' := ((mem_coneFaces_iff B c s).mp hs).resolve_left hnotS
  have ht' := ((mem_coneFaces_iff B c t).mp ht).resolve_left hnotT
  have hcone (u v : Finset E) (hu : u ∈ B.faces) (hv : v ∈ B.faces) :=
    cone_hull_inter a b (B.convexHull_subset_space hu |>.trans hB)
      (B.convexHull_subset_space hv |>.trans hB) (B.inter_subset_convexHull hu hv)
  have hmixed (u v : Finset E) (hu : u ∈ B.faces) (hv : v ∈ B.faces) :=
    cone_hull_inter_boundary a b (B.convexHull_subset_space hu |>.trans hB)
      (B.convexHull_subset_space hv |>.trans hB) (B.inter_subset_convexHull hu hv)
  rcases hs' with hs | ⟨u, hu, rfl⟩ <;> rcases ht' with ht | ⟨v, hv, rfl⟩
  · exact B.inter_subset_convexHull hs ht hx
  · have hh : x ∈ convexHull ℝ ((v : Set E) ∩ s) := by
      rw [← hmixed v s hv hs]
      exact ⟨by simpa only [Finset.coe_insert] using hx.2, hx.1⟩
    exact convexHull_mono (by intro y hy; exact ⟨hy.2, Finset.mem_insert_of_mem hy.1⟩) hh
  · have hh : x ∈ convexHull ℝ ((u : Set E) ∩ t) := by
      rw [← hmixed u t hu ht]
      exact ⟨by simpa only [Finset.coe_insert] using hx.1, hx.2⟩
    exact convexHull_mono (by intro y hy; exact ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩) hh
  · have hh : x ∈ convexHull ℝ (insert c ((u : Set E) ∩ v)) := by
      rw [← hcone u v hu hv]
      simpa only [Finset.coe_insert] using hx
    apply convexHull_mono _ hh
    intro y hy
    rcases hy with rfl | hy
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    · exact ⟨Finset.mem_insert_of_mem hy.1, Finset.mem_insert_of_mem hy.2⟩

def coneComplex {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := coneFaces B c
  isRelLowerSet_faces := coneFaces_down_closed B c
  indep := by
    intro s hs
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, ht, rfl⟩
    · exact affineIndependent_of_subsingleton ℝ _
    · exact B.indep hs
    · have hh := affineIndependent_insert (B.indep ht) (hspan t ht)
      rw [← Finset.coe_insert] at hh
      exact hh
  inter_subset_convexHull := coneFaces_inter_subset a b B c hB

lemma coneComplex_finite {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E))
    (hfinite : B.faces.Finite) : (coneComplex a b B c hB hspan).faces.Finite := by
  exact ((Set.finite_singleton _).union hfinite).union (hfinite.image _)

omit [DecidableEq E] in

lemma center_notMem_affineSpan_boundaryFace {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    {s : Finset E} (hs : s ∈ B.faces) : c ∉ affineSpan ℝ (s : Set E) := by
  have hn := B.nonempty_of_mem_faces hs
  obtain ⟨_, i, hi, hic⟩ := hB (B.convexHull_subset_space hs
    (vertexMean_mem_convexHull hn))
  have hle : ∀ x ∈ s, a i x ≤ b i := fun x hx =>
    (hB (B.subset_space hs hx)).1 i
  have he := (linear_vertexMean_eq_iff (a i) hn hle).mp hi
  intro hc
  exact (ne_of_lt hic) (linear_eq_on_affineSpan (a i) he hc)

lemma mem_coneComplex_space_iff {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E)) (x : E) :
    x ∈ (coneComplex a b B c hB hspan).space ↔
      x = c ∨ ∃ y ∈ B.space, x ∈ segment ℝ c y := by
  classical
  constructor
  · intro hx
    by_cases hxc : x = c
    · exact Or.inl hxc
    right
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, ht, rfl⟩
    · exact (hxc (by simpa using hx)).elim
    · exact ⟨x, B.convexHull_subset_space hs hx, right_mem_segment _ _ _⟩
    · obtain ⟨y, hy, _, _, _, _, hxy⟩ :=
        exists_positive_ray_of_mem_convexHull_insert (by simpa using hx) hxc
      exact ⟨y, B.convexHull_subset_space ht hy, hxy⟩
  · intro hh
    rcases hh with hxc | ⟨y, hy, hx⟩
    · subst x
      apply Geometry.SimplicialComplex.mem_space_iff.mpr
      exact ⟨{c}, (mem_coneFaces_iff B c {c}).mpr (Or.inl rfl), by simp⟩
    · obtain ⟨s, hs, hy⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hy
      apply Geometry.SimplicialComplex.mem_space_iff.mpr
      refine ⟨insert c s, (mem_coneFaces_iff B c _).mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩)), ?_⟩
      apply (convex_convexHull ℝ (insert c s : Finset E)).segment_subset _ _ hx
      · exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
      · exact convexHull_mono (by intro z hz; exact Finset.mem_insert_of_mem hz) hy

omit [DecidableEq E] in
lemma convex_cell {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Convex ℝ (cell a b) := by
  intro x hx y hy r s hr hs hrs i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    r * a i x + s * a i y ≤ r * b i + s * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
        (mul_le_mul_of_nonneg_left (hy i) hs)
    _ = b i := by rw [← add_mul, hrs, one_mul]

lemma coneComplex_space_eq_cell {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DecidableEq V]
    {I : Type*} [Fintype I] (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hbounded : Bornology.IsBounded (cell a b))
    (B : Geometry.SimplicialComplex ℝ V) (c : V) (hc : c ∈ cell a b)
    (hB : B.space = radialBoundary a b c) :
    (coneComplex a b B c hB.subset
      (fun _ hs => center_notMem_affineSpan_boundaryFace a b B c hB.subset hs)).space
      = cell a b := by
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (rfl | ⟨y, hy, hx⟩)
    · exact hc
    · exact (convex_cell a b).segment_subset hc (hB.subset hy).1 hx
  · intro hx
    by_cases hxc : x = c
    · exact Or.inl hxc
    obtain ⟨i, t, _, hy, hi, hic, hxy⟩ :=
      bounded_exists_ray_boundary a b hbounded hc hx hxc
    exact Or.inr ⟨c + t • (x-c), hB.symm.subset ⟨hy, i, hi, hic⟩, hxy⟩

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FiniteCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section Restriction

def restrictComplex (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ B.faces ∧ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨B.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨B.down_closed hs.1 hts ht, fun _ hx => hs.2 (hts hx)⟩
  indep hs := B.indep hs.1
  inter_subset_convexHull hs ht := B.inter_subset_convexHull hs.1 ht.1

lemma restrictComplex_finite (B : Geometry.SimplicialComplex ℝ E) (P : Set E)
    (hB : B.faces.Finite) : (restrictComplex B P).faces.Finite :=
  hB.subset (fun _ hs => hs.1)

def glueComplex (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    Geometry.SimplicialComplex ℝ E where
  faces := B.faces ∪ C.faces
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨B.nonempty_of_mem_faces hs, fun _ ht hn => Or.inl (B.down_closed hs ht hn)⟩
    · exact ⟨C.nonempty_of_mem_faces hs, fun _ ht hn => Or.inr (C.down_closed hs ht hn)⟩
  indep := by
    intro s hs
    exact hs.elim B.indep C.indep
  inter_subset_convexHull := by
    intro s t hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact B.inter_subset_convexHull hs ht
    · exact hcross s hs t ht
    · simpa only [Set.inter_comm] using hcross t ht s hs
    · exact C.inter_subset_convexHull hs ht

lemma glueComplex_finite (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    (hB : B.faces.Finite) (hC : C.faces.Finite) :
    (glueComplex B C hcross).faces.Finite := hB.union hC

lemma glueComplex_space (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    (glueComplex B C hcross).space = B.space ∪ C.space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_union,
    show (glueComplex B C hcross).faces = B.faces ∪ C.faces from rfl]
  aesop

end Restriction

section Trace

def RespectsSet (B : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ s ∈ B.faces, convexHull ℝ (s : Set E) ∩ P = convexHull ℝ ((s : Set E) ∩ P)

lemma restrictComplex_space_of_respects (B : Geometry.SimplicialComplex ℝ E)
    (P : Set E) (h : RespectsSet B P) :
    (restrictComplex B P).space = B.space ∩ P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    refine ⟨B.convexHull_subset_space hs.1 hx, ?_⟩
    have he : (s : Set E) ∩ P = s := Set.inter_eq_left.mpr hs.2
    have hx' : x ∈ convexHull ℝ (s : Set E) ∩ P := by
      rw [h s hs.1, he]
      exact hx
    exact hx'.2
  · rintro ⟨hx, hxP⟩
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    let t := s.filter (· ∈ P)
    have ht : (t : Set E) = (s : Set E) ∩ P := by ext; simp [t]
    have hxt : x ∈ convexHull ℝ (t : Set E) := by
      rw [ht, ← h s hs]
      exact ⟨hx, hxP⟩
    have hne : t.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
    refine Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨t, ⟨B.down_closed hs (Finset.filter_subset _ _) hne, ?_⟩, hxt⟩
    intro y hy
    exact (Finset.mem_filter.mp hy).2

lemma hull_inter_of_supporting_eq (s : Finset E) (P Q : Set E)
    (hsP : convexHull ℝ (s : Set E) ⊆ P) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ P, f x ≤ b) (hface : P ∩ Q = P ∩ {x | f x = b}) :
    convexHull ℝ (s : Set E) ∩ Q = convexHull ℝ ((s : Set E) ∩ Q) := by
  have hiff (x : E) (hx : x ∈ P) : x ∈ Q ↔ f x = b := by
    constructor
    · intro hq
      exact (hface.subset ⟨hx, hq⟩).2
    · intro he
      exact (hface.symm.subset ⟨hx, he⟩).2
  calc
    _ = convexHull ℝ (s : Set E) ∩ {x | f x = b} := by
      ext x
      exact and_congr_right (fun hx => hiff x (hsP hx))
    _ = convexHull ℝ ((s : Set E) ∩ {x | f x = b}) :=
      convexHull_inter_supporting _ f b (fun x hx => hf x (hsP (subset_convexHull _ _ hx)))
    _ = _ := by
      congr 1
      ext x
      exact and_congr_right (fun hx => (hiff x (hsP (subset_convexHull _ _ hx))).symm)

lemma respectsSet_of_supporting_eq (B : Geometry.SimplicialComplex ℝ E)
    (P Q : Set E) (hBP : B.space ⊆ P) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ P, f x ≤ b) (hface : P ∩ Q = P ∩ {x | f x = b}) :
    RespectsSet B Q := by
  intro s hs
  exact hull_inter_of_supporting_eq s P Q ((B.convexHull_subset_space hs).trans hBP)
    f b hf hface

lemma cross_inter_of_respects (B C : Geometry.SimplicialComplex ℝ E)
    (P : Set E) (hB : RespectsSet B P) (hC : C.space ⊆ P)
    (hcommon : restrictComplex B P ≤ C)
    {s t : Finset E} (hs : s ∈ B.faces) (ht : t ∈ C.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  classical
  intro x hx
  let u := s.filter (· ∈ P)
  have hu : (u : Set E) = (s : Set E) ∩ P := by ext; simp [u]
  have hxu : x ∈ convexHull ℝ (u : Set E) := by
    rw [hu, ← hB s hs]
    exact ⟨hx.1, hC (C.convexHull_subset_space ht hx.2)⟩
  have hne : u.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxu⟩)
  have huB : u ∈ (restrictComplex B P).faces :=
    ⟨B.down_closed hs (Finset.filter_subset _ _) hne,
      fun _ hy => (Finset.mem_filter.mp hy).2⟩
  have hi := C.inter_subset_convexHull (hcommon huB) ht ⟨hxu, hx.2⟩
  apply convexHull_mono _ hi
  intro y hy
  exact ⟨(Finset.mem_filter.mp hy.1).1, hy.2⟩

end Trace

section GeneralBoundary

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma mem_radialBoundary_of_supporting {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c x : V} (hc : c ∈ cell a b) (hx : x ∈ cell a b)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ) (hf : ∀ y ∈ cell a b, f y ≤ d)
    (hfc : f c < d) (hfx : f x = d) : x ∈ radialBoundary a b c := by
  have hxc : x ≠ c := by intro he; subst x; exact (ne_of_lt hfc) hfx
  obtain ⟨i, t, ht, hy, hi, hic, _⟩ := bounded_exists_ray_boundary a b hbounded hc hx hxc
  have hfy := hf _ hy
  simp only [map_add, map_smul, map_sub, smul_eq_mul, hfx] at hfy
  have ht1 : t = 1 := by nlinarith
  subst t
  simp only [one_smul, add_sub_cancel] at hi
  exact ⟨hx, i, hi, hic⟩

end GeneralBoundary

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def SupportingFace (Q P : Set V) : Prop :=
  ∃ (f : V →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ P, f x ≤ b) ∧
    Q = P ∩ {x | f x = b}

lemma SupportingFace.subset {Q P : Set V} (h : SupportingFace Q P) : Q ⊆ P := by
  obtain ⟨f, b, _, rfl⟩ := h
  exact Set.inter_subset_left

lemma SupportingFace.eq_convexHull_subset {s : Finset V} {Q : Set V}
    (hQ : SupportingFace Q (convexHull ℝ (s : Set V))) :
    ∃ t : Finset V, t ⊆ s ∧ Q = convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨f, b, hf, he⟩ := hQ
  refine ⟨s.filter (fun x => f x = b), Finset.filter_subset _ _, ?_⟩
  rw [he, convexHull_inter_supporting _ f b (fun x hx => hf x (subset_convexHull ℝ _ hx))]
  congr 1
  ext x
  simp

structure CellData (P : Set V) where
  n : ℕ
  a : Fin n → V →ₗ[ℝ] ℝ
  b : Fin n → ℝ
  eq_cell : P = cell a b
  bounded : Bornology.IsBounded P
  center : V
  center_mem : center ∈ P
  center_support : ∀ (f : V →ₗ[ℝ] ℝ) (d : ℝ), (∀ x ∈ P, f x ≤ d) →
    f center = d → ∀ x ∈ P, f x = d

lemma cell_reindex {I J : Type*} (e : I ≃ J) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    cell (fun j => a (e.symm j)) (fun j => b (e.symm j)) = cell a b := by
  ext x
  constructor
  · intro hx i
    simpa only [Equiv.symm_apply_apply] using hx (e i)
  · intro hx j
    exact hx (e.symm j)

noncomputable def CellData.ofPresentation {I : Type*} [Fintype I]
    (P : Set V) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (he : P = cell a b)
    (hb : Bornology.IsBounded P) (c : V) (hc : c ∈ P)
    (hcs : ∀ (f : V →ₗ[ℝ] ℝ) (d : ℝ), (∀ x ∈ P, f x ≤ d) →
      f c = d → ∀ x ∈ P, f x = d) : CellData P where
  n := Fintype.card I
  a := fun i => a ((Fintype.equivFin I).symm i)
  b := fun i => b ((Fintype.equivFin I).symm i)
  eq_cell := he.trans (cell_reindex (Fintype.equivFin I) a b).symm
  bounded := hb
  center := c
  center_mem := hc
  center_support := hcs

lemma vertexMean_supports {s : Finset V} (hs : s.Nonempty)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ)
    (hf : ∀ x ∈ convexHull ℝ (s : Set V), f x ≤ d)
    (hc : f (vertexMean s) = d) :
    ∀ x ∈ convexHull ℝ (s : Set V), f x = d := by
  have hv := (linear_vertexMean_eq_iff f hs (fun x hx =>
    hf x (subset_convexHull ℝ _ hx))).mp hc
  intro x hx
  exact linear_eq_on_affineSpan f hv (convexHull_subset_affineSpan (s : Set V) hx)

noncomputable def CellData.supportingFace {P Q : Set V} (p : CellData P)
    (s : Finset V) (hs : P = convexHull ℝ (s : Set V))
    (hQ : SupportingFace Q P) (hne : Q.Nonempty) : CellData Q := by
  classical
  refine Classical.choice ?_
  obtain ⟨f, d, hf, he⟩ := hQ
  let a' : Fin p.n ⊕ Bool → V →ₗ[ℝ] ℝ := Sum.elim p.a (fun j => if j then -f else f)
  let b' : Fin p.n ⊕ Bool → ℝ := Sum.elim p.b (fun j => if j then -d else d)
  have hcell : Q = cell a' b' := by
    ext x
    rw [he]
    constructor
    · rintro ⟨hx, hfx⟩ i
      change f x = d at hfx
      rcases i with i | i
      · exact (p.eq_cell ▸ hx) i
      · cases i <;> simp [a', b', hfx]
    · intro hx
      refine ⟨?_, le_antisymm (hx (Sum.inr false)) ?_⟩
      · rw [p.eq_cell]
        exact fun i => hx (Sum.inl i)
      · have hh := hx (Sum.inr true)
        simpa [a', b'] using hh
  have hQ' : SupportingFace Q (convexHull ℝ (s : Set V)) := hs ▸ ⟨f, d, hf, he⟩
  obtain ⟨t, _, ht⟩ := hQ'.eq_convexHull_subset
  have htn : t.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (ht ▸ hne))
  refine ⟨CellData.ofPresentation Q a' b' hcell (p.bounded.subset ?_) (vertexMean t) ?_ ?_⟩
  · exact fun x hx => (he.subset hx).1
  · rw [ht]
    exact vertexMean_mem_convexHull htn
  · intro g c hg heq x hx
    rw [ht] at hg hx
    exact vertexMean_supports htn g c hg heq x hx

lemma CellData.face_subset_boundary {P Q : Set V} (p : CellData P)
    (hQ : SupportingFace Q P) (hproper : Q ≠ P) :
    Q ⊆ radialBoundary p.a p.b p.center := by
  obtain ⟨f, d, hf, hQ⟩ := hQ
  have hc : f p.center < d := lt_of_le_of_ne (hf _ p.center_mem) (by
    intro he
    apply hproper
    rw [hQ]
    exact Set.inter_eq_left.mpr (fun x hx => p.center_support f d hf he x hx))
  intro x hx
  have hPx : x ∈ P := (hQ.subset hx).1
  apply mem_radialBoundary_of_supporting p.a p.b
    (p.eq_cell ▸ p.bounded) (p.eq_cell ▸ p.center_mem) (p.eq_cell ▸ hPx) f d
    (by simpa only [← p.eq_cell] using hf) hc
  exact (hQ.subset hx).2

lemma CellData.boundary_mem_face {P : Set V} (p : CellData P)
    {x : V} (hx : x ∈ radialBoundary p.a p.b p.center) :
    ∃ Q, SupportingFace Q P ∧ Q ≠ P ∧ x ∈ Q := by
  obtain ⟨hxp, i, hi, hic⟩ := hx
  refine ⟨P ∩ {y | p.a i y = p.b i}, ?_, ?_, ?_⟩
  · exact ⟨p.a i, p.b i, fun y hy => (p.eq_cell ▸ hy) i, rfl⟩
  · intro he
    have hc := he.symm.subset p.center_mem
    exact (ne_of_lt hic) hc.2
  · exact ⟨p.eq_cell.symm ▸ hxp, hi⟩

structure FiniteCellFamily (F : Finset (Set V)) : Prop where
  data : ∀ P ∈ F, Nonempty (CellData P)
  faces : ∀ P ∈ F, ∀ Q, SupportingFace Q P → Q.Nonempty → Q ∈ F
  inter : ∀ P ∈ F, ∀ Q ∈ F, SupportingFace (P ∩ Q) P

def familySpace (F : Finset (Set V)) : Set V := {x | ∃ P ∈ F, x ∈ P}

structure CellTriangulation (F : Finset (Set V)) where
  complex : Geometry.SimplicialComplex ℝ V
  finite : complex.faces.Finite
  space : complex.space = familySpace F
  trace : ∀ P ∈ F, RespectsSet complex P
  carrier : ∀ s ∈ complex.faces, ∃ P ∈ F, convexHull ℝ (s : Set V) ⊆ P

lemma CellTriangulation.respects_of_carrier {F : Finset (Set V)}
    (B : CellTriangulation F) (P : Set V)
    (hP : ∀ Q ∈ F, SupportingFace (Q ∩ P) Q) : RespectsSet B.complex P := by
  intro s hs
  obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
  obtain ⟨f, b, hf, he⟩ := hP Q hQ
  exact hull_inter_of_supporting_eq s Q P hsQ f b hf he

noncomputable def CellTriangulation.extend {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P)
    (B : CellTriangulation (F.erase P)) (p : CellData P) : CellTriangulation F := by
  classical
  have hBP : RespectsSet B.complex P := B.respects_of_carrier P (fun Q hQ =>
    hF.inter Q (Finset.mem_of_mem_erase hQ) P hm.1)
  let T := restrictComplex B.complex P
  have hT : T.space = radialBoundary p.a p.b p.center := by
    rw [show T.space = B.complex.space ∩ P from
      restrictComplex_space_of_respects B.complex P hBP, B.space]
    ext x
    constructor
    · rintro ⟨⟨Q, hQ, hxQ⟩, hxP⟩
      have hproper : P ∩ Q ≠ P := by
        intro he
        have hPQ : P ⊆ Q := fun y hy => (he.symm.subset hy).2
        have hQP := hm.2 (Finset.mem_of_mem_erase hQ) hPQ
        exact (Finset.mem_erase.mp hQ).1 (Set.Subset.antisymm hQP hPQ)
      exact p.face_subset_boundary
        (hF.inter P hm.1 Q (Finset.mem_of_mem_erase hQ)) hproper ⟨hxP, hxQ⟩
    · intro hx
      obtain ⟨Q, hQ, hproper, hxQ⟩ := p.boundary_mem_face hx
      exact ⟨⟨Q, Finset.mem_erase.mpr ⟨hproper, hF.faces P hm.1 Q hQ ⟨x, hxQ⟩⟩,
        hxQ⟩, hQ.subset hxQ⟩
  have hspan : ∀ s ∈ T.faces, p.center ∉ affineSpan ℝ (s : Set V) :=
    fun s hs => center_notMem_affineSpan_boundaryFace p.a p.b T p.center hT.subset hs
  let C := coneComplex p.a p.b T p.center hT.subset hspan
  have hC : C.space = P := by
    rw [p.eq_cell]
    exact coneComplex_space_eq_cell p.a p.b (p.eq_cell ▸ p.bounded)
      T p.center (p.eq_cell ▸ p.center_mem) hT
  have hTC : T ≤ C := by
    intro s hs
    exact (mem_coneFaces_iff T p.center s).mpr (Or.inr (Or.inl hs))
  have hcross : ∀ s ∈ B.complex.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set V) ∩ convexHull ℝ (t : Set V) ⊆
        convexHull ℝ ((s : Set V) ∩ (t : Set V)) :=
    fun _ hs _ ht => cross_inter_of_respects B.complex C P hBP hC.subset hTC hs ht
  refine ⟨glueComplex B.complex C hcross, ?_, ?_, ?_, ?_⟩
  · exact glueComplex_finite B.complex C hcross B.finite
      (coneComplex_finite p.a p.b T p.center hT.subset hspan
        (restrictComplex_finite B.complex P B.finite))
  · rw [glueComplex_space, B.space, hC]
    ext x
    constructor
    · rintro (⟨Q, hQ, hxQ⟩ | hxP)
      · exact ⟨Q, Finset.mem_of_mem_erase hQ, hxQ⟩
      · exact ⟨P, hm.1, hxP⟩
    · rintro ⟨Q, hQ, hxQ⟩
      by_cases he : Q = P
      · exact Or.inr (he ▸ hxQ)
      · exact Or.inl ⟨Q, Finset.mem_erase.mpr ⟨he, hQ⟩, hxQ⟩
  · intro Q hQ s hs
    rcases hs with hs | hs
    · by_cases he : Q = P
      · exact he ▸ hBP s hs
      · exact B.trace Q (Finset.mem_erase.mpr ⟨he, hQ⟩) s hs
    · obtain ⟨f, b, hf, he⟩ := hF.inter P hm.1 Q hQ
      exact respectsSet_of_supporting_eq C P Q hC.subset f b hf he s hs
  · intro s hs
    rcases hs with hs | hs
    · obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
      exact ⟨Q, Finset.mem_of_mem_erase hQ, hsQ⟩
    · exact ⟨P, hm.1, (C.convexHull_subset_space hs).trans hC.subset⟩

open scoped Classical

lemma CellTriangulation.mem_extend_faces {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P)
    (B : CellTriangulation (F.erase P)) (p : CellData P) (s : Finset V) :
    s ∈ (B.extend hF hm p).complex.faces ↔
      s ∈ B.complex.faces ∨ s = {p.center} ∨
        ∃ t ∈ B.complex.faces, (t : Set V) ⊆ P ∧ s = insert p.center t := by
  classical
  change s ∈ B.complex.faces ∨ s ∈ coneFaces (restrictComplex B.complex P) p.center ↔ _
  rw [mem_coneFaces_iff]
  constructor
  · rintro (hs | hs | hs | ⟨t, ht, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inl hs.1
    · exact Or.inr (Or.inr ⟨t, ht.1, ht.2, rfl⟩)
  · rintro (hs | hs | ⟨t, ht, htP, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inr ⟨t, ⟨ht, htP⟩, rfl⟩))

lemma CellData.center_mem_iff_subset {P Q : Set V} (p : CellData Q)
    (h : SupportingFace (Q ∩ P) Q) : p.center ∈ P ↔ Q ⊆ P := by
  constructor
  · intro hp
    obtain ⟨f, d, hf, he⟩ := h
    have hc := he.subset ⟨p.center_mem, hp⟩
    intro x hx
    exact (he.symm.subset ⟨hx, p.center_support f d hf hc.2 x hx⟩).2
  · intro h
    exact h p.center_mem

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CellTriangulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section CellVertices

open Filter

open scoped Topology

variable {I : Type*} [Fintype I]

noncomputable def activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) : Finset I :=
  Finset.univ.filter fun i => a i x = b i

lemma mem_activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) (i : I) :
    i ∈ activeConstraints a b x ↔ a i x = b i := by
  classical
  simp [activeConstraints]

lemma exists_extrapolate_mem
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {x y : E}
    (hx : x ∈ cell a b)
    (hactive : activeConstraints a b x = activeConstraints a b y) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ cell a b := by
  have hi (i : I) : ∀ᶠ t : ℝ in 𝓝 0, a i (x + t • (x - y)) ≤ b i := by
    by_cases h : a i x = b i
    · have hyi : a i y = b i := by
        rw [← mem_activeConstraints, ← hactive, mem_activeConstraints]
        exact h
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h, hyi, sub_self,
        mul_zero, add_zero, le_refl]
    · have hlt : a i x < b i := lt_of_le_of_ne (hx i) h
      have hc : Continuous (fun t : ℝ => a i x + t * (a i x - a i y)) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, a i x + t * (a i x - a i y) < b i :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [he] with t ht
      simpa only [map_add, map_smul, map_sub, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x + t • (x - y)) ≤ b i :=
    Filter.eventually_all.mpr hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

lemma activeConstraints_injOn_extremePoints
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Set.InjOn (activeConstraints a b) ((cell a b).extremePoints ℝ) := by
  intro x hx y hy hactive
  obtain ⟨t, ht, hz⟩ := exists_extrapolate_mem a b hx.1 hactive
  have hsum : t + 1 ≠ 0 := by positivity
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨t, 1, ht, by norm_num, ?_⟩
    simp only [smul_add, smul_sub, smul_smul]
    rw [show 1 / (t + 1) * t = t / (t + 1) by ring]
    calc
      _ = (1 / (t + 1) + t / (t + 1)) • x := by module
      _ = x := by rw [← add_div, add_comm 1 t, div_self hsum, one_smul]
  exact (hx.2 hy.1 hz hseg).symm

lemma finite_extremePoints_cell
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ((cell a b).extremePoints ℝ).Finite := by
  classical
  exact Set.Finite.of_injOn (t := Set.univ) (Set.mapsTo_univ _ _)
    (activeConstraints_injOn_extremePoints a b) Set.finite_univ

noncomputable def polyhedronVertices (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Finset E :=
  (finite_extremePoints_cell a b).toFinset

@[simp] lemma mem_polyhedronVertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) :
    x ∈ polyhedronVertices a b ↔ x ∈ (cell a b).extremePoints ℝ :=
  Set.Finite.mem_toFinset _

variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

lemma cell_eq_convexHull_vertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hc : IsCompact (cell a b)) :
    cell a b = convexHull ℝ (polyhedronVertices a b : Set E) := by
  have hv : Convex ℝ (cell a b) := by
    intro x hx y hy r s hr hs hrs i
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      r * a i x + s * a i y ≤ r * b i + s * b i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
          (mul_le_mul_of_nonneg_left (hy i) hs)
      _ = b i := by rw [← add_mul, hrs, one_mul]
  have he : (polyhedronVertices a b : Set E) =
      (cell a b).extremePoints ℝ := by
    ext x
    exact mem_polyhedronVertices a b x
  have h := closure_convexHull_extremePoints hc hv
  rw [← he, ((polyhedronVertices a b).finite_toSet.isClosed_convexHull (𝕜 := ℝ)).closure_eq] at h
  exact h.symm

end CellVertices

section Arrangements

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I] [Fintype J]

omit [Fintype I] in
lemma isClosed_cell (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) : IsClosed (cell a b) := by
  have he : cell a b = ⋂ i, {x | a i x ≤ b i} := by ext x; simp [cell]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (a i).continuous_of_finiteDimensional continuous_const

lemma cell_eq_convexHull_of_bounded (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hb : Bornology.IsBounded (cell a b)) :
    cell a b = convexHull ℝ (polyhedronVertices a b : Set V) :=
  cell_eq_convexHull_vertices a b (Metric.isCompact_of_isClosed_isBounded (isClosed_cell a b) hb)

noncomputable def CellData.ofBounded (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hb : Bornology.IsBounded (cell a b)) (hne : (cell a b).Nonempty) :
    CellData (cell a b) := by
  have he := cell_eq_convexHull_of_bounded a b hb
  have hvn : (polyhedronVertices a b).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (he ▸ hne))
  exact CellData.ofPresentation _ a b rfl hb (vertexMean (polyhedronVertices a b))
    (he ▸ vertexMean_mem_convexHull hvn) (fun f d hf hc x hx =>
      vertexMean_supports hvn f d (he ▸ hf) hc x (he ▸ hx))

end Arrangements

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CanonicalCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section CanonicalCenters

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def canonicalVertices (P : Set V) : Finset V :=
  if h : (P.extremePoints ℝ).Finite then h.toFinset else ∅

noncomputable def canonicalCenter (P : Set V) : V := vertexMean (canonicalVertices P)

lemma coe_canonicalVertices {P : Set V} (hP : (P.extremePoints ℝ).Finite) :
    (canonicalVertices P : Set V) = P.extremePoints ℝ := by
  simp [canonicalVertices, hP]

lemma finite_extremePoints_finiteHull (s : Finset V) :
    ((convexHull ℝ (s : Set V)).extremePoints ℝ).Finite :=
  s.finite_toSet.subset extremePoints_convexHull_subset

lemma finiteHull_eq_canonicalVertices (s : Finset V) :
    convexHull ℝ (s : Set V) =
      convexHull ℝ (canonicalVertices (convexHull ℝ (s : Set V)) : Set V) := by
  have hfin := finite_extremePoints_finiteHull s
  rw [coe_canonicalVertices hfin]
  have hk := closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (s : Set V))
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hk
  exact hk.symm

lemma canonicalCenter_mem_finiteHull {s : Finset V} (hs : s.Nonempty) :
    canonicalCenter (convexHull ℝ (s : Set V)) ∈ convexHull ℝ (s : Set V) := by
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    have hh : (convexHull ℝ (s : Set V)).Nonempty :=
      convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    exact convexHull_nonempty_iff.mp ((finiteHull_eq_canonicalVertices s) ▸ hh)
  exact (finiteHull_eq_canonicalVertices s).symm.subset (vertexMean_mem_convexHull hne)

lemma canonicalCenter_supports_finiteHull {s : Finset V} (hs : s.Nonempty)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ)
    (hf : ∀ x ∈ convexHull ℝ (s : Set V), f x ≤ d)
    (he : f (canonicalCenter (convexHull ℝ (s : Set V))) = d) :
    ∀ x ∈ convexHull ℝ (s : Set V), f x = d := by
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    have hh : (convexHull ℝ (s : Set V)).Nonempty :=
      convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    exact convexHull_nonempty_iff.mp ((finiteHull_eq_canonicalVertices s) ▸ hh)
  intro x hx
  exact vertexMean_supports hne f d ((finiteHull_eq_canonicalVertices s) ▸ hf)
    he x ((finiteHull_eq_canonicalVertices s) ▸ hx)

variable [FiniteDimensional ℝ V]

noncomputable def CellData.canonical {P : Set V} (p : CellData P) : CellData P := by
  let v := polyhedronVertices p.a p.b
  have he : P = convexHull ℝ (v : Set V) := p.eq_cell.trans
    (cell_eq_convexHull_of_bounded p.a p.b (p.eq_cell ▸ p.bounded))
  have hv : v.Nonempty := Finset.coe_nonempty.mp
    (convexHull_nonempty_iff.mp (he ▸ (show P.Nonempty from ⟨p.center, p.center_mem⟩)))
  exact { p with
    center := canonicalCenter P
    center_mem := by rw [he]; exact canonicalCenter_mem_finiteHull hv
    center_support := by
      rw [he]
      exact fun f d hf he => canonicalCenter_supports_finiteHull hv f d hf he }

end CanonicalCenters

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma affineIndependent_map_finset (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) :
    AffineIndependent ℝ ((↑) : s.map ⟨f, hf⟩ → F) := by
  have h := hs.map' f hf
  have he : f ∘ ((↑) : s → E) =
      ((↑) : s.map ⟨f, hf⟩ → F) ∘ (s.equivMap ⟨f, hf⟩) := rfl
  rw [he, affineIndependent_equiv] at h
  exact h

noncomputable def affineImageComplex (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) : Geometry.SimplicialComplex ℝ F where
  faces := (fun s : Finset E => s.map ⟨f, hf⟩) '' K.faces
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    refine ⟨(K.nonempty_of_mem_faces ht).map, ?_⟩
    intro u hut hu
    let t' := t.filter (fun x => f x ∈ u)
    have he : t'.map ⟨f, hf⟩ = u := by
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, t']
      constructor
      · rintro ⟨x, ⟨_, hu⟩, rfl⟩; exact hu
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (hut hy)
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    refine ⟨t', K.down_closed ht (Finset.filter_subset _ _) ?_, he⟩
    exact Finset.map_nonempty.mp (he.symm ▸ hu)
  indep := by
    rintro s ⟨t, ht, rfl⟩
    exact affineIndependent_map_finset f hf (K.indep ht)
  inter_subset_convexHull := by
    rintro s t ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ x hx
    have hconv (a : Finset E) :
        convexHull ℝ (a.map ⟨f, hf⟩ : Set F) = f '' convexHull ℝ (a : Set E) := by
      rw [Finset.coe_map]
      exact (f.image_convexHull (a : Set E)).symm
    rw [hconv, hconv, ← Set.image_inter hf] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hh := K.inter_subset_convexHull hu hv hy
    have hab : ((u.map ⟨f, hf⟩ ∩ v.map ⟨f, hf⟩ : Finset F) : Set F) =
        ((u ∩ v).map ⟨f, hf⟩ : Set F) := by rw [Finset.map_inter]
    rw [← Finset.coe_inter, hab, hconv]
    exact ⟨y, by simpa only [Finset.coe_inter] using hh, rfl⟩

lemma affineImageComplex_finite (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hK : K.faces.Finite) :
    (affineImageComplex K f hf).faces.Finite := hK.image _

lemma affineImageComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) :
    (affineImageComplex K f hf).space = f '' K.space := by
  ext y
  simp only [Geometry.SimplicialComplex.mem_space_iff, affineImageComplex, Set.mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hy⟩
    rw [Finset.coe_map] at hy
    change y ∈ convexHull ℝ (f '' (t : Set E)) at hy
    rw [← f.image_convexHull] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨t, ht, hx⟩, rfl⟩
  · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
    refine ⟨t.map ⟨f, hf⟩, ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    change f x ∈ convexHull ℝ (f '' (t : Set E))
    rw [← f.image_convexHull]
    exact ⟨x, hx, rfl⟩

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CutNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section EmbeddingNaturality

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma RespectsSet.affine_image {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (h : RespectsSet K P) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    RespectsSet (affineImageComplex K f hf) (f '' P) := by
  rintro s ⟨t, ht, rfl⟩
  rw [Finset.coe_map]
  change convexHull ℝ (f '' (t : Set V)) ∩ f '' P =
    convexHull ℝ ((f '' (t : Set V)) ∩ f '' P)
  rw [← f.image_convexHull, ← Set.image_inter hf, h t ht,
    f.image_convexHull, Set.image_inter hf]

noncomputable def CellTriangulation.affineImage {A : Finset (Set V)}
    (B : CellTriangulation A) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    CellTriangulation (A.image fun P => f '' P) where
  complex := affineImageComplex B.complex f hf
  finite := affineImageComplex_finite B.complex f hf B.finite
  space := by
    rw [affineImageComplex_space, B.space]
    ext y
    constructor
    · rintro ⟨x, ⟨P, hP, hx⟩, rfl⟩
      exact ⟨f '' P, Finset.mem_image_of_mem _ hP, x, hx, rfl⟩
    · rintro ⟨Q, hQ, hy⟩
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, ⟨P, hP, hx⟩, rfl⟩
  trace := by
    rintro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact (B.trace P hP).affine_image f hf
  carrier := by
    rintro s ⟨t, ht, rfl⟩
    obtain ⟨P, hP, htP⟩ := B.carrier t ht
    refine ⟨f '' P, Finset.mem_image_of_mem _ hP, ?_⟩
    rw [Finset.coe_map]
    change convexHull ℝ (f '' (t : Set V)) ⊆ f '' P
    rw [← f.image_convexHull]
    exact Set.image_mono htP

end EmbeddingNaturality

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_LocalCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section LocallyFiniteCuts

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev CutPatch (K : Geometry.SimplicialComplex ℝ V) :=
  {A : Finset (Finset V) // ∀ s ∈ A, s ∈ K.faces}

end LocallyFiniteCuts

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GeometricSubcomplexes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Local finiteness passes to a simplexwise finite subdivision. -/

namespace Sparse.Cuts

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

section

open Set Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def geometricRestriction (K : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

def IsMarked (K : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ x ∈ P, ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set E) ∧
    convexHull ℝ (s : Set E) ⊆ P

lemma IsMarked.subset_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : P ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs, _⟩ := hP x hx
  exact K.convexHull_subset_space hs hxs

lemma IsMarked.restriction_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : (geometricRestriction K P).space = P := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact hs.2 hxs
  · intro hx
    obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, hsub⟩, hxs⟩

lemma IsMarked.inter {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∩ Q) := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx.1
  obtain ⟨t, ht, hxt, htQ⟩ := hQ x hx.2
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs, hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxst⟩)
  refine ⟨s ∩ t, K.down_closed hs Finset.inter_subset_left hne, hxst, ?_⟩
  exact subset_inter ((convexHull_mono Finset.inter_subset_left).trans hsP)
    ((convexHull_mono Finset.inter_subset_right).trans htQ)

lemma card_lt_of_generic_hyperplane {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (heq : ∀ x ∈ t, f x = b) (hne : ∃ x ∈ s, f x ≠ b) :
    t.card < s.card := by
  apply ht.card_lt_card_of_affineSpan_lt_affineSpan
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) := by
    apply affineSpan_le.mpr
    exact hst.trans (convexHull_subset_affineSpan (s : Set E))
  apply lt_of_le_of_ne hle
  intro h
  have he : (t : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := heq
  have he' := AffineMap.eqOn_affineSpan he
  obtain ⟨x, hx, hnx⟩ := hne
  apply hnx
  exact he' (by rw [h]; exact subset_affineSpan ℝ (s : Set E) hx)

end

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped Classical

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma coe_filter_mem (s : Finset V) (P : Set V) :
    ((s.filter (· ∈ P) : Finset V) : Set V) = (s : Set V) ∩ P := by
  ext x
  simp

lemma respectsSet_face {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) {s : Finset V} (hs : s ∈ K.faces)
    (hne : (convexHull ℝ (s : Set V) ∩ P).Nonempty) :
    s.filter (· ∈ P) ∈ K.faces := by
  classical
  apply K.down_closed hs (Finset.filter_subset _ _)
  have hh := hP s hs
  rw [hh] at hne
  rw [← coe_filter_mem s P] at hne
  exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne)

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Subdivisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

open Set Finset

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

structure Subdivision (K : Geometry.SimplicialComplex ℝ V) where
  complex : Geometry.SimplicialComplex ℝ V
  space_eq : complex.space = K.space
  carrier : ∀ s ∈ complex.faces, ∃ t ∈ K.faces,
    convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V)
  respects : ∀ s ∈ K.faces, RespectsSet complex (convexHull ℝ (s : Set V))
  finite : ∀ s ∈ K.faces,
    (restrictComplex complex (convexHull ℝ (s : Set V))).faces.Finite

lemma complex_respects_simplex (K : Geometry.SimplicialComplex ℝ V)
    {t : Finset V} (ht : t ∈ K.faces) : RespectsSet K (convexHull ℝ (t : Set V)) := by
  intro s hs
  have hv : (s : Set V) ∩ convexHull ℝ (t : Set V) = (s : Set V) ∩ t := by
    ext x
    constructor
    · rintro ⟨hx,hxt⟩
      have hxv : x ∈ K.vertices := K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
        (Finset.singleton_nonempty _)
      exact ⟨hx,(K.vertex_mem_convexHull_iff hxv ht).mp hxt⟩
    · rintro ⟨hx,hxt⟩
      exact ⟨hx,subset_convexHull ℝ _ hxt⟩
  rw [hv,K.convexHull_inter_convexHull hs ht]

lemma complex_restrict_finite (K : Geometry.SimplicialComplex ℝ V)
    {t : Finset V} (ht : t ∈ K.faces) :
    (restrictComplex K (convexHull ℝ (t : Set V))).faces.Finite := by
  classical
  apply (t.powerset.finite_toSet).subset
  intro s hs
  apply Finset.mem_powerset.mpr
  apply (K.face_subset_face_iff hs.1 ht).mp
  exact convexHull_min hs.2 (convex_convexHull ℝ _)

namespace Subdivision

variable {K : Geometry.SimplicialComplex ℝ V}

def original (K : Geometry.SimplicialComplex ℝ V) : Subdivision K where
  complex := K
  space_eq := rfl
  carrier := fun s hs => ⟨s,hs,subset_rfl⟩
  respects := fun _ hs => complex_respects_simplex K hs
  finite := fun _ hs => complex_restrict_finite K hs

lemma marked (T : Subdivision K) {s : Finset V} (hs : s ∈ K.faces) :
    IsMarked T.complex (convexHull ℝ (s : Set V)) := by
  classical
  intro x hx
  have hxsp : x ∈ T.complex.space := T.space_eq.symm ▸ K.convexHull_subset_space hs hx
  obtain ⟨t,ht,hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxsp
  have he := T.respects s hs t ht
  have hxs : x ∈ convexHull ℝ ((t : Set V) ∩ convexHull ℝ (s : Set V)) := by
    rw [← he]
    exact ⟨hxt,hx⟩
  let u := t.filter (· ∈ convexHull ℝ (s : Set V))
  have hu : u ∈ T.complex.faces := respectsSet_face (T.respects s hs) ht ⟨x,hxt,hx⟩
  refine ⟨u,hu,?_,?_⟩
  · simpa only [u,coe_filter_mem] using hxs
  · apply convexHull_min
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
    · exact convex_convexHull ℝ _

end Subdivision

structure SubdivisionFamily (X : Type*) [TopologicalSpace X]
    (K : Geometry.SimplicialComplex ℝ V) where
  val : X → Subdivision K
  localConstancy : ∀ s ∈ K.faces, IsLocallyConstant
    (fun x => (restrictComplex (val x).complex (convexHull ℝ (s : Set V))).faces)

end

section

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

def Refines (L K : Geometry.SimplicialComplex ℝ V) : Prop :=
  ∃ S : Subdivision K, S.complex = L

lemma refines_self (K : Geometry.SimplicialComplex ℝ V) : Refines K K :=
  ⟨Subdivision.original K,rfl⟩

structure MarkedFamily (T : SubdivisionFamily X K) where
  val : X → Set V
  marked : ∀ x, IsMarked (T.val x).complex (val x)
  localConstancy : ∀ s ∈ K.faces, IsLocallyConstant (fun x =>
    (restrictComplex (geometricRestriction (T.val x).complex (val x))
      (convexHull ℝ (s : Set V))).faces)

def ComponentDiameter (ρ : V → V → ℝ) (P : Set V) (R : ℝ) : Prop :=
  ∀ C : Set V, IsPreconnected C → C ⊆ P →
    ∀ p ∈ C, ∀ q ∈ C, ρ p q ≤ R

def DimensionDrop (T S : Geometry.SimplicialComplex ℝ V) (P Z : Set V) : Prop :=
  ∀ F ∈ T.faces, convexHull ℝ (F : Set V) ⊆ P →
    ∀ E ∈ S.faces, convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) ∩ Z →
      E.card < F.card

structure AdmissibleStep (ρ : V → V → ℝ) (R : ℝ)
    (T : SubdivisionFamily X K) (P : MarkedFamily T) where
  next : SubdivisionFamily X K
  finer : ∀ x, Refines (next.val x).complex (T.val x).complex
  oldMarked : ∀ x, IsMarked (next.val x).complex (P.val x)
  zero : MarkedFamily next
  subset : ∀ x, zero.val x ⊆ P.val x
  dimensionDrop : ∀ x, DimensionDrop (T.val x).complex (next.val x).complex (P.val x) (zero.val x)
  diameter : ∀ x, ComponentDiameter ρ (P.val x \ zero.val x) (2*R)

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Subdivision

variable {K : Geometry.SimplicialComplex ℝ V} (S : Subdivision K)

lemma carrier_in {P : Set V} (hP : RespectsSet K P) {s : Finset V}
    (hs : s ∈ S.complex.faces) (hsp : (s : Set V) ⊆ P) :
    ∃ t ∈ K.faces, (t : Set V) ⊆ P ∧ convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨t,ht,hst⟩ := S.carrier s hs
  have hv := Set.subset_inter ((subset_convexHull ℝ _).trans hst) hsp
  have hne := (S.complex.nonempty_of_mem_faces hs).to_set.mono hv
  refine ⟨t.filter (· ∈ P),respectsSet_face hP ht hne,?_,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · apply convexHull_min _ (convex_convexHull ℝ _)
    simpa only [coe_filter_mem] using (hP t ht ▸ hv)

lemma preserves_respects {P : Set V} (hP : RespectsSet K P) : RespectsSet S.complex P := by
  classical
  intro s hs
  obtain ⟨t,ht,hst⟩ := S.carrier s hs
  by_cases hh : (convexHull ℝ (t : Set V) ∩ P).Nonempty
  · let u := t.filter (· ∈ P)
    have hu : u ∈ K.faces := respectsSet_face hP ht hh
    have he : convexHull ℝ (u : Set V) = convexHull ℝ (t : Set V) ∩ P := by
      simpa only [u,coe_filter_mem] using (hP t ht).symm
    have htrace := S.respects u hu s hs
    have hc : convexHull ℝ (s : Set V) ∩ convexHull ℝ (u : Set V) =
        convexHull ℝ (s : Set V) ∩ P := by
      rw [he,← Set.inter_assoc,Set.inter_eq_left.mpr hst]
    have hv : (s : Set V) ∩ convexHull ℝ (u : Set V) = (s : Set V) ∩ P := by
      rw [he,← Set.inter_assoc,Set.inter_eq_left.mpr ((subset_convexHull ℝ _).trans hst)]
    simpa only [hc,hv] using htrace
  · have hc : convexHull ℝ (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hh ⟨x,hst hx.1,hx.2⟩)
    have hv : (s : Set V) ∩ P = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun x hx => hh ⟨x,hst (subset_convexHull ℝ _ hx.1),hx.2⟩)
    rw [hc,hv,convexHull_empty]

lemma finite_on_respected {P : Set V} (hP : RespectsSet K P)
    (hf : (restrictComplex K P).faces.Finite) : (restrictComplex S.complex P).faces.Finite := by
  have hh : (⋃ t ∈ (restrictComplex K P).faces,
      (restrictComplex S.complex (convexHull ℝ (t : Set V))).faces).Finite :=
    hf.biUnion (fun t ht => S.finite t ht.1)
  apply hh.subset
  intro s hs
  obtain ⟨t,ht,htP,hst⟩ := S.carrier_in hP hs.1 hs.2
  exact Set.mem_iUnion₂.mpr ⟨t,⟨ht,htP⟩,hs.1,(subset_convexHull ℝ _).trans hst⟩

def trans {L : Geometry.SimplicialComplex ℝ V} (T : Subdivision L)
    (h : T.complex = K) : Subdivision L where
  complex := S.complex
  space_eq := S.space_eq.trans (h ▸ T.space_eq)
  carrier := by
    intro s hs
    obtain ⟨t,ht,hst⟩ := S.carrier s hs
    obtain ⟨u,hu,htu⟩ := T.carrier t (h.symm ▸ ht)
    exact ⟨u,hu,hst.trans htu⟩
  respects := fun s hs => S.preserves_respects (h ▸ T.respects s hs)
  finite := fun s hs => S.finite_on_respected (h ▸ T.respects s hs) (h ▸ T.finite s hs)

end Subdivision

lemma Refines.trans {K L M : Geometry.SimplicialComplex ℝ V}
    (hML : Refines M L) (hLK : Refines L K) : Refines M K := by
  obtain ⟨S,rfl⟩ := hML
  obtain ⟨T,hT⟩ := hLK
  exact ⟨S.trans T hT,rfl⟩

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedSubdivisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma Subdivision.carrier_marked {K : Geometry.SimplicialComplex ℝ V}
    (S : Subdivision K) {P : Set V} (hP : IsMarked K P) {E : Finset V}
    (hE : E ∈ S.complex.faces) (hEP : convexHull ℝ (E : Set V) ⊆ P) :
    ∃ F ∈ K.faces, convexHull ℝ (F : Set V) ⊆ P ∧
      convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) := by
  classical
  let c : ℝ := (E.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr
    (S.complex.nonempty_of_mem_faces hE).card_pos)
  have hsum : ∑ x ∈ E, c = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt (inv_pos.mp hc))
  have hb := Sparse.sum_weights_mem_convexHull E (fun _ _ => hc.le) hsum
  obtain ⟨F,hF,hbF,hFP⟩ := hP _ (hEP hb)
  let A := E.filter (· ∈ convexHull ℝ (F : Set V))
  have hbA : (∑ x ∈ E, c • x) ∈ convexHull ℝ (A : Set V) := by
    simpa only [A,coe_filter_mem] using (S.respects F hF E hE ▸
      (show (∑ x ∈ E, c • x) ∈ convexHull ℝ (E : Set V) ∩
        convexHull ℝ (F : Set V) from ⟨hb,hbF⟩))
  have hEA := Sparse.positiveCombination_carrier (S.complex.indep hE)
    (Finset.filter_subset _ _) (fun _ => c) (fun _ _ => hc) hsum hbA
  refine ⟨F,hF,hFP,convexHull_min ?_ (convex_convexHull ℝ _)⟩
  intro x hx
  exact (Finset.mem_filter.mp (hEA hx)).2

structure PointFiltration (K : Geometry.SimplicialComplex ℝ V) (n : ℕ) where
  T : ℕ → Geometry.SimplicialComplex ℝ V
  Z : ℕ → Set V
  top : T n = K
  top_space : Z n = K.space
  marked : ∀ i, i ≤ n → IsMarked (T i) (Z i)
  finer : ∀ i, i < n → Refines (T i) (T (i+1))
  nested : ∀ i, i < n → Z i ⊆ Z (i+1)
  drop : ∀ i, i < n → DimensionDrop (T (i+1)) (T i) (Z (i+1)) (Z i)

namespace PointFiltration

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ} (Q : PointFiltration K n)

lemma refines {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n) : Refines (Q.T j) (Q.T i) := by
  induction i, hji using Nat.le_induction with
  | base => exact refines_self _
  | succ i hji ih => exact ih (by omega) |>.trans (Q.finer i (by omega))

lemma subset {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n) : Q.Z j ⊆ Q.Z i := by
  induction i, hji using Nat.le_induction with
  | base => exact subset_rfl
  | succ i hji ih => exact (ih (by omega)).trans (Q.nested i (by omega))

lemma iterated_drop {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n)
    {F : Finset V} (hF : F ∈ (Q.T i).faces) (_hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z i)
    {E : Finset V} (hE : E ∈ (Q.T j).faces)
    (hEF : convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) ∩ Q.Z j) :
    E.card + (i-j) ≤ F.card := by
  classical
  generalize hd : i-j = d
  induction d using Nat.strong_induction_on generalizing j E with
  | h d ih =>
    by_cases hji' : j = i
    · subst j
      have hcard := (Q.T i).indep hE |>.card_le_card_of_subset_affineSpan
        ((subset_convexHull ℝ _).trans ((hEF.trans Set.inter_subset_left).trans
          (convexHull_subset_affineSpan _)))
      have : d = 0 := by simpa using hd.symm
      simpa [this] using hcard
    · have hj : j < i := by omega
      obtain ⟨S,hS⟩ := Q.finer j (by omega)
      obtain ⟨W,hW⟩ := Q.refines (show j+1 ≤ i by omega) hin
      have hm : IsMarked (Q.T (j+1)) (convexHull ℝ (F : Set V) ∩ Q.Z (j+1)) :=
        (hW ▸ W.marked hF).inter (Q.marked (j+1) (by omega))
      have hEP : convexHull ℝ (E : Set V) ⊆
          convexHull ℝ (F : Set V) ∩ Q.Z (j+1) :=
        Set.subset_inter (hEF.trans Set.inter_subset_left)
          ((hEF.trans Set.inter_subset_right).trans (Q.nested j (by omega)))
      obtain ⟨U,hU,hUP,hEU⟩ := S.carrier_marked hm (hS.symm ▸ hE) hEP
      have hcard := Q.drop j (by omega) U hU (hUP.trans Set.inter_subset_right)
        E hE (Set.subset_inter hEU (hEF.trans Set.inter_subset_right))
      have hrec := ih (i-(j+1)) (by omega) (show j+1 ≤ i by omega) hU hUP rfl
      omega

lemma dimension_bound (hK : ∀ F ∈ K.faces, F.card ≤ n+1) {i : ℕ} (hi : i ≤ n)
    {E : Finset V} (hE : E ∈ (Q.T i).faces) (hEZ : convexHull ℝ (E : Set V) ⊆ Q.Z i) :
    E.card ≤ i+1 := by
  obtain ⟨S,hS⟩ := Q.refines hi le_rfl
  obtain ⟨F,hF,hEF⟩ := S.carrier E (hS.symm ▸ hE)
  have hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z n := by
    rw [Q.top_space]
    exact K.convexHull_subset_space (Q.top ▸ hF)
  have hb := Q.iterated_drop hi le_rfl hF hFZ hE (Set.subset_inter hEF hEZ)
  have hc := hK F (Q.top ▸ hF)
  omega

lemma card_lower_of_mem_zero {i : ℕ} (hi : i ≤ n) {z : V} (hz : z ∈ Q.Z 0)
    {F : Finset V} (hF : F ∈ (Q.T i).faces) (hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z i)
    (hzF : z ∈ convexHull ℝ (F : Set V)) : i+1 ≤ F.card := by
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le i) hi
  have hm : IsMarked (Q.T 0) (convexHull ℝ (F : Set V) ∩ Q.Z 0) :=
    (hS ▸ S.marked hF).inter (Q.marked 0 (Nat.zero_le n))
  obtain ⟨E,hE,_,hEF⟩ := hm z ⟨hzF,hz⟩
  have hb := Q.iterated_drop (Nat.zero_le i) hi hF hFZ hE hEF
  have hc := (Q.T 0).nonempty_of_mem_faces hE |>.card_pos
  omega

end PointFiltration

end

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K S T : Geometry.SimplicialComplex ℝ V}

lemma DimensionDrop.refine {P Z : Set V} (h : DimensionDrop T S P Z)
    (hZ : IsMarked S Z) {L : Geometry.SimplicialComplex ℝ V}
    (hL : Refines L S) (hST : Refines S T) : DimensionDrop T L P Z := by
  obtain ⟨A,rfl⟩ := hL
  obtain ⟨B,rfl⟩ := hST
  intro F hF hFP E hE hEF
  have hm : IsMarked B.complex (convexHull ℝ (F : Set V) ∩ Z) :=
    (B.marked hF).inter hZ
  obtain ⟨C,hC,hCP,hEC⟩ := A.carrier_marked hm hE hEF
  have hcard : E.card ≤ C.card := (A.complex.indep hE).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hEC.trans (convexHull_subset_affineSpan _)))
  exact lt_of_le_of_lt hcard (h F hF hFP C hC hCP)

end

open Set Finset

open scoped Classical Topology

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TransportMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dual transportation metric on finitely supported probability vectors. -/

namespace BassTrace.Sparse

open Finset

structure FinProbability (Y : Type*) where
  coeff : Y →₀ ℝ
  nonneg : ∀ y, 0 ≤ coeff y
  total : coeff.sum (fun _ r => r) = 1

namespace FinProbability

variable {Y : Type*}

@[ext] theorem ext_coeff {p q : FinProbability Y} (h : p.coeff = q.coeff) : p = q := by
  cases p
  cases q
  cases h
  rfl

noncomputable def expectation (p : FinProbability Y) (f : Y → ℝ) : ℝ :=
  p.coeff.sum fun y r => r * f y

lemma expectation_const (p : FinProbability Y) (c : ℝ) :
    p.expectation (fun _ => c) = c := by
  classical
  unfold expectation Finsupp.sum at *
  rw [← Finset.sum_mul, show (∑ y ∈ p.coeff.support, p.coeff y) = 1 from p.total, one_mul]

lemma expectation_sub (p : FinProbability Y) (f g : Y → ℝ) :
    p.expectation (fun y => f y - g y) = p.expectation f - p.expectation g := by
  classical
  simp [expectation, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]

lemma expectation_neg (p : FinProbability Y) (f : Y → ℝ) :
    p.expectation (-f) = - p.expectation f := by
  classical
  simp [expectation, Finsupp.sum]

lemma expectation_mono (p : FinProbability Y) {f g : Y → ℝ} (h : ∀ y, f y ≤ g y) :
    p.expectation f ≤ p.expectation g := by
  classical
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (p.nonneg y)

lemma expectation_nonneg (p : FinProbability Y) {f : Y → ℝ} (h : ∀ y, 0 ≤ f y) :
    0 ≤ p.expectation f := by
  classical
  exact Finset.sum_nonneg fun y _ => mul_nonneg (p.nonneg y) (h y)

lemma abs_expectation_le (p : FinProbability Y) (f : Y → ℝ) :
    |p.expectation f| ≤ p.expectation (fun y => |f y|) := by
  classical
  unfold expectation Finsupp.sum
  calc
    |∑ y ∈ p.coeff.support, p.coeff y * f y|
      ≤ ∑ y ∈ p.coeff.support, |p.coeff y * f y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y ∈ p.coeff.support, p.coeff y * |f y| := by
      congr 1
      funext y
      rw [abs_mul, abs_of_nonneg (p.nonneg y)]

noncomputable def gap (p q : FinProbability Y) (f : Y → ℝ) : ℝ :=
  p.expectation f - q.expectation f

lemma gap_const (p q : FinProbability Y) (c : ℝ) : p.gap q (fun _ => c) = 0 := by
  simp [gap, expectation_const]

lemma gap_sub_const (p q : FinProbability Y) (f : Y → ℝ) (c : ℝ) :
    p.gap q (fun y => f y - c) = p.gap q f := by
  simp only [gap, expectation_sub, expectation_const]
  ring

lemma gap_neg (p q : FinProbability Y) (f : Y → ℝ) :
    p.gap q (-f) = -p.gap q f := by
  simp only [gap, expectation_neg]
  ring

lemma gap_telescope (p q r : FinProbability Y) (f : Y → ℝ) :
    p.gap r f = p.gap q f + q.gap r f := by
  simp only [gap]
  ring

lemma coeff_support_nonempty (p : FinProbability Y) : p.coeff.support.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : p.coeff = 0 := Finsupp.support_eq_empty.mp he
  have ht := p.total
  simp [hz] at ht

lemma gap_bound [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) (o : Y) :
    |p.gap q f| ≤ p.expectation (fun y => dist y o) +
      q.expectation (fun y => dist y o) := by
  rw [← gap_sub_const p q f (f o)]
  unfold gap
  calc
    |p.expectation (fun y => f y - f o) - q.expectation (fun y => f y - f o)|
      ≤ |p.expectation (fun y => f y - f o)| +
        |q.expectation (fun y => f y - f o)| := abs_sub _ _
    _ ≤ p.expectation (fun y => dist y o) + q.expectation (fun y => dist y o) := by
      apply add_le_add
      · apply (p.abs_expectation_le _).trans
        apply p.expectation_mono
        intro y
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul y o
      · apply (q.abs_expectation_le _).trans
        apply q.expectation_mono
        intro y
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul y o

noncomputable def transport [PseudoMetricSpace Y] (p q : FinProbability Y) : ℝ :=
  sSup {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r}

lemma potential_values_nonempty [PseudoMetricSpace Y] (p q : FinProbability Y) :
    {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r}.Nonempty := by
  refine ⟨0, fun _ => 0, (LipschitzWith.const 0).weaken (by norm_num), ?_⟩
  exact gap_const p q 0

lemma potential_values_bddAbove [PseudoMetricSpace Y] (p q : FinProbability Y) :
    BddAbove {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r} := by
  classical
  obtain ⟨o, _⟩ := p.coeff_support_nonempty
  refine ⟨p.expectation (fun y => dist y o) + q.expectation (fun y => dist y o), ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (le_abs_self _).trans (gap_bound p q f hf o)

lemma gap_le_transport [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) : p.gap q f ≤ p.transport q :=
  le_csSup (potential_values_bddAbove p q) ⟨f, hf, rfl⟩

lemma abs_gap_le_transport [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) : |p.gap q f| ≤ p.transport q := by
  apply abs_le.mpr
  constructor
  · have h := gap_le_transport p q (-f) hf.neg
    rw [gap_neg] at h
    linarith
  · exact gap_le_transport p q f hf

lemma transport_nonneg [PseudoMetricSpace Y] (p q : FinProbability Y) :
    0 ≤ p.transport q := by
  simpa [gap_const] using gap_le_transport p q (fun _ => 0) ((LipschitzWith.const 0).weaken (by norm_num))

lemma transport_le [PseudoMetricSpace Y] (p q : FinProbability Y) (b : ℝ)
    (h : ∀ f : Y → ℝ, LipschitzWith 1 f → p.gap q f ≤ b) : p.transport q ≤ b := by
  apply csSup_le (potential_values_nonempty p q)
  rintro r ⟨f, hf, rfl⟩
  exact h f hf

lemma transport_self [PseudoMetricSpace Y] (p : FinProbability Y) : p.transport p = 0 := by
  apply le_antisymm _ (transport_nonneg p p)
  apply transport_le
  intro f _
  simp [gap]

lemma transport_triangle [PseudoMetricSpace Y] (p q r : FinProbability Y) :
    p.transport r ≤ p.transport q + q.transport r := by
  apply transport_le
  intro f hf
  rw [gap_telescope p q r f]
  exact add_le_add (gap_le_transport p q f hf) (gap_le_transport q r f hf)

lemma transport_comm [PseudoMetricSpace Y] (p q : FinProbability Y) :
    p.transport q = q.transport p := by
  suffices ∀ p q : FinProbability Y, p.transport q ≤ q.transport p from
    le_antisymm (this p q) (this q p)
  intro p q
  apply transport_le
  intro f hf
  have h := gap_le_transport q p (-f) hf.neg
  simp only [gap, expectation_neg] at *
  linarith

lemma expectation_vertex_indicator [DecidableEq Y] (p : FinProbability Y) (v : Y) :
    p.expectation (fun y => if y = v then (1 : ℝ) else 0) = p.coeff v := by
  classical
  simp only [expectation, Finsupp.sum, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

lemma coordinate_control [MetricSpace Y] (p q : FinProbability Y)
    (hdiscrete : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) (v : Y) :
    |p.coeff v - q.coeff v| ≤ p.transport q := by
  classical
  let f : Y → ℝ := fun y => if y = v then 1 else 0
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [NNReal.coe_one, one_mul]
    by_cases hy : y = v <;> by_cases hz : z = v
    · simp [f, hy, hz]
    · simpa [f, hy, hz] using hdiscrete y z (fun h => hz (h ▸ hy))
    · simpa [f, hy, hz] using hdiscrete y z (fun h => hy (h.symm ▸ hz))
    · simp [f, hy, hz]
  simpa only [gap, f, expectation_vertex_indicator] using abs_gap_le_transport p q f hf

lemma transport_eq_zero_iff [MetricSpace Y] (p q : FinProbability Y)
    (hdiscrete : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) : p.transport q = 0 ↔ p = q := by
  constructor
  · intro h
    apply ext_coeff
    ext v
    have hv := coordinate_control p q hdiscrete v
    rw [h] at hv
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))
  · rintro rfl
    exact transport_self _

lemma expectation_eq_zero_of_support (p : FinProbability Y) (f : Y → ℝ)
    (hf : ∀ y ∈ p.coeff.support, f y = 0) : p.expectation f = 0 := by
  classical
  unfold expectation Finsupp.sum
  exact Finset.sum_eq_zero fun y hy => by
    change p.coeff y * f y = 0
    rw [hf y hy, mul_zero]

lemma exists_support_le_expectation (p : FinProbability Y) (f : Y → ℝ) :
    ∃ y ∈ p.coeff.support, f y ≤ p.expectation f := by
  classical
  by_contra! h
  have hlt : p.expectation (fun _ => p.expectation f) < p.expectation f := by
    unfold expectation Finsupp.sum
    apply Finset.sum_lt_sum
    · intro y hy
      exact (mul_lt_mul_of_pos_left (h y hy)
        (lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy)))).le
    · obtain ⟨y, hy⟩ := p.coeff_support_nonempty
      exact ⟨y, hy, mul_lt_mul_of_pos_left (h y hy)
        (lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy)))⟩
  rw [expectation_const] at hlt
  exact (lt_irrefl _ hlt)

lemma expectation_distance_support_le [MetricSpace Y] (c p : FinProbability Y) :
    p.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) ≤
      c.transport p := by
  have hc : c.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) = 0 := by
    apply expectation_eq_zero_of_support
    intro y hy
    exact Metric.infDist_zero_of_mem hy
  have hp : 0 ≤ p.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) :=
    p.expectation_nonneg fun _ => Metric.infDist_nonneg
  have h := abs_gap_le_transport c p
    (fun y => Metric.infDist y (c.coeff.support : Set Y))
    (Metric.lipschitz_infDist_pt _)
  simpa only [gap, hc, zero_sub, abs_neg, abs_of_nonneg hp] using h

lemma exists_support_pair_dist_le [MetricSpace Y] (c p : FinProbability Y) :
    ∃ a ∈ c.coeff.support, ∃ v ∈ p.coeff.support, dist a v ≤ c.transport p := by
  obtain ⟨v, hv, hvl⟩ := exists_support_le_expectation p
    (fun y => Metric.infDist y (c.coeff.support : Set Y))
  obtain ⟨a, ha, hva⟩ := c.coeff.support.finite_toSet.isCompact.exists_infDist_eq_dist
    (by simpa using c.coeff_support_nonempty) v
  refine ⟨a, ha, v, hv, ?_⟩
  rw [dist_comm, ← hva]
  exact hvl.trans (expectation_distance_support_le c p)

noncomputable def rho [PseudoMetricSpace Y] (n : ℕ) (p q : FinProbability Y) : ℝ :=
  p.transport q / Real.sqrt (n : ℝ)

lemma rho_triangle [PseudoMetricSpace Y] (n : ℕ) (p q r : FinProbability Y) :
    rho n p r ≤ rho n p q + rho n q r := by
  unfold rho
  rw [← add_div]
  exact div_le_div_of_nonneg_right (transport_triangle p q r) (Real.sqrt_nonneg _)

lemma rho_comm [PseudoMetricSpace Y] (n : ℕ) (p q : FinProbability Y) :
    rho n p q = rho n q p := by rw [rho, rho, transport_comm p q]

lemma sqrt_mul_rho [PseudoMetricSpace Y] {n : ℕ} (hn : 0 < n) (p q : FinProbability Y) :
    Real.sqrt (n : ℝ) * rho n p q = p.transport q := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
  unfold rho
  field_simp

lemma support_distance_rho [MetricSpace Y] {n : ℕ} (hn : 0 < n)
    (c p : FinProbability Y) :
    ∃ a ∈ c.coeff.support, ∃ v ∈ p.coeff.support,
      dist a v ≤ Real.sqrt (n : ℝ) * rho n c p := by
  rw [sqrt_mul_rho hn]
  exact exists_support_pair_dist_le c p

end FinProbability

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AffinePotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite affine branch geometry for the exact transport metric and compatible cuts. -/

namespace BassTrace.Sparse

open Set Filter

open scoped Topology

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

def halfspacePolyhedron (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

noncomputable def activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) : Finset I :=
  Finset.univ.filter fun i => a i x = b i

lemma mem_activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) (i : I) :
    i ∈ activeConstraints a b x ↔ a i x = b i := by
  classical
  simp [activeConstraints]

lemma exists_extrapolate_mem
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {x y : E}
    (hx : x ∈ halfspacePolyhedron a b)
    (hactive : activeConstraints a b x = activeConstraints a b y) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ halfspacePolyhedron a b := by
  have hi (i : I) : ∀ᶠ t : ℝ in 𝓝 0, a i (x + t • (x - y)) ≤ b i := by
    by_cases h : a i x = b i
    · have hyi : a i y = b i := by
        rw [← mem_activeConstraints, ← hactive, mem_activeConstraints]
        exact h
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h, hyi, sub_self,
        mul_zero, add_zero, le_refl]
    · have hlt : a i x < b i := lt_of_le_of_ne (hx i) h
      have hc : Continuous (fun t : ℝ => a i x + t * (a i x - a i y)) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, a i x + t * (a i x - a i y) < b i :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [he] with t ht
      simpa only [map_add, map_smul, map_sub, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x + t • (x - y)) ≤ b i :=
    Filter.eventually_all.mpr hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

lemma activeConstraints_injOn_extremePoints
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Set.InjOn (activeConstraints a b) ((halfspacePolyhedron a b).extremePoints ℝ) := by
  intro x hx y hy hactive
  obtain ⟨t, ht, hz⟩ := exists_extrapolate_mem a b hx.1 hactive
  have hsum : t + 1 ≠ 0 := by positivity
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨t, 1, ht, by norm_num, ?_⟩
    simp only [smul_add, smul_sub, smul_smul]
    rw [show 1 / (t + 1) * t = t / (t + 1) by ring]
    calc
      _ = (1 / (t + 1) + t / (t + 1)) • x := by module
      _ = x := by rw [← add_div, add_comm 1 t, div_self hsum, one_smul]
  exact (hx.2 hy.1 hz hseg).symm

lemma finite_extremePoints_halfspacePolyhedron
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ((halfspacePolyhedron a b).extremePoints ℝ).Finite := by
  classical
  exact Set.Finite.of_injOn (t := Set.univ) (Set.mapsTo_univ _ _)
    (activeConstraints_injOn_extremePoints a b) Set.finite_univ

noncomputable def polyhedronVertices (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Finset E :=
  (finite_extremePoints_halfspacePolyhedron a b).toFinset

@[simp] lemma mem_polyhedronVertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) :
    x ∈ polyhedronVertices a b ↔ x ∈ (halfspacePolyhedron a b).extremePoints ℝ :=
  Set.Finite.mem_toFinset _

section Potential

variable {V : Type*} [Fintype V] [MetricSpace V]

noncomputable def potentialLinear : (V × V) ⊕ Bool → (V → ℝ) →ₗ[ℝ] ℝ
  | .inl (v,w) => LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v - LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) w
  | .inr false => ∑ v : V, LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v
  | .inr true => -∑ v : V, LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v

def potentialBound : (V × V) ⊕ Bool → ℝ
  | .inl (v,w) => dist v w
  | .inr _ => 0

noncomputable def potentialVertices : Finset (V → ℝ) :=
  polyhedronVertices potentialLinear potentialBound

end Potential

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_NormedVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A normed ambient space for finitely supported real vectors. The ℓ² norm controls affine
topology and triangulations; balls use the separately defined transport metric. -/

namespace BassTrace.Sparse

section

variable {Y : Type*}

def vectorEmbedding : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 2 := by
  classical
  exact Finsupp.linearCombination ℝ (fun y => lp.single 2 y 1)

lemma vectorEmbedding_apply (v : Y →₀ ℝ) (y : Y) :
    vectorEmbedding v y = v y := by
  classical
  simp only [vectorEmbedding,Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

lemma vectorEmbedding_injective :
    Function.Injective (vectorEmbedding (Y := Y)) := by
  intro v w h
  ext y
  simpa only [vectorEmbedding_apply] using congrArg (fun f : lp (fun _ : Y => ℝ) 2 => f y) h

scoped instance realFinsuppNormedAddCommGroup : NormedAddCommGroup (Y →₀ ℝ) :=
  NormedAddCommGroup.induced _ _ vectorEmbedding vectorEmbedding_injective

scoped instance realFinsuppNormedSpace : NormedSpace ℝ (Y →₀ ℝ) :=
  NormedSpace.induced ℝ _ _ vectorEmbedding

open scoped BassTrace.Sparse

lemma coordinate_norm_le (v : Y →₀ ℝ) (y : Y) : ‖v y‖ ≤ ‖v‖ := by
  change ‖v y‖ ≤ ‖vectorEmbedding v‖
  rw [← vectorEmbedding_apply v y]
  exact lp.norm_apply_le_norm (by norm_num) _ _

def coordinateCLM (y : Y) : (Y →₀ ℝ) →L[ℝ] ℝ :=
  (Finsupp.lapply y).mkContinuous 1 (fun v => by simpa using coordinate_norm_le v y)

@[simp] lemma coordinateCLM_apply (y : Y) (v : Y →₀ ℝ) : coordinateCLM y v = v y := rfl

end

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ProbabilityGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open Finset

open scoped BassTrace.Sparse

variable {Y : Type*} [MetricSpace Y]

def centerBranchValue (S : Finset Y) (c : FinProbability Y) (l : S → ℝ) : ℝ :=
  ∑ y : S, c.coeff y * l y

def ballBranch (S : Finset Y) (c : FinProbability Y) (n : ℕ) (l : S → ℝ) :
    (Y →₀ ℝ) →L[ℝ] ℝ :=
  ∑ y : S, ((centerBranchValue S c l - l y) / Real.sqrt n) • coordinateCLM (y : Y)

omit [MetricSpace Y] in
lemma ballBranch_apply (S : Finset Y) (c : FinProbability Y) (n : ℕ)
    (l : S → ℝ) (p : Y →₀ ℝ) :
    ballBranch S c n l p = ∑ y : S,
      ((centerBranchValue S c l-l y)/Real.sqrt n) * p y := by
  simp only [ballBranch,_root_.sum_apply,smul_apply,
    coordinateCLM_apply,smul_eq_mul]

end

open Set Finset

open scoped BassTrace.Sparse

section

variable {Y : Type*}

def coefficientSum : (Y →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : Y => (1 : ℝ))

@[simp] lemma coefficientSum_apply (v : Y →₀ ℝ) :
    coefficientSum v = v.sum (fun _ r => r) := by
  simp [coefficientSum,Finsupp.linearCombination_apply]

@[simp] lemma coefficientSum_single (y : Y) (r : ℝ) :
    coefficientSum (Finsupp.single y r) = r := by simp

def probabilitySet (s : Finset Y) : Set (Y →₀ ℝ) :=
  {v | (∀ y, 0 ≤ v y) ∧ coefficientSum v = 1 ∧ v.support ⊆ s}

lemma convex_probabilitySet (s : Finset Y) : Convex ℝ (probabilitySet s) := by
  intro v hv w hw a b ha hb hab
  refine ⟨?_,?_,?_⟩
  · intro y
    change 0 ≤ a * v y + b * w y
    exact add_nonneg (mul_nonneg ha (hv.1 y)) (mul_nonneg hb (hw.1 y))
  · change coefficientSum (a • v + b • w) = 1
    rw [map_add,map_smul,map_smul,hv.2.1,hw.2.1]
    simpa using hab
  · intro y hy
    by_contra h
    have hv0 : v y = 0 := Finsupp.notMem_support_iff.mp (fun hy => h (hv.2.2 hy))
    have hw0 : w y = 0 := Finsupp.notMem_support_iff.mp (fun hy => h (hw.2.2 hy))
    exact (Finsupp.mem_support_iff.mp hy) (by simp [Finsupp.add_apply,Finsupp.smul_apply,hv0,hw0])

lemma single_mem_probabilitySet (s : Finset Y) {y : Y} (hy : y ∈ s) :
    Finsupp.single y (1 : ℝ) ∈ probabilitySet s := by
  classical
  refine ⟨?_, by simp, ?_⟩
  · intro z
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  · simpa using Finset.singleton_subset_iff.mpr hy

lemma sum_single_of_support_subset (s : Finset Y) (v : Y →₀ ℝ)
    (hv : v.support ⊆ s) :
    ∑ y ∈ s, v y • Finsupp.single y (1 : ℝ) = v := by
  classical
  ext z
  simp only [Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,Finsupp.single_apply]
  by_cases hz : z ∈ s
  · simp [hz,eq_comm]
  · have hvz := Finsupp.notMem_support_iff.mp (fun h => hz (hv h))
    simp [hz,hvz,eq_comm]

lemma sum_coeff_of_support_subset (s : Finset Y) (v : Y →₀ ℝ)
    (hv : v.support ⊆ s) : ∑ y ∈ s, v y = coefficientSum v := by
  rw [coefficientSum_apply,Finsupp.sum]
  exact (Finset.sum_subset hv (fun y _ hy => Finsupp.notMem_support_iff.mp hy)).symm

lemma convexHull_single_eq_probabilitySet (s : Finset Y) :
    convexHull ℝ ((fun y : Y => Finsupp.single y (1 : ℝ)) '' (s : Set Y)) =
      probabilitySet s := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨y,hy,rfl⟩
      exact single_mem_probabilitySet s hy
    · exact convex_probabilitySet s
  · intro v hv
    rw [← sum_single_of_support_subset s v hv.2.2]
    apply (convex_convexHull ℝ _).sum_mem
    · exact fun y _ => hv.1 y
    · exact (sum_coeff_of_support_subset s v hv.2.2).trans hv.2.1
    · intro y hy
      exact subset_convexHull ℝ _ ⟨y,hy,rfl⟩

lemma FinProbability.mem_geometric_simplex (p : FinProbability Y) (s : Finset Y) :
    p.coeff ∈ convexHull ℝ
        ((fun y : Y => Finsupp.single y (1 : ℝ)) '' (s : Set Y)) ↔
      p.coeff.support ⊆ s := by
  rw [convexHull_single_eq_probabilitySet]
  exact ⟨fun h => h.2.2,fun h => ⟨p.nonneg,by simpa using p.total,h⟩⟩

lemma probabilitySet_eq (s : Finset Y) :
    probabilitySet s = {v | ∃ p : FinProbability Y, p.coeff = v ∧ p.coeff.support ⊆ s} := by
  ext v
  constructor
  · intro h
    exact ⟨⟨v,h.1,by simpa using h.2.1⟩,rfl,h.2.2⟩
  · rintro ⟨p,rfl,hp⟩
    exact ⟨p.nonneg,by simpa using p.total,hp⟩

end

section

variable {Y : Type*} [DecidableEq Y]

lemma onFinsupp_faces (K : PreAbstractSimplicialComplex Y) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces =
      (fun s : Finset Y => s.image (fun y => Finsupp.single y (1 : ℝ))) '' K.faces := rfl

lemma onFinsupp_space (K : PreAbstractSimplicialComplex Y) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      {v | ∃ p : FinProbability Y, p.coeff = v ∧ p.coeff.support ∈ K.faces} := by
  ext v
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s,hs,hv⟩
    rw [onFinsupp_faces] at hs
    obtain ⟨t,ht,rfl⟩ := hs
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet,probabilitySet_eq] at hv
    obtain ⟨p,hp,hpt⟩ := hv
    exact ⟨p,hp,(K.isRelLowerSet_faces ht).2 hpt p.coeff_support_nonempty⟩
  · rintro ⟨p,rfl,hp⟩
    refine ⟨p.coeff.support.image (fun y => Finsupp.single y (1 : ℝ)),?_,?_⟩
    · exact ⟨p.coeff.support,hp,rfl⟩
    · rw [Finset.coe_image,p.mem_geometric_simplex]

end

variable {Y : Type*} [MetricSpace Y]

@[instance_reducible] def FinProbability.rhoMetric (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) : MetricSpace (FinProbability Y) where
  dist := FinProbability.rho n
  dist_self p := by simp [FinProbability.rho,FinProbability.transport_self]
  dist_comm := FinProbability.rho_comm n
  dist_triangle := FinProbability.rho_triangle n
  eq_of_dist_eq_zero := by
    intro p q hpq
    apply (FinProbability.transport_eq_zero_iff p q hd).mp
    rw [← FinProbability.sqrt_mul_rho hn,hpq,mul_zero]

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GraphRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

section

open scoped BigOperators

open FinProbability

variable {Y : Type*} (Γ : SimpleGraph Y)

@[instance_reducible] def graphMetric (hΓ : Γ.Connected) : MetricSpace Y where
  dist a b := (Γ.dist a b : ℝ)
  dist_self a := by simp
  dist_comm a b := by rw [Γ.dist_comm]
  dist_triangle a b c := by
    exact_mod_cast (hΓ.preconnected a b).dist_triangle_left c
  eq_of_dist_eq_zero {a b} hab := by
    exact (hΓ.preconnected a b).dist_eq_zero_iff.mp (by exact_mod_cast hab)

variable [DecidableEq Y] [Γ.LocallyFinite]

def neighborhood : ℕ → Y → Finset Y
  | 0, a => {a}
  | k+1, a => insert a ((Γ.neighborFinset a).biUnion (neighborhood k))

lemma walk_end_mem_neighborhood {a b : Y} (p : Γ.Walk a b) (k : ℕ)
    (hp : p.length ≤ k) : b ∈ neighborhood Γ k a := by
  induction k generalizing a b with
  | zero =>
    have he : a=b := p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)
    simp [neighborhood,he]
  | succ k ih =>
    cases p with
    | nil => simp [neighborhood]
    | @cons a w b haw p =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      exact ⟨w,(Γ.mem_neighborFinset a w).mpr haw,ih p (by simpa using hp)⟩

lemma dist_le_mem_neighborhood (hΓ : Γ.Connected) {a b : Y} {k : ℕ}
    (hab : Γ.dist a b ≤ k) : b ∈ neighborhood Γ k a := by
  obtain ⟨p,_,hp⟩ := hΓ.exists_path_of_dist a b
  exact walk_end_mem_neighborhood Γ p k (hp ▸ hab)

omit [DecidableEq Y] [Γ.LocallyFinite] in

lemma connected_set_diameter (σ : Finset Y) {n : ℕ} (hcard : σ.card=n+1)
    (hc : (Γ.induce (σ : Set Y)).Connected) {a b : Y} (ha : a∈σ) (hb : b∈σ) :
    Γ.dist a b ≤ n := by
  obtain ⟨p,hp,_⟩ := hc.exists_path_of_dist ⟨a,ha⟩ ⟨b,hb⟩
  have hl := hp.length_lt
  have hl' : p.length < n+1 := by
    calc p.length < _ := hl
         _ = σ.card := Fintype.card_of_subtype σ (fun _ => Iff.rfl)
         _ = n+1 := hcard
  have hdist := SimpleGraph.dist_le (p.map (SimpleGraph.Embedding.induce (G := Γ) (σ : Set Y)).toHom)
  rw [SimpleGraph.Walk.length_map] at hdist
  exact hdist.trans (Nat.le_of_lt_succ hl')

lemma meeting_simplex_vertices (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (c p : FinProbability Y) (σ : Finset Y) (hcard : σ.card=n+1)
    (hc : (Γ.induce (σ : Set Y)).Connected) (hp : p.coeff.support ⊆ σ)
    (s : ℝ) (hs : 0 ≤ s)
    (hball : @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s) :
    σ ⊆ c.coeff.support.biUnion
      (neighborhood Γ (⌊s * Real.sqrt (n : ℝ)⌋₊+n)) := by
  let : MetricSpace Y := graphMetric Γ hΓ
  obtain ⟨a,ha,v,hv,hav⟩ := support_distance_rho hn c p
  have hle : (Γ.dist a v : ℝ) ≤ s * Real.sqrt (n : ℝ) := by
    change (Γ.dist a v : ℝ) ≤ Real.sqrt (n : ℝ) * rho n c p at hav
    calc _ ≤ Real.sqrt (n : ℝ) * rho n c p := hav
         _ ≤ Real.sqrt (n : ℝ) * s := mul_le_mul_of_nonneg_left hball (Real.sqrt_nonneg _)
         _ = _ := mul_comm _ _
  have hnat : Γ.dist a v ≤ ⌊s * Real.sqrt (n : ℝ)⌋₊ :=
    (Nat.le_floor_iff (mul_nonneg hs (Real.sqrt_nonneg _))).mpr hle
  intro w hw
  apply Finset.mem_biUnion.mpr
  refine ⟨a,ha,dist_le_mem_neighborhood Γ hΓ ?_⟩
  exact (hΓ.preconnected a v).dist_triangle_left w |>.trans
    (Nat.add_le_add hnat (connected_set_diameter Γ σ hcard hc (hp hv) hw))

end

open Set Finset

end Sparse.GraphGeometry

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Topology

variable {Y : Type*} [DecidableEq Y] (Γ : SimpleGraph Y) [Γ.LocallyFinite]

def affineRealization (tops : Set (Finset Y)) : Set (Y →₀ ℝ) :=
  ⋃ σ ∈ tops, probabilitySet σ

def affineProbability (tops : Set (Finset Y)) (v : affineRealization tops) : FinProbability Y where
  coeff := v.val
  nonneg := by
    obtain ⟨σ,_,hσ⟩ := Set.mem_iUnion₂.mp v.property
    exact hσ.1
  total := by
    obtain ⟨σ,_,hσ⟩ := Set.mem_iUnion₂.mp v.property
    simpa using hσ.2.1

omit [DecidableEq Y] in
@[simp] lemma affineProbability_coeff (tops : Set (Finset Y)) (v : affineRealization tops) :
    (affineProbability tops v).coeff = v.val := rfl

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_OrbitForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.FinProbability

open Set Finset

variable {Y Z W : Type*}

def push (e : Y ≃ Z) (p : FinProbability Y) : FinProbability Z where
  coeff := Finsupp.equivMapDomain e p.coeff
  nonneg z := p.nonneg (e.symm z)
  total := by
    classical
    change ∑ z ∈ p.coeff.support.map e.toEmbedding, p.coeff (e.symm z) = 1
    rw [Finset.sum_map]
    simpa [Finsupp.sum] using p.total

@[simp] lemma push_coeff_apply (e : Y ≃ Z) (p : FinProbability Y) (z : Z) :
    (push e p).coeff z = p.coeff (e.symm z) := rfl

@[simp] lemma push_refl (p : FinProbability Y) : push (Equiv.refl Y) p = p := by
  ext y
  rfl

@[simp] lemma push_symm_push (e : Y ≃ Z) (p : FinProbability Y) :
    push e.symm (push e p) = p := by
  ext y
  simp

end BassTrace.Sparse.FinProbability

namespace BassTrace.Sparse

open scoped Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

scoped instance probabilityMulAction : MulAction H (FinProbability Y) where
  smul h p := p.push (MulAction.toPerm h)
  one_smul p := by
    ext y
    change p.coeff ((1 : H)⁻¹ • y) = p.coeff y
    simp
  mul_smul h k p := by
    ext y
    change p.coeff ((h * k)⁻¹ • y) = p.coeff (k⁻¹ • (h⁻¹ • y))
    simp [mul_smul]

open scoped BassTrace.Sparse

@[simp] lemma smul_probability_coeff (h : H) (p : FinProbability Y) (y : Y) :
    (h • p).coeff y = p.coeff (h⁻¹ • y) := rfl

end BassTrace.Sparse

namespace BassTrace.Sparse.OrbitForms

open Set Finset

variable {H Y I : Type*} [Group H] [MulAction H Y]

def push (h : H) : (Y →₀ ℝ) ≃ₗ[ℝ] (Y →₀ ℝ) :=
  Finsupp.domLCongr (MulAction.toPerm h)

@[simp] lemma push_apply (h : H) (p : Y →₀ ℝ) (y : Y) :
    push h p y = p (h⁻¹ • y) := by rfl

@[simp] lemma push_one (p : Y →₀ ℝ) : push (1:H) p = p := by ext y; simp

lemma push_mul (h k : H) (p : Y →₀ ℝ) : push (h*k) p = push h (push k p) := by
  ext y
  simp [mul_smul]

@[simp] lemma push_inv_push (h : H) (p : Y →₀ ℝ) : push h⁻¹ (push h p) = p := by
  rw [← push_mul,inv_mul_cancel,push_one]

structure Data (I : Type*) (Y : Type*) where
  form : I → (Y →₀ ℝ) →ₗ[ℝ] ℝ
  support : I → Finset Y
  vanish : ∀ i p, (∀ y ∈ support i, p y = 0) → form i p = 0

variable (d : Data I Y)

def form (j : H × I) : (Y →₀ ℝ) →ₗ[ℝ] ℝ :=
  (d.form j.2).comp (push j.1⁻¹).toLinearMap

lemma form_ne_zero_support {j : H × I} {p : Y →₀ ℝ} (hp : form d j p ≠ 0) :
    ∃ y ∈ d.support j.2, j.1 • y ∈ p.support := by
  by_contra! hh
  apply hp
  apply d.vanish
  intro y hy
  simpa using Finsupp.notMem_support_iff.mp (hh y hy)

variable [IsCancelSMul H Y]

lemma finite_form_ne_zero (i : I) (p : Y →₀ ℝ) :
    {h : H | form d (h,i) p ≠ 0}.Finite := by
  apply (Set.Finite.biUnion (d.support i).finite_toSet (fun y _ =>
    Set.Finite.preimage (fun h _ k _ he => IsCancelSMul.right_cancel h k y he)
      p.support.finite_toSet)).subset
  intro h hh
  obtain ⟨y,hy,hyp⟩ := form_ne_zero_support d hh
  exact Set.mem_iUnion₂.mpr ⟨y,hy,hyp⟩

variable [Fintype I]

lemma finite_relevant (s : Finset (Y →₀ ℝ)) :
    {j : H × I | ∃ p ∈ s, form d j p ≠ 0}.Finite := by
  classical
  have hi : (⋃ i : I, (fun h : H => (h,i)) ''
      (⋃ p ∈ (s : Set (Y →₀ ℝ)), {h : H | form d (h,i) p ≠ 0})).Finite := by
    apply Set.finite_iUnion
    intro i
    exact (Set.Finite.biUnion s.finite_toSet
      (fun p _ => finite_form_ne_zero d i p)).image _
  apply hi.subset
  rintro ⟨h,i⟩ ⟨p,hp,hh⟩
  exact Set.mem_iUnion.mpr ⟨i,h,Set.mem_iUnion₂.mpr ⟨p,hp,hh⟩,rfl⟩

def relevant (s : Finset (Y →₀ ℝ)) : Finset (H × I) := (finite_relevant d s).toFinset

@[simp] lemma mem_relevant (s : Finset (Y →₀ ℝ)) (j : H × I) :
    j ∈ relevant d s ↔ ∃ p ∈ s, form d j p ≠ 0 := by simp [relevant]

end BassTrace.Sparse.OrbitForms

namespace BassTrace.Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse

variable {H Y C : Type*} [Group H] [MulAction H Y] [MetricSpace Y]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

abbrev Index := Σ i : C, ↥(potentialVertices : Finset (S i → ℝ))

def data : OrbitForms.Data (Index S) Y where
  form j := (ballBranch (S j.1) (c j.1) n j.2.val).toLinearMap
  support j := S j.1
  vanish j p hp := by
    rw [ContinuousLinearMap.coe_coe,ballBranch_apply]
    apply Finset.sum_eq_zero
    intro y _
    rw [hp y y.property,mul_zero]

omit [MetricSpace Y] in
lemma push_coeff (h : H) (p : FinProbability Y) :
    OrbitForms.push h p.coeff = (h • p).coeff := by
  ext y
  rfl

end BassTrace.Sparse.BallOrbitForms

namespace BassTrace.Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse

variable {H Y I X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]

variable (d : Data I Y) {t : ℝ} (ht : 0 < t)

variable [TopologicalSpace X] [MulAction H X]

def Equivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    (T : Cuts.SubdivisionFamily X K) : Prop :=
  ∀ (k : H) (x : X) s, s ∈ (T.val x).complex.faces →
    s.map (push k).toEmbedding ∈ (T.val (k • x)).complex.faces

end BassTrace.Sparse.OrbitForms

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BallGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Finite-center selection from compactness of closed original simplices, without a
cocompactness assumption on the continuous ambient space. -/

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*} [DecidableEq Y]

lemma point_exists (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    ∃ p : FinProbability Y, p.coeff = v.val ∧ p.coeff.support ∈ K.faces := by
  exact (show v.val ∈ {w | ∃ p : FinProbability Y, p.coeff=w ∧ p.coeff.support ∈ K.faces} from
    (onFinsupp_space K) ▸ v.property)

def pointProbability (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) : FinProbability Y :=
  Classical.choose (point_exists K v)

lemma pointProbability_coeff (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    (pointProbability K v).coeff = v.val :=
  (Classical.choose_spec (point_exists K v)).1

lemma pointProbability_face (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    (pointProbability K v).coeff.support ∈ K.faces :=
  (Classical.choose_spec (point_exists K v)).2

def supportPatch (K : PreAbstractSimplicialComplex Y) (W : Finset Y) : Set (Y →₀ ℝ) :=
  {v | v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∧ v.support ⊆ W}

end Sparse.GraphGeometry

namespace Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [MetricSpace Y]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

def branches (h : H) (i : C) : Finset (H × Index S) :=
  Finset.univ.image (fun l : ↥(potentialVertices : Finset (S i → ℝ)) => (h,⟨i,l⟩))

def translatedPatch (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) : Set (Y →₀ ℝ) :=
  GraphGeometry.supportPatch K ((S i).map (MulAction.toPerm h).toEmbedding)

end Sparse.BallOrbitForms

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

def realizationDistance (n : ℕ) (p q : Y →₀ ℝ) : ℝ :=
  if hp : p ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
    if hq : q ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n
        (pointProbability K ⟨p,hp⟩) (pointProbability K ⟨q,hq⟩)
    else 0
  else 0

omit [Γ.LocallyFinite] [MetricSpace Y] in
lemma realizationDistance_apply (n : ℕ) (p q : FinProbability Y)
    (hp : p.coeff.support ∈ K.faces) (hq : q.coeff.support ∈ K.faces) :
    realizationDistance Γ hΓ K n p.coeff q.coeff =
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n p q := by
  have hp' : p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (onFinsupp_space K).symm ▸ ⟨p,rfl,hp⟩
  have hq' : q.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (onFinsupp_space K).symm ▸ ⟨q,rfl,hq⟩
  simp only [realizationDistance,dite_eq_left hp',dite_eq_left hq']
  congr 1 <;> apply FinProbability.ext_coeff <;> exact pointProbability_coeff K _

end

end Sparse.GraphGeometry

namespace Sparse.OrbitForms

open scoped BassTrace.Sparse

variable {H Y X : Type*} [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X]

def MarkedEquivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    {T : Cuts.SubdivisionFamily X K} (P : Cuts.MarkedFamily T) : Prop :=
  ∀ (k : H) (x : X) v, v ∈ P.val x → push k v ∈ P.val (k • x)

end Sparse.OrbitForms

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AdmissibleCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.OrbitForms

open Set Finset

variable {H Y X : Type*} [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X]

structure MarkedPair (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)) where
  T : Cuts.SubdivisionFamily X K
  P : Cuts.MarkedFamily T
  equivariant : Equivariant (H := H) T
  markedEquivariant : MarkedEquivariant (H := H) P

structure SeparatingFiltration (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ))
    (ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ) (R : ℝ) (n : ℕ) where
  pair : ℕ → MarkedPair (H := H) (X := X) K
  top : ∀ x, ((pair n).T.val x).complex = K
  top_space : ∀ x, (pair n).P.val x = K.space
  finer : ∀ i, i < n → ∀ x,
    Cuts.Refines (((pair i).T.val x).complex) (((pair (i+1)).T.val x).complex)
  nested : ∀ i, i < n → ∀ x, (pair i).P.val x ⊆ (pair (i+1)).P.val x
  drop : ∀ i, i < n → ∀ x,
    Cuts.DimensionDrop (((pair (i+1)).T.val x).complex) (((pair i).T.val x).complex)
      ((pair (i+1)).P.val x) ((pair i).P.val x)
  diameter : ∀ i, i < n → ∀ x,
    Cuts.ComponentDiameter ρ ((pair (i+1)).P.val x \ (pair i).P.val x) (2*R)

def SeparatingFiltration.point {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ} {n : ℕ}
    (Q : SeparatingFiltration (H := H) (X := X) K ρ R n) (x : X) :
    Cuts.PointFiltration K n where
  T := fun i => ((Q.pair i).T.val x).complex
  Z := fun i => (Q.pair i).P.val x
  top := Q.top x
  top_space := Q.top_space x
  marked := fun i _ => (Q.pair i).P.marked x
  finer := fun i hi => Q.finer i hi x
  nested := fun i hi => Q.nested i hi x
  drop := fun i hi => Q.drop i hi x

end Sparse.OrbitForms

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.Cuts

open Set Finset MeasureTheory

open scoped ENNReal

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

variable {T : SubdivisionFamily X K} (P : MarkedFamily T)

lemma MarkedFamily.trace_space (s : Finset V) (hs : s ∈ K.faces) (x : X) :
    (restrictComplex (geometricRestriction (T.val x).complex (P.val x))
      (convexHull ℝ (s : Set V))).space = P.val x ∩ convexHull ℝ (s : Set V) := by
  rw [restrictComplex_space_of_respects, (P.marked x).restriction_space]
  intro t ht
  exact (T.val x).respects s hs t ht.1

end Sparse.Cuts

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical Pointwise

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

def simplexVertices (s : Finset Y) : Finset (Y →₀ ℝ) :=
  s.image (fun y => Finsupp.single y (1 : ℝ))

def SourceTop (K : PreAbstractSimplicialComplex Y) (n : ℕ) :=
  {s : Finset Y // s ∈ K.faces ∧ s.card=n+1}

end

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ZeroStrata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

variable (hK : ∀ s∈K.faces,s.card≤n+1)

include hK in
lemma zero_inter_simplex_finite (σ : SourceTop K n) (x : X) :
    ((Q.pair 0).P.val x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))).Finite := by
  let L := Cuts.restrictComplex (Cuts.geometricRestriction ((Q.pair 0).T.val x).complex
    ((Q.pair 0).P.val x)) (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))
  have hs : simplexVertices σ.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces :=
    ⟨σ.val,σ.property.1,rfl⟩
  have hfin : L.faces.Finite := (((Q.pair 0).T.val x).finite _ hs).subset
    (fun t ht=>⟨ht.1.1,ht.2⟩)
  have hf : (⋃ t∈L.faces,(t : Set (Y →₀ ℝ))).Finite :=
    hfin.biUnion (fun t _=>t.finite_toSet)
  apply hf.subset
  intro v hv
  have hvL : v∈L.space := by
    change v∈(Cuts.restrictComplex (Cuts.geometricRestriction ((Q.pair 0).T.val x).complex
      ((Q.pair 0).P.val x)) (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).space
    rw [(Q.pair 0).P.trace_space _ hs]
    exact hv
  obtain ⟨t,ht,hvt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hvL
  have hc : t.card≤0+1 := (Q.point x).dimension_bound
    (by rintro _ ⟨s,hs,rfl⟩; exact Finset.card_image_le.trans (hK s hs))
    (Nat.zero_le n) ht.1.1 ht.1.2
  obtain ⟨w,rfl⟩ := Finset.card_eq_one.mp (by
    exact Nat.le_antisymm hc (L.nonempty_of_mem_faces ht).card_pos)
  have he : v=w := by simpa using hvt
  exact Set.mem_iUnion₂.mpr ⟨{w},ht,by simp [he]⟩

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FaceFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.Cuts

open Set Finset

open scoped Classical

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace PointFiltration

variable (Q : PointFiltration K n)

def FinalFace := {F : Finset V // F∈(Q.T 0).faces}

lemma final_mean_in_top (F : Q.FinalFace) : vertexMean F.val∈Q.Z n := by
  rw [Q.top_space]
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le n) le_rfl
  have hF : F.val∈S.complex.faces := hS.symm ▸ F.property
  have hh := S.complex.convexHull_subset_space hF
    (vertexMean_mem_convexHull (S.complex.nonempty_of_mem_faces hF))
  rw [S.space_eq,Q.top] at hh
  exact hh

lemma exists_face_level (F : Q.FinalFace) : ∃ i,i≤n ∧ vertexMean F.val∈Q.Z i :=
  ⟨n,le_rfl,Q.final_mean_in_top F⟩

def faceLevel (F : Q.FinalFace) : ℕ := Nat.find (Q.exists_face_level F)

lemma faceLevel_le (F : Q.FinalFace) : Q.faceLevel F≤n :=
  (Nat.find_spec (Q.exists_face_level F)).1

lemma mean_mem_faceLevel (F : Q.FinalFace) : vertexMean F.val∈Q.Z (Q.faceLevel F) :=
  (Nat.find_spec (Q.exists_face_level F)).2

lemma mean_notMem_below_level (F : Q.FinalFace) {i : ℕ} (hi : i<Q.faceLevel F) :
    vertexMean F.val∉Q.Z i := by
  intro h
  exact Nat.not_lt_of_ge (Nat.find_min' (Q.exists_face_level F)
    ⟨hi.le.trans (Q.faceLevel_le F),h⟩) hi

def below (i : ℕ) : Set V := if i=0 then ∅ else Q.Z (i-1)

def stratum (i : ℕ) : Set V := Q.Z i \ Q.below i

def faceComponent (F : Q.FinalFace) : Set V :=
  connectedComponentIn (Q.stratum (Q.faceLevel F)) (vertexMean F.val)

lemma mean_mem_stratum (F : Q.FinalFace) :
    vertexMean F.val∈Q.stratum (Q.faceLevel F) := by
  refine ⟨Q.mean_mem_faceLevel F,?_⟩
  unfold below
  split_ifs with h
  · simp
  · exact Q.mean_notMem_below_level F (by omega)

lemma mean_mem_component (F : Q.FinalFace) : vertexMean F.val∈Q.faceComponent F :=
  mem_connectedComponentIn (Q.mean_mem_stratum F)

lemma faceComponent_subset (F : Q.FinalFace) : Q.faceComponent F⊆Q.stratum (Q.faceLevel F) :=
  connectedComponentIn_subset _ _

end PointFiltration

end Sparse.Cuts

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

variable (hK : ∀ s∈K.faces,s.card≤n+1)

include hK in
lemma zero_support_top (x : X) {v : Y →₀ ℝ}
    (hv : v∈(Q.pair 0).P.val x) : v.support∈K.faces ∧ v.support.card=n+1 := by
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hv
  let p := GraphGeometry.pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := GraphGeometry.pointProbability_coeff K _
  have hs : v.support∈K.faces := hp ▸ GraphGeometry.pointProbability_face K ⟨v,hvK⟩
  have hf : simplexVertices v.support∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := ⟨_,hs,rfl⟩
  have hmem : v∈convexHull ℝ (simplexVertices v.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  have hl := (Q.point x).card_lower_of_mem_zero (i := n) le_rfl hv
    (show simplexVertices v.support∈((Q.point x).T n).faces by
      change _∈((Q.pair n).T.val x).complex.faces
      rw [Q.top]; exact hf)
    (show convexHull ℝ (simplexVertices v.support : Set (Y →₀ ℝ))⊆(Q.point x).Z n by
      change _⊆(Q.pair n).P.val x
      rw [Q.top_space]
      exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space hf) hmem
  exact ⟨hs,le_antisymm (hK _ hs) (hl.trans Finset.card_image_le)⟩

include hK in
lemma zero_isDiscrete (x : X) : IsDiscrete ((Q.pair 0).P.val x) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro p hp
  let σ : SourceTop K n := ⟨p.support,zero_support_top Q hK x hp⟩
  let U : Set (Y →₀ ℝ) := ⋂ y : p.support,{q | q y.val≠0}
  have hU : IsOpen U := isOpen_iInter_of_finite fun y=>isOpen_ne.preimage
    (coordinateCLM y.val).continuous
  have hpU : p∈U := Set.mem_iInter.mpr fun y=>Finsupp.mem_support_iff.mp y.property
  let A := (Q.pair 0).P.val x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))
  have hA : A.Finite := zero_inter_simplex_finite Q hK σ x
  have hsub : U∩(Q.pair 0).P.val x⊆A := by
    rintro q ⟨hqU,hq⟩
    have hs : p.support⊆q.support := fun y hy=>Finsupp.mem_support_iff.mpr
      (Set.mem_iInter.mp hqU ⟨y,hy⟩)
    have he : p.support=q.support := Finset.eq_of_subset_of_card_le hs (by
      rw [(zero_support_top Q hK x hp).2,(zero_support_top Q hK x hq).2])
    have hqK : q∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
      ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hq
    let r := GraphGeometry.pointProbability K ⟨q,hqK⟩
    refine ⟨hq,?_⟩
    change q∈convexHull ℝ (simplexVertices p.support : Set (Y →₀ ℝ))
    rw [show q=r.coeff from (GraphGeometry.pointProbability_coeff K ⟨q,hqK⟩).symm,
      simplexVertices,Finset.coe_image,r.mem_geometric_simplex]
    rw [GraphGeometry.pointProbability_coeff K ⟨q,hqK⟩]
    exact he.symm.subset
  refine ⟨U\(A\{p}),hU.sdiff (hA.sdiff.isClosed),?_⟩
  ext q
  constructor
  · rintro ⟨⟨hqu,hqa⟩,hq⟩
    by_contra hne
    exact hqa ⟨hsub ⟨hqu,hq⟩,hne⟩
  · intro hq
    have he : q=p := hq
    subst q
    exact ⟨⟨hpU,fun h=>h.2 rfl⟩,hp⟩

include hK in
lemma zero_component_subsingleton (x : X) (p : Y →₀ ℝ) :
    (connectedComponentIn ((Q.pair 0).P.val x) p).Subsingleton :=
  (isPreconnected_connectedComponentIn).isDiscrete_iff_subsingleton.mp
    ((zero_isDiscrete Q hK x).mono (connectedComponentIn_subset _ _))

end Sparse

namespace Sparse.GraphGeometry

open Set Finset

open Cuts.PointFiltration

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [DecidableEq Y] [Γ.LocallyFinite] in
include hK in
lemma original_card_bound : ∀ s∈K.faces,s.card≤n+1 := by
  intro s hs
  obtain ⟨σ,_,hst,hc,_⟩ := hK s hs
  exact (Finset.card_le_card hst).trans_eq hc

omit [Γ.LocallyFinite] in
lemma faceComponent_mem_space (x : X) (F : (Q.point x).FinalFace)
    {p : Y →₀ ℝ} (hp : p∈(Q.point x).faceComponent F) :
    p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  have hh := ((Q.point x).faceComponent_subset F hp).1
  have htop := (Q.point x).subset ((Q.point x).faceLevel_le F) le_rfl hh
  exact (Q.top_space x) ▸ htop

omit [Γ.LocallyFinite] in
include hK in
lemma faceComponent_distance (hR : 0≤R) (x : X) (F : (Q.point x).FinalFace)
    {p q : Y →₀ ℝ} (hp : p∈(Q.point x).faceComponent F)
    (hq : q∈(Q.point x).faceComponent F) :
    realizationDistance Γ hΓ K n p q≤2*R := by
  by_cases hz : (Q.point x).faceLevel F=0
  · have he : (Q.point x).faceComponent F=
        connectedComponentIn ((Q.pair 0).P.val x) (Cuts.vertexMean F.val) := by
      simp only [faceComponent,hz,stratum,below,ite_true, if_true,Set.sdiff_empty]
      rfl
    have heq : p=q := (zero_component_subsingleton Q (original_card_bound Γ hK) x _) (he ▸ hp) (he ▸ hq)
    subst q
    have hr : realizationDistance Γ hΓ K n p p=0 := by
      simp [realizationDistance,FinProbability.rho,FinProbability.transport_self]
    rw [hr]
    positivity
  · have hi : (Q.point x).faceLevel F-1<n := by
      have := (Q.point x).faceLevel_le F
      omega
    apply Q.diameter _ hi x ((Q.point x).faceComponent F)
      (isPreconnected_connectedComponentIn) ?_ p hp q hq
    have he : (Q.point x).stratum ((Q.point x).faceLevel F)=
        (Q.pair ((Q.point x).faceLevel F-1+1)).P.val x\
          (Q.pair ((Q.point x).faceLevel F-1)).P.val x := by
      have hi' : (Q.point x).faceLevel F-1+1=(Q.point x).faceLevel F := by omega
      rw [hi']
      simp only [stratum,below,ite_eq_right hz]
      rfl
    exact he ▸ (Q.point x).faceComponent_subset F

def labelWindow (n : ℕ) (R : ℝ) (s : Finset Y) : Finset Y :=
  s.biUnion (neighborhood Γ (⌊(2*R)*Real.sqrt (n : ℝ)⌋₊+n))

include hK in
lemma component_support_subset (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))
    {v : Y →₀ ℝ} (hv : v∈(Q.point x).faceComponent F) :
    v.support⊆labelWindow Γ n R s := by
  let p := pointProbability K ⟨Cuts.vertexMean F.val,
    faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)⟩
  let q := pointProbability K ⟨v,faceComponent_mem_space Γ hΓ Q x F hv⟩
  have hp : p.coeff=Cuts.vertexMean F.val := pointProbability_coeff K _
  have hq : q.coeff=v := pointProbability_coeff K _
  obtain ⟨τ,hτ,hqτ,hcard,hconn⟩ := hK q.coeff.support (pointProbability_face K _)
  have hdist : @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n p q≤2*R := by
    rw [← realizationDistance_apply Γ hΓ K n p q (pointProbability_face K _) (pointProbability_face K _),hp,hq]
    exact faceComponent_distance Γ hΓ Q hK hR x F ((Q.point x).mean_mem_component F) hv
  have hmem := meeting_simplex_vertices Γ hΓ hn p q τ hcard hconn hqτ (2*R)
    (by positivity) hdist
  have hps : p.coeff.support⊆s := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex] at hFs
    exact hFs
  rw [← hq]
  exact hqτ.trans (hmem.trans (Finset.biUnion_subset_biUnion_of_subset_left _ hps))

end Sparse.GraphGeometry

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

def supportVertices (U : Set (Y →₀ ℝ)) : Set Y :=
  {y | ∃p∈U,y∈p.support}

variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hK in
lemma componentSupport_subset (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    supportVertices ((Q.point x).faceComponent F)⊆
      (GraphGeometry.labelWindow Γ n R s : Set Y) := by
  rintro y ⟨p,hp,hy⟩
  exact GraphGeometry.component_support_subset Γ hΓ Q hK hn hR x F s hFs hp hy

include hK in
lemma componentSupport_finite (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) :
    (supportVertices ((Q.point x).faceComponent F)).Finite := by
  have hmK := GraphGeometry.faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)
  let p := GraphGeometry.pointProbability K ⟨Cuts.vertexMean F.val,hmK⟩
  have hp : p.coeff=Cuts.vertexMean F.val := GraphGeometry.pointProbability_coeff K _
  have hms : Cuts.vertexMean F.val∈convexHull ℝ
      (simplexVertices p.coeff.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  exact (Finset.finite_toSet (GraphGeometry.labelWindow Γ n R p.coeff.support)).subset
    (componentSupport_subset Γ hΓ Q hK hn hR x F p.coeff.support hms)

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.FiniteAverage

open Set Finset MeasureTheory

open scoped Classical

noncomputable section

section AlgebraicNorm

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

abbrev BIndex := Module.Free.ChooseBasisIndex ℝ V

def embedding : V →ₗ[ℝ] lp (fun _ : BIndex V=>ℝ) 2 :=
  (Finsupp.linearCombination ℝ (fun i=>lp.single 2 i 1)).comp
    (Module.Free.chooseBasis ℝ V).repr.toLinearMap

lemma embedding_apply (v : V) (i : BIndex V) :
    embedding V v i=(Module.Free.chooseBasis ℝ V).repr v i := by
  simp only [embedding,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,lp.coeFn_smul,
    Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

lemma embedding_injective : Function.Injective (embedding V) := by
  intro v w h
  apply (Module.Free.chooseBasis ℝ V).repr.injective
  ext i
  simpa only [embedding_apply] using congrArg (fun f : lp (fun _ : BIndex V=>ℝ) 2=>f i) h

abbrev algebraicNormedGroup : NormedAddCommGroup V :=
  NormedAddCommGroup.induced _ _ (embedding V) (embedding_injective V)

abbrev algebraicNormedSpace : letI := algebraicNormedGroup V; NormedSpace ℝ V :=
  NormedSpace.induced ℝ _ _ (embedding V)

end AlgebraicNorm

variable {X V W : Type*} [MeasurableSpace X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

variable (μ : Measure X)

def average (f : SimpleFunc X V) : V :=
  ∑v∈f.range, μ.real (f⁻¹' {v}) • v

lemma average_add [IsFiniteMeasure μ] (f g : SimpleFunc X V) :
    average μ (f+g)=average μ f+average μ g := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  simpa only [average,SimpleFunc.integral_eq] using
    SimpleFunc.integral_add (f.integrable_of_isFiniteMeasure) (g.integrable_of_isFiniteMeasure)

lemma average_map [IsFiniteMeasure μ] (L : V →ₗ[ℝ] W) (f : SimpleFunc X V) :
    average μ (f.map L)=L (average μ f) := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  let :=  algebraicNormedGroup W
  let :=  algebraicNormedSpace W
  rw [average,← SimpleFunc.integral_eq,
    SimpleFunc.map_integral f L f.integrable_of_isFiniteMeasure L.map_zero]
  simp only [average,map_sum,map_smul]

section LocallyConstant

variable [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]

variable {A : Type*}

def ofLocallyConstant (f : X → A) (hf : IsLocallyConstant f) : SimpleFunc X A where
  toFun := f
  measurableSet_fiber' v := (hf.isClopen_fiber v).isOpen.measurableSet
  finite_range' := hf.range_finite

@[simp] lemma ofLocallyConstant_apply (f : X → A) (hf : IsLocallyConstant f) (x : X) :
    ofLocallyConstant f hf x=f x := rfl

end LocallyConstant

end

end BassTrace.FiniteAverage

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ClosedPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Paths

open scoped BigOperators

section

variable {G ι : Type*} [Group G] [Fintype ι]

abbrev GroupMatrix := Matrix ι ι (MonoidAlgebra ℂ G)

abbrev ScalarMatrix := Matrix ι ι ℂ

def coefficient (e : GroupMatrix (G := G) (ι := ι)) (s : G) : ScalarMatrix (ι := ι) :=
  fun i j => (e i j).coeff s

def support (e : GroupMatrix (G := G) (ι := ι)) : Finset G := by
  classical
  exact Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (e i j).coeff.support

omit [Group G] in
lemma mem_support (e : GroupMatrix (G := G) (ι := ι)) (s : G) :
    s ∈ support e ↔ coefficient e s ≠ 0 := by
  classical
  simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finsupp.mem_support_iff]
  constructor
  · rintro ⟨i,j,h⟩ he
    exact h (congrFun (congrFun he i) j)
  · intro h
    by_contra he
    apply h
    ext i j
    by_contra hij
    exact he ⟨i,j,hij⟩

def kernel (e : GroupMatrix (G := G) (ι := ι)) (h k : G) : ScalarMatrix (ι := ι) :=
  coefficient e (h⁻¹*k)

end

section

variable {G : Type*} [Group G]

def pathSetoid (g : G) (n : ℕ) : Setoid (Fin (n+1) → G) where
  r h k := ∃ c : Subgroup.centralizer ({g} : Set G), ∀ i, (c : G)*h i = k i
  iseqv := ⟨fun h => ⟨1, by simp⟩, by
    rintro h k ⟨c,hc⟩
    refine ⟨c⁻¹, fun i => ?_⟩
    rw [← hc i]
    simp,
    by
    rintro h k l ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨d*c, fun i => ?_⟩
    change ((d:G)*(c:G))*h i = l i
    rw [mul_assoc,hc,hd]⟩

abbrev Orbit (g : G) (n : ℕ) := Quotient (pathSetoid g n)

def increment (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin (n+1)) : G :=
  (h i)⁻¹ * (if i = Fin.last n then g*h 0 else h (finRotate (n+1) i))

lemma increment_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    increment g n h i.castSucc = (h i.castSucc)⁻¹*h i.succ := by
  simp [increment,Fin.castSucc_ne_last]

lemma increment_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    increment g n h (Fin.last n) = (h (Fin.last n))⁻¹*g*h 0 := by
  simp [increment,mul_assoc]

lemma increment_invariant (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (h : Fin (n+1) → G) :
    increment g n (fun i => c*h i) = increment g n h := by
  funext i
  have hc := Subgroup.mem_centralizer_singleton_iff.mp c.property
  simp only [increment]
  split_ifs
  · rw [← mul_assoc g, ← hc, mul_assoc (c:G)]
    simp [mul_assoc]
  · simp [mul_assoc]

lemma increment_eq_imp_related (g : G) (n : ℕ) (h k : Fin (n+1) → G)
    (he : increment g n h = increment g n k) : pathSetoid g n h k := by
  let c : G := k 0*(h 0)⁻¹
  have hk (i : Fin (n+1)) : k i = c*h i := by
    induction i using Fin.induction with
    | zero => simp [c]
    | succ i hi =>
      have hi' := congrFun he i.castSucc
      rw [increment_castSucc,increment_castSucc,hi] at hi'
      have hm := congrArg (fun z => (c*h i.castSucc)*z) hi'
      simpa [mul_assoc] using hm.symm
  have ht := congrFun he (Fin.last n)
  rw [increment_last,increment_last,hk (Fin.last n),hk 0] at ht
  have hcg := congrArg (fun z => h (Fin.last n)*z*(h 0)⁻¹) ht
  have hc' : g = c⁻¹*g*c := by simpa [mul_inv_rev,mul_assoc] using hcg
  have hc : c*g = g*c := by
    calc c*g = c*(c⁻¹*g*c) := congrArg (c*·) hc'
         _ = g*c := by group
  exact ⟨⟨c,Subgroup.mem_centralizer_singleton_iff.mpr hc⟩,fun i => (hk i).symm⟩

def orbitIncrement (g : G) (n : ℕ) : Orbit g n → (Fin (n+1) → G) :=
  Quotient.lift (increment g n) (by
    rintro h k ⟨c,hc⟩
    have hk : k = fun i => c*h i := funext fun i => (hc i).symm
    rw [hk,increment_invariant])

lemma orbitIncrement_injective (g : G) (n : ℕ) :
    Function.Injective (orbitIncrement g n) := by
  intro q r
  induction q using Quotient.inductionOn with | _ h =>
    induction r using Quotient.inductionOn with | _ k =>
      exact fun he => Quotient.sound (increment_eq_imp_related g n h k he)

variable {ι : Type*} [Fintype ι]

def weight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : ℂ := by
  classical
  exact Matrix.trace (List.ofFn (fun i => coefficient e (increment g n h i))).prod

lemma weight_invariant (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (h : Fin (n+1) → G) :
    weight e g n (fun i => c*h i) = weight e g n h := by
  classical
  simp only [weight,increment_invariant]

lemma weight_ne_zero_support (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) (hw : weight e g n h ≠ 0) (i : Fin (n+1)) :
    increment g n h i ∈ support e := by
  classical
  apply (mem_support e _).mpr
  intro hi
  apply hw
  have hz : (0 : ScalarMatrix (ι := ι)) ∈
      List.ofFn (fun j => coefficient e (increment g n h j)) := by
    exact List.mem_ofFn.mpr ⟨i,hi⟩
  simp only [weight,List.prod_eq_zero hz,Matrix.trace_zero]

def orbitWeight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Orbit g n → ℂ := Quotient.lift (weight e g n) (by
  rintro h k ⟨c,hc⟩
  have hk : k = fun i => c*h i := funext fun i => (hc i).symm
  rw [hk,weight_invariant])

lemma orbitWeight_finite (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Function.HasFiniteSupport (orbitWeight e g n) := by
  classical
  have hfinite : {f : Fin (n+1) → G | ∀ i, f i ∈ support e}.Finite := by
    exact Set.Finite.pi' (fun _ => (support e).finite_toSet)
  apply (hfinite.preimage (orbitIncrement_injective g n).injOn).subset
  intro q hq
  induction q using Quotient.inductionOn with | _ h =>
    exact weight_ne_zero_support e g n h hq

def pathVector (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Orbit g n →₀ ℂ := Finsupp.ofSupportFinite (orbitWeight e g n) (orbitWeight_finite e g n)

end

section

variable {G : Type*} [Group G]

def twist (g : G) (n : ℕ) (h : Fin (n+1) → G) : Fin (n+1) → G :=
  Fin.snoc (fun i : Fin n => h i.succ) (g*h 0)

@[simp] lemma twist_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    twist g n h i.castSucc = h i.succ := by simp [twist]

@[simp] lemma twist_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twist g n h (Fin.last n) = g*h 0 := by simp [twist]

end

variable {G ι : Type*} [Group G] [Fintype ι]

def prefixProduct (e : GroupMatrix (G := G) (ι := ι)) {n : ℕ}
    (h : Fin (n+1) → G) : ScalarMatrix (ι := ι) := by
  classical
  exact (List.ofFn (fun i : Fin n => kernel e (h i.castSucc) (h i.succ))).prod

end BassTrace.Paths

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_PathWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Paths

open scoped BigOperators

section

variable {G : Type*} [Group G]

def deleteLast (g : G) (n : ℕ) : Orbit g (n+1) → Orbit g n :=
  Quotient.map (fun h i => h i.castSucc) (by
    rintro h k ⟨c,hc⟩
    exact ⟨c,fun i => hc i.castSucc⟩)

def insertOrbit (g : G) (n : ℕ) (h : Fin (n+1) → G) (u : G) : Orbit g (n+1) :=
  Quotient.mk _ (Fin.snoc h u)

@[simp] lemma deleteLast_insertOrbit (g : G) (n : ℕ) (h : Fin (n+1) → G) (u : G) :
    deleteLast g n (insertOrbit g n h u) = Quotient.mk _ h := by
  change Quotient.mk (pathSetoid g n) (fun i : Fin (n+1) => Fin.snoc (α := fun _ => G) h u i.castSucc) = Quotient.mk (pathSetoid g n) h
  congr 1
  funext i
  exact Fin.snoc_castSucc (α := fun _ => G) u h i

end

section

variable {G ι : Type*} [Group G] [Fintype ι]

def totalWeight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : ℂ :=
  (pathVector e g n).sum fun _ z => z

def zeroConjugate (g : G) (q : Orbit g 0) : G := orbitIncrement g 0 q 0

end

variable {G : Type*} [Group G]

lemma twist_equivariant (g : G) (n : ℕ) (c : Subgroup.centralizer ({g} : Set G))
    (h : Fin (n+1) → G) : twist g n (fun i => c*h i) = fun i => c*twist g n h i := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    simp only [twist_last]
    rw [← mul_assoc,← Subgroup.mem_centralizer_singleton_iff.mp c.property,mul_assoc]
  | cast i => simp only [twist_castSucc]

def orbitTwist (g : G) (n : ℕ) : Orbit g n → Orbit g n :=
  Quotient.map (twist g n) (by
    rintro h k ⟨c,hc⟩
    have hk : k = fun i => c*h i := funext fun i => (hc i).symm
    rw [hk,twist_equivariant]
    exact ⟨c,fun _ => rfl⟩)

variable {ι : Type*} [Fintype ι]

def deleteEntry (g : G) (n : ℕ) (i : Fin (n+2)) : Orbit g (n+1) → Orbit g n :=
  Quotient.map (fun h j => h (i.succAbove j)) (by
    rintro h k ⟨c,hc⟩
    exact ⟨c,fun j => hc (i.succAbove j)⟩)

end BassTrace.Paths

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ExteriorDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Exterior identities for the lift-independent Pfaffian detector. -/

namespace BassTrace.Detector

section

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma ι_mul_ι_neg (u v : M) :
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v =
      -(ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

lemma ι_commute_two (u v w : M) :
    Commute (ExteriorAlgebra.ι R u)
      (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w) := by
  change _ * _ = _ * _
  calc
    _ = (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) * ExteriorAlgebra.ι R w :=
      (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w)) := by
      rw [ι_mul_ι_neg u v, neg_mul, mul_assoc]
    _ = ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R u) := by
      rw [ι_mul_ι_neg u w, mul_neg, neg_neg]
    _ = _ := (mul_assoc _ _ _).symm

lemma ι_commute_degree_two (u : M) {b : ExteriorAlgebra R M} (hb : b ∈ ⋀[R]^2 M) :
    Commute (ExteriorAlgebra.ι R u) b := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R 2] at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨v, rfl⟩ := hb
    simpa [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      Matrix.vecTail] using ι_commute_two u (v 0) (v 1)
  | zero => exact Commute.zero_right _
  | add b c _ _ hb hc => exact hb.add_right hc
  | smul a b _ hb =>
    show ExteriorAlgebra.ι R u * (a • b) = (a • b) * ExteriorAlgebra.ι R u
    rw [mul_smul_comm, smul_mul_assoc, hb.eq]

lemma gauge_invariance (u v : M) {b : ExteriorAlgebra R M}
    (hb : b ∈ ⋀[R]^2 M) (m : ℕ) :
    ExteriorAlgebra.ι R u *
        (b + ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)^m =
      ExteriorAlgebra.ι R u * b^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_add, pow_succ, ← mul_assoc]
    have hcomm := (ι_commute_degree_two u hb).pow_right m
    have hz : ExteriorAlgebra.ι R u * b^m *
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
      rw [hcomm.eq, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι R u),
        ExteriorAlgebra.ι_sq_zero, zero_mul, mul_zero]
    simp only [mul_assoc] at hz ⊢
    rw [hz, add_zero]

end

open scoped BigOperators

section

variable {I : Type*} [Fintype I]

abbrev CoordinateSpace (I : Type*) := I →₀ ℂ

abbrev CoordinateAlgebra (I : Type*) := ExteriorAlgebra ℂ (CoordinateSpace I)

def coordinate (i : I) : CoordinateSpace I := Finsupp.single i 1

def coordinateVector (a : I → ℂ) : CoordinateSpace I := ∑ i, a i • coordinate i

def rawTwoForm (B : I → I → ℂ) : CoordinateAlgebra I :=
  ∑ i, ∑ j, B i j • (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j))

def twoForm (B : I → I → ℂ) : CoordinateAlgebra I := (2 : ℂ)⁻¹ • rawTwoForm B

lemma rawTwoForm_add (A B : I → I → ℂ) :
    rawTwoForm (fun i j => A i j + B i j) = rawTwoForm A + rawTwoForm B := by
  simp only [rawTwoForm, add_smul, Finset.sum_add_distrib]

lemma rawTwoForm_sub (A B : I → I → ℂ) :
    rawTwoForm (fun i j => A i j - B i j) = rawTwoForm A - rawTwoForm B := by
  simp only [rawTwoForm, sub_smul, Finset.sum_sub_distrib]

lemma rawTwoForm_rank_one (a b : I → ℂ) :
    rawTwoForm (fun i j => a i * b j) =
      ExteriorAlgebra.ι ℂ (coordinateVector a) * ExteriorAlgebra.ι ℂ (coordinateVector b) := by
  simp only [rawTwoForm, coordinateVector, map_sum, map_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

lemma twoForm_add (A B : I → I → ℂ) :
    twoForm (fun i j => A i j + B i j) = twoForm A + twoForm B := by
  simp only [twoForm, rawTwoForm_add, smul_add]

lemma twoForm_decomposable (a b : I → ℂ) :
    twoForm (fun i j => a i * b j - b i * a j) =
      ExteriorAlgebra.ι ℂ (coordinateVector a) * ExteriorAlgebra.ι ℂ (coordinateVector b) := by
  rw [twoForm, rawTwoForm_sub, rawTwoForm_rank_one, rawTwoForm_rank_one,
    ι_mul_ι_neg (coordinateVector b) (coordinateVector a), sub_neg_eq_add]
  module

lemma twoForm_mem (B : I → I → ℂ) : twoForm B ∈ ⋀[ℂ]^2 (CoordinateSpace I) := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  change _ ∈ (ExteriorAlgebra.ι ℂ).range^2
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

lemma twoForm_lift_change (B : I → I → ℂ) (r : I → ℂ) :
    twoForm (fun i j => B i j + r j - r i) = twoForm B +
      ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ExteriorAlgebra.ι ℂ (coordinateVector r) := by
  have he : (fun i j => B i j + r j - r i) =
      (fun i j => B i j + ((1 : ℂ)*r j-r i*1)) := by funext i j; ring
  rw [he, twoForm_add, twoForm_decomposable]

lemma detector_form_lift_independent (B : I → I → ℂ) (r : I → ℂ) (m : ℕ) :
    ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ((m.factorial : ℂ)⁻¹ • (twoForm (fun i j => B i j + r j - r i))^m) =
      ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ((m.factorial : ℂ)⁻¹ • (twoForm B)^m) := by
  rw [twoForm_lift_change, mul_smul_comm, mul_smul_comm,
    gauge_invariance _ _ (twoForm_mem B)]

def coordinateMap {J : Type*} (f : I → J) : CoordinateSpace I →ₗ[ℂ] CoordinateSpace J :=
  Finsupp.lmapDomain ℂ ℂ f

omit [Fintype I] in
@[simp] lemma coordinateMap_coordinate {J : Type*} (f : I → J) (i : I) :
    coordinateMap f (coordinate i) = coordinate (f i) := Finsupp.mapDomain_single

lemma coordinateMap_vector {J : Type*} [Fintype J] (f : I ≃ J) (a : I → ℂ) :
    coordinateMap f (coordinateVector a) = coordinateVector (a ∘ f.symm) := by
  simp only [coordinateVector, map_sum, map_smul, coordinateMap_coordinate]
  simpa only [Equiv.symm_apply_apply, Function.comp_def] using
    Equiv.sum_comp f (fun j => a (f.symm j) • coordinate j)

lemma twoForm_map {J : Type*} [Fintype J] (f : I ≃ J) (B : J → J → ℂ) :
    ExteriorAlgebra.map (coordinateMap f) (twoForm (fun i j => B (f i) (f j))) =
      twoForm B := by
  simp only [twoForm, rawTwoForm, map_smul, map_sum, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_coordinate]
  apply congrArg (fun x : CoordinateAlgebra J => (2 : ℂ)⁻¹ • x)
  calc
    _ = ∑ i : I, ∑ j : J, B (f i) j •
        (ExteriorAlgebra.ι ℂ (coordinate (f i)) * ExteriorAlgebra.ι ℂ (coordinate j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp f (fun j : J => B (f i) j •
        (ExteriorAlgebra.ι ℂ (coordinate (f i)) * ExteriorAlgebra.ι ℂ (coordinate j)))
    _ = _ := Equiv.sum_comp f (fun i : J => ∑ j : J, B i j •
        (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j)))

end

section

abbrev coordinateBasis (n : ℕ) : Module.Basis (Fin n) ℂ (CoordinateSpace (Fin n)) :=
  Finsupp.basisSingleOne

def topIndex (n : ℕ) : Set.powersetCard (Fin n) n :=
  Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin n)).toOrderEmbedding)

lemma topIndex_val (n : ℕ) : (topIndex n).val = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  change i ∈ Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin n)).toOrderEmbedding)
  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  exact ⟨i, rfl⟩

lemma topIndex_unique (n : ℕ) (s : Set.powersetCard (Fin n) n) : s = topIndex n := by
  apply Subtype.ext
  rw [topIndex_val]
  apply Finset.eq_univ_of_card
  simp only [Fintype.card_fin]
  exact s.property

abbrev topBasis (n : ℕ) := (coordinateBasis n).exteriorPower n

def topVolume (n : ℕ) : ⋀[ℂ]^n (CoordinateSpace (Fin n)) :=
  exteriorPower.ιMulti ℂ n coordinate

lemma topBasis_topIndex (n : ℕ) : topBasis n (topIndex n) = topVolume n := by
  rw [exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family, topIndex, Equiv.symm_apply_apply]
  rfl

def topCoefficient (n : ℕ) : (⋀[ℂ]^n (CoordinateSpace (Fin n))) →ₗ[ℂ] ℂ :=
  (topBasis n).coord (topIndex n)

lemma topCoefficient_topVolume (n : ℕ) : topCoefficient n (topVolume n) = 1 := by
  rw [← topBasis_topIndex]
  change (topBasis n).repr (topBasis n (topIndex n)) (topIndex n) = 1
  rw [Module.Basis.repr_self, Finsupp.single_eq_same]

lemma top_scalar (n : ℕ) (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    x = topCoefficient n x • topVolume n := by
  classical
  have hsum : (∑ s : Set.powersetCard (Fin n) n,
      (topBasis n).repr x s • topBasis n s) =
      (topBasis n).repr x (topIndex n) • topBasis n (topIndex n) := by
    apply Finset.sum_eq_single (topIndex n)
    · intro s _ hs; exact (hs (topIndex_unique n s)).elim
    · simp
  calc
    x = ∑ s, (topBasis n).repr x s • topBasis n s := ((topBasis n).sum_repr x).symm
    _ = _ := hsum
    _ = _ := by rw [topBasis_topIndex]; rfl

lemma homogeneous_mul {I : Type*} {n m : ℕ} {x y : CoordinateAlgebra I}
    (hx : x ∈ ⋀[ℂ]^n (CoordinateSpace I)) (hy : y ∈ ⋀[ℂ]^m (CoordinateSpace I)) :
    x*y ∈ ⋀[ℂ]^(n+m) (CoordinateSpace I) := by
  change _ ∈ (ExteriorAlgebra.ι ℂ).range^(n+m)
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy

lemma homogeneous_pow {I : Type*} {n : ℕ} {x : CoordinateAlgebra I}
    (hx : x ∈ ⋀[ℂ]^n (CoordinateSpace I)) (m : ℕ) :
    x^m ∈ ⋀[ℂ]^(n*m) (CoordinateSpace I) := by
  induction m with
  | zero => simp [ExteriorAlgebra.exteriorPower]
  | succ m ih =>
    rw [pow_succ, Nat.mul_succ]
    exact homogeneous_mul ih hx

def pfaffian (m : ℕ) (B : Fin (2*m) → Fin (2*m) → ℂ) : ℂ :=
  topCoefficient (2*m) ⟨(m.factorial : ℂ)⁻¹ • (twoForm B)^m,
    Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) m)⟩

lemma topVolume_map_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    exteriorPower.map n (coordinateMap σ) (topVolume n) =
      σ.sign • topVolume n := by
  simp only [topVolume, exteriorPower.map_apply_ιMulti]
  have he : (coordinateMap σ) ∘ coordinate = coordinate ∘ σ := by
    funext i
    exact coordinateMap_coordinate _ _
  rw [he]
  exact (exteriorPower.ιMulti ℂ n).map_perm coordinate σ

lemma topCoefficient_map_perm (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    topCoefficient n (exteriorPower.map n (coordinateMap σ) x) =
      σ.sign • topCoefficient n x := by
  conv_lhs => rw [top_scalar n x]
  rw [map_smul, topVolume_map_perm]
  simp only [Units.smul_def, map_zsmul, map_smul, topCoefficient_topVolume, smul_eq_mul]
  ring

end

lemma exteriorMap_coe {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (n : ℕ) (f : M →ₗ[ℂ] N) (x : ⋀[ℂ]^n M) :
    (exteriorPower.map n f x : ExteriorAlgebra ℂ N) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra ℂ M) := by
  have he : (⋀[ℂ]^n N).subtype.comp (exteriorPower.map n f) =
      (ExteriorAlgebra.map f).toLinearMap.comp (⋀[ℂ]^n M).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, AlgHom.toLinearMap_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun he x

def multiplyVector {I : Type*} (n : ℕ) (v : CoordinateSpace I) :
    (⋀[ℂ]^n (CoordinateSpace I)) →ₗ[ℂ] ⋀[ℂ]^(n+1) (CoordinateSpace I) where
  toFun x := ⟨ExteriorAlgebra.ι ℂ v * x, by
    change _ ∈ (ExteriorAlgebra.ι ℂ).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v, rfl⟩) x.property⟩
  map_add' x y := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact mul_smul_comm _ _ _

@[simp] lemma multiplyVector_coe {I : Type*} (n : ℕ) (v : CoordinateSpace I)
    (x : ⋀[ℂ]^n (CoordinateSpace I)) :
    (multiplyVector n v x : CoordinateAlgebra I) = ExteriorAlgebra.ι ℂ v * x := rfl

def insertCoordinate {n : ℕ} (i : Fin (n+1)) :
    (⋀[ℂ]^n (CoordinateSpace (Fin n))) →ₗ[ℂ] ⋀[ℂ]^(n+1) (CoordinateSpace (Fin (n+1))) :=
  (multiplyVector n (coordinate i)).comp (exteriorPower.map n (coordinateMap i.succAbove))

def pfaffianForm {I : Type*} [Fintype I] (m : ℕ) (B : I → I → ℂ) :
    ⋀[ℂ]^(2*m) (CoordinateSpace I) :=
  ⟨(m.factorial : ℂ)⁻¹ • (twoForm B)^m,
    Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) m)⟩

def detectorForm {I : Type*} [Fintype I] (m : ℕ) (B : I → I → ℂ) :
    ⋀[ℂ]^(2*m+1) (CoordinateSpace I) :=
  multiplyVector (2*m) (coordinateVector (fun _ => 1)) (pfaffianForm m B)

def detector (m : ℕ) (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) : ℂ :=
  topCoefficient (2*m+1) (detectorForm m B)

lemma detector_lift_independent (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (r : Fin (2*m+1) → ℂ) :
    detector m (fun i j => B i j + r j - r i) = detector m B := by
  apply congrArg (topCoefficient (2*m+1))
  apply Subtype.ext
  exact detector_form_lift_independent B r m

lemma pfaffianForm_map {I J : Type*} [Fintype I] [Fintype J] (f : I ≃ J)
    (m : ℕ) (B : J → J → ℂ) :
    exteriorPower.map (2*m) (coordinateMap f) (pfaffianForm m (fun i j => B (f i) (f j))) =
      pfaffianForm m B := by
  apply Subtype.ext
  simp only [exteriorMap_coe, pfaffianForm, map_smul, map_pow, twoForm_map]

lemma detectorForm_map {I J : Type*} [Fintype I] [Fintype J] (f : I ≃ J)
    (m : ℕ) (B : J → J → ℂ) :
    exteriorPower.map (2*m+1) (coordinateMap f) (detectorForm m (fun i j => B (f i) (f j))) =
      detectorForm m B := by
  apply Subtype.ext
  simp only [exteriorMap_coe, detectorForm, multiplyVector_coe, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_vector, pfaffianForm, map_smul, map_pow, twoForm_map]
  rfl

lemma pfaffian_perm (m : ℕ) (B : Fin (2*m) → Fin (2*m) → ℂ) (σ : Equiv.Perm (Fin (2*m))) :
    pfaffian m (fun i j => B (σ i) (σ j)) = σ.sign • pfaffian m B := by
  have he := congrArg (topCoefficient (2*m)) (pfaffianForm_map σ m B)
  rw [topCoefficient_map_perm] at he
  change σ.sign • pfaffian m (fun i j => B (σ i) (σ j)) = pfaffian m B at he
  rw [← he, smul_smul, Int.units_mul_self, one_smul]

lemma detector_perm (m : ℕ) (B : Fin (2*m+1) → Fin (2*m+1) → ℂ)
    (σ : Equiv.Perm (Fin (2*m+1))) :
    detector m (fun i j => B (σ i) (σ j)) = σ.sign • detector m B := by
  have he := congrArg (topCoefficient (2*m+1)) (detectorForm_map σ m B)
  rw [topCoefficient_map_perm] at he
  change σ.sign • detector m (fun i j => B (σ i) (σ j)) = detector m B at he
  rw [← he, smul_smul, Int.units_mul_self, one_smul]

end BassTrace.Detector

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_PfaffianDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Alternating functions on vertex labels extend to oriented exterior chains. -/

namespace Oriented

open scoped BigOperators

variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]

instance instCoeFunAltFunctionForallForallFin_2 {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩

end Oriented

/-! The augmented exterior chain complex and contraction on homogeneous exterior submodules. -/

namespace Detector

open scoped BigOperators

lemma scalar_alt_zero {Y : Type*} {n : ℕ} (f : (Fin n → Y) → ℂ)
    (hf : ∀ v (σ : Equiv.Perm (Fin n)), f (v ∘ σ) = σ.sign • f v)
    (v : Fin n → Y) (hv : ¬ Function.Injective v) : f v = 0 := by
  classical
  obtain ⟨i, j, hvij, hij⟩ := Function.not_injective_iff.mp hv
  have he : v ∘ Equiv.swap i j = v := by
    funext k
    by_cases hki : k = i
    · subst k; simp [hvij]
    by_cases hkj : k = j
    · subst k; simp [hvij]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hh := hf v (Equiv.swap i j)
  rw [he, Equiv.Perm.sign_swap hij] at hh
  change f v = (-1 : ℤ) • f v at hh
  have hn : f v = - f v := by simpa only [neg_one_zsmul] using hh
  linear_combination (1 / 2 : ℂ) * hn

def pfaffianAlt {Y : Type*} (m : ℕ) (β : Y → Y → ℂ) :
    Oriented.AltFunction Y (2*m) ℂ where
  toFun v := pfaffian m (fun i j => β (v i) (v j))
  perm v σ := pfaffian_perm m (fun i j => β (v i) (v j)) σ
  zero v hv := scalar_alt_zero (fun w => pfaffian m (fun i j => β (w i) (w j)))
    (fun w σ => pfaffian_perm m (fun i j => β (w i) (w j)) σ) v hv

def detectorAlt {Y : Type*} (m : ℕ) (β : Y → Y → ℂ) :
    Oriented.AltFunction Y (2*m+1) ℂ where
  toFun v := detector m (fun i j => β (v i) (v j))
  perm v σ := detector_perm m (fun i j => β (v i) (v j)) σ
  zero v hv := scalar_alt_zero (fun w => detector m (fun i j => β (w i) (w j)))
    (fun w σ => detector_perm m (fun i j => β (w i) (w j)) σ) v hv

open scoped BigOperators

open Oriented ChainHomotopy

variable {Y : Type*} [LinearOrder Y]

def cocycle (m : ℕ) (β : Y → Y → ℂ) : Degree Y (2*m+1) →ₗ[ℂ] ℂ :=
  (detectorAlt m β).lift

lemma cocycle_wedge (m : ℕ) (β : Y → Y → ℂ) (v : Fin (2*m+1) → Y) :
    cocycle m β (wedge (2*m+1) v) = detector m (fun i j => β (v i) (v j)) :=
  (detectorAlt m β).lift_wedge v

end Detector

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_RelativeExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Relative exponents use orbit representatives internally, without assuming an equivariant section. -/

namespace RelativeExponents

variable {G : Type*} [Group G]

abbrev Positions (g : G) :=
  (Multiplicative ℤ × Multiplicative ℤ) × Subgroup.centralizer ({g} : Set G)

lemma centralizer_commutes (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Commute g (c : G) :=
  (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm

def positionHom (g : G) : Positions g →* G × G where
  toFun a := (g ^ Multiplicative.toAdd a.1.1 * a.2,
    g ^ Multiplicative.toAdd a.1.2 * a.2)
  map_one' := by simp
  map_mul' a b := by
    apply Prod.ext
    · change g ^ (Multiplicative.toAdd a.1.1 + Multiplicative.toAdd b.1.1) *
          ((a.2 : G) * b.2) = (g ^ Multiplicative.toAdd a.1.1 * a.2) *
          (g ^ Multiplicative.toAdd b.1.1 * b.2)
      rw [zpow_add]
      have hc := (centralizer_commutes g a.2).symm.zpow_right
        (Multiplicative.toAdd b.1.1)
      simp only [mul_assoc]
      rw [← mul_assoc (a.2 : G), hc.eq, mul_assoc]
    · change g ^ (Multiplicative.toAdd a.1.2 + Multiplicative.toAdd b.1.2) *
          ((a.2 : G) * b.2) = (g ^ Multiplicative.toAdd a.1.2 * a.2) *
          (g ^ Multiplicative.toAdd b.1.2 * b.2)
      rw [zpow_add]
      have hc := (centralizer_commutes g a.2).symm.zpow_right
        (Multiplicative.toAdd b.1.2)
      simp only [mul_assoc]
      rw [← mul_assoc (a.2 : G), hc.eq, mul_assoc]

def character (g : G) (a : Positions g) : ℝ :=
  ((Multiplicative.toAdd a.1.2 : ℤ) : ℝ) - ((Multiplicative.toAdd a.1.1 : ℤ) : ℝ)

end RelativeExponents

namespace Detector

section

open scoped BigOperators

open Oriented ChainHomotopy

variable {G : Type*} [Group G]

def Vertex (g : G) := Quotient (QuotientGroup.rightRel (Subgroup.zpowers g))

def project (g : G) (h : G) : Vertex g := Quotient.mk _ h

def sectionLift (g : G) (y : Vertex g) : G := y.out

lemma project_sectionLift (g : G) (y : Vertex g) :
    project g (sectionLift g y) = y := Quotient.out_eq y

lemma project_eq_iff (g h k : G) :
    project g h = project g k ↔ ∃ r : ℤ, g^r*h = k := by
  constructor
  · intro he
    have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hr
    exact ⟨r, (eq_mul_inv_iff_mul_eq.mp hr)⟩
  · rintro ⟨r, rfl⟩
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simp only [mul_inv_cancel_right]
    exact (Subgroup.zpowers g).zpow_mem (Subgroup.mem_zpowers g) r

lemma exists_section_power (g h : G) :
    ∃ r : ℤ, g^r*h = sectionLift g (project g h) := by
  apply (project_eq_iff g _ _).mp
  exact (project_sectionLift g _).symm

def centralizerAct (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Vertex g → Vertex g := Quotient.lift (fun h => project g (c*h)) (by
  intro h k hhk
  obtain ⟨r, hr⟩ := (project_eq_iff g h k).mp (Quotient.sound hhk)
  apply (project_eq_iff g _ _).mpr
  refine ⟨r, ?_⟩
  have hc := (RelativeExponents.centralizer_commutes g c).zpow_left r
  rw [← mul_assoc, hc.eq, mul_assoc, hr])

@[simp] lemma centralizerAct_project (g : G)
    (c : Subgroup.centralizer ({g} : Set G)) (h : G) :
    centralizerAct g c (project g h) = project g (c*h) := rfl

lemma centralizerAct_one (g : G) (y : Vertex g) :
    centralizerAct g 1 y = y := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g ((1:G)*h) = project g h
    rw [one_mul]

lemma centralizerAct_mul (g : G) (c d : Subgroup.centralizer ({g} : Set G))
    (y : Vertex g) : centralizerAct g (c*d) y =
      centralizerAct g c (centralizerAct g d y) := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (((c:G)*d)*h) = project g (c*(d*h))
    rw [mul_assoc]

lemma detector_section (g : G) (β : G → G → ℂ)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (m : ℕ) (h : Fin (2*m+1) → G) :
    detector m (fun i j => β (sectionLift g (project g (h i)))
      (sectionLift g (project g (h j)))) =
      detector m (fun i j => β (h i) (h j)) := by
  choose r hr using fun i => exists_section_power g (h i)
  have hb : (fun i j => β (sectionLift g (project g (h i)))
      (sectionLift g (project g (h j)))) =
      (fun i j => β (h i) (h j) + (r j : ℂ) - (r i : ℂ)) := by
    funext i j
    rw [← hr i, ← hr j, hl]
  rw [hb]
  exact detector_lift_independent m (fun i j => β (h i) (h j)) (fun i => (r i : ℂ))

lemma detector_section_invariant (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
      β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (m : ℕ) (c : Subgroup.centralizer ({g} : Set G)) (v : Fin (2*m+1) → Vertex g) :
    detector m (fun i j => β (sectionLift g (centralizerAct g c (v i)))
      (sectionLift g (centralizerAct g c (v j)))) =
      detector m (fun i j => β (sectionLift g (v i)) (sectionLift g (v j))) := by
  have hp (i) : centralizerAct g c (v i) =
      project g (c*sectionLift g (v i)) := by
    rw [← centralizerAct_project, project_sectionLift]
  simp only [hp]
  rw [detector_section g β hl m (fun i => c*sectionLift g (v i))]
  simp only [hc]

end

section

open Oriented ChainHomotopy

variable {G : Type*} [Group G]

def cosetCocycle (g : G) (m : ℕ) (β : G → G → ℂ) :
    Degree (Vertex g) (2*m+1) →ₗ[ℂ] ℂ := by
  classical
  letI : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  exact cocycle m (fun y z => β (sectionLift g y) (sectionLift g z))

lemma cosetCocycle_wedge (g : G) (m : ℕ) (β : G → G → ℂ)
    (v : Fin (2*m+1) → Vertex g) :
    cosetCocycle g m β (wedge (2*m+1) v) =
      detector m (fun i j => β (sectionLift g (v i)) (sectionLift g (v j))) := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  unfold cosetCocycle
  exact cocycle_wedge _ _ _

lemma cosetCocycle_invariant (g : G) (m : ℕ) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
      β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (c : Subgroup.centralizer ({g} : Set G))
    (x : Degree (Vertex g) (2*m+1)) :
    cosetCocycle g m β (relabel (2*m+1) (centralizerAct g c) x) =
      cosetCocycle g m β x := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  have he : (cosetCocycle g m β).comp (relabel (2*m+1) (centralizerAct g c)) =
      cosetCocycle g m β := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, relabel_wedge, cosetCocycle_wedge,
      Function.comp_apply]
    exact detector_section_invariant g β hc hl m c v
  exact LinearMap.congr_fun he x

end

open scoped BigOperators

end Detector

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TwistedPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Detector

open scoped BigOperators

variable {G : Type*} [Group G]

def twistedRotation (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin (n+1)) : G :=
  g ^ (if i = Fin.last n then (1 : ℤ) else 0) * h (finRotate (n+1) i)

end Detector

namespace Paths

open scoped BigOperators

def weightedSum {A : Type*} (v : A →₀ ℂ) (f : A → ℂ) : ℂ :=
  v.sum fun a z => z*f a

end Paths

namespace Detector

open scoped BigOperators

open BassTrace.Paths

section

variable {G : Type*} [Group G]

variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)

def orbitPfaffian (m : ℕ) : Orbit g (2*m+1) → ℂ :=
  Quotient.lift (fun h => pfaffian (m+1) (fun i j => β (h i) (h j))) (by
    rintro h k ⟨c,hh⟩
    have hk : k = fun i => c*h i := funext fun i => (hh i).symm
    rw [hk]
    simp only [hc])

def orbitDetector (m : ℕ) : Orbit g (2*m) → ℂ :=
  Quotient.lift (fun h => detector m (fun i j => β (h i) (h j))) (by
    rintro h k ⟨c,hh⟩
    have hk : k = fun i => c*h i := funext fun i => (hh i).symm
    rw [hk]
    simp only [hc])

variable {ι : Type*} [Fintype ι]

def pfaffianSum (e : GroupMatrix (G := G) (ι := ι)) : ℕ → ℂ
  | 0 => totalWeight e g 0
  | m+1 => weightedSum (pathVector e g (2*m+1)) (orbitPfaffian g β hc m)

def detectorSum (e : GroupMatrix (G := G) (ι := ι)) (m : ℕ) : ℂ :=
  weightedSum (pathVector e g (2*m)) (orbitDetector g β hc m)

end

end Detector

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_PathComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.PathChains

section

open scoped BigOperators

open Oriented ChainHomotopy Paths Detector

variable {G : Type*} [Group G]

def relations (g : G) (n : ℕ) : Submodule ℂ (Degree (Vertex g) n) :=
  Submodule.span ℂ (Set.range fun p : Subgroup.centralizer ({g} : Set G) ×
    Degree (Vertex g) n => relabel n (centralizerAct g p.1) p.2-p.2)

abbrev Coinvariant (g : G) (n : ℕ) := Degree (Vertex g) n ⧸ relations g n

def quotientMap (g : G) (n : ℕ) : Degree (Vertex g) n →ₗ[ℂ] Coinvariant g n :=
  (relations g n).mkQ

lemma quotientMap_invariant (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (x : Degree (Vertex g) n) :
    quotientMap g n (relabel n (centralizerAct g c) x) = quotientMap g n x := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨(c,x),rfl⟩)

lemma d_relations (g : G) (n : ℕ) {x : Degree (Vertex g) (n+1)}
    (hx : x ∈ relations g (n+1)) : d n x ∈ relations g n := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c,y⟩,rfl⟩ := hx
    rw [map_sub,d_relabel]
    exact Submodule.subset_span ⟨(c,d n y),rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

def quotientD (g : G) (n : ℕ) : Coinvariant g (n+1) →ₗ[ℂ] Coinvariant g n :=
  (relations g (n+1)).liftQ ((quotientMap g n).comp (d n)) (by
    intro x hx
    change quotientMap g n (d n x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (d_relations g n hx))

@[simp] lemma quotientD_mk (g : G) (n : ℕ) (x : Degree (Vertex g) (n+1)) :
    quotientD g n (quotientMap g (n+1) x) = quotientMap g n (d n x) := rfl

def pathProjection (g : G) (n : ℕ) : Orbit g n → Coinvariant g (n+1) :=
  Quotient.lift (fun h => quotientMap g (n+1) (wedge (n+1) (project g ∘ h))) (by
    intro h k hhk
    obtain ⟨c,hc⟩ := hhk
    have he : k = fun i => (c:G)*h i := funext fun i => (hc i).symm
    rw [he]
    simpa only [relabel_wedge, Function.comp_def, centralizerAct_project] using
      (quotientMap_invariant g (n+1) c (wedge (n+1) (project g ∘ h))).symm)

@[simp] lemma pathProjection_mk (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    pathProjection g n (Quotient.mk _ h) =
      quotientMap g (n+1) (wedge (n+1) (project g ∘ h)) := rfl

variable {ι : Type*} [Fintype ι]

def pathChain (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Coinvariant g (n+1) :=
  Finsupp.linearCombination ℂ (pathProjection g n) (pathVector e g n)

end

open scoped BigOperators

open Oriented ChainHomotopy Paths Detector

variable {G : Type*} [Group G]

variable {ι : Type*} [Fintype ι]

variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k+s-r)

def quotientCocycle (m : ℕ) : Coinvariant g (2*m+1) →ₗ[ℂ] ℂ :=
  (relations g (2*m+1)).liftQ (cosetCocycle g m β) (by
    intro x hx
    change cosetCocycle g m β x = 0
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨c,y⟩,rfl⟩ := hx
      rw [map_sub,cosetCocycle_invariant g m β hc hl,sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add,hx,hy,add_zero]
    | smul a x _ hx => rw [map_smul,hx,smul_zero])

end BassTrace.PathChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CentralizerGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.Detector

section

variable {G : Type*} [Group G]

lemma SubtypeCentralizer_commutes (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Commute g (c : G) := (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm

abbrev Centralizer (g : G) := Subgroup.centralizer ({g} : Set G)

def generator (g : G) : Centralizer g :=
  ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[simp] lemma generator_coe (g : G) : (generator g : G) = g := rfl

lemma generator_commutes (g : G) (c : Centralizer g) : Commute (generator g) c := by
  apply Subtype.ext
  exact (SubtypeCentralizer_commutes g c).eq

def cyclic (g : G) : Subgroup (Centralizer g) := Subgroup.zpowers (generator g)

instance cyclic_normal (g : G) : (cyclic g).Normal where
  conj_mem a ha c := by
    obtain ⟨r,rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc := (generator_commutes g c).zpow_left r
    rw [← hc.eq,mul_inv_cancel_right]
    exact (Subgroup.zpowers (generator g)).zpow_mem (Subgroup.mem_zpowers _) r

abbrev ActingGroup (g : G) := Centralizer g ⧸ cyclic g

def centralizerPerm (g : G) : Centralizer g →* Equiv.Perm (Vertex g) where
  toFun c := {
    toFun := centralizerAct g c
    invFun := centralizerAct g c⁻¹
    left_inv y := by rw [← centralizerAct_mul,inv_mul_cancel,centralizerAct_one]
    right_inv y := by rw [← centralizerAct_mul,mul_inv_cancel,centralizerAct_one] }
  map_one' := Equiv.ext (centralizerAct_one g)
  map_mul' c d := Equiv.ext (centralizerAct_mul g c d)

lemma cyclic_le_ker (g : G) : cyclic g ≤ (centralizerPerm g).ker := by
  rintro c hc
  obtain ⟨r,rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  apply Equiv.ext
  intro y
  induction y using Quotient.inductionOn with | _ h =>
    change project g (g^r*h) = project g h
    apply (project_eq_iff g _ _).mpr
    refine ⟨-r, ?_⟩
    simp [← mul_assoc]

def quotientPerm (g : G) : ActingGroup g →* Equiv.Perm (Vertex g) :=
  QuotientGroup.lift (cyclic g) (centralizerPerm g) (cyclic_le_ker g)

instance vertexAction (g : G) : MulAction (ActingGroup g) (Vertex g) :=
  MulAction.compHom (Vertex g) (quotientPerm g)

@[simp] lemma quotient_smul_project (g : G) (c : Centralizer g) (h : G) :
    (QuotientGroup.mk c : ActingGroup g) • project g h = project g (c*h) := rfl

end

open Set Finset

variable {G : Type*} [Group G]

def rightMul (g s : G) : Vertex g → Vertex g :=
  Quotient.map' (fun h => h*s) (by
    intro h k hk
    obtain ⟨r,hr⟩ := (project_eq_iff g h k).mp (Quotient.sound hk)
    apply Quotient.exact
    apply (project_eq_iff g _ _).mpr
    exact ⟨r,by rw [← mul_assoc,hr]⟩)

@[simp] lemma rightMul_project (g s h : G) : rightMul g s (project g h) = project g (h*s) := rfl

@[simp] lemma rightMul_one (g : G) (y : Vertex g) : rightMul g 1 y = y := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (h*1) = project g h
    rw [mul_one]

lemma rightMul_mul (g s t : G) (y : Vertex g) :
    rightMul g (s*t) y = rightMul g t (rightMul g s y) := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (h*(s*t)) = project g ((h*s)*t)
    rw [mul_assoc]

def supportGraph (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) : SimpleGraph (Vertex g) where
  Adj y z := y ≠ z ∧ ∃ s ∈ S, rightMul g s y = z
  symm := ⟨by
    rintro y z ⟨hne,s,hs,rfl⟩
    refine ⟨hne.symm,s⁻¹,hS s hs,?_⟩
    rw [← rightMul_mul,mul_inv_cancel,rightMul_one]⟩
  loopless := ⟨by rintro y ⟨h,_⟩; exact h rfl⟩

lemma supportGraph_finite_neighbors (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (y : Vertex g) : ((supportGraph g S hS).neighborSet y).Finite := by
  classical
  apply (S.image (fun s => rightMul g s y)).finite_toSet.subset
  rintro z ⟨_,s,hs,rfl⟩
  exact Finset.mem_image_of_mem _ hs

scoped instance supportGraphLocallyFinite (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) : (supportGraph g S hS).LocallyFinite :=
  fun y => (supportGraph_finite_neighbors g S hS y).fintype

open scoped BassTrace.Detector

end BassTrace.Detector

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FreeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

noncomputable section

namespace BassTrace.FreeParameter

open Set MeasureTheory

open scoped Pointwise

universe u v

variable {H : Type u} [Group H] (S : Subgroup H)

noncomputable def residue (t : H) : S :=
  ⟨(Quotient.out (QuotientGroup.mk t : H ⧸ S))⁻¹ * t,
    QuotientGroup.leftRel_apply.mp
      (@Quotient.exact' _ (QuotientGroup.leftRel S) _ _ (Quotient.out_eq' _))⟩

lemma residue_out (q : H ⧸ S) : residue S q.out = 1 := by
  apply Subtype.ext
  simp [residue]

lemma residue_mul (t : H) (s : S) : residue S (t * s) = residue S t * s := by
  apply Subtype.ext
  simp [residue, QuotientGroup.mk_mul_of_mem _ s.property, mul_assoc]

lemma out_mul_residue (t : H) :
    (Quotient.out (QuotientGroup.mk t : H ⧸ S)) * residue S t = t := by
  simp [residue]

variable {C : Type v} [Group C] (χ : S →* C)

abbrev Offsets := (H ⧸ S) → C

noncomputable def encode (ω : Offsets S (C := C)) (t : H) : C :=
  ω (QuotientGroup.mk t) * χ (residue S t)

lemma encode_out (ω : Offsets S (C := C)) (q : H ⧸ S) :
    encode S χ ω q.out = ω q := by
  simp [encode, residue_out]

lemma encode_mul (ω : Offsets S (C := C)) (t : H) (s : S) :
    encode S χ ω (t * s) = encode S χ ω t * χ s := by
  simp [encode, QuotientGroup.mk_mul_of_mem _ s.property, residue_mul, mul_assoc]

lemma encode_injective : Function.Injective (encode S χ) := by
  intro ω η h
  funext q
  simpa only [encode_out] using congrFun h q.out

noncomputable def shift (h : H) (ω : Offsets S (C := C)) : Offsets S (C := C) :=
  fun q => encode S χ ω (h⁻¹ * q.out)

lemma encode_shift (h : H) (ω : Offsets S (C := C)) (t : H) :
    encode S χ (shift S χ h ω) t = encode S χ ω (h⁻¹ * t) := by
  change encode S χ ω (h⁻¹ * (QuotientGroup.mk t : H ⧸ S).out) *
    χ (residue S t) = _
  rw [← encode_mul, mul_assoc, out_mul_residue]

lemma shift_one (ω : Offsets S (C := C)) : shift S χ 1 ω = ω := by
  apply encode_injective S χ
  funext t
  simp [encode_shift]

lemma shift_mul (h k : H) (ω : Offsets S (C := C)) :
    shift S χ (h * k) ω = shift S χ h (shift S χ k ω) := by
  apply encode_injective S χ
  funext t
  simp [encode_shift, mul_assoc]

section Probability

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

noncomputable def uniform : Measure C := (PMF.uniformOfFintype C).toMeasure

instance uniform_probability : IsProbabilityMeasure (uniform (C := C)) := by
  unfold uniform
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def offsetMeasure : Measure (Offsets S (C := C)) :=
  Measure.infinitePi (fun _ : H ⧸ S => uniform (C := C))

instance offsetMeasure_probability : IsProbabilityMeasure (offsetMeasure S (C := C)) := by
  unfold offsetMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Probability

structure Character (a : H) where
  Color : Type u
  [group : Group Color]
  [finite : Finite Color]
  value : Subgroup.zpowers a →* Color
  detects : value ⟨a, Subgroup.mem_zpowers a⟩ ≠ 1

attribute [instance] Character.group Character.finite

lemma zpowers_subtype_generator (a : H) :
    Subgroup.zpowers (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp s.property
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨j, ?_⟩
  apply Subtype.ext
  exact hj

noncomputable def character (a : H) (ha : a ≠ 1) : Character a := by
  classical
  by_cases hf : IsOfFinOrder a
  · letI : Finite (Subgroup.zpowers a) := hf.finite_zpowers
    exact { Color := Subgroup.zpowers a
            group := inferInstance
            finite := inferInstance
            value := MonoidHom.id _
            detects := fun h => ha (congrArg Subtype.val h) }
  · letI : Infinite (Subgroup.zpowers a) := (infinite_zpowers.mpr hf).to_subtype
    let e := intEquivOfZPowersEqTop
      (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) (zpowers_subtype_generator a)
    let f : Subgroup.zpowers a →* ULift.{u} (Multiplicative (ZMod 2)) :=
      MulEquiv.ulift.symm.toMonoidHom.comp
        ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))).comp e.symm.toMonoidHom)
    refine { Color := ULift.{u} (Multiplicative (ZMod 2))
             group := inferInstance
             finite := inferInstance
             value := f
             detects := ?_ }
    intro he
    have he' := congrArg (fun z : ULift (Multiplicative (ZMod 2)) => z.down.toAdd) he
    have hx : e.symm ⟨a, Subgroup.mem_zpowers a⟩ = Multiplicative.ofAdd 1 :=
      intEquivOfZPowersEqTop_symm_self (zpowers_subtype_generator a)
    norm_num [f, hx] at he'
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) he'

namespace Character

variable {a : H} (F : Character a)

instance colorTopology : TopologicalSpace F.Color := ⊥

instance colorDiscrete : DiscreteTopology F.Color := ⟨rfl⟩

instance colorMeasurable : MeasurableSpace F.Color := ⊤

instance colorSingleton : MeasurableSingletonClass F.Color := ⟨fun _ => trivial⟩

instance colorBorel : BorelSpace F.Color := ⟨borel_eq_top_of_discrete.symm⟩

noncomputable instance colorFintype : Fintype F.Color := Fintype.ofFinite _

end Character

variable (H)

abbrev Space := (a : {a : H // a ≠ 1}) →
  Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)

instance spaceTopology : TopologicalSpace (Space H) :=
  inferInstanceAs (TopologicalSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceMeasurable : MeasurableSpace (Space H) :=
  inferInstanceAs (MeasurableSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceCompact : CompactSpace (Space H) :=
  inferInstanceAs (CompactSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceT2 : T2Space (Space H) :=
  inferInstanceAs (T2Space ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceTotallyDisconnected : TotallyDisconnectedSpace (Space H) :=
  inferInstanceAs (TotallyDisconnectedSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance quotientCountable [Countable H] (S : Subgroup H) : Countable (H ⧸ S) :=
  (QuotientGroup.mk_surjective (s := S)).countable

instance spaceMetrizable [Countable H] : TopologicalSpace.MetrizableSpace (Space H) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceBorel [Countable H] : BorelSpace (Space H) :=
  inferInstanceAs (BorelSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

noncomputable instance spaceAction : MulAction H (Space H) where
  smul h ω a := shift _ (character a.val a.property).value h (ω a)
  one_smul ω := funext fun a => shift_one _ _ (ω a)
  mul_smul h k ω := funext fun a => shift_mul _ _ h k (ω a)

noncomputable def probability : Measure (Space H) :=
  Measure.infinitePi (fun a : {a : H // a ≠ 1} =>
    offsetMeasure (Subgroup.zpowers a.val) (C := (character a.val a.property).Color))

instance probability_isProbability : IsProbabilityMeasure (probability H) := by
  have : ∀ a : {a : H // a ≠ 1}, IsProbabilityMeasure
      (offsetMeasure (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)) :=
    fun a => offsetMeasure_probability _
  unfold probability
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BassTrace.FreeParameter

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SubdivisionWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset

open scoped Classical Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

def generatedComplex (T : Finset (Finset Y)) : PreAbstractSimplicialComplex Y where
  faces := {s | s.Nonempty ∧ ∃h : H,∃t∈T,s⊆h • t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    obtain ⟨h,u,hu,hsu⟩ := hs.2
    exact ⟨ht,h,u,hu,hts.trans hsu⟩

lemma generatedComplex_top_mem (T : Finset (Finset Y)) {t : Finset Y}
    (ht : t∈T) (hne : t.Nonempty) : t∈(generatedComplex (H := H) T).faces :=
  ⟨hne,1,t,ht,by simp only [one_smul,Finset.Subset.refl]⟩

end

section

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R)

def componentVertices (x : X) (F : (Q.point x).FinalFace) : Finset Y :=
  (componentSupport_finite Γ hΓ Q hK hn hR x F).toFinset

@[simp] lemma mem_componentVertices (x : X) (F : (Q.point x).FinalFace) (y : Y) :
    y∈componentVertices Γ hΓ Q hK hn hR x F ↔
      y∈supportVertices ((Q.point x).faceComponent F) := Set.Finite.mem_toFinset _

end

open Set Finset

open scoped BassTrace.Sparse Classical

end BassTrace.Sparse

namespace BassTrace.SubdivisionChains

section

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]

variable {K : PreAbstractSimplicialComplex Y}

variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

def chart {k : ℕ} (v : Fin k → Y) : (Y →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi (fun i=>Finsupp.lapply (v i))

omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
@[simp] lemma chart_apply {k : ℕ} (v : Fin k → Y) (p : Y →₀ ℝ) (i : Fin k) :
    chart v p i=p (v i) := rfl

def localTriangulation (s : Finset Y) :=
  Cuts.restrictComplex T.complex (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))

omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_finite (s : Finset Y) (hs : s∈K.faces) :
    (localTriangulation T s).faces.Finite := T.finite (simplexVertices s) ⟨s,hs,rfl⟩

def tupleSubdivision (k : ℕ) (v : Fin (k+1) → Y) : Degree (Y →₀ ℝ) (k+1) :=
  if hs : Finset.univ.image v∈K.faces then
    chain (faces (localTriangulation T (Finset.univ.image v))
      (localTriangulation_finite T _ hs) (k+1)) (chart v)
  else 0

omit [LinearOrder Y] in
lemma chain_chart_perm {k : ℕ} (A : Finset (Set.powersetCard (Y →₀ ℝ) (k+1)))
    (v : Fin (k+1) → Y) (σ : Equiv.Perm (Fin (k+1))) :
    chain A (chart (v ∘ σ))=(Equiv.Perm.sign σ) • chain A (chart v) := by
  unfold chain
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have he : Matrix.det (fun i=>chart (v ∘ σ) (vertices s i))=
      (Equiv.Perm.sign σ : ℝ)*Matrix.det (fun i=>chart v (vertices s i)) :=
    by exact Matrix.det_permute' σ (fun i j=>vertices s i (v j))
  rw [he]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp only [h,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,
      Real.sign_neg,Complex.ofReal_neg,Units.neg_smul,one_smul]
    exact _root_.neg_smul (Real.sign (Matrix.det (fun i=>chart v (vertices s i))) : ℂ)
      (basis (k+1) s)

lemma tupleSubdivision_perm (k : ℕ) (v : Fin (k+1) → Y)
    (σ : Equiv.Perm (Fin (k+1))) :
    tupleSubdivision T k (v ∘ σ)=(Equiv.Perm.sign σ) • tupleSubdivision T k v := by
  unfold tupleSubdivision
  simp only [tuple_image_perm]
  split_ifs with hs
  · exact chain_chart_perm _ v σ
  · simp

lemma tupleSubdivision_zero (k : ℕ) (v : Fin (k+1) → Y)
    (hv : ¬Function.Injective v) : tupleSubdivision T k v=0 := by
  unfold tupleSubdivision
  split_ifs with hs
  · unfold chain
    apply Finset.sum_eq_zero
    intro s _
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hv
    have hd : Matrix.det (fun a=>chart v (vertices s a))=0 :=
      Matrix.det_zero_of_column_eq hne (fun a=>congrArg (vertices s a) hij)
    rw [hd,Real.sign_zero,Complex.ofReal_zero,zero_smul]
  · rfl

def subdivisionValues (k : ℕ) : AltFunction Y (k+1) (Degree (Y →₀ ℝ) (k+1)) where
  toFun := tupleSubdivision T k
  perm := tupleSubdivision_perm T k
  zero := tupleSubdivision_zero T k

def subdivision : ∀ k, Degree Y k →ₗ[ℂ] Degree (Y →₀ ℝ) k
  | 0 => relabel 0 (fun y=>Finsupp.single y (1:ℝ))
  | k+1 => (subdivisionValues T k).lift

@[simp] lemma subdivision_wedge_succ (k : ℕ) (v : Fin (k+1) → Y) :
    subdivision T (k+1) (wedge (k+1) v)=tupleSubdivision T k v :=
  (subdivisionValues T k).lift_wedge v

end

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

end BassTrace.SubdivisionChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SparseChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

def augmentedComplex (K : PreAbstractSimplicialComplex Y) : ChainHomotopy.Complex Y where
  faces := insert ∅ K.faces
  empty_mem := Set.mem_insert _ _
  down_closed := by
    intro s t hs hts
    by_cases ht : t.Nonempty
    · rcases hs with rfl | hs
      · exact False.elim (ht.ne_empty (Finset.subset_empty.mp hts))
      · exact Set.mem_insert_of_mem _ ((K.isRelLowerSet_faces hs).2 hts ht)
    · exact Set.mem_insert_iff.mpr (Or.inl (Finset.not_nonempty_iff_eq_empty.mp ht))

end BassTrace.Sparse

namespace BassTrace.PathChains

section

open Set Finset Oriented ChainHomotopy Paths Detector Sparse BarycentricChains

open scoped Classical Pointwise BassTrace.Detector

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]

def topPaths (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : Finset (Finset (Vertex g)) :=
  (((pathVector e g n).support).filter (fun q=>Function.Injective (project g ∘ q.out))).image
    (fun q=>Finset.univ.image (project g ∘ q.out))

lemma topPaths_mem (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (q : Orbit g n) (hq : q∈(pathVector e g n).support)
    (hi : Function.Injective (project g ∘ q.out)) :
    Finset.univ.image (project g ∘ q.out) ∈ topPaths e g n := by
  exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hi⟩,rfl⟩

def pathSupport (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    PreAbstractSimplicialComplex (Vertex g) := generatedComplex (H := ActingGroup g) (topPaths e g n)

def liftPath (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : Degree (Vertex g) (n+1) :=
  Finsupp.linearCombination ℂ (fun q : Orbit g n=>wedge (n+1) (project g ∘ q.out)) (pathVector e g n)

lemma liftPath_mem (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) [LinearOrder (Vertex g)] :
    liftPath e g n∈(augmentedComplex (pathSupport e g n)).chains (n+1) := by
  classical
  unfold liftPath Finsupp.linearCombination
  simp only [Finsupp.lsum_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro q hq
  change (pathVector e g n) q • wedge (n+1) (project g ∘ q.out) ∈ _
  by_cases hi : Function.Injective (project g ∘ q.out)
  · apply Submodule.smul_mem
    apply Complex.wedge_mem
    apply Set.mem_insert_of_mem
    apply generatedComplex_top_mem (topPaths e g n)
    · convert topPaths_mem e g n q hq hi using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      exact Subsingleton.elim _ _
    · exact Finset.image_nonempty.mpr Finset.univ_nonempty
  · simp only [wedge_eq_zero_of_not_injective _ hi,smul_zero]
    exact Submodule.zero_mem _

end

open Oriented ChainHomotopy Paths Detector Sparse BarycentricChains

open scoped Classical BassTrace.Detector

end BassTrace.PathChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AveragedChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.FiniteAverage

open Set Finset MeasureTheory

open scoped Classical

variable {X V W Z : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Z] [Module ℂ Z]

variable (μ : Measure X) [IsFiniteMeasure μ]

def locallyConstantLinearMap (F : X → V →ₗ[ℂ] W)
    (hF : ∀v,IsLocallyConstant (fun x=>F x v)) : V →ₗ[ℂ] W where
  toFun v := average μ (ofLocallyConstant _ (hF v))
  map_add' a b := by
    have he : ofLocallyConstant (fun x=>F x (a+b)) (hF (a+b)) =
        ofLocallyConstant (fun x=>F x a) (hF a)+ofLocallyConstant (fun x=>F x b) (hF b) := by
      ext x
      exact map_add (F x) a b
    rw [he,average_add]
  map_smul' r v := by
    let L : W →ₗ[ℝ] W := (r • (LinearMap.id : W →ₗ[ℂ] W)).restrictScalars ℝ
    have he : ofLocallyConstant (fun x=>F x (r • v)) (hF (r • v)) =
        (ofLocallyConstant (fun x=>F x v) (hF v)).map L := by
      ext x
      exact map_smul (F x) r v
    rw [he,average_map]
    rfl

end BassTrace.FiniteAverage

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BarycentricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.BarycentricChains

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence

variable {V Y : Type*} [LinearOrder V]

def filteredLabel (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ) :
    ∀k,Set.powersetCard V (k+1) → Degree Y (k+1)
  | 0,s => if ℓ s.val=0 then labelMap b 1 (basis 1 s) else 0
  | k+1,s => if ℓ s.val=k+1 then cone (k+1) (b s.val)
      (∑i : Fin (k+2),(-1:ℂ)^i.val • filteredLabel b ℓ k (eraseFace s i)) else 0

def filteredCount (ℓ : Finset V → ℕ) : ∀k,Set.powersetCard V (k+1) → ℕ
  | 0,s => if ℓ s.val=0 then 1 else 0
  | k+1,s => if ℓ s.val=k+1 then ∑i : Fin (k+2),filteredCount ℓ k (eraseFace s i) else 0

end

section

open Set Finset

open scoped Classical

open OrientedIncidence Fundamental Sparse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearOrder V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace ActualFlags

variable (Q : Cuts.PointFiltration K n)

def level (s : Finset V) : ℕ := if hs : s∈(Q.T 0).faces then Q.faceLevel ⟨s,hs⟩ else 0

end ActualFlags

end

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence Sparse

variable {V Y : Type*} [LinearOrder V]

def coneLeft (k : ℕ) (c : Degree Y k) : (Y →₀ ℂ) →ₗ[ℂ] Degree Y (k+1) where
  toFun b:=cone k b c
  map_add' a b:=by ext; simp only [cone_coe,map_add,add_mul,Submodule.coe_add]
  map_smul' r b:=by ext; simp only [cone_coe,map_smul,smul_mul_assoc,Submodule.coe_smul,RingHom.id_apply]

end

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence Sparse Fundamental

end BassTrace.BarycentricChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Definitions
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Core definitions for matrix and projective-module traces. -/

noncomputable section

namespace BassTrace

open scoped Classical

namespace K0

open scoped Classical BigOperators

section

variable {R : Type*} [Ring R]

def classOf (e : Idempotent R) : Group R := QuotientAddGroup.mk' (relations R) (FreeAbelianGroup.of e)

end

variable {G : Type*} [_root_.Group G]

def classTrace (a : MonoidAlgebra ℂ G) : ConjClasses G →₀ ℂ :=
  Finsupp.mapDomain ConjClasses.mk a.coeff

end K0

namespace RightProjective

open scoped Classical BigOperators

open MulOpposite

section

variable {R : Type*} [Ring R]

instance rightModuleIdentityRingHomInvPair :
    RingHomInvPair (RingHom.id Rᵐᵒᵖ) (RingHom.id Rᵐᵒᵖ) := RingHomInvPair.ids

end

open scoped Classical

universe u v

structure Object (R : Type u) [Ring R] where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module Rᵐᵒᵖ carrier]
  [finite : Module.Finite Rᵐᵒᵖ carrier]
  [projective : Module.Projective Rᵐᵒᵖ carrier]

attribute [instance] Object.addCommGroup Object.module Object.finite Object.projective

end RightProjective

end BassTrace

end

end OAI
end



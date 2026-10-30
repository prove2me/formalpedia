-- Prove2me | Definitions.Def_OAIQ115N004
-- name    : OAIQ115N004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:26:05.748081+00:00
-- url     : https://prove2.me/theorems/8aa7acd6-0833-4f5a-ba80-193a17b2986e
-- title:
--   Definitions bundle OAIQ115N004 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 29 definitions, 1 inductive type or structure, 1 instance and 45 theorems. The definitions and types are `OAI.NaimarkZFC.AtomicAmalgamData`, `OAI.NaimarkZFC.AtomicCStar`, `OAI.NaimarkZFC.AtomicHilbertSpace`, `OAI.NaimarkZFC.AtomicOperators`, `OAI.NaimarkZFC.atomicAlgebra`, `OAI.NaimarkZFC.atomicCStarAlgebra`, `OAI.NaimarkZFC.atomicCenteredSubmodule`, `OAI.NaimarkZFC.atomicColumnReps`, `OAI.NaimarkZFC.atomicCommonAtom`, `OAI.NaimarkZFC.atomicFactor`, `OAI.NaimarkZFC.atomicFockRepresentation`, `OAI.NaimarkZFC.atomicLeft`, `OAI.NaimarkZFC.atomicStarAlgebra`, `OAI.NaimarkZFC.atomicState`, `OAI.NaimarkZFC.atomicVacuum`, `OAI.NaimarkZFC.finiteAtomicDiagonal`, `OAI.NaimarkZFC.fockBlockUnitary`, `OAI.NaimarkZFC.fockColumnVertex`, `OAI.NaimarkZFC.fockStartProjection`, `OAI.NaimarkZFC.fockVacuum`, `OAI.NaimarkZFC.fockVacuumIndex`, `OAI.NaimarkZFC.hilbertSumMap`, `OAI.NaimarkZFC.hilbertSumRepresentation`, `OAI.NaimarkZFC.indexedColumnRepresentation`, `OAI.NaimarkZFC.l2Embed`, `OAI.NaimarkZFC.l2Reindex`, `OAI.NaimarkZFC.l2RootTruncation`, `OAI.NaimarkZFC.l2Sigma`, `OAI.NaimarkZFC.operatorVectorFunctional`, `OAI.NaimarkZFC.sumHilbertBasis`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_States`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/States.lean).
--
--   **Imports.** It imports the bundles `OAIQ115N000` and `OAIQ115N001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N007`, `OAIQ115N008` and `OAIQ115N009`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ115N000
import Definitions.Def_OAIQ115N001

section
-- module Solutions.OAIQ115_Naimark.Naimark_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

instance cornerPartialOrder : PartialOrder (CStarCorner e he) :=
  CStarAlgebra.spectralOrder _

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology

open scoped ComplexOrder ComplexStarModule

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

open scoped CStarAlgebra

open Filter Topology
open scoped ComplexOrder ComplexStarModule

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projectionRow_eigen (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    [DecidableEq V] (l k : V) (x : H) (hx : x ∈ projectionRow π e k) :
    π (e l).1 x = if l = k then x else 0 := by
  rcases hx with ⟨u,rfl⟩
  change (π (e l).1 * π (e k).1) u = _
  rw [← map_mul]
  by_cases hlk : l = k
  · subst k; rw [(e l).property.isIdempotentElem.eq, ite_eq_left rfl]; rfl
  · rw [horth l k hlk, map_zero, zero_apply, ite_eq_right hlk]

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem tracialColumnBasis_row (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V)
    (j : Option (Σ l, CenteredColumnIndex τ hτ e l r)) :
    tracialColumnBasis τ hτ e horth hmass hpos r j ∈
      projectionRow (traceColumnRepresentation τ hτ (e r)) e (columnVertex r j) := by
  cases j with
  | none => exact ⟨columnUnit τ hτ (e r), by
      rw [tracialColumnBasis_none]
      exact columnUnit_ownRow τ hτ (e r)⟩
  | some j =>
    rcases j with ⟨l,t⟩
    simp only [tracialColumnBasis, vacuumRowBasis, HilbertBasis.coe_mkOfOrthogonalEqBot,
      vacuumRowFamily]
    exact (hilbertChoiceBasis (CenteredColumn τ hτ e l r) t).property.1

def indexedColumnRepresentation (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) :
    A →⋆ₐ[ℂ] (ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ) →L[ℂ]
      ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ)) := by
  letI : Algebra ℂ (TraceColumn τ hτ (e r) →L[ℂ] TraceColumn τ hτ (e r)) :=
    ContinuousLinearMap.algebra
  exact ((tracialColumnBasis τ hτ e horth hmass hpos r).repr.conjStarAlgEquiv).toStarAlgHom.comp
    (traceColumnRepresentation τ hτ (e r))

theorem indexedColumnRepresentation_atom [DecidableEq V] (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r l : V)
    (x : ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ))
    (j : Option (Σ l, CenteredColumnIndex τ hτ e l r)) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r (e l).1 x j =
      if l = columnVertex r j then x j else 0 := by
  classical
  let b := tracialColumnBasis τ hτ e horth hmass hpos r
  let π := traceColumnRepresentation τ hτ (e r)
  change b.repr (π (e l).1 (b.repr.symm x)) j = _
  have hs : (π (e l).1).adjoint = π (e l).1 := ((e l).property.map π).isSelfAdjoint.star_eq
  have eigen : π (e l).1 (b j) = if l = columnVertex r j then b j else 0 :=
    projectionRow_eigen π e horth l _ _
      (tracialColumnBasis_row τ hτ e horth hmass hpos r j)
  calc
    b.repr (π (e l).1 (b.repr.symm x)) j =
        inner ℂ (b j) (π (e l).1 (b.repr.symm x)) := b.repr_apply_apply _ j
    _ = inner ℂ ((π (e l).1).adjoint (b j)) (b.repr.symm x) :=
      (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    _ = inner ℂ (if l = columnVertex r j then b j else 0) (b.repr.symm x) :=
      congrArg (fun vector : TraceColumn τ hτ (e r) => inner ℂ vector (b.repr.symm x))
        ((congrArg (fun operator : TraceColumn τ hτ (e r) →L[ℂ] TraceColumn τ hτ (e r) =>
          operator (b j)) hs).trans eigen)
    _ = if l = columnVertex r j then x j else 0 := by
      split_ifs
      · exact (b.repr_apply_apply (b.repr.symm x) j).symm.trans
          (congrArg (fun vector => vector j) (b.repr.apply_symm_apply x))
      · exact inner_zero_left _

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem hilbertBasisReindex_apply (b : HilbertBasis ι ℂ H) (e : ι ≃ κ) (j : κ) :
    hilbertBasisReindex b e j = b (e.symm j) := by
  simp [hilbertBasisReindex]

@[simp] theorem l2Basis_apply [DecidableEq ι] (i : ι) : l2Basis ι i = lp.single 2 i (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]; rfl

def l2Reindex (e : ι ≃ κ) : ℓ²(ι, ℂ) ≃ₗᵢ[ℂ] ℓ²(κ, ℂ) :=
  (hilbertBasisReindex (l2Basis ι) e).repr

@[simp] theorem l2Reindex_apply (e : ι ≃ κ) (x : ℓ²(ι, ℂ)) (j : κ) :
    l2Reindex e x j = x (e.symm j) := by
  classical
  rw [l2Reindex, HilbertBasis.repr_apply_apply, hilbertBasisReindex_apply, l2Basis_apply]
  simp [lp.inner_single_left]

@[simp] theorem l2Reindex_single [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (i : ι) (c : ℂ) :
    l2Reindex e (lp.single 2 i c) = lp.single 2 (e i) c := by
  classical
  ext j
  simp only [l2Reindex_apply, lp.single_apply]
  by_cases h : j = e i
  · subst j; simp
  · have h' : e.symm j ≠ i := fun he => h (by simpa using congrArg e he)
    simp [h, h']

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

omit [∀ i, CompleteSpace (H i)] in

theorem sumBasis_orthonormal [DecidableEq ι] (b : ∀ i, HilbertBasis (J i) ℂ (H i)) :
    Orthonormal ℂ (fun j : Σ i, J i => lp.single 2 j.1 (b j.1 j.2)) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro ⟨i,j⟩
    simpa only [lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))] using (b i).orthonormal.1 j
  · rintro ⟨i,j⟩ ⟨k,l⟩ hne
    rw [lp.inner_single_left]
    by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := fun h => hne (by subst l; rfl)
      simpa only [lp.single_apply, Pi.single_eq_same] using (b i).orthonormal.2 hjl
    · simp [lp.single_apply, hik]

def sumHilbertBasis [DecidableEq ι] (b : ∀ i, HilbertBasis (J i) ℂ (H i)) :
    HilbertBasis (Σ i, J i) ℂ (lp H 2) :=
  HilbertBasis.mkOfOrthogonalEqBot (sumBasis_orthonormal b) (by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    ext i
    apply (b i).repr.injective
    ext j
    simp only [lp.coeFn_zero, Pi.zero_apply, map_zero]
    rw [HilbertBasis.repr_apply_apply]
    have hm := (Submodule.mem_orthogonal _ _).mp hx (lp.single 2 i (b i j))
      (Submodule.subset_span ⟨⟨i,j⟩, rfl⟩)
    simpa only [lp.inner_single_left] using hm)

@[simp] theorem sumHilbertBasis_apply [DecidableEq ι]
    (b : ∀ i, HilbertBasis (J i) ℂ (H i)) (j : Σ i, J i) :
    sumHilbertBasis b j = lp.single 2 j.1 (b j.1 j.2) := by
  simp [sumHilbertBasis]

def l2Sigma [DecidableEq ι] (J : ι → Type*) :
    lp (fun i => ℓ²(J i, ℂ)) 2 ≃ₗᵢ[ℂ] ℓ²((Σ i, J i), ℂ) :=
  (sumHilbertBasis fun i => l2Basis (J i)).repr

@[simp] theorem l2Sigma_apply [DecidableEq ι] (x : lp (fun i => ℓ²(J i, ℂ)) 2)
    (j : Σ i, J i) : l2Sigma J x j = x j.1 j.2 := by
  classical
  rw [l2Sigma, HilbertBasis.repr_apply_apply, sumHilbertBasis_apply,
    l2Basis_apply, lp.inner_single_left]
  simp [lp.inner_single_left]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

def hilbertSumMap (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : lp H 2 →L[ℂ] lp K 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => T i (x i),
        ((lp.memℓp x).norm.const_mul C).mono fun i =>
          ((T i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))⟩
      map_add' := fun x y => by ext i; exact map_add (T i) _ _
      map_smul' := fun c x => by ext i; exact map_smul (T i) _ _ }
    C (fun x => by
      calc
        _ ≤ ‖C • lp.toNorm x‖ := lp.norm_mono (by norm_num) fun i => by
          change ‖T i (x i)‖ ≤ ‖C * ‖x i‖‖
          rw [Real.norm_of_nonneg (mul_nonneg hC (norm_nonneg _))]
          exact ((T i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
        _ = C * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hC, lp.norm_toNorm])

@[simp] theorem hilbertSumMap_apply (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp H 2) (i : ι) :
    hilbertSumMap T C hC hT x i = T i (x i) := rfl

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

theorem hilbertSumMap_adjoint (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) :
    hilbertSumMap (fun i => (T i).adjoint) C hC (fun i => by simpa using hT i) =
      (hilbertSumMap T C hC hT).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum, hilbertSumMap_apply]
  apply tsum_congr
  intro i
  exact ContinuousLinearMap.adjoint_inner_left (T i) _ _

variable {A : Type*} [CStarAlgebra A]

def hilbertSumRepresentation (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := hilbertSumMap (fun i => π i a) ‖a‖ (norm_nonneg _) (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) a)
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_mul' a b := by ext x i; simp
  commutes' c := by
    ext x i
    change (π i (algebraMap ℂ A c)) (x i) = c • x i
    exact congrArg (fun T : H i →L[ℂ] H i => T (x i)) ((π i).commutes c)
  map_star' a := by
    have h := hilbertSumMap_adjoint (fun i => π i a) ‖a‖ (norm_nonneg _)
      (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) a)
    change _ = (hilbertSumMap (fun i => π i a) ‖a‖ (norm_nonneg _) _).adjoint
    rw [← h]
    ext x i
    exact congrArg (fun T : H i →L[ℂ] H i => T (x i)) (map_star (π i) a)

@[simp] theorem hilbertSumRepresentation_apply (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
    (a : A) (x : lp H 2) (i : ι) : hilbertSumRepresentation π a x i = π i a (x i) := rfl

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def fockBlockUnitary (i : I) : FactorBlockSpace L i ≃ₗᵢ[ℂ] AtomicFockSpace L := by
  classical
  exact (l2Sigma fun t : FockTail L i => ColumnIndex L i t.1.2.1).trans
    (l2Reindex (fockBlockEquiv L i))

@[simp] theorem fockBlockUnitary_apply (i : I) (x : FactorBlockSpace L i)
    (j : FockIndex L) :
    fockBlockUnitary L i x j = x (fockSplit L i j).1 (fockSplit L i j).2 := by
  classical
  simp only [fockBlockUnitary, LinearIsometryEquiv.trans_apply, l2Reindex_apply, l2Sigma_apply]
  rfl

@[simp] theorem fockBlockUnitary_apply_join (i : I) (x : FactorBlockSpace L i)
    (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    fockBlockUnitary L i x (fockJoin L i ⟨t,c⟩) = x t c := by
  rw [fockBlockUnitary_apply, fockSplit_join]

@[simp] theorem fockBlockUnitary_symm_apply (i : I) (x : AtomicFockSpace L)
    (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    (fockBlockUnitary L i).symm x t c = x (fockJoin L i ⟨t,c⟩) := by
  have h := fockBlockUnitary_apply_join L i ((fockBlockUnitary L i).symm x) t c
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

def atomicFockRepresentation
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (i : I) : A i →⋆ₐ[ℂ] (AtomicFockSpace L →L[ℂ] AtomicFockSpace L) :=
  ((fockBlockUnitary L i).conjStarAlgEquiv).toStarAlgHom.comp
    (hilbertSumRepresentation fun t : FockTail L i => π i t.1.2.1)

theorem atomicFockRepresentation_block
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (i : I) (a : A i) (x : AtomicFockSpace L) (t : FockTail L i)
    (c : ColumnIndex L i t.1.2.1) :
    atomicFockRepresentation L π i a x (fockJoin L i ⟨t,c⟩) =
      π i t.1.2.1 a ((fockBlockUnitary L i).symm x t) c := by
  change fockBlockUnitary L i
    ((hilbertSumRepresentation fun t : FockTail L i => π i t.1.2.1) a
    ((fockBlockUnitary L i).symm x)) (fockJoin L i ⟨t,c⟩) = _
  rw [fockBlockUnitary_apply_join, hilbertSumRepresentation_apply]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def fockColumnVertex (i : I) (r : V) : ColumnIndex L i r → V
  | none => r
  | some ⟨l,_⟩ => l

omit [DecidableEq I] in
@[simp] theorem fockJoin_left (i : I) (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    (fockJoin L i ⟨t,c⟩).2.1 = fockColumnVertex L i t.1.2.1 c := by
  cases c with
  | none => rfl
  | some c => cases c; rfl

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

theorem atomicFockRepresentation_diagonal [DecidableEq V]
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (e : ∀ i, V → A i)
    (hdiag : ∀ i r l, ∀ x : ℓ²(ColumnIndex L i r, ℂ), ∀ c,
      π i r (e i l) x c = if l = fockColumnVertex L i r c then x c else 0)
    (i : I) (l : V) (x : AtomicFockSpace L) (j : FockIndex L) :
    atomicFockRepresentation L π i (e i l) x j = if l = j.2.1 then x j else 0 := by
  obtain ⟨⟨t,c⟩, rfl⟩ := (fockBlockEquiv L i).surjective j
  change atomicFockRepresentation L π i (e i l) x (fockJoin L i ⟨t,c⟩) = _
  rw [atomicFockRepresentation_block, hdiag, fockBlockUnitary_symm_apply]
  change (if l = fockColumnVertex L i t.1.2.1 c then
    x (fockJoin L i ⟨t,c⟩) else 0) =
    if l = (fockJoin L i ⟨t,c⟩).2.1 then x (fockJoin L i ⟨t,c⟩) else 0
  rw [fockJoin_left]

theorem atomicFockRepresentation_agree_atoms [DecidableEq V]
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (e : ∀ i, V → A i)
    (hdiag : ∀ i r l, ∀ x : ℓ²(ColumnIndex L i r, ℂ), ∀ c,
      π i r (e i l) x c = if l = fockColumnVertex L i r c then x c else 0)
    (i k : I) (l : V) :
    atomicFockRepresentation L π i (e i l) = atomicFockRepresentation L π k (e k l) := by
  ext x j
  rw [atomicFockRepresentation_diagonal L π e hdiag,
    atomicFockRepresentation_diagonal L π e hdiag]

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def fockStartProjection (i : I) : AtomicFockSpace L →L[ℂ] AtomicFockSpace L :=
  hilbertSumMap (fun j : FockIndex L =>
    if j.1 = some i then (1 : ℂ →L[ℂ] ℂ) else 0) 1 zero_le_one
    (fun j => by split_ifs <;> simp)

@[simp] theorem fockStartProjection_apply (i : I) (x : AtomicFockSpace L) (j : FockIndex L) :
    fockStartProjection L i x j = if j.1 = some i then x j else 0 := by
  simp only [fockStartProjection, hilbertSumMap_apply]
  split_ifs <;> rfl

@[simp] theorem fockStartProjection_star (i : I) :
    star (fockStartProjection L i) = fockStartProjection L i := by
  change (fockStartProjection L i).adjoint = _
  rw [fockStartProjection, ← hilbertSumMap_adjoint]
  ext x j
  simp only [hilbertSumMap_apply]
  split_ifs <;> simp [ContinuousLinearMap.adjoint_one]

end

open scoped InnerProductSpace lp
variable {V J : Type*}

def l2Embed (e : V ↪ J) : ℓ²(V, ℂ) →ₗᵢ[ℂ] ℓ²(J, ℂ) :=
  ((l2Basis J).orthonormal.comp e e.injective).orthogonalFamily.linearIsometry

@[simp] theorem l2Embed_single [DecidableEq V] [DecidableEq J] (e : V ↪ J) (r : V) (c : ℂ) :
    l2Embed e (lp.single 2 r c) = lp.single 2 (e r) c := by
  rw [l2Embed, OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply, l2Basis_apply, ← lp.single_smul]

@[simp] theorem l2Embed_apply (e : V ↪ J) (z : ℓ²(V, ℂ)) (r : V) :
    l2Embed e z (e r) = z r := by
  classical
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z).mapL
    ((lp.evalCLM ℂ (fun _ : J => ℂ) 2 (e r)).comp (l2Embed e).toContinuousLinearMap)
  simpa [lp.evalCLM, l2Embed_single, lp.single_apply, Pi.single_apply, e.injective.eq_iff] using h.tsum_eq.symm

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*)

def fockVacuumIndex : V ↪ FockIndex L where
  toFun r := ⟨none, r, .nil r⟩
  inj' _r _s hrs := congrArg (fun j : FockIndex L => j.2.1) hrs

def fockVacuum (z : ℓ²(V, ℂ)) : AtomicFockSpace L := l2Embed (fockVacuumIndex L) z

@[simp] theorem fockVacuum_apply_nil (z : ℓ²(V, ℂ)) (r : V) :
    fockVacuum L z ⟨none,r,.nil r⟩ = z r := l2Embed_apply _ _ _

@[simp] theorem fockVacuum_norm (z : ℓ²(V, ℂ)) : ‖fockVacuum L z‖ = ‖z‖ :=
  (l2Embed _).norm_map z

end

section
open scoped lp InnerProductSpace ENNReal
variable {V : Type*} (w : V → ℝ) (hw : ∀ r, 0 ≤ w r) (hm : HasSum w 1)

@[simp] theorem atomicWeightVector_apply (r : V) :
    atomicWeightVector w hw hm r = (Real.sqrt (w r) : ℂ) := rfl

@[simp] theorem atomicWeightVector_norm : ‖atomicWeightVector w hw hm‖ = 1 := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (atomicWeightVector w hw hm)
  have hc (r : V) : ‖atomicWeightVector w hw hm r‖ ^ 2 = w r := by
    simp only [atomicWeightVector_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw r)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hc, hm.tsum_eq] at hn
  nlinarith [norm_nonneg (atomicWeightVector w hw hm)]

end

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorVectorFunctional (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ where
  toFun T := inner ℂ ξ (T ξ)
  map_add' S T := by simp
  map_smul' c T := by simp
  cont := by fun_prop

@[simp] theorem operatorVectorFunctional_apply (ξ : H) (T : H →L[ℂ] H) :
    operatorVectorFunctional ξ T = inner ℂ ξ (T ξ) := rfl

@[simp] theorem operatorVectorFunctional_star (ξ : H) (T : H →L[ℂ] H) :
    operatorVectorFunctional ξ (star T) = star (operatorVectorFunctional ξ T) := by
  change inner ℂ ξ (T.adjoint ξ) = star (inner ℂ ξ (T ξ))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (T ξ) ξ).symm

section
open scoped InnerProductSpace lp

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

abbrev AtomicHilbertSpace : Type _ := AtomicFockSpace (AtomicLetters d)

def atomicColumnReps (i : I) (r : V) :
    A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex (AtomicLetters d) i r, ℂ) →L[ℂ]
      ℓ²(ColumnIndex (AtomicLetters d) i r, ℂ)) :=
  indexedColumnRepresentation (d i).trace (d i).tracial (d i).atom
    (d i).orthogonal (d i).mass (d i).positive r

variable [DecidableEq I]

def atomicLeft (i : I) : A i →⋆ₐ[ℂ] (AtomicHilbertSpace d →L[ℂ] AtomicHilbertSpace d) :=
  atomicFockRepresentation (AtomicLetters d) (atomicColumnReps d) i

theorem atomicLeft_atoms [DecidableEq V] (i k : I) (r : V) :
    atomicLeft d i ((d i).atom r).1 = atomicLeft d k ((d k).atom r).1 := by
  apply atomicFockRepresentation_agree_atoms (AtomicLetters d) (atomicColumnReps d)
    (fun i r => ((d i).atom r).1)
  intro j r l x c
  have hv : fockColumnVertex (AtomicLetters d) j r c = columnVertex r c := by
    cases c <;> rfl
  simpa only [atomicColumnReps, hv] using indexedColumnRepresentation_atom
    (d j).trace (d j).tracial (d j).atom (d j).orthogonal (d j).mass (d j).positive r l x c

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

def atomicVacuum (k : I) : AtomicHilbertSpace d :=
  fockVacuum (AtomicLetters d)
    (atomicWeightVector (fun r => ((d k).trace ((d k).atom r).1).re)
      (fun r => ((d k).positive r).le)
      (by simpa only [(d k).normalized, Complex.one_re] using (d k).mass))

@[simp] theorem atomicVacuum_norm (k : I) : ‖atomicVacuum d k‖ = 1 := by
  rw [atomicVacuum, fockVacuum_norm, atomicWeightVector_norm]

end

section

variable {I B : Type*} [Ring B] [Algebra ℂ B]

omit [Algebra ℂ B] in
@[simp] theorem wordValue_nil : wordValue ([] : List (I × B)) = 1 := rfl
omit [Algebra ℂ B] in
@[simp] theorem wordValue_cons (x : I × B) (w : List (I × B)) :
    wordValue (x :: w) = x.2 * wordValue w := rfl

end

section

variable {V B : Type*} [Ring B] [Algebra ℂ B]

variable (q : V → B)
variable (hq : ∀ r, q r * q r = q r)
variable (ho : ∀ r t, r ≠ t → q r * q t = 0)

omit [Algebra ℂ B] in
include hq ho in
lemma atom_mul_sum [DecidableEq V] (s : Finset V) (r : V) :
    q r * (∑ t ∈ s, q t) = if r ∈ s then q r else 0 := by
  rw [Finset.mul_sum]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, Finset.sum_eq_single r]
    · exact hq r
    · intro t _ ht
      exact ho r t ht.symm
    · exact fun hn => (hn hr).elim
  · rw [ite_eq_right hr]
    exact Finset.sum_eq_zero fun t ht => ho r t (by rintro rfl; exact hr ht)

include hq ho in
theorem finiteAtomicSpan_mul {s : Finset V} {a b : B}
    (ha : a ∈ finiteAtomicSpan q s) (hb : b ∈ finiteAtomicSpan q s) :
    a * b ∈ finiteAtomicSpan q s := by
  classical
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨r, hr, rfl⟩
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨t, _, rfl⟩
      by_cases ht : r = t
      · subst t
        rw [hq]
        exact Submodule.subset_span ⟨r, hr, rfl⟩
      · rw [ho r t ht]
        exact Submodule.zero_mem _
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (finiteAtomicSpan q s).add_mem hb hc
    | smul c b _ hb => simpa only [mul_smul_comm] using (finiteAtomicSpan q s).smul_mem c hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (finiteAtomicSpan q s).add_mem ha hc
  | smul c a _ ha => simpa only [smul_mul_assoc] using (finiteAtomicSpan q s).smul_mem c ha

def finiteAtomicDiagonal (s : Finset V) : NonUnitalSubalgebra ℂ B where
  __ := finiteAtomicSpan q s
  mul_mem' := finiteAtomicSpan_mul q hq ho

@[simp] theorem finiteAtomicDiagonal_toSubmodule (s : Finset V) :
    (finiteAtomicDiagonal q hq ho s).toSubmodule = finiteAtomicSpan q s := rfl

variable (φ : B →ₗ[ℂ] ℂ)

@[simp] theorem atomCornerFunctional_apply (r : V) (a : B) :
    atomCornerFunctional q φ r a = φ (q r * a * q r) := rfl

def atomicCenteredSubmodule (F : NonUnitalSubalgebra ℂ B) : Submodule ℂ B :=
  F.toSubmodule ⊓ ⨅ r, LinearMap.ker (atomCornerFunctional q φ r)

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

def l2RootTruncation (root : J → V) (s : Finset V) : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => if root j ∈ s then x j else 0,
        (lp.memℓp x).mono' (by intro j; split_ifs <;> simp_all)⟩
      map_add' := by
        intro x y
        ext j
        change (if root j ∈ s then x j + y j else 0) =
          (if root j ∈ s then x j else 0) + (if root j ∈ s then y j else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c x
        ext j
        change (if root j ∈ s then c • x j else 0) = c • (if root j ∈ s then x j else 0)
        split_ifs <;> simp }
    1 (by
      intro x
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro j
      change ‖if root j ∈ s then x j else 0‖ ≤ ‖x j‖
      split_ifs <;> simp)

@[simp] theorem l2RootTruncation_apply (root : J → V) (s : Finset V)
    (x : ℓ²(J, ℂ)) (j : J) :
    l2RootTruncation root s x j = if root j ∈ s then x j else 0 := rfl

variable [DecidableEq J]

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

abbrev AtomicOperators := AtomicHilbertSpace d →L[ℂ] AtomicHilbertSpace d

def atomicFactor (i : I) : NonUnitalSubalgebra ℂ (AtomicOperators d) :=
  NonUnitalAlgHom.range (atomicLeft d i).toAlgHom.toNonUnitalAlgHom

def atomicCommonAtom (k : I) (r : V) : AtomicOperators d :=
  atomicLeft d k ((d k).atom r).1

def atomicState (k : I) : AtomicOperators d →ₗ[ℂ] ℂ :=
  (operatorVectorFunctional (atomicVacuum d k)).toLinearMap

omit [DecidableEq I] in
@[simp] theorem atomicState_apply (k : I) (T : AtomicOperators d) :
    atomicState d k T = inner ℂ (atomicVacuum d k) (T (atomicVacuum d k)) := rfl

theorem atomicCommonAtom_idempotent (k : I) (r : V) :
    atomicCommonAtom d k r * atomicCommonAtom d k r = atomicCommonAtom d k r := by
  rw [atomicCommonAtom, ← map_mul, ((d k).atom r).property.isIdempotentElem.eq]

theorem atomicCommonAtom_orthogonal (k : I) (r t : V) (h : r ≠ t) :
    atomicCommonAtom d k r * atomicCommonAtom d k t = 0 := by
  rw [atomicCommonAtom, atomicCommonAtom, ← map_mul, (d k).orthogonal r t h, map_zero]

theorem atomicCommonAtom_mem [DecidableEq V] (k i : I) (r : V) :
    atomicCommonAtom d k r ∈ atomicFactor d i := by
  exact ⟨((d i).atom r).1, atomicLeft_atoms d i k r⟩

theorem atomicFactor_star (i : I) (a : AtomicOperators d) (ha : a ∈ atomicFactor d i) :
    star a ∈ atomicFactor d i := by
  change ∃ b, atomicLeft d i b = a at ha
  rcases ha with ⟨a,rfl⟩
  change ∃ b, atomicLeft d i b = star (atomicLeft d i a)
  exact ⟨star a, map_star _ _⟩

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]

theorem atomicCommonAtom_apply (k : I) (r : V) (x : AtomicHilbertSpace d)
    (j : FockIndex (AtomicLetters d)) :
    atomicCommonAtom d k r x j = if r = j.2.1 then x j else 0 := by
  apply atomicFockRepresentation_diagonal (AtomicLetters d) (atomicColumnReps d)
    (fun i r => ((d i).atom r).1)
  intro i r l x c
  have hv : fockColumnVertex (AtomicLetters d) i r c = columnVertex r c := by
    cases c <;> rfl
  simpa only [atomicColumnReps, hv] using indexedColumnRepresentation_atom
    (d i).trace (d i).tracial (d i).atom (d i).orthogonal (d i).mass (d i).positive r l x c

def atomicAlgebra : Subalgebra ℂ (AtomicOperators d) :=
  Algebra.adjoin ℂ (⋃ i, (atomicFactor d i : Set (AtomicOperators d)))

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

def atomicStarAlgebra : StarSubalgebra ℂ (AtomicOperators d) where
  toSubalgebra := atomicAlgebra d
  star_mem' := by
    intro T hT
    change star T ∈ atomicAlgebra d
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      rcases Set.mem_iUnion.mp hT with ⟨i,hi⟩
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i,atomicFactor_star d i T hi⟩)
    | algebraMap c =>
      simpa only [Algebra.algebraMap_eq_smul_one, star_smul, star_one] using
        (atomicAlgebra d).algebraMap_mem (star c)
    | add T U _ _ hT hU =>
      rw [star_add]
      exact (atomicAlgebra d).add_mem hT hU
    | mul T U _ _ hT hU =>
      rw [star_mul]
      exact (atomicAlgebra d).mul_mem hU hT

def atomicCStarAlgebra : StarSubalgebra ℂ (AtomicOperators d) :=
  (atomicStarAlgebra d).topologicalClosure

abbrev AtomicCStar := atomicCStarAlgebra d

end

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped CStarAlgebra

section
open scoped InnerProductSpace ComplexOrder CStarAlgebra lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
variable {Δ : Type*} [CStarAlgebra Δ]

structure AtomicAmalgamData where
  diagonal : ∀ i, Δ →⋆ₐ[ℂ] A i
  coordinate : Δ → V → ℂ
  atom_mul : ∀ i x r, ((d i).atom r).1 * diagonal i x =
    coordinate x r • ((d i).atom r).1
  expectation : ∀ i, A i →L[ℂ] Δ
  fix : ∀ i x, expectation i (diagonal i x) = x
  left : ∀ i x a, expectation i (diagonal i x * a) = x * expectation i a
  centered : ∀ i a, expectation i a = 0 → ∀ r,
    (d i).trace (((d i).atom r).1 * a * ((d i).atom r).1) = 0
  base : I
  weights : ∀ i r, ((d base).trace ((d base).atom r).1).re =
    ((d i).trace ((d i).atom r).1).re

end

open scoped ComplexOrder CStarAlgebra

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end



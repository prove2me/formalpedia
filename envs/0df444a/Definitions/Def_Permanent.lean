-- Prove2me | Definitions.Def_Permanent
-- name    : Permanent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-19T10:54:31.198+00:00
-- url     : https://prove2.me/theorems/2bcdbb7a-bdbb-4749-bc96-7e5e6a2e4d4c
-- title:
--   Permanent
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
namespace MvPolynomial.IsWeightedHomogeneous
end MvPolynomial.IsWeightedHomogeneous
namespace Finset
noncomputable def equivMap_tenProofs {α β : Type*}
    (f : α ↪ β) (s : Finset α) : s ≃ s.map f :=
  Equiv.ofBijective
    (fun a : s =>
      (⟨f a, Finset.mem_map.mpr ⟨a, a.property, rfl⟩⟩ : s.map f))
    ⟨by
      intro a b h
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val h), by
      intro b
      obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp b.property
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩
end Finset
namespace PermanentCircuitCompatibility
end PermanentCircuitCompatibility
namespace PermanentRollout
section Standalone_PermanentRolloutRoot
open scoped BigOperators
inductive Instruction (ι : Type) where
  | input (i : ι)
  | scalar (c : ℂ)
  | add (left right : ℕ)
  | sub (left right : ℕ)
  | mul (left right : ℕ)
def Instruction.referencesBounded {ι : Type} (position : ℕ) : Instruction ι → Bool
  | .input _ => true
  | .scalar _ => true
  | .add left right => left < position && right < position
  | .sub left right => left < position && right < position
  | .mul left right => left < position && right < position
def Instruction.isArithmetic {ι : Type} : Instruction ι → Bool
  | .input _ => false
  | .scalar _ => false
  | .add _ _ => true
  | .sub _ _ => true
  | .mul _ _ => true
noncomputable def Instruction.eval {ι : Type}
    (values : Array (MvPolynomial ι ℂ)) : Instruction ι → MvPolynomial ι ℂ
  | .input i => MvPolynomial.X i
  | .scalar c => MvPolynomial.C c
  | .add left right => values.getD left 0 + values.getD right 0
  | .sub left right => values.getD left 0 - values.getD right 0
  | .mul left right => values.getD left 0 * values.getD right 0
structure ArithmeticCircuit (ι : Type) where
  program : List (Instruction ι)
  output : ℕ
  output_lt : output < program.length
  valid : ∀ position : Fin program.length,
    (program.get position).referencesBounded position.val
noncomputable def ArithmeticCircuit.values {ι : Type}
    (circuit : ArithmeticCircuit ι) : Array (MvPolynomial ι ℂ) :=
  circuit.program.foldl
    (fun values instruction => values.push (instruction.eval values)) #[]
noncomputable def ArithmeticCircuit.polynomial {ι : Type}
    (circuit : ArithmeticCircuit ι) : MvPolynomial ι ℂ :=
  circuit.values.getD circuit.output 0
def ArithmeticCircuit.size {ι : Type} (circuit : ArithmeticCircuit ι) : ℕ :=
  (circuit.program.filter Instruction.isArithmetic).length
noncomputable def circuitComplexity {ι : Type} (f : MvPolynomial ι ℂ) : ℕ :=
  sInf {size : ℕ | ∃ circuit : ArithmeticCircuit ι,
    circuit.polynomial = f ∧ circuit.size = size}
noncomputable def permanent (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  Matrix.permanent (fun row column => MvPolynomial.X (row, column))
noncomputable def minorSum (t s d : ℕ) : MvPolynomial (Fin t × Fin s) ℂ :=
  ∑ rows ∈ (Finset.univ : Finset (Fin t)).powersetCard d,
    ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
      ∑ matching : rows ≃ columns,
        ∏ row : rows, MvPolynomial.X (row.val, (matching row).val)
noncomputable def powerSum (t s : ℕ) (rows : Finset (Fin t)) :
    MvPolynomial (Fin t × Fin s) ℂ :=
  ∑ column : Fin s, ∏ row ∈ rows, MvPolynomial.X (row, column)
noncomputable def criticalLocus {ι : Type}
    (P : MvPolynomial ι ℂ) : Set (ι → ℂ) :=
  {point | ∀ i : ι, MvPolynomial.eval point (MvPolynomial.pderiv i P) = 0}
end Standalone_PermanentRolloutRoot
section Standalone_Geometry
open scoped BigOperators
@[simp] theorem mem_criticalLocus_iff {ι : Type} (P : MvPolynomial ι ℂ)
    (point : ι → ℂ) :
    point ∈ criticalLocus P ↔
      ∀ i : ι, MvPolynomial.eval point (MvPolynomial.pderiv i P) = 0 := by
  rfl
noncomputable def linearSubspaceCoordinatePolynomial {k m : ℕ}
    (E : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (i : Fin m) :
    MvPolynomial (Fin k) ℂ :=
  ∑ j : Fin k,
    MvPolynomial.C ((E (Pi.single j 1)) i) * MvPolynomial.X j
theorem eval_linearSubspaceCoordinatePolynomial {k m : ℕ}
    (E : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (i : Fin m) (u : Fin k → ℂ) :
    MvPolynomial.eval u (linearSubspaceCoordinatePolynomial E i) = E u i := by
  classical
  calc
    MvPolynomial.eval u (linearSubspaceCoordinatePolynomial E i) =
        ∑ j : Fin k, (E (Pi.single j 1)) i * u j := by
      simp [linearSubspaceCoordinatePolynomial]
    _ = E u i := by
      conv_rhs => rw [pi_eq_sum_univ' u]
      simp [Finset.sum_apply, mul_comm]
noncomputable def linearSubspacePolynomialPullback {k m : ℕ}
    (E : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin k) ℂ :=
  MvPolynomial.aeval (linearSubspaceCoordinatePolynomial E)
theorem eval_linearSubspacePolynomialPullback {k m : ℕ}
    (E : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (u : Fin k → ℂ) (p : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.eval u (linearSubspacePolynomialPullback E p) =
      MvPolynomial.eval (E u) p := by
  change
    MvPolynomial.aeval u
        (MvPolynomial.aeval (linearSubspaceCoordinatePolynomial E) p) =
      MvPolynomial.aeval (E u) p
  have hcoordinates :
      (fun i =>
        MvPolynomial.aeval u (linearSubspaceCoordinatePolynomial E i)) =
        E u := by
    funext i
    exact eval_linearSubspaceCoordinatePolynomial E i u
  rw [MvPolynomial.comp_aeval_apply, hcoordinates]
theorem linearSubspacePolynomialPullback_surjective_of_leftInverse
    {k m : ℕ}
    (E : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (R : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hleft : Function.LeftInverse R E) :
    Function.Surjective (linearSubspacePolynomialPullback E) := by
  intro p
  refine ⟨linearSubspacePolynomialPullback R p,
    MvPolynomial.funext ?_⟩
  intro u
  rw [eval_linearSubspacePolynomialPullback,
    eval_linearSubspacePolynomialPullback, hleft u]
noncomputable def submoduleCoordinateEmbedding {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (Fin t → ℂ) :=
  W.subtype.comp (Module.finBasis ℂ W).equivFun.symm.toLinearMap
noncomputable def submoduleCoordinateRetraction {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    (Fin t → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
  (Module.finBasis ℂ W).equivFun.toLinearMap.comp W.subtype.leftInverse
theorem submoduleCoordinateRetraction_leftInverse {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    Function.LeftInverse (submoduleCoordinateRetraction W)
      (submoduleCoordinateEmbedding W) := by
  intro u
  change
    (Module.finBasis ℂ W).equivFun
        (W.subtype.leftInverse
          (W.subtype ((Module.finBasis ℂ W).equivFun.symm u))) = u
  rw [LinearMap.leftInverse_apply_of_inj W.ker_subtype]
  exact (Module.finBasis ℂ W).equivFun.apply_symm_apply u
noncomputable def submodulePolynomialRestriction {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    MvPolynomial (Fin t) ℂ →ₐ[ℂ]
      MvPolynomial (Fin (Module.finrank ℂ W)) ℂ :=
  linearSubspacePolynomialPullback (submoduleCoordinateEmbedding W)
theorem submodulePolynomialRestriction_surjective {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    Function.Surjective (submodulePolynomialRestriction W) :=
  linearSubspacePolynomialPullback_surjective_of_leftInverse
    (submoduleCoordinateEmbedding W) (submoduleCoordinateRetraction W)
    (submoduleCoordinateRetraction_leftInverse W)
theorem ker_submodulePolynomialRestriction_eq_vanishingIdeal {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    RingHom.ker (submodulePolynomialRestriction W).toRingHom =
      MvPolynomial.vanishingIdeal ℂ
        (W : Set (Fin t → ℂ)) := by
  ext p
  change
    submodulePolynomialRestriction W p = 0 ↔
      ∀ v ∈ (W : Set (Fin t → ℂ)), MvPolynomial.aeval v p = 0
  constructor
  · intro hp v hv
    let w : W := ⟨v, hv⟩
    let u : Fin (Module.finrank ℂ W) → ℂ :=
      (Module.finBasis ℂ W).equivFun w
    have heval := congrArg (MvPolynomial.eval u) hp
    rw [map_zero] at heval
    change
      MvPolynomial.eval u
          (linearSubspacePolynomialPullback
            (submoduleCoordinateEmbedding W) p) = 0 at heval
    rw [eval_linearSubspacePolynomialPullback] at heval
    have hpoint : submoduleCoordinateEmbedding W u = v := by
      change
        (↑((Module.finBasis ℂ W).equivFun.symm
          ((Module.finBasis ℂ W).equivFun w)) : Fin t → ℂ) = v
      rw [LinearEquiv.symm_apply_apply]
    rw [hpoint] at heval
    simpa [MvPolynomial.aeval_def] using heval
  · intro hp
    apply MvPolynomial.funext
    intro u
    simp only [map_zero]
    change
      MvPolynomial.eval u
        (linearSubspacePolynomialPullback
          (submoduleCoordinateEmbedding W) p) = 0
    rw [eval_linearSubspacePolynomialPullback]
    apply hp
    exact ((Module.finBasis ℂ W).equivFun.symm u).property
noncomputable def submoduleVanishingIdealCoordinateRingEquiv {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    (MvPolynomial (Fin t) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ (W : Set (Fin t → ℂ))) ≃ₐ[ℂ]
        MvPolynomial (Fin (Module.finrank ℂ W)) ℂ :=
  (Ideal.quotientEquivAlgOfEq ℂ
    (ker_submodulePolynomialRestriction_eq_vanishingIdeal W).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (submodulePolynomialRestriction_surjective W))
end Standalone_Geometry
section Standalone_Bezout
end Standalone_Bezout
section Standalone_FiberDimension
open Ideal
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
end Standalone_FiberDimension
section Standalone_GenericAvoidance
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
abbrev permanentRolloutUniformOutputChartDomain (k m : ℕ) : Type :=
  (Fin k → ℂ) × (Fin (k + 1) → Fin m → ℂ)
def permanentRolloutNormalizedInput {k : ℕ}
    (j : Fin (k + 1)) (x : Fin k → ℂ) : Fin (k + 1) → ℂ :=
  j.insertNth 1 x
def permanentRolloutOutputChart {k m : ℕ}
    (g : (Fin (k + 1) → ℂ) → (Fin (m + 1) → ℂ))
    (j : Fin (k + 1)) (ell : Fin (m + 1))
    (z : permanentRolloutUniformOutputChartDomain k m) :
    Fin (k + 1) → Fin (m + 1) → ℂ :=
  fun r =>
    ell.insertNth
      (-(∑ q : Fin m,
        z.2 r q * g (permanentRolloutNormalizedInput j z.1)
          (ell.succAbove q)) /
        g (permanentRolloutNormalizedInput j z.1) ell)
      (z.2 r)
noncomputable def permanentRolloutLinearCoordinateCombination
    (m : ℕ) :
    (Fin m → ℂ) →ₗ[ℂ] MvPolynomial (Fin m) ℂ where
  toFun c := ∑ i, c i • MvPolynomial.X i
  map_add' c d := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp [Finset.smul_sum, smul_smul]
section HomogeneousPrimeInputAvoidance
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def permanentRolloutHomogeneousLinearSliceIdeal
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ) : Ideal (MvPolynomial (Fin m) ℂ) :=
  I ⊔ Ideal.span (Set.range fun j =>
    permanentRolloutLinearCoordinateCombination m (c j))
end HomogeneousPrimeInputAvoidance
end
end Standalone_GenericAvoidance
section Standalone_FiniteMaps
noncomputable def homogeneousMapIdeal {ι : Type*}
    (F : ι → MvPolynomial ι ℂ) : Ideal (MvPolynomial ι ℂ) :=
  Ideal.span (Set.range F)
noncomputable def homogeneousMapSubalgebra {ι : Type*}
    (F : ι → MvPolynomial ι ℂ) : Subalgebra ℂ (MvPolynomial ι ℂ) :=
  Algebra.adjoin ℂ (Set.range F)
noncomputable def homogeneousMapFiberIdeal {ι : Type*}
    (F : ι → MvPolynomial ι ℂ) (point : ι → ℂ) :
    Ideal (MvPolynomial ι ℂ) :=
  Ideal.span (Set.range fun i => F i - MvPolynomial.C (point i))
abbrev homogeneousMapClosedFiber {ι : Type*}
    (F : ι → MvPolynomial ι ℂ) (point : ι → ℂ) :=
  MvPolynomial ι ℂ ⧸ homogeneousMapFiberIdeal F point
theorem zeroLocus_homogeneousMapIdeal {ι : Type*}
    (F : ι → MvPolynomial ι ℂ) :
    MvPolynomial.zeroLocus ℂ (homogeneousMapIdeal F) =
      {point : ι → ℂ | ∀ i, MvPolynomial.eval point (F i) = 0} := by
  rw [homogeneousMapIdeal, MvPolynomial.zeroLocus_span]
  ext point
  simp [MvPolynomial.aeval_def]
theorem vanishingIdeal_origin_eq_idealOfVars {ι : Type*} :
    MvPolynomial.vanishingIdeal ℂ ({0} : Set (ι → ℂ)) =
      MvPolynomial.idealOfVars ι ℂ := by
  ext p
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff,
    MvPolynomial.aeval_zero]
  change MvPolynomial.constantCoeff p = 0 ↔
    p ∈ MvPolynomial.idealOfVars ι ℂ
  rw [← pow_one (MvPolynomial.idealOfVars ι ℂ),
    MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hp m hm
    have hmzero : m = 0 :=
      (Finsupp.degree_eq_zero_iff m).mp (Nat.lt_one_iff.mp hm)
    simpa [hmzero, ← MvPolynomial.constantCoeff_eq] using hp
  · intro hp
    simpa [← MvPolynomial.constantCoeff_eq] using hp 0 (by simp)
theorem radical_homogeneousMapIdeal_eq_idealOfVars {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    (homogeneousMapIdeal F).radical = MvPolynomial.idealOfVars ι ℂ := by
  have hfiber : MvPolynomial.zeroLocus ℂ (homogeneousMapIdeal F) =
      ({0} : Set (ι → ℂ)) := by
    rw [zeroLocus_homogeneousMapIdeal]
    ext point
    simpa using hzero point
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ), hfiber,
    vanishingIdeal_origin_eq_idealOfVars]
theorem exists_idealOfVars_pow_le_homogeneousMapIdeal {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    ∃ n : ℕ, MvPolynomial.idealOfVars ι ℂ ^ n ≤ homogeneousMapIdeal F := by
  have hrad := radical_homogeneousMapIdeal_eq_idealOfVars F hzero
  obtain ⟨n, hn⟩ := (homogeneousMapIdeal F).exists_radical_pow_le_of_fg
    (hrad.symm ▸ MvPolynomial.idealOfVars_fg ι ℂ)
  exact ⟨n, hrad ▸ hn⟩
end Standalone_FiniteMaps
section Standalone_HomogeneousFiniteness
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
theorem homogeneousMap_coordinate_mem_subalgebra
    {ι : Type*} (F : ι → MvPolynomial ι ℂ) (i : ι) :
    F i ∈ homogeneousMapSubalgebra F := by
  exact Algebra.subset_adjoin (Set.mem_range_self i)
noncomputable def homogeneousMapLowDegreeSubmodule
    (ι : Type*) (N : ℕ) : Submodule ℂ (MvPolynomial ι ℂ) :=
  ⨆ n ∈ Finset.range N, MvPolynomial.homogeneousSubmodule ι ℂ n
theorem homogeneousMapLowDegreeSubmodule_fg
    {ι : Type*} [Finite ι] (N : ℕ) :
    (homogeneousMapLowDegreeSubmodule ι N).FG := by
  unfold homogeneousMapLowDegreeSubmodule
  exact Submodule.fg_biSup (Finset.range N)
    (MvPolynomial.homogeneousSubmodule ι ℂ)
    (fun n _ => MvPolynomial.homogeneousSubmodule_fg ι ℂ n)
theorem homogeneous_mem_homogeneousMapLowDegreeSubmodule
    {ι : Type*} {p : MvPolynomial ι ℂ} {n N : ℕ}
    (hp : p.IsHomogeneous n) (hn : n < N) :
    p ∈ homogeneousMapLowDegreeSubmodule ι N := by
  unfold homogeneousMapLowDegreeSubmodule
  apply (le_iSup (fun j : ℕ =>
    ⨆ _ : j ∈ Finset.range N,
      MvPolynomial.homogeneousSubmodule ι ℂ j) n)
  apply (le_iSup (fun _ : n ∈ Finset.range N =>
    MvPolynomial.homogeneousSubmodule ι ℂ n)
    (Finset.mem_range.mpr hn))
  exact hp
theorem homogeneous_mem_idealOfVars_pow_of_le
    {ι : Type*} {p : MvPolynomial ι ℂ} {n N : ℕ}
    (hp : p.IsHomogeneous n) (hN : N ≤ n) :
    p ∈ MvPolynomial.idealOfVars ι ℂ ^ N := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro monomial hmonomial
  apply hp.coeff_eq_zero
  omega
theorem homogeneousComponent_mul_of_right_isHomogeneous
    {ι : Type*} (g f : MvPolynomial ι ℂ) {e n : ℕ}
    (hf : f.IsHomogeneous e) (hen : e ≤ n) :
    MvPolynomial.homogeneousComponent n (g * f) =
      MvPolynomial.homogeneousComponent (n - e) g * f := by
  have hcomponent (q : MvPolynomial ι ℂ) (j : ℕ) :
      (DirectSum.decompose
        (MvPolynomial.homogeneousSubmodule ι ℂ) q j :
          MvPolynomial ι ℂ) = MvPolynomial.homogeneousComponent j q := by
    change
      (((inferInstance : DirectSum.Decomposition
        (MvPolynomial.homogeneousSubmodule ι ℂ)).decompose' q j :
          MvPolynomial ι ℂ)) = _
    rw [show (inferInstance : DirectSum.Decomposition
      (MvPolynomial.homogeneousSubmodule ι ℂ)) =
        MvPolynomial.decomposition from Subsingleton.elim _ _]
    exact MvPolynomial.decomposition.decompose'_apply q j
  have hprojection :=
    DirectSum.coe_decompose_mul_of_right_mem_of_le
      (𝒜 := MvPolynomial.homogeneousSubmodule ι ℂ)
      (a := g) (b := f) (n := n) (i := e) hf hen
  simpa only [hcomponent] using hprojection
theorem homogeneousMapIdeal_homogeneous_representation
    {ι : Type*} [Fintype ι]
    (F : ι → MvPolynomial ι ℂ) {e n : ℕ}
    (hF : ∀ i, (F i).IsHomogeneous e) (hen : e ≤ n)
    (p : MvPolynomial ι ℂ) (hp : p.IsHomogeneous n)
    (hmem : p ∈ homogeneousMapIdeal F) :
    ∃ coefficients : ι → MvPolynomial ι ℂ,
      (∀ i, (coefficients i).IsHomogeneous (n - e)) ∧
      ∑ i, coefficients i * F i = p := by
  classical
  unfold homogeneousMapIdeal at hmem
  obtain ⟨coefficients, hcoefficients⟩ :=
    (Ideal.mem_span_range_iff_exists_fun).mp hmem
  refine ⟨fun i =>
    MvPolynomial.homogeneousComponent (n - e) (coefficients i),
    fun i => MvPolynomial.homogeneousComponent_isHomogeneous
      (n - e) (coefficients i), ?_⟩
  have hcomponent := congrArg
    (fun q : MvPolynomial ι ℂ => MvPolynomial.homogeneousComponent n q)
    hcoefficients
  simp only [map_sum] at hcomponent
  simp_rw [homogeneousComponent_mul_of_right_isHomogeneous _ _ (hF _) hen]
    at hcomponent
  simpa [MvPolynomial.homogeneousComponent_eq_self hp] using hcomponent
theorem homogeneousMap_moduleFinite
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    Module.Finite (homogeneousMapSubalgebra F) (MvPolynomial ι ℂ) := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨N₀, hN₀⟩ :=
    exists_idealOfVars_pow_le_homogeneousMapIdeal F hzero
  obtain ⟨generators, hgenerators⟩ :=
    homogeneousMapLowDegreeSubmodule_fg (ι := ι) (max N₀ e)
  let T := homogeneousMapSubalgebra F
  let M : Submodule T (MvPolynomial ι ℂ) :=
    Submodule.span T (generators : Set (MvPolynomial ι ℂ))
  have hlow :
      homogeneousMapLowDegreeSubmodule ι (max N₀ e) ≤
        M.restrictScalars ℂ := by
    rw [← hgenerators]
    exact Submodule.span_le_restrictScalars ℂ T
      (generators : Set (MvPolynomial ι ℂ))
  have hgraded : ∀ n : ℕ, ∀ p : MvPolynomial ι ℂ,
      p.IsHomogeneous n → p ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      by_cases hn : n < max N₀ e
      · exact hlow
          (homogeneous_mem_homogeneousMapLowDegreeSubmodule hp hn)
      · have hmax : max N₀ e ≤ n := Nat.le_of_not_gt hn
        have he_le : e ≤ n := le_trans (Nat.le_max_right N₀ e) hmax
        have hN_le : N₀ ≤ n := le_trans (Nat.le_max_left N₀ e) hmax
        have hp_ideal : p ∈ homogeneousMapIdeal F :=
          hN₀ (homogeneous_mem_idealOfVars_pow_of_le hp hN_le)
        obtain ⟨coefficients, hcoefficients, hsum⟩ :=
          homogeneousMapIdeal_homogeneous_representation
            F hF he_le p hp hp_ideal
        rw [← hsum]
        apply M.sum_mem
        intro i _
        have hcoefficient : coefficients i ∈ M :=
          ih (n - e) (by omega) (coefficients i) (hcoefficients i)
        have hscalar := M.smul_mem
          (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ : T)
          hcoefficient
        simpa [Algebra.smul_def, mul_comm] using hscalar
  apply Module.Finite.of_fg_top
  refine ⟨generators, ?_⟩
  change M = ⊤
  apply top_unique
  intro p _
  rw [← MvPolynomial.sum_homogeneousComponent p]
  exact M.sum_mem fun n _ =>
    hgraded n (MvPolynomial.homogeneousComponent n p)
      (MvPolynomial.homogeneousComponent_isHomogeneous n p)
theorem homogeneousMap_isTranscendenceBasis
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    IsTranscendenceBasis ℂ F := by
  letI : Module.Finite (Algebra.adjoin ℂ (Set.range F))
      (MvPolynomial ι ℂ) :=
    homogeneousMap_moduleFinite F e he hF hzero
  apply Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℂ F
  simp
theorem homogeneousMap_algebraicIndependent
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    AlgebraicIndependent ℂ F :=
  (homogeneousMap_isTranscendenceBasis F e he hF hzero).1
noncomputable def homogeneousMapCoordinateAlgEquiv
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    MvPolynomial ι ℂ ≃ₐ[ℂ] homogeneousMapSubalgebra F :=
  (homogeneousMap_algebraicIndependent F e he hF hzero).aevalEquiv
section FractionField
end FractionField
end Standalone_HomogeneousFiniteness
section Standalone_LeadingForms
open scoped BigOperators
noncomputable def coordinateEsymm {t : ℕ} (u : Fin t → ℂ) (q : ℕ) : ℂ :=
  ((Finset.univ : Finset (Fin t)).val.map u).esymm q
noncomputable def deletedCoordinateEsymm {t : ℕ}
    (u : Fin t → ℂ) (i : Fin t) (q : ℕ) : ℂ :=
  (((Finset.univ : Finset (Fin t)).erase i).val.map u).esymm q
noncomputable def deletedCoordinateEsymmPolynomial (t q : ℕ) (i : Fin t) :
    MvPolynomial (Fin t) ℂ :=
  (((Finset.univ : Finset (Fin t)).erase i).val.map
    (fun j => (MvPolynomial.X j : MvPolynomial (Fin t) ℂ))).esymm q
end Standalone_LeadingForms
section Standalone_ProjectiveDimension
open scoped LinearAlgebra.Projectivization
section AlgebraicProjectiveLeadingForms
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def homogeneousLinearSliceIdeal {t n : ℕ}
    (I : Ideal (MvPolynomial (Fin t) ℂ)) (c : Fin n → Fin t → ℂ) :
    Ideal (MvPolynomial (Fin t) ℂ) :=
  I ⊔ Ideal.span (Set.range fun j =>
    permanentRolloutLinearCoordinateCombination t (c j))
end AlgebraicProjectiveLeadingForms
end Standalone_ProjectiveDimension
noncomputable section Standalone_ProjectiveSlicing
open scoped BigOperators LinearAlgebra.Projectivization
noncomputable abbrev criticalCoordinateRing {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) : Type :=
  MvPolynomial (Fin m) ℂ ⧸
    homogeneousMapIdeal (fun i : Fin m => MvPolynomial.pderiv i P)
noncomputable def criticalLocusDimension {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) : WithBot ℕ∞ :=
  ringKrullDim (criticalCoordinateRing P)
noncomputable def gradientVector {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (v : Fin m → ℂ) : Fin m → ℂ :=
  fun i => MvPolynomial.eval v (MvPolynomial.pderiv i P)
def projectiveCriticalLocus {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) : Set (ℙ ℂ (Fin m → ℂ)) :=
  {point | ∃ (v : Fin m → ℂ) (hv : v ≠ 0),
    Projectivization.mk ℂ v hv = point ∧ v ∈ criticalLocus P}
noncomputable def linearCoordinatePolynomial {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (row : Fin m) : MvPolynomial (Fin k) ℂ :=
  ∑ j : Fin k,
    MvPolynomial.C ((W (Pi.single j 1)) row) * MvPolynomial.X j
noncomputable def slicedGradientPolynomial {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (i : Fin k) : MvPolynomial (Fin k) ℂ :=
  ∑ j : Fin m,
    MvPolynomial.C ((A (Pi.single j 1)) i) *
      MvPolynomial.aeval
        (fun row => linearCoordinatePolynomial W row)
        (MvPolynomial.pderiv j P)
noncomputable def oneDimensionalInputSlice {m : ℕ}
    (v : Fin m → ℂ) : (Fin 1 → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  LinearMap.smulRight
    (LinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →ₗ[ℂ] ℂ) v
def projectiveSlicedGradientImage {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    Set (ℙ ℂ (Fin m → ℂ)) :=
  {point | ∃ (u : Fin k → ℂ) (_hu : u ≠ 0)
      (hgradient : gradientVector P (W u) ≠ 0),
    Projectivization.mk ℂ (gradientVector P (W u)) hgradient = point}
attribute [local instance] MvPolynomial.gradedAlgebra
end Standalone_ProjectiveSlicing
section Standalone_MultivariateBezout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def homogeneousPolynomialMulLinearMap
    {ι : Type*} (f : MvPolynomial ι ℂ) {e : ℕ}
    (hf : f.IsHomogeneous e) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι ℂ n →ₗ[ℂ]
      MvPolynomial.homogeneousSubmodule ι ℂ (e + n) :=
  LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule ι ℂ (e + n))
    ((Algebra.lmul ℂ (MvPolynomial ι ℂ) f).domRestrict
      (MvPolynomial.homogeneousSubmodule ι ℂ n))
    (fun p => hf.mul p.property)
noncomputable def homogeneousMapGradedIdealPiece
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ) :
    Submodule ℂ (MvPolynomial.homogeneousSubmodule ι ℂ n) :=
  (I.restrictScalars ℂ).comap
    (MvPolynomial.homogeneousSubmodule ι ℂ n).subtype
abbrev homogeneousMapGradedQuotientPiece
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ) : Type _ :=
  MvPolynomial.homogeneousSubmodule ι ℂ n ⧸
    homogeneousMapGradedIdealPiece I n
noncomputable def homogeneousMapGradedQuotientMulLinearMap
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ} (hf : f.IsHomogeneous e) (n : ℕ) :
    homogeneousMapGradedQuotientPiece I n →ₗ[ℂ]
      homogeneousMapGradedQuotientPiece I (e + n) :=
  (homogeneousMapGradedIdealPiece I n).mapQ
    (homogeneousMapGradedIdealPiece I (e + n))
    (homogeneousPolynomialMulLinearMap f hf n)
    (by
      intro p hp
      change f * (p : MvPolynomial ι ℂ) ∈ I
      exact I.mul_mem_left f hp)
noncomputable def homogeneousMapFiniteGradedQuotientSumLinearMap
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (N : ℕ) :
    ((i : Fin N) → homogeneousMapGradedQuotientPiece I i) →ₗ[ℂ]
      (MvPolynomial ι ℂ ⧸ I) :=
  Submodule.piQuotientLift
    (fun i : Fin N => homogeneousMapGradedIdealPiece I i)
    (I.restrictScalars ℂ)
    (fun i : Fin N =>
      (MvPolynomial.homogeneousSubmodule ι ℂ i).subtype)
    (fun i => show homogeneousMapGradedIdealPiece I i ≤
      (I.restrictScalars ℂ).comap
        (MvPolynomial.homogeneousSubmodule ι ℂ i).subtype from le_rfl)
theorem homogeneousMapFiniteGradedQuotientSumLinearMap_injective
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (N : ℕ) :
    Function.Injective (homogeneousMapFiniteGradedQuotientSumLinearMap I N) := by
  classical
  intro x y hxy
  have hx :
      homogeneousMapFiniteGradedQuotientSumLinearMap I N (x - y) = 0 := by
    calc
      homogeneousMapFiniteGradedQuotientSumLinearMap I N (x - y) =
          homogeneousMapFiniteGradedQuotientSumLinearMap I N x -
            homogeneousMapFiniteGradedQuotientSumLinearMap I N y :=
        (homogeneousMapFiniteGradedQuotientSumLinearMap I N).map_sub x y
      _ = 0 := sub_eq_zero.mpr hxy
  let z := x - y
  have hz : homogeneousMapFiniteGradedQuotientSumLinearMap I N z = 0 := hx
  choose p hp using fun i : Fin N =>
    (homogeneousMapGradedIdealPiece I i).mkQ_surjective (z i)
  have hzp : z = fun i : Fin N => Submodule.Quotient.mk (p i) :=
    funext fun i => (hp i).symm
  rw [hzp] at hz
  change
    Submodule.piQuotientLift
      (fun i : Fin N => homogeneousMapGradedIdealPiece I i)
      (I.restrictScalars ℂ)
      (fun i : Fin N =>
        (MvPolynomial.homogeneousSubmodule ι ℂ i).subtype)
      (fun i => show homogeneousMapGradedIdealPiece I i ≤
        (I.restrictScalars ℂ).comap
          (MvPolynomial.homogeneousSubmodule ι ℂ i).subtype from le_rfl)
      (fun i => Submodule.Quotient.mk (p i)) = 0 at hz
  rw [Submodule.piQuotientLift_mk] at hz
  have hsum := (Submodule.Quotient.mk_eq_zero
    (I.restrictScalars ℂ)).mp hz
  simp [LinearMap.lsum_apply] at hsum
  have hz0 : z = 0 := by
    apply funext
    intro i
    rw [Pi.zero_apply]
    rw [hzp]
    apply (Submodule.Quotient.mk_eq_zero
      (homogeneousMapGradedIdealPiece I i)).mpr
    have hcomponent :=
      MvPolynomial.homogeneousComponent_mem_of_mem hI hsum (i : ℕ)
    have hcomponent_eq :
        MvPolynomial.homogeneousComponent (i : ℕ)
          (∑ j : Fin N, (p j : MvPolynomial ι ℂ)) = p i := by
      rw [map_sum]
      calc
        (∑ j : Fin N,
          MvPolynomial.homogeneousComponent (i : ℕ)
            (p j : MvPolynomial ι ℂ)) =
            ∑ j : Fin N,
              if (i : ℕ) = (j : ℕ) then
                (p j : MvPolynomial ι ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          exact MvPolynomial.homogeneousComponent_of_mem (p j).property
        _ = (if (i : ℕ) = (i : ℕ) then
              (p i : MvPolynomial ι ℂ) else 0) := by
          apply Finset.sum_eq_single i
          · intro j _ hj
            rw [if_neg]
            intro hij
            exact hj (Fin.ext hij.symm)
          · simp
        _ = p i := if_pos rfl
    rw [hcomponent_eq] at hcomponent
    exact hcomponent
  exact sub_eq_zero.mp hz0
theorem homogeneousMapFiniteGradedQuotientSumLinearMap_surjective
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (N : ℕ)
    (hhigh : ∀ n : ℕ, N ≤ n →
      ∀ p : MvPolynomial ι ℂ, p.IsHomogeneous n → p ∈ I) :
    Function.Surjective
      (homogeneousMapFiniteGradedQuotientSumLinearMap I N) := by
  classical
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ p =>
    let q : (i : Fin N) →
        MvPolynomial.homogeneousSubmodule ι ℂ i :=
      fun i => ⟨MvPolynomial.homogeneousComponent i p,
        MvPolynomial.homogeneousComponent_isHomogeneous i p⟩
    refine ⟨fun i => Submodule.Quotient.mk (q i), ?_⟩
    change
      Submodule.piQuotientLift
        (fun i : Fin N => homogeneousMapGradedIdealPiece I i)
        (I.restrictScalars ℂ)
        (fun i : Fin N =>
          (MvPolynomial.homogeneousSubmodule ι ℂ i).subtype)
        (fun i => show homogeneousMapGradedIdealPiece I i ≤
          (I.restrictScalars ℂ).comap
            (MvPolynomial.homogeneousSubmodule ι ℂ i).subtype from le_rfl)
        (fun i => Submodule.Quotient.mk (q i)) =
          Submodule.Quotient.mk p
    rw [Submodule.piQuotientLift_mk]
    apply (Submodule.Quotient.eq (I.restrictScalars ℂ)).mpr
    have hfull :
        (∑ j ∈ Finset.range (N + (p.totalDegree + 1)),
          MvPolynomial.homogeneousComponent j p) = p := by
      have htailzero :
          (∑ j ∈ Finset.range N,
            MvPolynomial.homogeneousComponent
              (p.totalDegree + 1 + j) p) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        apply MvPolynomial.homogeneousComponent_eq_zero
        omega
      rw [Nat.add_comm, Finset.sum_range_add]
      rw [MvPolynomial.sum_homogeneousComponent]
      rw [htailzero, add_zero]
    have hsplit :
        p = (∑ i : Fin N, (q i : MvPolynomial ι ℂ)) +
          ∑ j ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent (N + j) p := by
      calc
        p = (∑ j ∈ Finset.range (N + (p.totalDegree + 1)),
          MvPolynomial.homogeneousComponent j p) := hfull.symm
        _ = (∑ j ∈ Finset.range N,
              MvPolynomial.homogeneousComponent j p) +
            ∑ j ∈ Finset.range (p.totalDegree + 1),
              MvPolynomial.homogeneousComponent (N + j) p :=
          Finset.sum_range_add _ _ _
        _ = (∑ i : Fin N, (q i : MvPolynomial ι ℂ)) +
            ∑ j ∈ Finset.range (p.totalDegree + 1),
              MvPolynomial.homogeneousComponent (N + j) p := by
          congr 1
          change
            (∑ j ∈ Finset.range N,
              MvPolynomial.homogeneousComponent j p) =
                ∑ i : Fin N, MvPolynomial.homogeneousComponent (i : ℕ) p
          exact
            (Fin.sum_univ_eq_sum_range
              (fun j => MvPolynomial.homogeneousComponent j p) N).symm
    have htail :
        (∑ j ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.homogeneousComponent (N + j) p) ∈ I := by
      apply Ideal.sum_mem
      intro j _
      apply hhigh (N + j) (Nat.le_add_right N j)
      exact MvPolynomial.homogeneousComponent_isHomogeneous (N + j) p
    simp [LinearMap.lsum_apply]
    rw [hsplit]
    simpa using I.neg_mem htail
noncomputable def homogeneousMapFiniteGradedQuotientEquiv
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (N : ℕ)
    (hhigh : ∀ n : ℕ, N ≤ n →
      ∀ p : MvPolynomial ι ℂ, p.IsHomogeneous n → p ∈ I) :
    ((i : Fin N) → homogeneousMapGradedQuotientPiece I i) ≃ₗ[ℂ]
      (MvPolynomial ι ℂ ⧸ I) :=
  LinearEquiv.ofBijective
    (homogeneousMapFiniteGradedQuotientSumLinearMap I N)
    ⟨homogeneousMapFiniteGradedQuotientSumLinearMap_injective I hI N,
      homogeneousMapFiniteGradedQuotientSumLinearMap_surjective I N hhigh⟩
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
theorem homogeneousMapGradedSupSpanPiece_eq_sup
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ}
    (hf : f.IsHomogeneous e) (n : ℕ) :
    homogeneousMapGradedIdealPiece (I ⊔ Ideal.span {f}) (e + n) =
      homogeneousMapGradedIdealPiece I (e + n) ⊔
        LinearMap.range (homogeneousPolynomialMulLinearMap f hf n) := by
  classical
  ext p
  constructor
  · intro hp
    change (p : MvPolynomial ι ℂ) ∈ I ⊔ Ideal.span {f} at hp
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp
    obtain ⟨q, hq⟩ := (Ideal.mem_span_singleton').mp hb
    let agraded : MvPolynomial.homogeneousSubmodule ι ℂ (e + n) :=
      ⟨MvPolynomial.homogeneousComponent (e + n) a,
        MvPolynomial.homogeneousComponent_isHomogeneous (e + n) a⟩
    let qgraded : MvPolynomial.homogeneousSubmodule ι ℂ n :=
      ⟨MvPolynomial.homogeneousComponent n q,
        MvPolynomial.homogeneousComponent_isHomogeneous n q⟩
    let bgraded : MvPolynomial.homogeneousSubmodule ι ℂ (e + n) :=
      homogeneousPolynomialMulLinearMap f hf n qgraded
    have ha' : agraded ∈ homogeneousMapGradedIdealPiece I (e + n) :=
      MvPolynomial.homogeneousComponent_mem_of_mem hI ha (e + n)
    have hb' : bgraded ∈
        LinearMap.range (homogeneousPolynomialMulLinearMap f hf n) :=
      ⟨qgraded, rfl⟩
    have hsum : agraded + bgraded = p := by
      apply Subtype.ext
      change MvPolynomial.homogeneousComponent (e + n) a +
        f * MvPolynomial.homogeneousComponent n q =
        (p : MvPolynomial ι ℂ)
      have hcomponent := congrArg
        (MvPolynomial.homogeneousComponent (e + n)) hab
      rw [map_add, ← hq,
        homogeneousComponent_mul_of_right_isHomogeneous q f hf
          (Nat.le_add_right e n),
        MvPolynomial.homogeneousComponent_eq_self p.property] at hcomponent
      simpa [Nat.add_sub_cancel_left, mul_comm] using hcomponent
    rw [← hsum]
    exact Submodule.add_mem_sup ha' hb'
  · intro hp
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp
    rw [← hab]
    change (a : MvPolynomial ι ℂ) + (b : MvPolynomial ι ℂ) ∈
      I ⊔ Ideal.span {f}
    apply (I ⊔ Ideal.span {f}).add_mem
    · exact Ideal.mem_sup_left ha
    · obtain ⟨q, hq⟩ := hb
      rw [← hq]
      change f * (q : MvPolynomial ι ℂ) ∈ I ⊔ Ideal.span {f}
      apply Ideal.mem_sup_right
      apply Ideal.mem_span_singleton.mpr
      exact ⟨q, rfl⟩
noncomputable def homogeneousMapGradedSupSpanQuotientEquivCokernel
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ}
    (hf : f.IsHomogeneous e) (n : ℕ) :
    (homogeneousMapGradedQuotientPiece I (e + n) ⧸
      LinearMap.range
        (homogeneousMapGradedQuotientMulLinearMap I f hf n)) ≃ₗ[ℂ]
      homogeneousMapGradedQuotientPiece (I ⊔ Ideal.span {f}) (e + n) := by
  let S0 := homogeneousMapGradedIdealPiece I (e + n)
  let T := LinearMap.range (homogeneousPolynomialMulLinearMap f hf n)
  have hrange :
      LinearMap.range
        (homogeneousMapGradedQuotientMulLinearMap I f hf n) =
        T.map S0.mkQ := by
    exact Submodule.range_mapQ
      (homogeneousMapGradedIdealPiece I n)
      S0 (homogeneousPolynomialMulLinearMap f hf n)
      (by
        intro p hp
        change f * (p : MvPolynomial ι ℂ) ∈ I
        exact I.mul_mem_left f hp)
  have hfull : S0 ⊔ T =
      homogeneousMapGradedIdealPiece (I ⊔ Ideal.span {f}) (e + n) :=
    (homogeneousMapGradedSupSpanPiece_eq_sup I hI f hf n).symm
  exact (Submodule.quotEquivOfEq _ _ hrange).trans
    ((Submodule.quotientQuotientEquivQuotientSup S0 T).trans
      (Submodule.quotEquivOfEq _ _ hfull))
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
noncomputable def homogeneousMapFinSuccLinearPlaneRoot
    {n : ℕ} (c : Fin (n + 1) → ℂ) : MvPolynomial (Fin n) ℂ :=
  -(MvPolynomial.C ((c 0)⁻¹) *
    ∑ i : Fin n, MvPolynomial.C (c (Fin.succ i)) * MvPolynomial.X i)
theorem homogeneousMap_allRank_finSucc_linearCoordinateCombination_finSucc
    {n : ℕ} (c : Fin (n + 1) → ℂ) :
    MvPolynomial.finSuccEquiv ℂ n
        (permanentRolloutLinearCoordinateCombination (n + 1) c) =
      Polynomial.C (MvPolynomial.C (c 0)) * Polynomial.X +
        Polynomial.C
          (∑ i : Fin n,
            MvPolynomial.C (c (Fin.succ i)) * MvPolynomial.X i) := by
  have hC (z : ℂ) :
      MvPolynomial.finSuccEquiv ℂ n (MvPolynomial.C z) =
        Polynomial.C (MvPolynomial.C z) :=
    (MvPolynomial.finSuccEquiv ℂ n).commutes z
  simp [permanentRolloutLinearCoordinateCombination,
    Fin.sum_univ_succ, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ, Algebra.smul_def, hC]
theorem homogeneousMap_allRank_finSucc_linearCoordinateCombination_normalized
    {n : ℕ} (c : Fin (n + 1) → ℂ) (hc : c 0 ≠ 0) :
    Ideal.span
      ({MvPolynomial.finSuccEquiv ℂ n
        (permanentRolloutLinearCoordinateCombination (n + 1) c)} :
        Set (Polynomial (MvPolynomial (Fin n) ℂ))) =
      Ideal.span
        ({Polynomial.X - Polynomial.C
          (homogeneousMapFinSuccLinearPlaneRoot c)} :
          Set (Polynomial (MvPolynomial (Fin n) ℂ))) := by
  rw [homogeneousMap_allRank_finSucc_linearCoordinateCombination_finSucc]
  have ha : IsUnit (MvPolynomial.C (c 0) : MvPolynomial (Fin n) ℂ) :=
    (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  have hua : IsUnit
      (Polynomial.C (MvPolynomial.C (c 0)) :
        Polynomial (MvPolynomial (Fin n) ℂ)) :=
    ha.map Polynomial.C
  have hpivot :
      Polynomial.C (MvPolynomial.C (c 0)) *
        Polynomial.C (MvPolynomial.C ((c 0)⁻¹)) =
        (1 : Polynomial (MvPolynomial (Fin n) ℂ)) := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc,
      map_one, map_one]
  let T : MvPolynomial (Fin n) ℂ :=
    ∑ i : Fin n,
      MvPolynomial.C (c (Fin.succ i)) * MvPolynomial.X i
  have hfactor :
      Polynomial.C (MvPolynomial.C (c 0)) * Polynomial.X +
          Polynomial.C T =
        Polynomial.C (MvPolynomial.C (c 0)) *
          (Polynomial.X - Polynomial.C
            (homogeneousMapFinSuccLinearPlaneRoot c)) := by
    change
      Polynomial.C (MvPolynomial.C (c 0)) * Polynomial.X +
        Polynomial.C T =
      Polynomial.C (MvPolynomial.C (c 0)) *
        (Polynomial.X - Polynomial.C
          (-(MvPolynomial.C ((c 0)⁻¹) * T)))
    calc
      Polynomial.C (MvPolynomial.C (c 0)) * Polynomial.X +
          Polynomial.C T =
        Polynomial.C (MvPolynomial.C (c 0)) * Polynomial.X +
          1 * Polynomial.C T := by rw [one_mul]
      _ = Polynomial.C (MvPolynomial.C (c 0)) * Polynomial.X +
          (Polynomial.C (MvPolynomial.C (c 0)) *
            Polynomial.C (MvPolynomial.C ((c 0)⁻¹))) *
              Polynomial.C T := by rw [hpivot]
      _ = Polynomial.C (MvPolynomial.C (c 0)) *
          (Polynomial.X +
            Polynomial.C (MvPolynomial.C ((c 0)⁻¹)) *
              Polynomial.C T) := by ring
      _ = Polynomial.C (MvPolynomial.C (c 0)) *
          (Polynomial.X - Polynomial.C
            (-(MvPolynomial.C ((c 0)⁻¹) * T))) := by
          simp
  change Ideal.span
      ({Polynomial.C (MvPolynomial.C (c 0)) * Polynomial.X +
        Polynomial.C T} : Set (Polynomial (MvPolynomial (Fin n) ℂ))) = _
  rw [hfactor]
  exact Ideal.span_singleton_mul_left_unit hua _
noncomputable def homogeneousMapFinSuccFirstPivotPlaneQuotientEquiv
    {n : ℕ} (c : Fin (n + 1) → ℂ) (hc : c 0 ≠ 0) :
    (MvPolynomial (Fin (n + 1)) ℂ ⧸
      Ideal.span
        ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
          Set (MvPolynomial (Fin (n + 1)) ℂ))) ≃ₐ[ℂ]
      MvPolynomial (Fin n) ℂ := by
  let E := MvPolynomial.finSuccEquiv ℂ n
  let I : Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
    Ideal.span
      ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
        Set (MvPolynomial (Fin (n + 1)) ℂ))
  let J : Ideal (Polynomial (MvPolynomial (Fin n) ℂ)) :=
    Ideal.span
      ({Polynomial.X - Polynomial.C
        (homogeneousMapFinSuccLinearPlaneRoot c)} :
        Set (Polynomial (MvPolynomial (Fin n) ℂ)))
  have hIJ : J = I.map E.toRingEquiv.toRingHom := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    exact (homogeneousMap_allRank_finSucc_linearCoordinateCombination_normalized c hc).symm
  exact
    (Ideal.quotientEquivAlg I J E hIJ).trans
      ((Polynomial.quotientSpanXSubCAlgEquiv
        (homogeneousMapFinSuccLinearPlaneRoot c)).restrictScalars ℂ)
theorem homogeneousMap_allRank_linearCoordinateCombination_rename
    {m : ℕ} (equiv : Fin m ≃ Fin m) (c : Fin m → ℂ) :
    MvPolynomial.rename equiv
      (permanentRolloutLinearCoordinateCombination m c) =
      permanentRolloutLinearCoordinateCombination m
        (fun i => c (equiv.symm i)) := by
  classical
  change MvPolynomial.rename equiv
      (∑ i, c i • MvPolynomial.X i) =
    ∑ i, c (equiv.symm i) • MvPolynomial.X i
  simp_rw [MvPolynomial.smul_eq_C_mul, map_sum, map_mul,
    MvPolynomial.rename_C, MvPolynomial.rename_X]
  exact Fintype.sum_equiv equiv
    (fun i => MvPolynomial.C (c i) * MvPolynomial.X (equiv i))
    (fun i =>
      MvPolynomial.C (c (equiv.symm i)) * MvPolynomial.X i)
    (by intro i; simp)
theorem homogeneousMap_allRank_finSucc_swappedPlaneIdeal
    {n : ℕ} (c : Fin (n + 1) → ℂ) (j : Fin (n + 1)) :
    Ideal.span
      ({permanentRolloutLinearCoordinateCombination (n + 1)
          (fun i => c ((Equiv.swap (0 : Fin (n + 1)) j).symm i))} :
        Set (MvPolynomial (Fin (n + 1)) ℂ)) =
      (Ideal.span
        ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
          Set (MvPolynomial (Fin (n + 1)) ℂ))).map
        (MvPolynomial.renameEquiv ℂ
          (Equiv.swap (0 : Fin (n + 1)) j)).toRingEquiv.toRingHom := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  exact
    (homogeneousMap_allRank_linearCoordinateCombination_rename
      (Equiv.swap (0 : Fin (n + 1)) j) c).symm
noncomputable def homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (j : Fin (n + 1)) (hj : c j ≠ 0) :
    (MvPolynomial (Fin (n + 1)) ℂ ⧸
      Ideal.span
        ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
          Set (MvPolynomial (Fin (n + 1)) ℂ))) ≃ₐ[ℂ]
      MvPolynomial (Fin n) ℂ := by
  let equiv := Equiv.swap (0 : Fin (n + 1)) j
  let d : Fin (n + 1) → ℂ := fun i => c (equiv.symm i)
  have hd : d 0 ≠ 0 := by
    simpa [d, equiv] using hj
  exact
    (Ideal.quotientEquivAlg
      (Ideal.span
        ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
          Set (MvPolynomial (Fin (n + 1)) ℂ)))
      (Ideal.span
        ({permanentRolloutLinearCoordinateCombination (n + 1) d} :
          Set (MvPolynomial (Fin (n + 1)) ℂ)))
      (MvPolynomial.renameEquiv ℂ equiv)
      (homogeneousMap_allRank_finSucc_swappedPlaneIdeal c j)).trans
        (homogeneousMapFinSuccFirstPivotPlaneQuotientEquiv d hd)
open scoped BigOperators
noncomputable def homogeneousMapFinSuccFirstPivotPlaneMap
    {n : ℕ} (c : Fin (n + 1) → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.pi fun row : Fin (n + 1) =>
    Fin.cases
      (-((c 0)⁻¹) •
        ∑ i : Fin n, (c i.succ) • LinearMap.proj i)
      (fun i : Fin n => LinearMap.proj i) row
noncomputable def homogeneousMapFinSuccFirstPivotPlaneRoot
    {n : ℕ} (c : Fin (n + 1) → ℂ) :
    MvPolynomial (Fin n) ℂ :=
  -(MvPolynomial.C ((c 0)⁻¹) *
    ∑ i : Fin n, MvPolynomial.C (c i.succ) * MvPolynomial.X i)
noncomputable def homogeneousMapFinSuccPivotPermutation
    {n : ℕ} (j : Fin (n + 1)) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.pi fun i : Fin (n + 1) =>
    LinearMap.proj (Equiv.swap (0 : Fin (n + 1)) j i)
noncomputable def homogeneousMapFinSuccArbitraryPivotPlaneMap
    {n : ℕ} (c : Fin (n + 1) → ℂ) (j : Fin (n + 1)) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  (homogeneousMapFinSuccPivotPermutation j).comp
    (homogeneousMapFinSuccFirstPivotPlaneMap
      (fun i => c ((Equiv.swap (0 : Fin (n + 1)) j).symm i)))
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
noncomputable def homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
    (k e n : ℕ) (restricted : Finset (Fin k)) : ℕ :=
  (((Finset.univ : Finset (Fin k)).finsuppAntidiag n).filter
    (fun d => ∀ i ∈ restricted, d i < e)).card
noncomputable def homogeneousMapAllKBoxHilbertCoefficient
    (k e n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin e)).filter
    (fun a => (∑ i : Fin k, (a i : ℕ)) = n)).card
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
def homogeneousMapAllKSourcePrefix (k j : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i => i.val < j
@[simp] theorem homogeneousMap_allRank_sourcePrefix_zero (k : ℕ) :
    homogeneousMapAllKSourcePrefix k 0 = ∅ := by
  ext i
  simp [homogeneousMapAllKSourcePrefix]
@[simp] theorem homogeneousMap_allRank_sourcePrefix_full (k : ℕ) :
    homogeneousMapAllKSourcePrefix k k = Finset.univ := by
  ext i
  simp [homogeneousMapAllKSourcePrefix]
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def homogeneousMapAllKCoordinateSubsetIdeal
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (restricted : Finset (Fin k)) : Ideal (MvPolynomial (Fin k) ℂ) :=
  Ideal.span (F '' (restricted : Set (Fin k)))
noncomputable def homogeneousMapAllKActualCoordinateHilbert
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (restricted : Finset (Fin k)) (n : ℕ) : ℕ :=
  Module.finrank ℂ
    (homogeneousMapGradedQuotientPiece
      (homogeneousMapAllKCoordinateSubsetIdeal F restricted) n)
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def homogeneousMapReesTargetHom
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : ι → ℂ) :
    homogeneousMapSubalgebra F →ₐ[ℂ] Polynomial ℂ :=
  (MvPolynomial.aeval fun i : ι =>
    Polynomial.C (target i) * Polynomial.X ^ e).comp
    (homogeneousMapCoordinateAlgEquiv F e he hF hzero).symm.toAlgHom
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def homogeneousMapAllTargetReesCoordinate
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (i : Fin k) :
    MvPolynomial (Fin (k + 1)) ℂ :=
  MvPolynomial.rename Fin.succ (F i) -
    MvPolynomial.C (target i) * MvPolynomial.X (0 : Fin (k + 1)) ^ e
noncomputable def homogeneousMapAllTargetReesZeroHyperplaneEquiv (k : ℕ) :
    (MvPolynomial (Fin (k + 1)) ℂ ⧸
      Ideal.span ({MvPolynomial.X (0 : Fin (k + 1))} :
        Set (MvPolynomial (Fin (k + 1)) ℂ))) ≃ₐ[ℂ]
      MvPolynomial (Fin k) ℂ := by
  let E := MvPolynomial.finSuccEquiv ℂ k
  let I : Ideal (MvPolynomial (Fin (k + 1)) ℂ) :=
    Ideal.span ({MvPolynomial.X (0 : Fin (k + 1))} :
      Set (MvPolynomial (Fin (k + 1)) ℂ))
  let J : Ideal (Polynomial (MvPolynomial (Fin k) ℂ)) :=
    Ideal.span ({Polynomial.X - Polynomial.C 0} :
      Set (Polynomial (MvPolynomial (Fin k) ℂ)))
  have hIJ : J = I.map E.toRingEquiv.toRingHom := by
    simp [I, J, Ideal.map_span, E,
      MvPolynomial.finSuccEquiv_X_zero]
  exact (Ideal.quotientEquivAlg I J E hIJ).trans
    ((Polynomial.quotientSpanXSubCAlgEquiv
      (0 : MvPolynomial (Fin k) ℂ)).restrictScalars ℂ)
abbrev homogeneousMapAllTargetReesQuotient
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) :=
  MvPolynomial (Fin (k + 1)) ℂ ⧸
    Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e))
noncomputable def homogeneousMapAllTargetReesParameterRingHom
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) :
    Polynomial ℂ →+* homogeneousMapAllTargetReesQuotient F target e :=
  (Ideal.Quotient.mk
    (Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e)))).comp
      (Polynomial.aeval
        (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1)))).toRingHom
noncomputable abbrev homogeneousMapAllTargetReesParameterAlgebra
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) :
    Algebra (Polynomial ℂ) (homogeneousMapAllTargetReesQuotient F target e) :=
  (homogeneousMapAllTargetReesParameterRingHom F target e).toAlgebra
noncomputable def homogeneousMapAllTargetReesChartIdeal (k : ℕ) (a : ℂ) :
    Ideal (MvPolynomial (Fin (k + 1)) ℂ) :=
  Ideal.span ({MvPolynomial.X (0 : Fin (k + 1)) - MvPolynomial.C a} :
    Set (MvPolynomial (Fin (k + 1)) ℂ))
noncomputable def homogeneousMapAllTargetReesChartHyperplaneEquiv
    (k : ℕ) (a : ℂ) :
    (MvPolynomial (Fin (k + 1)) ℂ ⧸
      homogeneousMapAllTargetReesChartIdeal k a) ≃ₐ[ℂ]
      MvPolynomial (Fin k) ℂ := by
  let E := MvPolynomial.finSuccEquiv ℂ k
  let I := homogeneousMapAllTargetReesChartIdeal k a
  let J : Ideal (Polynomial (MvPolynomial (Fin k) ℂ)) :=
    Ideal.span ({Polynomial.X -
      Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin k) ℂ)} :
      Set (Polynomial (MvPolynomial (Fin k) ℂ)))
  have hIJ : J = I.map E.toRingEquiv.toRingHom := by
    have hC : E (MvPolynomial.C a) =
        Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin k) ℂ) := by
      simpa using E.commutes a
    simp [I, J, homogeneousMapAllTargetReesChartIdeal,
      Ideal.map_span, E, MvPolynomial.finSuccEquiv_X_zero, hC]
  exact (Ideal.quotientEquivAlg I J E hIJ).trans
    ((Polynomial.quotientSpanXSubCAlgEquiv
      (MvPolynomial.C a : MvPolynomial (Fin k) ℂ)).restrictScalars ℂ)
theorem homogeneousMap_allTarget_reesChartHyperplaneEquiv_mk
    {k : ℕ} (a : ℂ) (p : MvPolynomial (Fin (k + 1)) ℂ) :
    homogeneousMapAllTargetReesChartHyperplaneEquiv k a
      (Ideal.Quotient.mk
        (homogeneousMapAllTargetReesChartIdeal k a) p) =
      (MvPolynomial.finSuccEquiv ℂ k p).eval
        (MvPolynomial.C a) := by
  rfl
theorem homogeneousMap_allTarget_finSucc_rename_eval_constant
    {k : ℕ} (a : ℂ) (p : MvPolynomial (Fin k) ℂ) :
    (MvPolynomial.finSuccEquiv ℂ k
      (MvPolynomial.rename Fin.succ p)).eval
        (MvPolynomial.C a) = p := by
  induction p using MvPolynomial.induction_on with
  | C z =>
      simpa using congrArg (Polynomial.eval
        (MvPolynomial.C a : MvPolynomial (Fin k) ℂ))
        ((MvPolynomial.finSuccEquiv ℂ k).commutes z)
  | add p q hp hq =>
      simp [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      simp [map_mul, Polynomial.eval_mul,
        MvPolynomial.finSuccEquiv_X_succ, hp]
theorem homogeneousMap_allTarget_reesChartHyperplaneEquiv_coordinate
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (a : ℂ)
    (i : Fin k) :
    homogeneousMapAllTargetReesChartHyperplaneEquiv k a
      (Ideal.Quotient.mk (homogeneousMapAllTargetReesChartIdeal k a)
        (homogeneousMapAllTargetReesCoordinate F target e i)) =
      F i - MvPolynomial.C (target i * a ^ e) := by
  have hC : (MvPolynomial.finSuccEquiv ℂ k)
      (MvPolynomial.C (target i)) =
      Polynomial.C (MvPolynomial.C (target i) : MvPolynomial (Fin k) ℂ) := by
    simpa using (MvPolynomial.finSuccEquiv ℂ k).commutes (target i)
  rw [homogeneousMap_allTarget_reesChartHyperplaneEquiv_mk]
  unfold homogeneousMapAllTargetReesCoordinate
  rw [map_sub, Polynomial.eval_sub, map_mul, Polynomial.eval_mul,
    map_pow, Polynomial.eval_pow,
    MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval_X,
    homogeneousMap_allTarget_finSucc_rename_eval_constant]
  rw [hC]
  simp
noncomputable def homogeneousMapAllTargetReesSourceRingHom
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) :
    homogeneousMapSubalgebra F →+*
      homogeneousMapAllTargetReesQuotient F target e :=
  (Ideal.Quotient.mk
    (Ideal.span (Set.range
      (homogeneousMapAllTargetReesCoordinate F target e)))).comp
    ((MvPolynomial.rename Fin.succ).toRingHom.comp
      (homogeneousMapSubalgebra F).val.toRingHom)
noncomputable abbrev homogeneousMapAllTargetReesSourceAlgebra
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) :
    Algebra (homogeneousMapSubalgebra F)
      (homogeneousMapAllTargetReesQuotient F target e) :=
  (homogeneousMapAllTargetReesSourceRingHom F target e).toAlgebra
open scoped TensorProduct
noncomputable def homogeneousMapAllTargetReesChart
    (k : ℕ) (a : ℂ) :
    MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin k) ℂ :=
  (homogeneousMapAllTargetReesChartHyperplaneEquiv k a).toAlgHom.comp
    (Ideal.Quotient.mkₐ ℂ (homogeneousMapAllTargetReesChartIdeal k a))
theorem homogeneousMapAllTargetReesChart_ker
    (k : ℕ) (a : ℂ) :
    RingHom.ker (homogeneousMapAllTargetReesChart k a).toRingHom =
      homogeneousMapAllTargetReesChartIdeal k a := by
  ext p
  change
    homogeneousMapAllTargetReesChartHyperplaneEquiv k a
      (Ideal.Quotient.mk (homogeneousMapAllTargetReesChartIdeal k a) p) = 0 ↔
      p ∈ homogeneousMapAllTargetReesChartIdeal k a
  constructor
  · intro hp
    have hpzero :
        Ideal.Quotient.mk (homogeneousMapAllTargetReesChartIdeal k a) p = 0 :=
      (homogeneousMapAllTargetReesChartHyperplaneEquiv k a).injective
        (by simpa using hp)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hpzero
  · intro hp
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
theorem homogeneousMapAllTargetReesChart_surjective
    (k : ℕ) (a : ℂ) :
    Function.Surjective (homogeneousMapAllTargetReesChart k a) :=
  (homogeneousMapAllTargetReesChartHyperplaneEquiv k a).surjective.comp
    Ideal.Quotient.mk_surjective
theorem homogeneousMapAllTargetReesEquationIdeal_map_chart
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (a : ℂ) :
    (Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e))).map
      (homogeneousMapAllTargetReesChart k a).toRingHom =
      homogeneousMapFiberIdeal F (fun i => target i * a ^ e) := by
  rw [Ideal.map_span, homogeneousMapFiberIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i,
      (homogeneousMap_allTarget_reesChartHyperplaneEquiv_coordinate
        F target e a i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨homogeneousMapAllTargetReesCoordinate F target e i,
      ⟨i, rfl⟩,
      homogeneousMap_allTarget_reesChartHyperplaneEquiv_coordinate
        F target e a i⟩
noncomputable def homogeneousMapAllTargetReesChartFiberEquiv
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (a : ℂ) :
    (MvPolynomial (Fin (k + 1)) ℂ ⧸
      (Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e)) ⊔
        homogeneousMapAllTargetReesChartIdeal k a)) ≃ₐ[ℂ]
      homogeneousMapClosedFiber F (fun i => target i * a ^ e) := by
  let I : Ideal (MvPolynomial (Fin (k + 1)) ℂ) :=
    Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e))
  let J := homogeneousMapAllTargetReesChartIdeal k a
  let fiber := homogeneousMapFiberIdeal F (fun i => target i * a ^ e)
  let chart := homogeneousMapAllTargetReesChart k a
  let quotientMap : MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ]
      MvPolynomial (Fin k) ℂ ⧸ fiber :=
    (Ideal.Quotient.mkₐ ℂ fiber).comp chart
  have hsurjective : Function.Surjective quotientMap :=
    Ideal.Quotient.mk_surjective.comp
      (homogeneousMapAllTargetReesChart_surjective k a)
  have hkernel : RingHom.ker quotientMap.toRingHom = I ⊔ J := by
    change RingHom.ker
      ((Ideal.Quotient.mk fiber).comp chart.toRingHom) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    change
      (homogeneousMapFiberIdeal F (fun i => target i * a ^ e)).comap
        (homogeneousMapAllTargetReesChart k a).toRingHom = I ⊔ J
    rw [← homogeneousMapAllTargetReesEquationIdeal_map_chart F target e a]
    have h := Ideal.comap_map_of_surjective
      (homogeneousMapAllTargetReesChart k a).toRingHom
      (homogeneousMapAllTargetReesChart_surjective k a) I
    have hker : Ideal.comap (homogeneousMapAllTargetReesChart k a).toRingHom ⊥ = J := by
      change RingHom.ker (homogeneousMapAllTargetReesChart k a).toRingHom = J
      exact homogeneousMapAllTargetReesChart_ker k a
    rw [hker] at h
    exact h
  exact (Ideal.quotientEquivAlgOfEq ℂ hkernel.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurjective)
noncomputable def homogeneousMapAllTargetReesDoubleQuotientFiberEquiv
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (a : ℂ) :
    (homogeneousMapAllTargetReesQuotient F target e ⧸
      (homogeneousMapAllTargetReesChartIdeal k a).map
        (Ideal.Quotient.mkₐ ℂ
          (Ideal.span (Set.range
            (homogeneousMapAllTargetReesCoordinate F target e))))) ≃ₐ[ℂ]
      homogeneousMapClosedFiber F (fun i => target i * a ^ e) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ ℂ
    (Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e)))
    (homogeneousMapAllTargetReesChartIdeal k a)).trans
      (homogeneousMapAllTargetReesChartFiberEquiv F target e a)
theorem homogeneousMapAllTargetReesParameterMaximalIdeal_map
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (a : ℂ) :
    letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
        homogeneousMapAllTargetReesParameterAlgebra F target e
    (RingHom.ker (Polynomial.evalRingHom a)).map
      (algebraMap (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e)) =
    (homogeneousMapAllTargetReesChartIdeal k a).map
      (Ideal.Quotient.mk
        (Ideal.span (Set.range
          (homogeneousMapAllTargetReesCoordinate F target e)))) := by
  letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMapAllTargetReesParameterAlgebra F target e
  have hgenerator :
      algebraMap (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e)
        (Polynomial.X - Polynomial.C a) =
      Ideal.Quotient.mk
        (Ideal.span (Set.range
          (homogeneousMapAllTargetReesCoordinate F target e)))
        (MvPolynomial.X (0 : Fin (k + 1)) - MvPolynomial.C a) := by
    change
      Ideal.Quotient.mk
        (Ideal.span (Set.range
          (homogeneousMapAllTargetReesCoordinate F target e)))
        (Polynomial.aeval
          (MvPolynomial.X (0 : Fin (k + 1)))
          (Polynomial.X - Polynomial.C a)) = _
    simp
  rw [Polynomial.ker_evalRingHom,
    homogeneousMapAllTargetReesChartIdeal, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_singleton]
  rw [hgenerator]
noncomputable def homogeneousMapAllTargetReesPolynomialParameterFiberEquiv
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (a : ℂ) :
    letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
        homogeneousMapAllTargetReesParameterAlgebra F target e
    (homogeneousMapAllTargetReesQuotient F target e ⧸
      (RingHom.ker (Polynomial.evalRingHom a)).map
        (algebraMap (Polynomial ℂ)
          (homogeneousMapAllTargetReesQuotient F target e))) ≃ₐ[ℂ]
      homogeneousMapClosedFiber F (fun i => target i * a ^ e) := by
  letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMapAllTargetReesParameterAlgebra F target e
  have hideal := homogeneousMapAllTargetReesParameterMaximalIdeal_map F target e a
  exact (Ideal.quotientEquivAlgOfEq ℂ hideal).trans
    (homogeneousMapAllTargetReesDoubleQuotientFiberEquiv F target e a)
end Standalone_MultivariateBezout
noncomputable section Standalone_FreeAffine
open scoped BigOperators
structure FreeAffineForm (ι : Type*) where
  constant : ℂ
  inputCoefficients : ι →₀ ℂ
  gateCoefficients : ℕ →₀ ℂ
namespace FreeAffineForm
def eval {ι : Type*} (form : FreeAffineForm ι)
    (values : Array (MvPolynomial ι ℂ)) : MvPolynomial ι ℂ :=
  MvPolynomial.C form.constant +
    Finsupp.linearCombination ℂ MvPolynomial.X form.inputCoefficients +
    Finsupp.linearCombination ℂ (fun index => values.getD index 0)
      form.gateCoefficients
@[simp] protected def zero {ι : Type*} : FreeAffineForm ι := ⟨0, 0, 0⟩
instance {ι : Type*} : Zero (FreeAffineForm ι) := ⟨FreeAffineForm.zero⟩
@[simp] protected def add {ι : Type*} (left right : FreeAffineForm ι) :
    FreeAffineForm ι :=
  ⟨left.constant + right.constant,
    left.inputCoefficients + right.inputCoefficients,
    left.gateCoefficients + right.gateCoefficients⟩
instance {ι : Type*} : Add (FreeAffineForm ι) := ⟨FreeAffineForm.add⟩
@[simp] protected def sub {ι : Type*} (left right : FreeAffineForm ι) :
    FreeAffineForm ι :=
  ⟨left.constant - right.constant,
    left.inputCoefficients - right.inputCoefficients,
    left.gateCoefficients - right.gateCoefficients⟩
instance {ι : Type*} : Sub (FreeAffineForm ι) := ⟨FreeAffineForm.sub⟩
@[simp] protected def smul {ι : Type*} (coefficient : ℂ) (form : FreeAffineForm ι) :
    FreeAffineForm ι :=
  ⟨coefficient * form.constant,
    coefficient • form.inputCoefficients,
    coefficient • form.gateCoefficients⟩
instance {ι : Type*} : SMul ℂ (FreeAffineForm ι) :=
  ⟨FreeAffineForm.smul⟩
def scalar {ι : Type*} (coefficient : ℂ) : FreeAffineForm ι :=
  ⟨coefficient, 0, 0⟩
def input {ι : Type*} (index : ι) : FreeAffineForm ι :=
  ⟨0, Finsupp.single index 1, 0⟩
def gate {ι : Type*} (index : ℕ) : FreeAffineForm ι :=
  ⟨0, 0, Finsupp.single index 1⟩
@[simp] theorem eval_zero {ι : Type*}
    (values : Array (MvPolynomial ι ℂ)) :
    (0 : FreeAffineForm ι).eval values = 0 := by
  change
    MvPolynomial.C (0 : ℂ) +
      Finsupp.linearCombination ℂ MvPolynomial.X (0 : ι →₀ ℂ) +
      Finsupp.linearCombination ℂ (fun index => values.getD index 0)
        (0 : ℕ →₀ ℂ) = 0
  simp
@[simp] theorem eval_scalar {ι : Type*} (coefficient : ℂ)
    (values : Array (MvPolynomial ι ℂ)) :
    (scalar coefficient : FreeAffineForm ι).eval values =
      MvPolynomial.C coefficient := by
  simp [eval, scalar]
@[simp] theorem eval_input {ι : Type*} (index : ι)
    (values : Array (MvPolynomial ι ℂ)) :
    (input index).eval values = MvPolynomial.X index := by
  simp [eval, input]
@[simp] theorem eval_gate {ι : Type*} (index : ℕ)
    (values : Array (MvPolynomial ι ℂ)) :
    (gate index : FreeAffineForm ι).eval values = values.getD index 0 := by
  simp [eval, gate]
@[simp] theorem eval_add {ι : Type*} (left right : FreeAffineForm ι)
    (values : Array (MvPolynomial ι ℂ)) :
    (left + right).eval values = left.eval values + right.eval values := by
  change
    MvPolynomial.C (left.constant + right.constant) +
      Finsupp.linearCombination ℂ MvPolynomial.X
        (left.inputCoefficients + right.inputCoefficients) +
      Finsupp.linearCombination ℂ (fun index => values.getD index 0)
        (left.gateCoefficients + right.gateCoefficients) = _
  simp [eval, add_assoc, add_left_comm, add_comm]
@[simp] theorem eval_sub {ι : Type*} (left right : FreeAffineForm ι)
    (values : Array (MvPolynomial ι ℂ)) :
    (left - right).eval values = left.eval values - right.eval values := by
  change
    MvPolynomial.C (left.constant - right.constant) +
      Finsupp.linearCombination ℂ MvPolynomial.X
        (left.inputCoefficients - right.inputCoefficients) +
      Finsupp.linearCombination ℂ (fun index => values.getD index 0)
        (left.gateCoefficients - right.gateCoefficients) = _
  simp [eval, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
@[simp] theorem eval_smul {ι : Type*} (coefficient : ℂ)
    (form : FreeAffineForm ι) (values : Array (MvPolynomial ι ℂ)) :
    (coefficient • form).eval values = coefficient • form.eval values := by
  change
    MvPolynomial.C (coefficient * form.constant) +
      Finsupp.linearCombination ℂ MvPolynomial.X
        (coefficient • form.inputCoefficients) +
      Finsupp.linearCombination ℂ (fun index => values.getD index 0)
        (coefficient • form.gateCoefficients) = _
  simp [eval, MvPolynomial.smul_eq_C_mul]
end FreeAffineForm
structure FreeAffineInput (ι : Type*) where
  constant : ℂ
  inputCoefficients : ι →₀ ℂ
namespace FreeAffineInput
def polynomial {ι : Type*} (input : FreeAffineInput ι) :
    MvPolynomial ι ℂ :=
  MvPolynomial.C input.constant +
    Finsupp.linearCombination ℂ MvPolynomial.X input.inputCoefficients
end FreeAffineInput
namespace FreeAffineForm
def substituteInputs {ι κ : Type*} (form : FreeAffineForm ι)
    (substitution : ι → FreeAffineInput κ) : FreeAffineForm κ where
  constant := form.constant +
    Finsupp.linearCombination ℂ
      (fun index => (substitution index).constant) form.inputCoefficients
  inputCoefficients := Finsupp.linearCombination ℂ
    (fun index => (substitution index).inputCoefficients)
    form.inputCoefficients
  gateCoefficients := form.gateCoefficients
end FreeAffineForm
inductive FreeAffineInstruction (ι : Type*) where
  | affine (form : FreeAffineForm ι)
  | mul (left right : ℕ)
namespace FreeAffineInstruction
def referencesBounded {ι : Type*} (position : ℕ) :
    FreeAffineInstruction ι → Bool
  | .affine form =>
    decide (∀ index ∈ form.gateCoefficients.support, index < position)
  | .mul left right => decide (left < position) && decide (right < position)
def isMultiplication {ι : Type*} : FreeAffineInstruction ι → Bool
  | .affine _ => false
  | .mul _ _ => true
def eval {ι : Type*} (values : Array (MvPolynomial ι ℂ)) :
    FreeAffineInstruction ι → MvPolynomial ι ℂ
  | .affine form => form.eval values
  | .mul left right => values.getD left 0 * values.getD right 0
def substituteInputs {ι κ : Type*}
    (substitution : ι → FreeAffineInput κ) :
    FreeAffineInstruction ι → FreeAffineInstruction κ
  | .affine form => .affine (form.substituteInputs substitution)
  | .mul left right => .mul left right
@[simp] theorem referencesBounded_substituteInputs {ι κ : Type*}
    (substitution : ι → FreeAffineInput κ)
    (instruction : FreeAffineInstruction ι) (position : ℕ) :
    (instruction.substituteInputs substitution).referencesBounded position =
      instruction.referencesBounded position := by
  cases instruction <;> rfl
def ofInstruction {ι : Type} : Instruction ι → FreeAffineInstruction ι
  | .input index => .affine (FreeAffineForm.input index)
  | .scalar coefficient => .affine (FreeAffineForm.scalar coefficient)
  | .add left right =>
    .affine (FreeAffineForm.gate left + FreeAffineForm.gate right)
  | .sub left right =>
    .affine (FreeAffineForm.gate left - FreeAffineForm.gate right)
  | .mul left right => .mul left right
@[simp] theorem eval_ofInstruction {ι : Type}
    (instruction : Instruction ι) (values : Array (MvPolynomial ι ℂ)) :
    (ofInstruction instruction).eval values = instruction.eval values := by
  cases instruction <;>
    simp [ofInstruction, eval, Instruction.eval]
theorem referencesBounded_ofInstruction {ι : Type}
    (instruction : Instruction ι) (position : ℕ)
    (valid : instruction.referencesBounded position) :
    (ofInstruction instruction).referencesBounded position := by
  cases instruction with
  | input index =>
    simp [ofInstruction, referencesBounded, FreeAffineForm.input]
  | scalar coefficient =>
    simp [ofInstruction, referencesBounded, FreeAffineForm.scalar]
  | add left right =>
    simp only [Instruction.referencesBounded, Bool.and_eq_true,
      decide_eq_true_eq] at valid
    simp only [ofInstruction, referencesBounded,
      FreeAffineForm.gate, decide_eq_true_eq]
    intro index hindex
    rw [Finsupp.mem_support_iff] at hindex
    by_cases hleft : index = left
    · simpa [hleft] using valid.1
    · by_cases hright : index = right
      · simpa [hright] using valid.2
      · change
          ((Finsupp.single left (1 : ℂ) + Finsupp.single right 1 : ℕ →₀ ℂ)
            index) ≠ 0
          at hindex
        simp [hleft, hright] at hindex
  | sub left right =>
    simp only [Instruction.referencesBounded, Bool.and_eq_true,
      decide_eq_true_eq] at valid
    simp only [ofInstruction, referencesBounded,
      FreeAffineForm.gate, decide_eq_true_eq]
    intro index hindex
    rw [Finsupp.mem_support_iff] at hindex
    by_cases hleft : index = left
    · simpa [hleft] using valid.1
    · by_cases hright : index = right
      · simpa [hright] using valid.2
      · change
          ((Finsupp.single left (1 : ℂ) - Finsupp.single right 1 : ℕ →₀ ℂ)
            index) ≠ 0
          at hindex
        simp [hleft, hright] at hindex
  | mul left right =>
    simpa [ofInstruction, referencesBounded,
      Instruction.referencesBounded] using valid
end FreeAffineInstruction
structure FreeAffineCircuit (ι : Type*) where
  program : List (FreeAffineInstruction ι)
  outputs : List (FreeAffineForm ι)
  valid : ∀ position : Fin program.length,
    (program.get position).referencesBounded position.val
  validOutputs : ∀ form ∈ outputs, ∀ index : ℕ,
    form.gateCoefficients index ≠ 0 → index < program.length
namespace FreeAffineCircuit
def values {ι : Type*} (circuit : FreeAffineCircuit ι) :
    Array (MvPolynomial ι ℂ) :=
  circuit.program.foldl
    (fun values instruction => values.push (instruction.eval values)) #[]
def polynomials {ι : Type*} (circuit : FreeAffineCircuit ι) :
    List (MvPolynomial ι ℂ) :=
  circuit.outputs.map fun form => form.eval circuit.values
def multiplicationCount {ι : Type*} (circuit : FreeAffineCircuit ι) : ℕ :=
  (circuit.program.filter FreeAffineInstruction.isMultiplication).length
def substituteInputs {ι κ : Type*} (circuit : FreeAffineCircuit ι)
    (substitution : ι → FreeAffineInput κ) : FreeAffineCircuit κ where
  program := circuit.program.map
    (FreeAffineInstruction.substituteInputs substitution)
  outputs := circuit.outputs.map
    (fun form => form.substituteInputs substitution)
  valid := by
    intro position
    have hposition : position.val < circuit.program.length := by
      simpa using position.isLt
    have hvalid := circuit.valid ⟨position.val, hposition⟩
    simpa using hvalid
  validOutputs := by
    intro form hform index hindex
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hform
    simpa using circuit.validOutputs original horiginal index hindex
@[simp] theorem multiplicationCount_substituteInputs {ι κ : Type*}
    (circuit : FreeAffineCircuit ι)
    (substitution : ι → FreeAffineInput κ) :
    (circuit.substituteInputs substitution).multiplicationCount =
      circuit.multiplicationCount := by
  change
    ((circuit.program.map
      (FreeAffineInstruction.substituteInputs substitution)).filter
      FreeAffineInstruction.isMultiplication).length =
      (circuit.program.filter
        FreeAffineInstruction.isMultiplication).length
  induction circuit.program with
  | nil => simp
  | cons instruction tail ih =>
    cases instruction <;>
      simp [FreeAffineInstruction.substituteInputs,
        FreeAffineInstruction.isMultiplication, ih]
def withOutputs {ι : Type*} (circuit : FreeAffineCircuit ι)
    (outputs : List (FreeAffineForm ι))
    (validOutputs : ∀ form ∈ outputs, ∀ index : ℕ,
      form.gateCoefficients index ≠ 0 → index < circuit.program.length) :
    FreeAffineCircuit ι where
  program := circuit.program
  outputs := outputs
  valid := circuit.valid
  validOutputs := validOutputs
def ofArithmetic {ι : Type} (circuit : ArithmeticCircuit ι) :
    FreeAffineCircuit ι where
  program := circuit.program.map FreeAffineInstruction.ofInstruction
  outputs := [FreeAffineForm.gate circuit.output]
  valid := by
    intro position
    have hposition : position.val < circuit.program.length := by
      simpa using position.isLt
    have hvalid := circuit.valid ⟨position.val, hposition⟩
    simpa using FreeAffineInstruction.referencesBounded_ofInstruction
      (circuit.program.get ⟨position.val, hposition⟩) position.val hvalid
  validOutputs := by
    intro form hform index hindex
    simp only [List.mem_singleton] at hform
    subst form
    change (Finsupp.single circuit.output (1 : ℂ)) index ≠ 0 at hindex
    have heq : index = circuit.output :=
      (Finsupp.single_apply_ne_zero.mp hindex).1
    simpa [heq] using circuit.output_lt
@[simp] theorem values_ofArithmetic {ι : Type}
    (circuit : ArithmeticCircuit ι) :
    (ofArithmetic circuit).values = circuit.values := by
  simp only [values, ofArithmetic, ArithmeticCircuit.values, List.foldl_map]
  simp_rw [FreeAffineInstruction.eval_ofInstruction]
end FreeAffineCircuit
end Standalone_FreeAffine
noncomputable section Standalone_ReverseMode
open scoped BigOperators
structure ReverseAdjoint (ι : Type*) where
  inputAdjoints : ι →₀ MvPolynomial ι ℂ
  gateAdjoints : ℕ →₀ MvPolynomial ι ℂ
  multiplicationCount : ℕ
namespace ReverseAdjoint
def scaleCoefficients {ι κ : Type*}
    (adjoint : MvPolynomial ι ℂ) (coefficients : κ →₀ ℂ) :
    κ →₀ MvPolynomial ι ℂ :=
  coefficients.mapRange (fun coefficient =>
    MvPolynomial.C coefficient * adjoint) (by simp)
@[simp] theorem scaleCoefficients_apply {ι κ : Type*}
    (adjoint : MvPolynomial ι ℂ) (coefficients : κ →₀ ℂ)
    (index : κ) :
    scaleCoefficients adjoint coefficients index =
      MvPolynomial.C (coefficients index) * adjoint := by
  simp [scaleCoefficients]
def affine {ι : Type*} (state : ReverseAdjoint ι)
    (position : ℕ) (form : FreeAffineForm ι) : ReverseAdjoint ι where
  inputAdjoints := state.inputAdjoints +
    scaleCoefficients (state.gateAdjoints position)
      form.inputCoefficients
  gateAdjoints := state.gateAdjoints.erase position +
    scaleCoefficients (state.gateAdjoints position)
      form.gateCoefficients
  multiplicationCount := state.multiplicationCount
@[simp] theorem affine_inputAdjoints_apply {ι : Type*}
    (state : ReverseAdjoint ι) (position : ℕ)
    (form : FreeAffineForm ι) (input : ι) :
    (state.affine position form).inputAdjoints input =
      state.inputAdjoints input +
        MvPolynomial.C (form.inputCoefficients input) *
          state.gateAdjoints position := by
  simp [affine]
def mul {ι : Type*} (state : ReverseAdjoint ι)
    (values : Array (MvPolynomial ι ℂ))
    (position left right : ℕ) : ReverseAdjoint ι where
  inputAdjoints := state.inputAdjoints
  gateAdjoints := state.gateAdjoints.erase position +
    Finsupp.single left
      (state.gateAdjoints position * values.getD right 0) +
    Finsupp.single right
      (state.gateAdjoints position * values.getD left 0)
  multiplicationCount := state.multiplicationCount + 2
def step {ι : Type*} (values : Array (MvPolynomial ι ℂ))
    (state : ReverseAdjoint ι)
    (instruction : FreeAffineInstruction ι × ℕ) : ReverseAdjoint ι :=
  match instruction.1 with
  | .affine form => state.affine instruction.2 form
  | .mul left right => state.mul values instruction.2 left right
def initial {ι : Type*} (output : FreeAffineForm ι) : ReverseAdjoint ι where
  inputAdjoints := scaleCoefficients 1 output.inputCoefficients
  gateAdjoints := scaleCoefficients 1 output.gateCoefficients
  multiplicationCount := 0
def potential {ι : Type*} (state : ReverseAdjoint ι)
    (values : Array (MvPolynomial ι ℂ)) (input : ι) :
    MvPolynomial ι ℂ :=
  state.inputAdjoints input +
    Finsupp.linearCombination (MvPolynomial ι ℂ)
      (fun gate => MvPolynomial.pderiv input (values.getD gate 0))
      state.gateAdjoints
def forwardStep {ι : Type*} (values : Array (MvPolynomial ι ℂ))
    (instruction : FreeAffineInstruction ι) :
    Array (MvPolynomial ι ℂ) :=
  values.push (instruction.eval values)
def run {ι : Type*} (circuit : FreeAffineCircuit ι)
    (output : FreeAffineForm ι) : ReverseAdjoint ι :=
  (circuit.program.zipIdx.reverse).foldl
    (step circuit.values) (initial output)
def appendInstruction {ι : Type*} (circuit : FreeAffineCircuit ι)
    (instruction : FreeAffineInstruction ι)
    (hvalid : instruction.referencesBounded circuit.program.length) :
    FreeAffineCircuit ι where
  program := circuit.program ++ [instruction]
  outputs := circuit.outputs
  valid := by
    intro position
    by_cases hposition : position.val < circuit.program.length
    · change
        ((circuit.program ++ [instruction])[position.val]).referencesBounded
          position.val
      rw [List.getElem_append_left hposition]
      exact circuit.valid ⟨position.val, hposition⟩
    · have hlast : position.val = circuit.program.length := by
        have hlt := position.isLt
        simp only [List.length_append, List.length_singleton] at hlt
        omega
      change
        ((circuit.program ++ [instruction])[position.val]).referencesBounded
          position.val
      rw [List.getElem_append_right (by omega)]
      simpa [hlast] using hvalid
  validOutputs := by
    intro form hform index hindex
    have hbound := circuit.validOutputs form hform index hindex
    simp only [List.length_append, List.length_singleton]
    omega
def appendReverseProducts {ι : Type*}
    (circuit : FreeAffineCircuit ι) (adjoint : FreeAffineForm ι)
    (left right : ℕ)
    (hadjoint : ∀ index, adjoint.gateCoefficients index ≠ 0 →
      index < circuit.program.length)
    (hleft : left < circuit.program.length)
    (hright : right < circuit.program.length) : FreeAffineCircuit ι := by
  have haffine :
      (FreeAffineInstruction.affine adjoint).referencesBounded
        circuit.program.length := by
    simp only [FreeAffineInstruction.referencesBounded,
      decide_eq_true_eq]
    intro index hindex
    exact hadjoint index (Finsupp.mem_support_iff.mp hindex)
  let first := appendInstruction circuit (.affine adjoint) haffine
  have hfirst : first.program.length = circuit.program.length + 1 := by
    simp [first, appendInstruction]
  have hrightProduct :
      (FreeAffineInstruction.mul circuit.program.length right :
        FreeAffineInstruction ι).referencesBounded
          first.program.length := by
    simp only [FreeAffineInstruction.referencesBounded,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · omega
    · omega
  let second := appendInstruction first
    (.mul circuit.program.length right) hrightProduct
  have hsecond : second.program.length = circuit.program.length + 2 := by
    simp [second, first, appendInstruction]
  have hleftProduct :
      (FreeAffineInstruction.mul circuit.program.length left :
        FreeAffineInstruction ι).referencesBounded
          second.program.length := by
    simp only [FreeAffineInstruction.referencesBounded,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · omega
    · omega
  exact appendInstruction second
    (.mul circuit.program.length left) hleftProduct
theorem appendReverseProducts_program_length {ι : Type*}
    (circuit : FreeAffineCircuit ι) (adjoint : FreeAffineForm ι)
    (left right : ℕ)
    (hadjoint : ∀ index, adjoint.gateCoefficients index ≠ 0 →
      index < circuit.program.length)
    (hleft : left < circuit.program.length)
    (hright : right < circuit.program.length) :
    (appendReverseProducts circuit adjoint left right
      hadjoint hleft hright).program.length =
        circuit.program.length + 3 := by
  simp [appendReverseProducts, appendInstruction]
theorem affineForm_gateBound_mono {ι : Type*}
    (form : FreeAffineForm ι) {oldBound newBound : ℕ}
    (hbound : oldBound ≤ newBound)
    (hvalid : ∀ index, form.gateCoefficients index ≠ 0 →
      index < oldBound) :
    ∀ index, form.gateCoefficients index ≠ 0 → index < newBound := by
  intro index hindex
  exact Nat.lt_of_lt_of_le (hvalid index hindex) hbound
theorem affineForm_gateBound_add {ι : Type*}
    (left right : FreeAffineForm ι) (bound : ℕ)
    (hleft : ∀ index, left.gateCoefficients index ≠ 0 → index < bound)
    (hright : ∀ index, right.gateCoefficients index ≠ 0 → index < bound) :
    ∀ index, (left + right).gateCoefficients index ≠ 0 →
      index < bound := by
  intro index hindex
  change ((left.gateCoefficients + right.gateCoefficients : ℕ →₀ ℂ) index) ≠ 0
    at hindex
  by_cases hleftZero : left.gateCoefficients index = 0
  · apply hright index
    intro hrightZero
    apply hindex
    simp [hleftZero, hrightZero]
  · exact hleft index hleftZero
theorem affineForm_gateBound_smul {ι : Type*}
    (coefficient : ℂ) (form : FreeAffineForm ι) (bound : ℕ)
    (hvalid : ∀ index, form.gateCoefficients index ≠ 0 →
      index < bound) :
    ∀ index, (coefficient • form).gateCoefficients index ≠ 0 →
      index < bound := by
  intro index hindex
  change ((coefficient • form.gateCoefficients : ℕ →₀ ℂ) index) ≠ 0 at hindex
  apply hvalid index
  intro hzero
  apply hindex
  simp [hzero]
theorem affineForm_gateBound_gate {ι : Type*}
    (position bound : ℕ) (hposition : position < bound) :
    ∀ index,
      (FreeAffineForm.gate position : FreeAffineForm ι).gateCoefficients
        index ≠ 0 → index < bound := by
  intro index hindex
  change (Finsupp.single position (1 : ℂ)) index ≠ 0 at hindex
  have heq := (Finsupp.single_apply_ne_zero.mp hindex).1
  simpa [heq] using hposition
structure CircuitAdjoint (ι : Type*) where
  circuit : FreeAffineCircuit ι
  sourceLength : ℕ
  sourceLength_le : sourceLength ≤ circuit.program.length
  inputAdjoints : ι → FreeAffineForm ι
  gateAdjoints : ℕ → FreeAffineForm ι
  validInputAdjoints : ∀ input index,
    (inputAdjoints input).gateCoefficients index ≠ 0 →
      index < circuit.program.length
  validGateAdjoints : ∀ gate index,
    (gateAdjoints gate).gateCoefficients index ≠ 0 →
      index < circuit.program.length
namespace CircuitAdjoint
def initial {ι : Type*} (circuit : FreeAffineCircuit ι)
    (output : FreeAffineForm ι) : CircuitAdjoint ι where
  circuit := circuit
  sourceLength := circuit.program.length
  sourceLength_le := le_rfl
  inputAdjoints := fun input =>
    FreeAffineForm.scalar (output.inputCoefficients input)
  gateAdjoints := fun gate =>
    FreeAffineForm.scalar (output.gateCoefficients gate)
  validInputAdjoints := by
    intro input index hindex
    simp [FreeAffineForm.scalar] at hindex
  validGateAdjoints := by
    intro gate index hindex
    simp [FreeAffineForm.scalar] at hindex
def affine {ι : Type*} (state : CircuitAdjoint ι)
    (position : ℕ) (form : FreeAffineForm ι) : CircuitAdjoint ι where
  circuit := state.circuit
  sourceLength := state.sourceLength
  sourceLength_le := state.sourceLength_le
  inputAdjoints := fun input =>
    state.inputAdjoints input +
      form.inputCoefficients input • state.gateAdjoints position
  gateAdjoints := fun gate =>
    if gate = position then 0 else
      state.gateAdjoints gate +
        form.gateCoefficients gate • state.gateAdjoints position
  validInputAdjoints := by
    intro input index hindex
    exact affineForm_gateBound_add
      (state.inputAdjoints input)
      (form.inputCoefficients input • state.gateAdjoints position)
      state.circuit.program.length
      (state.validInputAdjoints input)
      (affineForm_gateBound_smul (form.inputCoefficients input)
        (state.gateAdjoints position) state.circuit.program.length
        (state.validGateAdjoints position)) index hindex
  validGateAdjoints := by
    intro gate index hindex
    by_cases hgate : gate = position
    · subst gate
      simp only [] at hindex
      change ((0 : ℕ →₀ ℂ) index) ≠ 0 at hindex
      simp at hindex
    · apply affineForm_gateBound_add
        (state.gateAdjoints gate)
        (form.gateCoefficients gate • state.gateAdjoints position)
        state.circuit.program.length
        (state.validGateAdjoints gate)
        (affineForm_gateBound_smul (form.gateCoefficients gate)
          (state.gateAdjoints position) state.circuit.program.length
          (state.validGateAdjoints position)) index
      simpa [hgate] using hindex
def mul {ι : Type*} (state : CircuitAdjoint ι)
    (position left right : ℕ)
    (hleft : left < state.sourceLength)
    (hright : right < state.sourceLength) : CircuitAdjoint ι := by
  let hadjoint : ∀ index,
      (state.gateAdjoints position).gateCoefficients index ≠ 0 →
        index < state.circuit.program.length :=
    state.validGateAdjoints position
  let hleft' : left < state.circuit.program.length :=
    Nat.lt_of_lt_of_le hleft state.sourceLength_le
  let hright' : right < state.circuit.program.length :=
    Nat.lt_of_lt_of_le hright state.sourceLength_le
  let next := appendReverseProducts state.circuit
    (state.gateAdjoints position) left right hadjoint hleft' hright'
  have hnext : next.program.length = state.circuit.program.length + 3 :=
    appendReverseProducts_program_length state.circuit
      (state.gateAdjoints position) left right hadjoint hleft' hright'
  refine
    { circuit := next
      sourceLength := state.sourceLength
      sourceLength_le :=
        Nat.le_trans state.sourceLength_le (by omega)
      inputAdjoints := state.inputAdjoints
      gateAdjoints := fun gate =>
        (if gate = position then 0 else state.gateAdjoints gate) +
          (if gate = left then
            FreeAffineForm.gate (state.circuit.program.length + 1)
          else 0) +
          (if gate = right then
            FreeAffineForm.gate (state.circuit.program.length + 2)
          else 0)
      validInputAdjoints := ?_
      validGateAdjoints := ?_ }
  · intro input index hindex
    apply affineForm_gateBound_mono (state.inputAdjoints input)
      (by omega) (state.validInputAdjoints input) index hindex
  · intro gate index hindex
    have hbase :
        ∀ index,
          (if gate = position then (0 : FreeAffineForm ι)
            else state.gateAdjoints gate).gateCoefficients index ≠ 0 →
              index < next.program.length := by
      by_cases hgate : gate = position
      · subst gate
        intro index hindex
        simp only [] at hindex
        change ((0 : ℕ →₀ ℂ) index) ≠ 0 at hindex
        simp at hindex
      · simpa [hgate] using
          affineForm_gateBound_mono (state.gateAdjoints gate)
            (by omega) (state.validGateAdjoints gate)
    have hleftForm :
        ∀ index,
          (if gate = left then
            FreeAffineForm.gate (state.circuit.program.length + 1)
          else (0 : FreeAffineForm ι)).gateCoefficients index ≠ 0 →
            index < next.program.length := by
      by_cases hgate : gate = left
      · simpa [hgate] using
          affineForm_gateBound_gate (ι := ι)
            (state.circuit.program.length + 1)
            next.program.length (by omega)
      · simp only [hgate, ↓reduceIte]
        intro index hindex
        change ((0 : ℕ →₀ ℂ) index) ≠ 0 at hindex
        simp at hindex
    have hrightForm :
        ∀ index,
          (if gate = right then
            FreeAffineForm.gate (state.circuit.program.length + 2)
          else (0 : FreeAffineForm ι)).gateCoefficients index ≠ 0 →
            index < next.program.length := by
      by_cases hgate : gate = right
      · simpa [hgate] using
          affineForm_gateBound_gate (ι := ι)
            (state.circuit.program.length + 2)
            next.program.length (by omega)
      · simp only [hgate, ↓reduceIte]
        intro index hindex
        change ((0 : ℕ →₀ ℂ) index) ≠ 0 at hindex
        simp at hindex
    exact affineForm_gateBound_add
      ((if gate = position then 0 else state.gateAdjoints gate) +
        (if gate = left then
          FreeAffineForm.gate (state.circuit.program.length + 1)
        else 0))
      (if gate = right then
        FreeAffineForm.gate (state.circuit.program.length + 2)
      else 0)
      next.program.length
      (affineForm_gateBound_add
        (if gate = position then 0 else state.gateAdjoints gate)
        (if gate = left then
          FreeAffineForm.gate (state.circuit.program.length + 1)
        else 0)
        next.program.length hbase hleftForm)
      hrightForm index hindex
@[simp] theorem mul_circuit {ι : Type*}
    (state : CircuitAdjoint ι) (position left right : ℕ)
    (hleft : left < state.sourceLength)
    (hright : right < state.sourceLength) :
    (state.mul position left right hleft hright).circuit =
      appendReverseProducts state.circuit
        (state.gateAdjoints position) left right
        (state.validGateAdjoints position)
        (Nat.lt_of_lt_of_le hleft state.sourceLength_le)
        (Nat.lt_of_lt_of_le hright state.sourceLength_le) := rfl
@[simp] theorem mul_inputAdjoints_apply {ι : Type*}
    (state : CircuitAdjoint ι) (position left right : ℕ)
    (hleft : left < state.sourceLength)
    (hright : right < state.sourceLength) (input : ι) :
    (state.mul position left right hleft hright).inputAdjoints input =
      state.inputAdjoints input := rfl
@[simp] theorem mul_gateAdjoints_apply {ι : Type*}
    (state : CircuitAdjoint ι) (position left right : ℕ)
    (hleft : left < state.sourceLength)
    (hright : right < state.sourceLength) (gate : ℕ) :
    (state.mul position left right hleft hright).gateAdjoints gate =
      (if gate = position then 0 else state.gateAdjoints gate) +
        (if gate = left then
          FreeAffineForm.gate (state.circuit.program.length + 1)
        else 0) +
        (if gate = right then
          FreeAffineForm.gate (state.circuit.program.length + 2)
        else 0) := rfl
end CircuitAdjoint
def instructionCost {ι : Type*} : FreeAffineInstruction ι → ℕ
  | .affine _ => 0
  | .mul _ _ => 2
namespace CircuitAdjoint
def step {ι : Type*} (state : CircuitAdjoint ι)
    (instruction : FreeAffineInstruction ι × ℕ) : CircuitAdjoint ι :=
  match instruction.1 with
  | .affine form => state.affine instruction.2 form
  | .mul left right =>
    if h : left < state.sourceLength ∧ right < state.sourceLength then
      state.mul instruction.2 left right h.1 h.2
    else
      state
@[simp] theorem step_sourceLength {ι : Type*}
    (state : CircuitAdjoint ι)
    (instruction : FreeAffineInstruction ι × ℕ) :
    (step state instruction).sourceLength = state.sourceLength := by
  rcases instruction with ⟨instruction, position⟩
  cases instruction with
  | affine form => rfl
  | mul left right =>
    by_cases h : left < state.sourceLength ∧
      right < state.sourceLength
    · simp [step, h, mul]
    · simp [step, h]
def run {ι : Type*} (circuit : FreeAffineCircuit ι)
    (output : FreeAffineForm ι) : CircuitAdjoint ι :=
  circuit.program.zipIdx.reverse.foldl step (initial circuit output)
end CircuitAdjoint
end ReverseAdjoint
end Standalone_ReverseMode
section Standalone_AffineBezout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def affineTotalDegreeFilteredPiece
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ) :
    Submodule ℂ (MvPolynomial ι ℂ ⧸ I) :=
  (MvPolynomial.restrictTotalDegree ι ℂ n).map
    (Ideal.Quotient.mkₐ ℂ I).toLinearMap
noncomputable def affineTotalDegreeFilteredProjection
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ) :
    MvPolynomial.restrictTotalDegree ι ℂ n →ₗ[ℂ]
      affineTotalDegreeFilteredPiece I n :=
  LinearMap.codRestrict (affineTotalDegreeFilteredPiece I n)
    ((Ideal.Quotient.mkₐ ℂ I).toLinearMap.domRestrict
      (MvPolynomial.restrictTotalDegree ι ℂ n)) (by
        intro p
        apply Submodule.mem_map.mpr
        exact ⟨p, p.property, rfl⟩)
theorem affine_total_degree_filtered_projection_surjective
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ) :
    Function.Surjective (affineTotalDegreeFilteredProjection I n) := by
  intro x
  obtain ⟨p, hp, hpimage⟩ := Submodule.mem_map.mp x.property
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  exact hpimage
noncomputable instance affine_total_degree_filtered_piece_finite
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ) :
    Module.Finite ℂ (affineTotalDegreeFilteredPiece I n) :=
  Module.Finite.of_surjective
    (affineTotalDegreeFilteredProjection I n)
    (affine_total_degree_filtered_projection_surjective I n)
theorem affine_total_degree_filtered_piece_mem_iff
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ)
    (x : MvPolynomial ι ℂ ⧸ I) :
    x ∈ affineTotalDegreeFilteredPiece I n ↔
      ∃ p : MvPolynomial ι ℂ, p.totalDegree ≤ n ∧
        Ideal.Quotient.mk I p = x := by
  simp [affineTotalDegreeFilteredPiece,
    MvPolynomial.mem_restrictTotalDegree]
noncomputable def affineTotalDegreeFilteredFactor
    {ι : Type*} {I J : Ideal (MvPolynomial ι ℂ)}
    (hIJ : I ≤ J) (n : ℕ) :
    affineTotalDegreeFilteredPiece I n →ₗ[ℂ]
      affineTotalDegreeFilteredPiece J n :=
  LinearMap.codRestrict (affineTotalDegreeFilteredPiece J n)
    ((Ideal.Quotient.factorₐ ℂ hIJ).toLinearMap.domRestrict
      (affineTotalDegreeFilteredPiece I n)) (by
        intro x
        obtain ⟨p, hp, hpimage⟩ :=
          (affine_total_degree_filtered_piece_mem_iff
            I n x).mp x.property
        apply (affine_total_degree_filtered_piece_mem_iff J n _).mpr
        refine ⟨p, hp, ?_⟩
        change Ideal.Quotient.mk J p =
          Ideal.Quotient.factorₐ ℂ hIJ (x : MvPolynomial ι ℂ ⧸ I)
        rw [← hpimage]
        rfl)
noncomputable def affineTotalDegreeFilteredMul
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (g : MvPolynomial ι ℂ) (n : ℕ) :
    affineTotalDegreeFilteredPiece I n →ₗ[ℂ]
      affineTotalDegreeFilteredPiece I (g.totalDegree + n) :=
  LinearMap.codRestrict
    (affineTotalDegreeFilteredPiece I (g.totalDegree + n))
    ((LinearMap.mulLeft ℂ (Ideal.Quotient.mk I g)).domRestrict
        (affineTotalDegreeFilteredPiece I n)) (by
      intro x
      obtain ⟨p, hp, hpimage⟩ :=
        (affine_total_degree_filtered_piece_mem_iff I n x).mp x.property
      apply (affine_total_degree_filtered_piece_mem_iff
        I (g.totalDegree + n) _).mpr
      refine ⟨g * p,
        (MvPolynomial.totalDegree_mul g p).trans
          (Nat.add_le_add_left hp g.totalDegree), ?_⟩
      change Ideal.Quotient.mk I (g * p) =
        Ideal.Quotient.mk I g * (x : MvPolynomial ι ℂ ⧸ I)
      rw [map_mul, hpimage])
def affineCumulative (H : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (m + 1), H i
noncomputable def affineTotalDegreeHilbert
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ)) (n : ℕ) : ℕ :=
  Module.finrank ℂ (affineTotalDegreeFilteredPiece I n)
noncomputable def affineGateGraphIdeal {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin q) ℂ) :=
  Ideal.span (Set.range fun j : Fin q =>
    MvPolynomial.X (Sum.inr j) -
      MvPolynomial.rename Sum.inl (gate j))
noncomputable def affineGateGraphEvaluation {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) :
    MvPolynomial (Fin k ⊕ Fin q) ℂ →ₐ[ℂ]
      MvPolynomial (Fin k) ℂ :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X gate)
theorem affineGateGraphEvaluation_kills {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (f : MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (hf : f ∈ affineGateGraphIdeal gate) :
    affineGateGraphEvaluation gate f = 0 := by
  rw [affineGateGraphIdeal, Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨coefficients, hcoefficients⟩ := hf
  rw [← hcoefficients, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_mul]
  have hgate : affineGateGraphEvaluation gate
      (MvPolynomial.X (Sum.inr j) -
        MvPolynomial.rename Sum.inl (gate j)) = 0 := by
    unfold affineGateGraphEvaluation
    rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_rename]
    simp [Function.comp_def]
  rw [hgate, mul_zero]
noncomputable def affineGateGraphToInput {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) :
    (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) →ₐ[ℂ]
      MvPolynomial (Fin k) ℂ :=
  Ideal.Quotient.liftₐ (affineGateGraphIdeal gate)
    (affineGateGraphEvaluation gate)
    (affineGateGraphEvaluation_kills gate)
noncomputable def affineGateGraphFromInput {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) :
    MvPolynomial (Fin k) ℂ →ₐ[ℂ]
      (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) :=
  (Ideal.Quotient.mkₐ ℂ (affineGateGraphIdeal gate)).comp
    (MvPolynomial.rename Sum.inl)
theorem affineGateGraph_mk_gate_eq {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) (j : Fin q) :
    Ideal.Quotient.mk (affineGateGraphIdeal gate)
        (MvPolynomial.X (Sum.inr j)) =
      Ideal.Quotient.mk (affineGateGraphIdeal gate)
        (MvPolynomial.rename Sum.inl (gate j)) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩
theorem affineGateGraphToInput_comp_fromInput {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) :
    (affineGateGraphToInput gate).comp (affineGateGraphFromInput gate) =
      AlgHom.id ℂ (MvPolynomial (Fin k) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  change MvPolynomial.aeval (Sum.elim MvPolynomial.X gate)
      (MvPolynomial.rename Sum.inl (MvPolynomial.X i)) =
    MvPolynomial.X i
  simp
theorem affineGateGraphFromInput_comp_toInput {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) :
    (affineGateGraphFromInput gate).comp (affineGateGraphToInput gate) =
      AlgHom.id ℂ
        (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) := by
  apply Ideal.Quotient.algHom_ext
  simp only [AlgHom.comp_assoc, affineGateGraphToInput,
    Ideal.Quotient.liftₐ_comp, AlgHom.id_comp]
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with i | j
  · simp [affineGateGraphFromInput, affineGateGraphEvaluation]
  · simpa [affineGateGraphFromInput, affineGateGraphEvaluation] using
      (affineGateGraph_mk_gate_eq gate j).symm
noncomputable def affineGateGraphInputAlgEquiv {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) :
    (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) ≃ₐ[ℂ]
      MvPolynomial (Fin k) ℂ :=
  AlgEquiv.ofAlgHom (affineGateGraphToInput gate)
    (affineGateGraphFromInput gate)
    (affineGateGraphToInput_comp_fromInput gate)
    (affineGateGraphFromInput_comp_toInput gate)
noncomputable def affineGateRawOutputIdeal {k q : ℕ}
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (target : Fin k → ℂ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin q) ℂ) :=
  Ideal.span (Set.range fun i : Fin k =>
    output i - MvPolynomial.C (target i))
noncomputable def affineGateGraphOutputIdeal {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (target : Fin k → ℂ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) :=
  (affineGateRawOutputIdeal output target).map
    (Ideal.Quotient.mkₐ ℂ (affineGateGraphIdeal gate))
theorem affineGateRawOutputIdeal_map_evaluation {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i) :
    (affineGateRawOutputIdeal output target).map
        (affineGateGraphEvaluation gate).toRingHom =
      homogeneousMapFiberIdeal F target := by
  classical
  rw [affineGateRawOutputIdeal, homogeneousMapFiberIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    simp [houtput i]
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp [houtput i]
theorem affineGateGraphOutputIdeal_map {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i) :
    (affineGateGraphOutputIdeal gate output target).map
        (affineGateGraphInputAlgEquiv gate :
          (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) →+*
            MvPolynomial (Fin k) ℂ) =
      homogeneousMapFiberIdeal F target := by
  unfold affineGateGraphOutputIdeal
  calc
    ((affineGateRawOutputIdeal output target).map
      (Ideal.Quotient.mkₐ ℂ (affineGateGraphIdeal gate))).map
        (affineGateGraphInputAlgEquiv gate :
          (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) →+*
            MvPolynomial (Fin k) ℂ) =
      (affineGateRawOutputIdeal output target).map
        ((affineGateGraphInputAlgEquiv gate :
          (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) →+*
            MvPolynomial (Fin k) ℂ).comp
              (Ideal.Quotient.mk (affineGateGraphIdeal gate))) := by
                exact Ideal.map_map _ _
    _ = homogeneousMapFiberIdeal F target := by
      exact affineGateRawOutputIdeal_map_evaluation
        gate output F target houtput
noncomputable def affineGateGraphClosedFiberAlgEquiv {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i) :
    ((MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ affineGateGraphIdeal gate) ⧸
      affineGateGraphOutputIdeal gate output target) ≃ₐ[ℂ]
        homogeneousMapClosedFiber F target :=
  Ideal.quotientEquivAlg
    (affineGateGraphOutputIdeal gate output target)
    (homogeneousMapFiberIdeal F target)
    (affineGateGraphInputAlgEquiv gate)
    (affineGateGraphOutputIdeal_map gate output F target houtput).symm
noncomputable def affineGateGraphTotalIdeal {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (target : Fin k → ℂ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin q) ℂ) :=
  affineGateGraphIdeal gate ⊔ affineGateRawOutputIdeal output target
noncomputable def affineGateGraphTotalClosedFiberAlgEquiv {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i) :
    (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸
      affineGateGraphTotalIdeal gate output target) ≃ₐ[ℂ]
        homogeneousMapClosedFiber F target := by
  unfold affineGateGraphTotalIdeal
  exact (DoubleQuot.quotQuotEquivQuotSupₐ ℂ
    (affineGateGraphIdeal gate)
    (affineGateRawOutputIdeal output target)).symm.trans
      (affineGateGraphClosedFiberAlgEquiv gate output F target houtput)
noncomputable def affineGatePrefixGraphIdeal {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) (n : ℕ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin q) ℂ) :=
  Ideal.span (Set.range fun j : {j : Fin q // j.val < n} =>
    MvPolynomial.X (Sum.inr (j : Fin q)) -
      MvPolynomial.rename Sum.inl (gate j))
noncomputable def affineGatePrefixEvaluation {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) (n : ℕ) :
    MvPolynomial (Fin k ⊕ Fin q) ℂ →ₐ[ℂ]
      MvPolynomial (Fin k ⊕ Fin q) ℂ :=
  MvPolynomial.aeval (Sum.elim
    (fun i : Fin k => MvPolynomial.X (Sum.inl i))
    (fun j : Fin q => if j.val < n then
      MvPolynomial.rename Sum.inl (gate j) else
      MvPolynomial.X (Sum.inr j)))
theorem affine_gate_prefix_graph_ideal_eq_ker {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) (n : ℕ) :
    affineGatePrefixGraphIdeal gate n =
      RingHom.ker (affineGatePrefixEvaluation gate n).toRingHom := by
  classical
  apply le_antisymm
  · rw [affineGatePrefixGraphIdeal, Ideal.span_le]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    change affineGatePrefixEvaluation gate n
      (MvPolynomial.X (Sum.inr j) -
        MvPolynomial.rename Sum.inl (gate j)) = 0
    unfold affineGatePrefixEvaluation
    rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_rename]
    simp only [Sum.elim_inr, if_pos hj]
    have hinput :
        ((Sum.elim
          (fun i : Fin k => MvPolynomial.X (Sum.inl i))
          (fun j : Fin q => if j.val < n then
            MvPolynomial.rename Sum.inl (gate j) else
            MvPolynomial.X (Sum.inr j))) ∘ Sum.inl) =
          (fun i : Fin k => MvPolynomial.X (Sum.inl i)) := by
      funext i
      rfl
    rw [hinput]
    have hrename :
        MvPolynomial.rename (Sum.inl : Fin k → Fin k ⊕ Fin q) (gate j) =
          MvPolynomial.aeval
            (fun i : Fin k => MvPolynomial.X (Sum.inl i)) (gate j) := by
      simpa [Function.comp_def] using
        DFunLike.congr_fun
          (MvPolynomial.rename_eq_aeval
            (R := ℂ) (Sum.inl : Fin k → Fin k ⊕ Fin q)) (gate j)
    rw [← hrename, sub_self]
  · intro p hp
    let I := affineGatePrefixGraphIdeal gate n
    let φ : MvPolynomial (Fin k ⊕ Fin q) ℂ →+*
        (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ I) :=
      Ideal.Quotient.mk I
    let ψ : MvPolynomial (Fin k ⊕ Fin q) ℂ →+*
        (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ I) :=
      φ.comp (affineGatePrefixEvaluation gate n).toRingHom
    have hC : φ.comp MvPolynomial.C = ψ.comp MvPolynomial.C := by
      ext c
      simp [φ, ψ, affineGatePrefixEvaluation]
    have heq : φ p = ψ p := by
      apply MvPolynomial.hom_congr_vars hC (p₁ := p) (p₂ := p)
        (hp := rfl)
      intro v _ _
      rcases v with i | j
      · simp [φ, ψ, affineGatePrefixEvaluation]
      · by_cases hj : j.val < n
        · have hmem : MvPolynomial.X (Sum.inr j) -
              MvPolynomial.rename Sum.inl (gate j) ∈ I :=
            Ideal.subset_span ⟨⟨j, hj⟩, rfl⟩
          have hquot :
              Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr j)) =
                Ideal.Quotient.mk I
                  (MvPolynomial.rename Sum.inl (gate j)) := by
            rw [← sub_eq_zero, ← map_sub,
              Ideal.Quotient.eq_zero_iff_mem]
            exact hmem
          simpa [φ, ψ, affineGatePrefixEvaluation, hj]
            using hquot
        · simp [φ, ψ, affineGatePrefixEvaluation, hj]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change φ p = 0
    rw [heq]
    change φ (affineGatePrefixEvaluation gate n p) = 0
    change affineGatePrefixEvaluation gate n p = 0 at hp
    rw [hp, map_zero]
theorem affine_gate_prefix_evaluation_eq_graph_of_previous
    {k q : ℕ} (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (n : ℕ) (p : MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (hprevious : ∀ i : Fin q, Sum.inr i ∈ p.vars → i.val < n) :
    affineGatePrefixEvaluation gate n p =
      MvPolynomial.rename Sum.inl (affineGateGraphEvaluation gate p) := by
  classical
  let φ : MvPolynomial (Fin k ⊕ Fin q) ℂ →+*
      MvPolynomial (Fin k ⊕ Fin q) ℂ :=
    (affineGatePrefixEvaluation gate n).toRingHom
  let ψ : MvPolynomial (Fin k ⊕ Fin q) ℂ →+*
      MvPolynomial (Fin k ⊕ Fin q) ℂ :=
    ((MvPolynomial.rename Sum.inl).comp
      (affineGateGraphEvaluation gate)).toRingHom
  have hC : φ.comp MvPolynomial.C = ψ.comp MvPolynomial.C := by
    ext c
    simp [φ, ψ, affineGatePrefixEvaluation,
      affineGateGraphEvaluation]
  change φ p = ψ p
  apply MvPolynomial.hom_congr_vars hC (p₁ := p) (p₂ := p)
    (hp := rfl)
  intro v hv _
  rcases v with i | i
  · simp [φ, ψ, affineGatePrefixEvaluation,
      affineGateGraphEvaluation]
  · have hi : i.val < n := hprevious i hv
    simp [φ, ψ, affineGatePrefixEvaluation,
      affineGateGraphEvaluation, hi]
noncomputable def affineTriangularInstructionPrefixIdeal {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ) (n : ℕ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin q) ℂ) :=
  Ideal.span (Set.range fun j : {j : Fin q // j.val < n} =>
    MvPolynomial.X (Sum.inr (j : Fin q)) - rhs j)
theorem affine_triangular_instruction_prefix_ideal_eq_graph
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (n : ℕ) :
    affineTriangularInstructionPrefixIdeal rhs n =
      affineGatePrefixGraphIdeal gate n := by
  classical
  let I := affineTriangularInstructionPrefixIdeal rhs n
  have hgraph : ∀ m : ℕ, ∀ j : Fin q, j.val = m → j.val < n →
      MvPolynomial.X (Sum.inr j) -
        MvPolynomial.rename Sum.inl (gate j) ∈ I := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hj hjn
      let φ : MvPolynomial (Fin k ⊕ Fin q) ℂ →+*
          (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ I) :=
        Ideal.Quotient.mk I
      let ψ : MvPolynomial (Fin k ⊕ Fin q) ℂ →+*
          (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸ I) :=
        ((Ideal.Quotient.mkₐ ℂ I).comp
          ((MvPolynomial.rename Sum.inl).comp
            (affineGateGraphEvaluation gate))).toRingHom
      have hC : φ.comp MvPolynomial.C = ψ.comp MvPolynomial.C := by
        ext c
        simp [φ, ψ, affineGateGraphEvaluation]
      have hprevious (p : MvPolynomial (Fin k ⊕ Fin q) ℂ)
          (hp : ∀ i : Fin q, Sum.inr i ∈ p.vars → i.val < j.val) :
          φ p = ψ p := by
        apply MvPolynomial.hom_congr_vars hC (p₁ := p) (p₂ := p)
          (hp := rfl)
        intro v hv _
        rcases v with i | i
        · simp [φ, ψ, affineGateGraphEvaluation]
        · have him : i.val < m := hj ▸ hp i hv
          have hin : i.val < n := (hp i hv).trans hjn
          have himem := ih i.val him i rfl hin
          have hieq :
              Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr i)) =
                Ideal.Quotient.mk I
                  (MvPolynomial.rename Sum.inl (gate i)) := by
            rw [← sub_eq_zero, ← map_sub,
              Ideal.Quotient.eq_zero_iff_mem]
            exact himem
          simpa [φ, ψ, affineGateGraphEvaluation] using hieq
      have hprimitive :
          MvPolynomial.X (Sum.inr j) - rhs j ∈ I :=
        Ideal.subset_span ⟨⟨j, hjn⟩, rfl⟩
      have heq :
          Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr j)) =
            Ideal.Quotient.mk I
              (MvPolynomial.rename Sum.inl (gate j)) := by
        calc
          Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr j)) =
              Ideal.Quotient.mk I (rhs j) := by
                rw [← sub_eq_zero, ← map_sub,
                  Ideal.Quotient.eq_zero_iff_mem]
                exact hprimitive
          _ = φ (rhs j) := rfl
          _ = ψ (rhs j) := hprevious (rhs j) (htop j)
          _ = Ideal.Quotient.mk I
                (MvPolynomial.rename Sum.inl (gate j)) := by
                simp [ψ, hgate j]
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      exact heq
  apply le_antisymm
  · rw [affineTriangularInstructionPrefixIdeal, Ideal.span_le,
      affine_gate_prefix_graph_ideal_eq_ker]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    change affineGatePrefixEvaluation gate n
      (MvPolynomial.X (Sum.inr j) - rhs j) = 0
    rw [map_sub,
      affine_gate_prefix_evaluation_eq_graph_of_previous
        gate n (rhs j) (fun i hi => (htop j i hi).trans hj)]
    have hX : affineGatePrefixEvaluation gate n
        (MvPolynomial.X (Sum.inr j)) =
          MvPolynomial.rename Sum.inl (gate j) := by
      simp [affineGatePrefixEvaluation, hj]
    rw [hX, ← hgate j, sub_self]
  · rw [affineGatePrefixGraphIdeal, Ideal.span_le]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    exact hgraph j.val j rfl hj
noncomputable def affineTriangularInstructionIdeal {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin q) ℂ) :=
  Ideal.span (Set.range fun j : Fin q =>
    MvPolynomial.X (Sum.inr j) - rhs j)
theorem affine_triangular_instruction_ideal_eq_graph
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val) :
    affineTriangularInstructionIdeal rhs = affineGateGraphIdeal gate := by
  classical
  have hinstruction :
      affineTriangularInstructionPrefixIdeal rhs q =
        affineTriangularInstructionIdeal rhs := by
    unfold affineTriangularInstructionPrefixIdeal
      affineTriangularInstructionIdeal
    congr 1
    ext p
    simp
  have hgraph : affineGatePrefixGraphIdeal gate q =
      affineGateGraphIdeal gate := by
    unfold affineGatePrefixGraphIdeal affineGateGraphIdeal
    congr 1
    ext p
    simp
  calc
    affineTriangularInstructionIdeal rhs =
        affineTriangularInstructionPrefixIdeal rhs q := hinstruction.symm
    _ = affineGatePrefixGraphIdeal gate q :=
      affine_triangular_instruction_prefix_ideal_eq_graph
        rhs gate hgate htop q
    _ = affineGateGraphIdeal gate := hgraph
noncomputable def affineTriangularInstructionInputAlgEquiv
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val) :
    (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸
      affineTriangularInstructionIdeal rhs) ≃ₐ[ℂ]
        MvPolynomial (Fin k) ℂ :=
  (Ideal.quotientEquivAlgOfEq ℂ
    (affine_triangular_instruction_ideal_eq_graph
      rhs gate hgate htop)).trans
        (affineGateGraphInputAlgEquiv gate)
noncomputable def affineTriangularInstructionOutputClosedFiberAlgEquiv
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i) :
    (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸
      (affineTriangularInstructionIdeal rhs ⊔
        affineGateRawOutputIdeal output target)) ≃ₐ[ℂ]
      homogeneousMapClosedFiber F target := by
  have hideal :
      affineTriangularInstructionIdeal rhs ⊔
          affineGateRawOutputIdeal output target =
        affineGateGraphTotalIdeal gate output target := by
    unfold affineGateGraphTotalIdeal
    rw [affine_triangular_instruction_ideal_eq_graph
      rhs gate hgate htop]
  exact (Ideal.quotientEquivAlgOfEq ℂ hideal).trans
    (affineGateGraphTotalClosedFiberAlgEquiv
      gate output F target houtput)
noncomputable def freeAffineGateReference {k n : ℕ} (r : ℕ) :
    MvPolynomial (Fin k ⊕ Fin n) ℂ :=
  if h : r < n then MvPolynomial.X (Sum.inr ⟨r, h⟩) else 0
noncomputable def freeAffineExtendedForm {k n : ℕ}
    (form : FreeAffineForm (Fin k)) :
    MvPolynomial (Fin k ⊕ Fin n) ℂ :=
  MvPolynomial.C form.constant +
    Finsupp.linearCombination ℂ
      (fun i : Fin k => MvPolynomial.X (Sum.inl i))
      form.inputCoefficients +
    Finsupp.linearCombination ℂ
      (freeAffineGateReference (k := k) (n := n))
      form.gateCoefficients
noncomputable def freeAffineInstructionRhs {k n : ℕ} :
    FreeAffineInstruction (Fin k) → MvPolynomial (Fin k ⊕ Fin n) ℂ
  | .affine form => freeAffineExtendedForm form
  | .mul left right =>
      freeAffineGateReference (k := k) (n := n) left *
        freeAffineGateReference (k := k) (n := n) right
noncomputable def freeAffineCircuitGate
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (j : Fin circuit.program.length) : MvPolynomial (Fin k) ℂ :=
  circuit.values.getD j.val 0
noncomputable def freeAffineCircuitGraphEvaluation
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k)) :
    MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ →ₐ[ℂ]
      MvPolynomial (Fin k) ℂ :=
  MvPolynomial.aeval
    (Sum.elim MvPolynomial.X (freeAffineCircuitGate circuit))
noncomputable def freeAffineCircuitInstructionEquation
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (j : Fin circuit.program.length) :
    MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ :=
  MvPolynomial.X (Sum.inr j) -
    freeAffineInstructionRhs
      (n := circuit.program.length) (circuit.program.get j)
end Standalone_AffineBezout
section Standalone_ParameterBounds
def blockWidth (d : ℕ) : ℕ := 4 * d
def blockCount (n d : ℕ) : ℕ := n / (2 * blockWidth d)
def blockRows (n d : ℕ) : ℕ := blockCount n d * blockWidth d
def blockColumns (n d : ℕ) : ℕ := n - blockRows n d + d
def blockVariables (n d : ℕ) : ℕ := blockRows n d * blockColumns n d
def powerSumParameter (d : ℕ) : ℕ := 2 ^ blockWidth d - 1
def sliceRank (n d : ℕ) : ℕ := blockVariables n d / 4
theorem two_mul_blockRows_le (n d : ℕ) : 2 * blockRows n d ≤ n := by
  simpa [blockRows, blockCount, mul_assoc, mul_comm, mul_left_comm] using
    Nat.div_mul_le_self n (2 * blockWidth d)
theorem three_le_blockCount {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : 3 ≤ blockCount n d := by
  have hden : 0 < 2 * blockWidth d := by
    simp only [blockWidth]
    omega
  unfold blockCount
  apply (Nat.le_div_iff_mul_le hden).2
  omega
theorem three_mul_blockWidth_le_blockRows {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : 3 * blockWidth d ≤ blockRows n d := by
  simpa [blockRows, mul_comm] using
    Nat.mul_le_mul_right (blockWidth d) (three_le_blockCount hd hn)
theorem degree_le_blockRows {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : d ≤ blockRows n d := by
  have hrows := three_mul_blockWidth_le_blockRows hd hn
  simp only [blockWidth] at hrows
  omega
theorem degree_le_blockColumns (n d : ℕ) : d ≤ blockColumns n d := by
  have hrows := two_mul_blockRows_le n d
  unfold blockColumns
  omega
theorem block_size_identity (n d : ℕ) :
    blockRows n d + blockColumns n d - d = n := by
  have hrows := two_mul_blockRows_le n d
  unfold blockColumns
  omega
end Standalone_ParameterBounds
section Standalone_Asymptotics
end Standalone_Asymptotics
section Standalone_BlockPermanent
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable def rectangularPermanent
    {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R]
    (A : Matrix α β R) : R :=
  ∑ matching : α ≃ β, ∏ row : α, A row (matching row)
noncomputable def sourceBlockMatrix
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R) :
    Matrix (Fin r ⊕ Fin (s - d)) (Fin s ⊕ Fin (r - d)) R :=
  Matrix.fromBlocks X U
    (fun (_ : Fin (s - d)) (_ : Fin s) => 1)
    (0 : Matrix (Fin (s - d)) (Fin (r - d)) R)
@[simp] theorem sourceBlockMatrix_apply₁₁
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (row : Fin r) (column : Fin s) :
    sourceBlockMatrix r s d X U (.inl row) (.inl column) = X row column := by
  rfl
@[simp] theorem sourceBlockMatrix_apply₁₂
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (row : Fin r) (column : Fin (r - d)) :
    sourceBlockMatrix r s d X U (.inl row) (.inr column) = U row column := by
  rfl
@[simp] theorem sourceBlockMatrix_apply₂₁
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (row : Fin (s - d)) (column : Fin s) :
    sourceBlockMatrix r s d X U (.inr row) (.inl column) = 1 := by
  rfl
@[simp] theorem sourceBlockMatrix_apply₂₂
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (row : Fin (s - d)) (column : Fin (r - d)) :
    sourceBlockMatrix r s d X U (.inr row) (.inr column) = 0 := by
  rfl
noncomputable def sourceBlockMatchingWeight
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d))) : R :=
  ∏ row, sourceBlockMatrix r s d X U row (matching row)
noncomputable def sourceBlockAlpha
    {R : Type*} [CommSemiring R] (r d : ℕ)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (I : Finset (Fin r)) : R :=
  ∑ matching : {row : Fin r // row ∉ I} ≃ Fin (r - d),
    ∏ row : {row : Fin r // row ∉ I}, U row.val (matching row)
noncomputable def sourceBlockMinor
    {R : Type*} [CommSemiring R] (r s : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (I : Finset (Fin r)) (J : Finset (Fin s)) : R :=
  ∑ matching : I ≃ J,
    ∏ row : I, X row.val (matching row).val
noncomputable def sourceBlockMatchingExpansion
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R) : R :=
  ((s - d).factorial : R) *
    ∑ I ∈ (Finset.univ : Finset (Fin r)).powersetCard d,
      ∑ J ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
        sourceBlockAlpha r d U I * sourceBlockMinor r s X I J
noncomputable def sourceBlockMatchingOf
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J}) :
    (Fin r ⊕ Fin (s - d)) ≃ (Fin s ⊕ Fin (r - d)) :=
  calc
    Fin r ⊕ Fin (s - d) ≃
        (I ⊕ {row : Fin r // row ∉ I}) ⊕ Fin (s - d) :=
      (Equiv.sumCompl (fun row : Fin r => row ∈ I)).symm.sumCongr
        (Equiv.refl (Fin (s - d)))
    _ ≃ (J ⊕ Fin (r - d)) ⊕ {column : Fin s // column ∉ J} :=
      (variableMatching.sumCongr constantMatching).sumCongr onesMatching
    _ ≃ J ⊕ (Fin (r - d) ⊕ {column : Fin s // column ∉ J}) :=
      Equiv.sumAssoc _ _ _
    _ ≃ J ⊕ ({column : Fin s // column ∉ J} ⊕ Fin (r - d)) :=
      (Equiv.refl J).sumCongr (Equiv.sumComm _ _)
    _ ≃ (J ⊕ {column : Fin s // column ∉ J}) ⊕ Fin (r - d) :=
      (Equiv.sumAssoc _ _ _).symm
    _ ≃ Fin s ⊕ Fin (r - d) :=
      (Equiv.sumCompl (fun column : Fin s => column ∈ J)).sumCongr
        (Equiv.refl (Fin (r - d)))
@[simp] theorem sourceBlockMatchingOf_apply_selected
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J})
    (row : I) :
    sourceBlockMatchingOf r s d I J
        variableMatching constantMatching onesMatching (.inl row.val) =
      .inl (variableMatching row).val := by
  simp [sourceBlockMatchingOf, row.property]
@[simp] theorem sourceBlockMatchingOf_apply_complement
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J})
    (row : {row : Fin r // row ∉ I}) :
    sourceBlockMatchingOf r s d I J
        variableMatching constantMatching onesMatching (.inl row.val) =
      .inr (constantMatching row) := by
  simp [sourceBlockMatchingOf, row.property]
@[simp] theorem sourceBlockMatchingOf_apply_lower
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J})
    (row : Fin (s - d)) :
    sourceBlockMatchingOf r s d I J
        variableMatching constantMatching onesMatching (.inr row) =
      .inl (onesMatching row).val := by
  simp [sourceBlockMatchingOf]
noncomputable def sourceBlockSelectedRows
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d))) : Finset (Fin r) :=
  Finset.univ.filter
    (fun row => ∃ column : Fin s, matching (.inl row) = .inl column)
noncomputable def sourceBlockSelectedColumns
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d))) : Finset (Fin s) :=
  Finset.univ.filter
    (fun column => ∃ row : Fin r, matching (.inl row) = .inl column)
@[simp] theorem sourceBlock_mem_selectedRows
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (row : Fin r) :
    row ∈ sourceBlockSelectedRows r s d matching ↔
      ∃ column : Fin s, matching (.inl row) = .inl column := by
  simp [sourceBlockSelectedRows]
@[simp] theorem sourceBlock_mem_selectedColumns
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (column : Fin s) :
    column ∈ sourceBlockSelectedColumns r s d matching ↔
      ∃ row : Fin r, matching (.inl row) = .inl column := by
  simp [sourceBlockSelectedColumns]
theorem sourceBlockMatchingOf_isValid
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J}) :
    ∀ row : Fin (s - d), ∃ column : Fin s,
      sourceBlockMatchingOf r s d I J
        variableMatching constantMatching onesMatching
          (.inr row) = .inl column := by
  intro row
  exact ⟨(onesMatching row).val,
    sourceBlockMatchingOf_apply_lower r s d I J
      variableMatching constantMatching onesMatching row⟩
noncomputable def sourceBlockVariableFunction
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d))) :
    sourceBlockSelectedRows r s d matching →
      sourceBlockSelectedColumns r s d matching := by
  intro row
  have hcolumn : ∃ column : Fin s,
      matching (.inl row.val) = .inl column :=
    (sourceBlock_mem_selectedRows r s d matching row.val).mp row.property
  refine ⟨Classical.choose hcolumn, ?_⟩
  exact (sourceBlock_mem_selectedColumns r s d matching _).mpr
    ⟨row.val, Classical.choose_spec hcolumn⟩
theorem sourceBlockVariableFunction_spec
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (row : sourceBlockSelectedRows r s d matching) :
    matching (.inl row.val) =
      .inl (sourceBlockVariableFunction r s d matching row).val := by
  unfold sourceBlockVariableFunction
  exact Classical.choose_spec
    ((sourceBlock_mem_selectedRows r s d matching row.val).mp row.property)
theorem sourceBlockVariableFunction_bijective
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d))) :
    Function.Bijective (sourceBlockVariableFunction r s d matching) := by
  constructor
  · intro row₁ row₂ heq
    apply Subtype.ext
    have hmatch :
        matching (.inl row₁.val) = matching (.inl row₂.val) := by
      calc
        matching (.inl row₁.val) =
            .inl (sourceBlockVariableFunction r s d matching row₁).val :=
          sourceBlockVariableFunction_spec r s d matching row₁
        _ = .inl (sourceBlockVariableFunction r s d matching row₂).val :=
          congrArg Sum.inl (congrArg Subtype.val heq)
        _ = matching (.inl row₂.val) :=
          (sourceBlockVariableFunction_spec r s d matching row₂).symm
    exact Sum.inl.inj (matching.injective hmatch)
  · intro column
    obtain ⟨row, hrow⟩ :=
      (sourceBlock_mem_selectedColumns r s d matching column.val).mp
        column.property
    have hselected : row ∈ sourceBlockSelectedRows r s d matching :=
      (sourceBlock_mem_selectedRows r s d matching row).mpr
        ⟨column.val, hrow⟩
    refine ⟨⟨row, hselected⟩, ?_⟩
    apply Subtype.ext
    exact Sum.inl.inj
      ((sourceBlockVariableFunction_spec r s d matching
        ⟨row, hselected⟩).symm.trans hrow)
noncomputable def sourceBlockVariableMatchingOf
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d))) :
    sourceBlockSelectedRows r s d matching ≃
      sourceBlockSelectedColumns r s d matching :=
  Equiv.ofBijective (sourceBlockVariableFunction r s d matching)
    (sourceBlockVariableFunction_bijective r s d matching)
theorem sourceBlockVariableMatchingOf_spec
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (row : sourceBlockSelectedRows r s d matching) :
    matching (.inl row.val) =
      .inl (sourceBlockVariableMatchingOf r s d matching row).val := by
  exact sourceBlockVariableFunction_spec r s d matching row
theorem sourceBlockConstant_exists
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (row : {row : Fin r //
      row ∉ sourceBlockSelectedRows r s d matching}) :
    ∃ column : Fin (r - d), matching (.inl row.val) = .inr column := by
  cases hcolumn : matching (.inl row.val) with
  | inl column =>
      exfalso
      exact row.property
        ((sourceBlock_mem_selectedRows r s d matching row.val).mpr
          ⟨column, hcolumn⟩)
  | inr column =>
      exact ⟨column, rfl⟩
noncomputable def sourceBlockConstantFunction
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (row : {row : Fin r //
      row ∉ sourceBlockSelectedRows r s d matching}) : Fin (r - d) :=
  Classical.choose (sourceBlockConstant_exists r s d matching row)
theorem sourceBlockConstantFunction_spec
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (row : {row : Fin r //
      row ∉ sourceBlockSelectedRows r s d matching}) :
    matching (.inl row.val) =
      .inr (sourceBlockConstantFunction r s d matching row) :=
  Classical.choose_spec (sourceBlockConstant_exists r s d matching row)
theorem sourceBlockConstantFunction_bijective
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    Function.Bijective (sourceBlockConstantFunction r s d matching) := by
  constructor
  · intro row₁ row₂ heq
    apply Subtype.ext
    have hmatch :
        matching (.inl row₁.val) = matching (.inl row₂.val) := by
      calc
        matching (.inl row₁.val) =
            .inr (sourceBlockConstantFunction r s d matching row₁) :=
          sourceBlockConstantFunction_spec r s d matching row₁
        _ = .inr (sourceBlockConstantFunction r s d matching row₂) :=
          congrArg Sum.inr heq
        _ = matching (.inl row₂.val) :=
          (sourceBlockConstantFunction_spec r s d matching row₂).symm
    exact Sum.inl.inj (matching.injective hmatch)
  · intro column
    have hpre := matching.apply_symm_apply (.inr column)
    cases hrow : matching.symm (.inr column) with
    | inl row =>
        have hhit : matching (.inl row) = .inr column := by
          simpa [hrow] using hpre
        have hnot : row ∉ sourceBlockSelectedRows r s d matching := by
          intro hselected
          obtain ⟨left, hleft⟩ :=
            (sourceBlock_mem_selectedRows r s d matching row).mp hselected
          rw [hhit] at hleft
          cases hleft
        refine ⟨⟨row, hnot⟩, ?_⟩
        exact Sum.inr.inj
          ((sourceBlockConstantFunction_spec r s d matching
            ⟨row, hnot⟩).symm.trans hhit)
    | inr row =>
        have hhit : matching (.inr row) = .inr column := by
          simpa [hrow] using hpre
        obtain ⟨left, hleft⟩ := hvalid row
        rw [hleft] at hhit
        cases hhit
noncomputable def sourceBlockConstantMatchingOf
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    {row : Fin r // row ∉ sourceBlockSelectedRows r s d matching} ≃
      Fin (r - d) :=
  Equiv.ofBijective (sourceBlockConstantFunction r s d matching)
    (sourceBlockConstantFunction_bijective r s d matching hvalid)
theorem sourceBlockConstantMatchingOf_spec
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column)
    (row : {row : Fin r //
      row ∉ sourceBlockSelectedRows r s d matching}) :
    matching (.inl row.val) =
      .inr (sourceBlockConstantMatchingOf r s d matching hvalid row) := by
  exact sourceBlockConstantFunction_spec r s d matching row
noncomputable def sourceBlockOnesFunction
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    Fin (s - d) →
      {column : Fin s //
        column ∉ sourceBlockSelectedColumns r s d matching} := by
  intro row
  refine ⟨Classical.choose (hvalid row), ?_⟩
  intro hselected
  obtain ⟨upper, hupper⟩ :=
    (sourceBlock_mem_selectedColumns r s d matching
      (Classical.choose (hvalid row))).mp hselected
  have hconflict :
      (Sum.inl upper : Fin r ⊕ Fin (s - d)) = .inr row :=
    matching.injective (hupper.trans (Classical.choose_spec (hvalid row)).symm)
  cases hconflict
theorem sourceBlockOnesFunction_spec
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column)
    (row : Fin (s - d)) :
    matching (.inr row) =
      .inl (sourceBlockOnesFunction r s d matching hvalid row).val := by
  unfold sourceBlockOnesFunction
  exact Classical.choose_spec (hvalid row)
theorem sourceBlockOnesFunction_bijective
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    Function.Bijective (sourceBlockOnesFunction r s d matching hvalid) := by
  constructor
  · intro row₁ row₂ heq
    have hmatch : matching (.inr row₁) = matching (.inr row₂) := by
      calc
        matching (.inr row₁) =
            .inl (sourceBlockOnesFunction r s d matching hvalid row₁).val :=
          sourceBlockOnesFunction_spec r s d matching hvalid row₁
        _ = .inl (sourceBlockOnesFunction r s d matching hvalid row₂).val :=
          congrArg Sum.inl (congrArg Subtype.val heq)
        _ = matching (.inr row₂) :=
          (sourceBlockOnesFunction_spec r s d matching hvalid row₂).symm
    exact Sum.inr.inj (matching.injective hmatch)
  · intro column
    have hpre := matching.apply_symm_apply (.inl column.val)
    cases hrow : matching.symm (.inl column.val) with
    | inl row =>
        have hhit : matching (.inl row) = .inl column.val := by
          simpa [hrow] using hpre
        exact (column.property
          ((sourceBlock_mem_selectedColumns r s d matching column.val).mpr
            ⟨row, hhit⟩)).elim
    | inr row =>
        have hhit : matching (.inr row) = .inl column.val := by
          simpa [hrow] using hpre
        refine ⟨row, ?_⟩
        apply Subtype.ext
        exact Sum.inl.inj
          ((sourceBlockOnesFunction_spec r s d matching hvalid row).symm.trans
            hhit)
noncomputable def sourceBlockOnesMatchingOf
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    Fin (s - d) ≃
      {column : Fin s //
        column ∉ sourceBlockSelectedColumns r s d matching} :=
  Equiv.ofBijective (sourceBlockOnesFunction r s d matching hvalid)
    (sourceBlockOnesFunction_bijective r s d matching hvalid)
theorem sourceBlockOnesMatchingOf_spec
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column)
    (row : Fin (s - d)) :
    matching (.inr row) =
      .inl (sourceBlockOnesMatchingOf r s d matching hvalid row).val := by
  exact sourceBlockOnesFunction_spec r s d matching hvalid row
theorem sourceBlockMatchingOf_recovered
    (r s d : ℕ)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    sourceBlockMatchingOf r s d
      (sourceBlockSelectedRows r s d matching)
      (sourceBlockSelectedColumns r s d matching)
      (sourceBlockVariableMatchingOf r s d matching)
      (sourceBlockConstantMatchingOf r s d matching hvalid)
      (sourceBlockOnesMatchingOf r s d matching hvalid) = matching := by
  apply Equiv.ext
  intro row
  cases row with
  | inl upper =>
      by_cases hupper : upper ∈ sourceBlockSelectedRows r s d matching
      · exact
          (sourceBlockMatchingOf_apply_selected r s d
            (sourceBlockSelectedRows r s d matching)
            (sourceBlockSelectedColumns r s d matching)
            (sourceBlockVariableMatchingOf r s d matching)
            (sourceBlockConstantMatchingOf r s d matching hvalid)
            (sourceBlockOnesMatchingOf r s d matching hvalid)
            ⟨upper, hupper⟩).trans
          (sourceBlockVariableMatchingOf_spec r s d matching
            ⟨upper, hupper⟩).symm
      · exact
          (sourceBlockMatchingOf_apply_complement r s d
            (sourceBlockSelectedRows r s d matching)
            (sourceBlockSelectedColumns r s d matching)
            (sourceBlockVariableMatchingOf r s d matching)
            (sourceBlockConstantMatchingOf r s d matching hvalid)
            (sourceBlockOnesMatchingOf r s d matching hvalid)
            ⟨upper, hupper⟩).trans
          (sourceBlockConstantMatchingOf_spec r s d matching hvalid
            ⟨upper, hupper⟩).symm
  | inr lower =>
      exact
        (sourceBlockMatchingOf_apply_lower r s d
          (sourceBlockSelectedRows r s d matching)
          (sourceBlockSelectedColumns r s d matching)
          (sourceBlockVariableMatchingOf r s d matching)
          (sourceBlockConstantMatchingOf r s d matching hvalid)
          (sourceBlockOnesMatchingOf r s d matching hvalid) lower).trans
        (sourceBlockOnesMatchingOf_spec r s d matching hvalid lower).symm
theorem sourceBlockSelectedRows_card_of_valid
    (r s d : ℕ) (hr : d ≤ r)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    (sourceBlockSelectedRows r s d matching).card = d := by
  have hconstant := Fintype.card_congr
    (sourceBlockConstantMatchingOf r s d matching hvalid)
  rw [Fintype.card_subtype_compl
    (fun row : Fin r => row ∈ sourceBlockSelectedRows r s d matching)]
    at hconstant
  simp only [Fintype.card_fin, Fintype.card_coe] at hconstant
  have hbound : (sourceBlockSelectedRows r s d matching).card ≤ r := by
    simpa using Finset.card_le_univ
      (sourceBlockSelectedRows r s d matching)
  omega
theorem sourceBlockSelectedColumns_card_of_valid
    (r s d : ℕ) (hr : d ≤ r)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hvalid : ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    (sourceBlockSelectedColumns r s d matching).card = d := by
  have hvariable := Fintype.card_congr
    (sourceBlockVariableMatchingOf r s d matching)
  simp only [Fintype.card_coe] at hvariable
  have hrows := sourceBlockSelectedRows_card_of_valid r s d hr matching hvalid
  omega
@[simp] theorem sourceBlockSelectedRows_matchingOf
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J}) :
    sourceBlockSelectedRows r s d
      (sourceBlockMatchingOf r s d I J
        variableMatching constantMatching onesMatching) = I := by
  ext row
  simp only [sourceBlockSelectedRows, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨column, hcolumn⟩
    by_contra hrow
    have hright := sourceBlockMatchingOf_apply_complement r s d I J
      variableMatching constantMatching onesMatching ⟨row, hrow⟩
    rw [hright] at hcolumn
    cases hcolumn
  · intro hrow
    refine ⟨(variableMatching ⟨row, hrow⟩).val, ?_⟩
    exact sourceBlockMatchingOf_apply_selected r s d I J
      variableMatching constantMatching onesMatching ⟨row, hrow⟩
@[simp] theorem sourceBlockSelectedColumns_matchingOf
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J}) :
    sourceBlockSelectedColumns r s d
      (sourceBlockMatchingOf r s d I J
        variableMatching constantMatching onesMatching) = J := by
  ext column
  simp only [sourceBlockSelectedColumns, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨row, hcolumn⟩
    have hrow : row ∈ I := by
      by_contra hn
      have hright := sourceBlockMatchingOf_apply_complement r s d I J
        variableMatching constantMatching onesMatching ⟨row, hn⟩
      rw [hright] at hcolumn
      cases hcolumn
    have hleft := sourceBlockMatchingOf_apply_selected r s d I J
      variableMatching constantMatching onesMatching ⟨row, hrow⟩
    have heq : (variableMatching ⟨row, hrow⟩).val = column :=
      Sum.inl_injective (hleft.symm.trans hcolumn)
    rw [← heq]
    exact (variableMatching ⟨row, hrow⟩).property
  · intro hcolumn
    let row : I := variableMatching.symm ⟨column, hcolumn⟩
    refine ⟨row.val, ?_⟩
    simpa only [row, Equiv.apply_symm_apply] using
      sourceBlockMatchingOf_apply_selected r s d I J
        variableMatching constantMatching onesMatching row
theorem sourceBlockMatchingOf_injective
    (r s d : ℕ) (I : Finset (Fin r)) (J : Finset (Fin s)) :
    Function.Injective
      (fun data :
        (I ≃ J) ×
          ({row : Fin r // row ∉ I} ≃ Fin (r - d)) ×
          (Fin (s - d) ≃ {column : Fin s // column ∉ J}) =>
        sourceBlockMatchingOf r s d I J data.1 data.2.1 data.2.2) := by
  rintro ⟨variable₁, constant₁, ones₁⟩
    ⟨variable₂, constant₂, ones₂⟩ hmatching
  have hvariable : variable₁ = variable₂ := by
    apply Equiv.ext
    intro row
    apply Subtype.ext
    simpa using congrArg
      (fun matching => matching (.inl row.val)) hmatching
  have hconstant : constant₁ = constant₂ := by
    apply Equiv.ext
    intro row
    simpa using congrArg
      (fun matching => matching (.inl row.val)) hmatching
  have hones : ones₁ = ones₂ := by
    apply Equiv.ext
    intro row
    apply Subtype.ext
    simpa using congrArg
      (fun matching => matching (.inr row)) hmatching
  simp [hvariable, hconstant, hones]
abbrev SourceBlockMatchingData (r s d : ℕ) : Type :=
  Σ I : ((Finset.univ : Finset (Fin r)).powersetCard d),
    Σ J : ((Finset.univ : Finset (Fin s)).powersetCard d),
      (I.val ≃ J.val) ×
        ({row : Fin r // row ∉ I.val} ≃ Fin (r - d)) ×
        (Fin (s - d) ≃ {column : Fin s // column ∉ J.val})
noncomputable def sourceBlockDataMatching
    (r s d : ℕ) (data : SourceBlockMatchingData r s d) :
    (Fin r ⊕ Fin (s - d)) ≃ (Fin s ⊕ Fin (r - d)) :=
  sourceBlockMatchingOf r s d data.1.val data.2.1.val
    data.2.2.1 data.2.2.2.1 data.2.2.2.2
@[simp] theorem sourceBlockSelectedRows_dataMatching
    (r s d : ℕ) (data : SourceBlockMatchingData r s d) :
    sourceBlockSelectedRows r s d (sourceBlockDataMatching r s d data) =
      data.1.val := by
  exact sourceBlockSelectedRows_matchingOf r s d data.1.val data.2.1.val
    data.2.2.1 data.2.2.2.1 data.2.2.2.2
@[simp] theorem sourceBlockSelectedColumns_dataMatching
    (r s d : ℕ) (data : SourceBlockMatchingData r s d) :
    sourceBlockSelectedColumns r s d (sourceBlockDataMatching r s d data) =
      data.2.1.val := by
  exact sourceBlockSelectedColumns_matchingOf r s d data.1.val data.2.1.val
    data.2.2.1 data.2.2.2.1 data.2.2.2.2
theorem sourceBlockDataMatching_injective
    (r s d : ℕ) :
    Function.Injective (sourceBlockDataMatching r s d) := by
  intro data₁ data₂ hmatching
  have hrows : data₁.1 = data₂.1 := by
    apply Subtype.ext
    exact
      (sourceBlockSelectedRows_dataMatching r s d data₁).symm.trans
      ((congrArg (sourceBlockSelectedRows r s d) hmatching).trans
        (sourceBlockSelectedRows_dataMatching r s d data₂))
  have hcolumns : data₁.2.1 = data₂.2.1 := by
    apply Subtype.ext
    exact
      (sourceBlockSelectedColumns_dataMatching r s d data₁).symm.trans
      ((congrArg (sourceBlockSelectedColumns r s d) hmatching).trans
        (sourceBlockSelectedColumns_dataMatching r s d data₂))
  rcases data₁ with ⟨I, ⟨J, components₁⟩⟩
  rcases data₂ with ⟨I', ⟨J', components₂⟩⟩
  change I = I' at hrows
  change J = J' at hcolumns
  subst I'
  subst J'
  change
    sourceBlockMatchingOf r s d I.val J.val
        components₁.1 components₁.2.1 components₁.2.2 =
      sourceBlockMatchingOf r s d I.val J.val
        components₂.1 components₂.2.1 components₂.2.2 at hmatching
  have hdata := sourceBlockMatchingOf_injective r s d I.val J.val hmatching
  exact congrArg
    (fun components :
      (I.val ≃ J.val) ×
        ({row : Fin r // row ∉ I.val} ≃ Fin (r - d)) ×
        (Fin (s - d) ≃ {column : Fin s // column ∉ J.val}) =>
      (⟨I, ⟨J, components⟩⟩ : SourceBlockMatchingData r s d))
    hdata
abbrev SourceBlockValidMatching (r s d : ℕ) : Type :=
  {matching :
    (Fin r ⊕ Fin (s - d)) ≃ (Fin s ⊕ Fin (r - d)) //
      ∀ row : Fin (s - d),
        ∃ column : Fin s, matching (.inr row) = .inl column}
noncomputable def sourceBlockDataValidMatching
    (r s d : ℕ) (data : SourceBlockMatchingData r s d) :
    SourceBlockValidMatching r s d :=
  ⟨sourceBlockDataMatching r s d data,
    sourceBlockMatchingOf_isValid r s d data.1.val data.2.1.val
      data.2.2.1 data.2.2.2.1 data.2.2.2.2⟩
theorem sourceBlockDataValidMatching_bijective
    (r s d : ℕ) (hr : d ≤ r) :
    Function.Bijective (sourceBlockDataValidMatching r s d) := by
  constructor
  · intro data₁ data₂ hdata
    apply sourceBlockDataMatching_injective r s d
    exact congrArg Subtype.val hdata
  · rintro ⟨matching, hvalid⟩
    let selectedRows :
        ((Finset.univ : Finset (Fin r)).powersetCard d) :=
      ⟨sourceBlockSelectedRows r s d matching, by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _,
          sourceBlockSelectedRows_card_of_valid r s d hr matching hvalid⟩⟩
    let selectedColumns :
        ((Finset.univ : Finset (Fin s)).powersetCard d) :=
      ⟨sourceBlockSelectedColumns r s d matching, by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _,
          sourceBlockSelectedColumns_card_of_valid r s d hr matching hvalid⟩⟩
    refine ⟨⟨selectedRows, ⟨selectedColumns,
      sourceBlockVariableMatchingOf r s d matching,
      sourceBlockConstantMatchingOf r s d matching hvalid,
      sourceBlockOnesMatchingOf r s d matching hvalid⟩⟩, ?_⟩
    apply Subtype.ext
    exact sourceBlockMatchingOf_recovered r s d matching hvalid
noncomputable def sourceBlockMatchingDataEquiv
    (r s d : ℕ) (hr : d ≤ r) :
    SourceBlockMatchingData r s d ≃ SourceBlockValidMatching r s d :=
  Equiv.ofBijective (sourceBlockDataValidMatching r s d)
    (sourceBlockDataValidMatching_bijective r s d hr)
theorem sourceBlock_column_complement_card
    (s d : ℕ) (J : Finset (Fin s)) (hJ : J.card = d) :
    Fintype.card {column : Fin s // column ∉ J} = s - d := by
  rw [Fintype.card_subtype_compl (fun column : Fin s => column ∈ J)]
  simp [Fintype.card_coe, hJ]
noncomputable def sourceBlockOnesEquiv
    (s d : ℕ) (J : Finset (Fin s)) (hJ : J.card = d) :
    Fin (s - d) ≃ {column : Fin s // column ∉ J} :=
  Fintype.equivOfCardEq (by
    simp [sourceBlock_column_complement_card s d J hJ])
noncomputable def sourceBlockGluedFibre
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (I : Finset (Fin r)) (J : Finset (Fin s)) : R :=
  ∑ variableMatching : I ≃ J,
    ∑ constantMatching :
      {row : Fin r // row ∉ I} ≃ Fin (r - d),
      ∑ onesMatching :
        Fin (s - d) ≃ {column : Fin s // column ∉ J},
        ∏ row, sourceBlockMatrix r s d X U row
          (sourceBlockMatchingOf r s d I J
            variableMatching constantMatching onesMatching row)
end Standalone_BlockPermanent
section Standalone_CircuitDAG
inductive CircuitInstructionReference {ι : Type} :
    Instruction ι → ℕ → Prop where
  | add_left (left right : ℕ) :
      CircuitInstructionReference (.add left right) left
  | add_right (left right : ℕ) :
      CircuitInstructionReference (.add left right) right
  | sub_left (left right : ℕ) :
      CircuitInstructionReference (.sub left right) left
  | sub_right (left right : ℕ) :
      CircuitInstructionReference (.sub left right) right
  | mul_left (left right : ℕ) :
      CircuitInstructionReference (.mul left right) left
  | mul_right (left right : ℕ) :
      CircuitInstructionReference (.mul left right) right
end Standalone_CircuitDAG
section Standalone_Combinatorics
open scoped BigOperators
end Standalone_Combinatorics
section Standalone_SquareZero
open scoped BigOperators
noncomputable def squareZeroIdeal (r : ℕ) : Ideal (MvPolynomial (Fin r) ℂ) :=
  Ideal.span (Set.range fun i : Fin r => (MvPolynomial.X i) ^ 2)
abbrev SquareZeroAlgebra (r : ℕ) :=
  MvPolynomial (Fin r) ℂ ⧸ squareZeroIdeal r
noncomputable def squareZeroVariable (r : ℕ) (i : Fin r) : SquareZeroAlgebra r :=
  Ideal.Quotient.mk (squareZeroIdeal r) (MvPolynomial.X i)
@[simp] theorem squareZeroVariable_sq (r : ℕ) (i : Fin r) :
    squareZeroVariable r i ^ 2 = 0 := by
  change (Ideal.Quotient.mk (squareZeroIdeal r) (MvPolynomial.X i)) ^ 2 = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩
noncomputable def squareZeroBlockSum (r : ℕ) (block : Finset (Fin r)) :
    SquareZeroAlgebra r :=
  ∑ i ∈ block, squareZeroVariable r i
end Standalone_SquareZero
section Standalone_Subtree
open scoped BigOperators
inductive BlockTree (ι : Type*) where
  | leaf (label : ι)
  | branch (left right : BlockTree ι)
namespace BlockTree
@[simp] def leaves {ι : Type*} [DecidableEq ι] : BlockTree ι → Finset ι
  | .leaf i => {i}
  | .branch left right => leaves left ∪ leaves right
@[simp] def leafList {ι : Type*} : BlockTree ι → List ι
  | .leaf i => [i]
  | .branch left right => leafList left ++ leafList right
theorem mem_leaves_iff {ι : Type*} [DecidableEq ι]
    (tree : BlockTree ι) (i : ι) :
    i ∈ tree.leaves ↔ i ∈ tree.leafList := by
  induction tree with
  | leaf label => simp
  | branch left right left_ih right_ih =>
    simp [left_ih, right_ih]
end BlockTree
@[simp] noncomputable def subtreeCoefficient {ι : Type*} [DecidableEq ι]
    (lam : ℂ) : BlockTree ι → ι → ℂ
  | .leaf label, i => if i = label then 1 else 0
  | .branch left right, i =>
      (∑ j ∈ left.leaves, subtreeCoefficient lam left j) *
          subtreeCoefficient lam right i +
        lam * (∑ j ∈ right.leaves, subtreeCoefficient lam right j) *
          subtreeCoefficient lam left i
noncomputable def subtreeCoefficientTotal {ι : Type*} [DecidableEq ι]
    (lam : ℂ) (tree : BlockTree ι) : ℂ :=
  ∑ i ∈ tree.leaves, subtreeCoefficient lam tree i
@[simp] theorem subtreeCoefficientTotal_leaf {ι : Type*} [DecidableEq ι]
    (lam : ℂ) (label : ι) :
    subtreeCoefficientTotal lam (.leaf label) = 1 := by
  simp [subtreeCoefficientTotal]
noncomputable def subtreeFormProduct
    {R ι : Type*} [CommSemiring R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (lam : ℂ) : BlockTree ι → R
  | .leaf i => y i ^ (t - d)
  | .branch left right =>
      subtreeFormProduct y t d lam left *
        subtreeFormProduct y t d lam right *
          ((∑ i ∈ left.leaves, y i) ^ d +
            algebraMap ℂ R lam * (∑ i ∈ right.leaves, y i) ^ d)
@[simp] theorem subtreeFormProduct_branch
    {R ι : Type*} [CommSemiring R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (lam : ℂ) (left right : BlockTree ι) :
    subtreeFormProduct y t d lam (.branch left right) =
      subtreeFormProduct y t d lam left *
        subtreeFormProduct y t d lam right *
          ((∑ i ∈ left.leaves, y i) ^ d +
            algebraMap ℂ R lam * (∑ i ∈ right.leaves, y i) ^ d) := rfl
noncomputable def subtreeLinearFormProduct
    {R ι : Type*} [CommRing R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (ζ : ℂ) : BlockTree ι → R
  | .leaf i => y i ^ (t - d)
  | .branch left right =>
      subtreeLinearFormProduct y t d ζ left *
        subtreeLinearFormProduct y t d ζ right *
          ∏ j ∈ Finset.range d,
            ((∑ i ∈ left.leaves, y i) +
              algebraMap ℂ R (2 * ζ ^ j) *
                (∑ i ∈ right.leaves, y i))
end Standalone_Subtree
section Standalone_Coefficients
open scoped BigOperators
noncomputable def squareFreeExponent {ι : Type*} (rows : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator rows (fun _ _ => 1)
@[simp] theorem squareFreeExponent_apply {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (i : ι) :
    squareFreeExponent rows i = if i ∈ rows then 1 else 0 := by
  classical
  simp [squareFreeExponent, Finsupp.indicator_apply]
@[simp] theorem squareFreeExponent_support {ι : Type*} (rows : Finset ι) :
    (squareFreeExponent rows).support = rows := by
  classical
  ext i
  simp [Finsupp.mem_support_iff, squareFreeExponent_apply]
theorem eq_squareFreeExponent_support_of_le {ι : Type*}
    (rows : Finset ι) (exponent : ι →₀ ℕ)
    (hle : exponent ≤ squareFreeExponent rows) :
    exponent = squareFreeExponent exponent.support := by
  classical
  ext i
  by_cases hi : exponent i = 0
  · simp [squareFreeExponent_apply, Finsupp.mem_support_iff, hi]
  · have hpos : 1 ≤ exponent i := Nat.one_le_iff_ne_zero.mpr hi
    have hupper : exponent i ≤ squareFreeExponent rows i := hle i
    have hbound : squareFreeExponent rows i ≤ 1 := by
      rw [squareFreeExponent_apply]
      split <;> omega
    have hone : exponent i = 1 := by omega
    simp [squareFreeExponent_apply, Finsupp.mem_support_iff, hone]
noncomputable def squareFreeMonomial {ι : Type*}
    (rows : Finset ι) : MvPolynomial ι ℂ :=
  ∏ i ∈ rows, MvPolynomial.X i
theorem coeff_squareFree_variable_sq_mul {ι : Type*}
    (rows : Finset ι) (i : ι) (p : MvPolynomial ι ℂ) :
    MvPolynomial.coeff (squareFreeExponent rows)
      ((MvPolynomial.X i) ^ 2 * p) = 0 := by
  classical
  rw [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_monomial_mul']
  split_ifs with h
  · have hi : 2 ≤ squareFreeExponent rows i :=
      Finsupp.single_le_iff.mp h
    have hbound : squareFreeExponent rows i ≤ 1 := by
      rw [squareFreeExponent_apply]
      split <;> omega
    omega
  · rfl
theorem coeff_squareFree_mul_of_forall_eq_zero {ι : Type*}
    (p q : MvPolynomial ι ℂ)
    (hp : ∀ rows : Finset ι,
      MvPolynomial.coeff (squareFreeExponent rows) p = 0)
    (rows : Finset ι) :
    MvPolynomial.coeff (squareFreeExponent rows) (q * p) = 0 := by
  classical
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro decomposition hdecomposition
  have hsum : decomposition.1 + decomposition.2 = squareFreeExponent rows :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hdecomposition
  have hle : decomposition.2 ≤ squareFreeExponent rows := by
    rw [← hsum]
    exact le_add_left le_rfl
  have hsquare := eq_squareFreeExponent_support_of_le
    rows decomposition.2 hle
  rw [hsquare, hp decomposition.2.support, mul_zero]
theorem coeff_squareFree_eq_zero_of_mem_squareZeroIdeal
    (r : ℕ) {p : MvPolynomial (Fin r) ℂ}
    (hp : p ∈ squareZeroIdeal r) (rows : Finset (Fin r)) :
    MvPolynomial.coeff (squareFreeExponent rows) p = 0 := by
  change p ∈ Ideal.span
    (Set.range fun i : Fin r => (MvPolynomial.X i) ^ 2) at hp
  have hall : ∀ target : Finset (Fin r),
      MvPolynomial.coeff (squareFreeExponent target) p = 0 := by
    induction hp using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro target
        simpa using coeff_squareFree_variable_sq_mul
          target i (1 : MvPolynomial (Fin r) ℂ)
    | zero =>
        intro target
        simp
    | add x y hx hy ihx ihy =>
        intro target
        rw [MvPolynomial.coeff_add, ihx target, ihy target, add_zero]
    | smul a x hx ih =>
        intro target
        simpa only [smul_eq_mul] using
          coeff_squareFree_mul_of_forall_eq_zero x a ih target
  exact hall rows
noncomputable def squareZeroCoefficient (r : ℕ) (rows : Finset (Fin r)) :
    SquareZeroAlgebra r →ₗ[ℂ] ℂ := by
  let I : Submodule ℂ (MvPolynomial (Fin r) ℂ) :=
    (squareZeroIdeal r).restrictScalars ℂ
  let coefficient : MvPolynomial (Fin r) ℂ →ₗ[ℂ] ℂ :=
    MvPolynomial.lcoeff ℂ (squareFreeExponent rows)
  have hkernel : I ≤ LinearMap.ker coefficient := by
    intro p hp
    change MvPolynomial.coeff (squareFreeExponent rows) p = 0
    exact coeff_squareFree_eq_zero_of_mem_squareZeroIdeal r hp rows
  exact (I.liftQ coefficient hkernel).comp
    (Submodule.Quotient.restrictScalarsEquiv ℂ
      (squareZeroIdeal r)).symm.toLinearMap
@[simp] theorem squareZeroCoefficient_mk (r : ℕ)
    (rows : Finset (Fin r)) (p : MvPolynomial (Fin r) ℂ) :
    squareZeroCoefficient r rows (Ideal.Quotient.mk (squareZeroIdeal r) p) =
      MvPolynomial.coeff (squareFreeExponent rows) p := by
  rfl
noncomputable def columnLinearForm {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) (column : Fin k) :
    MvPolynomial (Fin r) ℂ :=
  ∑ row : Fin r, MvPolynomial.C (U row column) * MvPolynomial.X row
noncomputable def columnLinearFormProduct {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) : MvPolynomial (Fin r) ℂ :=
  ∏ column : Fin k, columnLinearForm U column
noncomputable def columnAssignmentExponent {r k : ℕ}
    (assignment : Fin k → Fin r) : Fin r →₀ ℕ :=
  ∑ column : Fin k, Finsupp.single (assignment column) 1
theorem columnAssignmentExponent_apply {r k : ℕ}
    (assignment : Fin k → Fin r) (row : Fin r) :
    columnAssignmentExponent assignment row =
      ((Finset.univ : Finset (Fin k)).filter
        (fun column => assignment column = row)).card := by
  classical
  simp [columnAssignmentExponent, Finsupp.single_apply,
    Finset.sum_boole]
@[simp] theorem columnAssignmentExponent_support {r k : ℕ}
    (assignment : Fin k → Fin r) :
    (columnAssignmentExponent assignment).support =
      (Finset.univ : Finset (Fin k)).image assignment := by
  classical
  ext row
  simp [Finsupp.mem_support_iff, columnAssignmentExponent_apply]
theorem columnAssignment_injective_of_squareFree {r k : ℕ}
    (assignment : Fin k → Fin r) (rows : Finset (Fin r))
    (hassignment : columnAssignmentExponent assignment =
      squareFreeExponent rows) :
    Function.Injective assignment := by
  classical
  intro left right heq
  let fiber : Finset (Fin k) :=
    (Finset.univ : Finset (Fin k)).filter
      (fun column => assignment column = assignment left)
  have hcard : fiber.card ≤ 1 := by
    change ((Finset.univ : Finset (Fin k)).filter
      (fun column => assignment column = assignment left)).card ≤ 1
    rw [← columnAssignmentExponent_apply, hassignment,
      squareFreeExponent_apply]
    split <;> omega
  exact (Finset.card_le_one.mp hcard)
    left (by simp [fiber]) right (by simp [fiber, heq])
theorem columnAssignment_image_eq_of_squareFree {r k : ℕ}
    (assignment : Fin k → Fin r) (rows : Finset (Fin r))
    (hassignment : columnAssignmentExponent assignment =
      squareFreeExponent rows) :
    (Finset.univ : Finset (Fin k)).image assignment = rows := by
  have hs := congrArg Finsupp.support hassignment
  simpa only [columnAssignmentExponent_support,
    squareFreeExponent_support] using hs
noncomputable def squareFreeColumnMatchingPermutation {r k : ℕ}
    (rows : Finset (Fin r)) (rowEquiv : Fin k ≃ {row // row ∈ rows})
    (assignment : Fin k → Fin r)
    (hassignment : columnAssignmentExponent assignment =
      squareFreeExponent rows) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective
    (fun column => rowEquiv.symm
      ⟨assignment column, by
        rw [← columnAssignment_image_eq_of_squareFree assignment rows
          hassignment]
        exact Finset.mem_image.mpr
          ⟨column, Finset.mem_univ column, rfl⟩⟩)
    (by
      apply (Fintype.bijective_iff_injective_and_card _).mpr
      constructor
      · intro left right hmatch
        apply columnAssignment_injective_of_squareFree
          assignment rows hassignment
        have hrows := congrArg rowEquiv hmatch
        simpa using congrArg Subtype.val hrows
      · rfl)
@[simp] theorem squareFreeColumnMatchingPermutation_apply {r k : ℕ}
    (rows : Finset (Fin r)) (rowEquiv : Fin k ≃ {row // row ∈ rows})
    (assignment : Fin k → Fin r)
    (hassignment : columnAssignmentExponent assignment =
      squareFreeExponent rows) (column : Fin k) :
    (rowEquiv
      (squareFreeColumnMatchingPermutation rows rowEquiv assignment
        hassignment column)).val = assignment column := by
  simp [squareFreeColumnMatchingPermutation]
end Standalone_Coefficients
section Standalone_Partition
open scoped BigOperators
noncomputable def partitionMobius {t : ℕ} {rows : Finset (Fin t)}
    (partition : Finpartition rows) : ℂ :=
  ∏ block ∈ partition.parts,
    (-1 : ℂ) ^ (block.card - 1) * (block.card - 1).factorial
noncomputable def partitionBlockFactor {t : ℕ} {rows : Finset (Fin t)}
    (p : Finset (Fin t) → ℂ) (partition : Finpartition rows) :
    MvPolynomial (Fin t) ℂ :=
  ∏ block ∈ partition.parts,
    (MvPolynomial.C (p block) - ∏ row ∈ block, MvPolynomial.X row)
noncomputable def partitionDerivative (t d : ℕ) (i : Fin t)
    (p : Finset (Fin t) → ℂ) : MvPolynomial (Fin t) ℂ :=
  ∑ rows ∈ ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
    ∑ partition : Finpartition rows,
      MvPolynomial.C (partitionMobius partition) * partitionBlockFactor p partition
end Standalone_Partition
section Standalone_PartitionMatching
open scoped BigOperators
noncomputable def sourceMatchingEmbedding
    {t s : ℕ} (rows : Finset (Fin t))
    (data : Σ columns :
      {columns : Finset (Fin s) //
        columns ∈ (Finset.univ : Finset (Fin s)).powersetCard rows.card},
      rows ≃ columns.val) : rows ↪ Fin s :=
  data.2.toEmbedding.trans (Function.Embedding.subtype _)
theorem sourceMatchingEmbedding_bijective
    {t s : ℕ} (rows : Finset (Fin t)) :
    Function.Bijective (sourceMatchingEmbedding (s := s) rows) := by
  classical
  constructor
  · rintro ⟨⟨leftColumns, hleftColumns⟩, leftMatching⟩
      ⟨⟨rightColumns, hrightColumns⟩, rightMatching⟩ heq
    have hcolumns : leftColumns = rightColumns := by
      ext column
      constructor
      · intro hcolumn
        obtain ⟨row, hrow⟩ := leftMatching.surjective ⟨column, hcolumn⟩
        have hpoint := DFunLike.congr_fun heq row
        change (leftMatching row).val = (rightMatching row).val at hpoint
        have hleft : (leftMatching row).val = column :=
          congrArg Subtype.val hrow
        have hright : (rightMatching row).val = column := hpoint.symm.trans hleft
        exact hright ▸ (rightMatching row).property
      · intro hcolumn
        obtain ⟨row, hrow⟩ := rightMatching.surjective ⟨column, hcolumn⟩
        have hpoint := DFunLike.congr_fun heq row
        change (leftMatching row).val = (rightMatching row).val at hpoint
        have hright : (rightMatching row).val = column :=
          congrArg Subtype.val hrow
        have hleft : (leftMatching row).val = column := hpoint.trans hright
        exact hleft ▸ (leftMatching row).property
    subst rightColumns
    have hmatching : leftMatching = rightMatching := by
      apply Equiv.ext
      intro row
      apply Subtype.ext
      have hpoint := DFunLike.congr_fun heq row
      change (leftMatching row).val = (rightMatching row).val at hpoint
      exact hpoint
    subst rightMatching
    rfl
  · intro embedding
    let columns : Finset (Fin s) :=
      (Finset.univ : Finset rows).map embedding
    have hcard :
        columns ∈ (Finset.univ : Finset (Fin s)).powersetCard rows.card := by
      simp [columns]
    let matching : rows ≃ columns := Equiv.ofBijective
      (fun row : rows => (⟨embedding row, by
        simp [columns]⟩ : columns)) (by
        constructor
        · intro left right h
          exact embedding.injective (congrArg Subtype.val h)
        · intro column
          have hmem : column.val ∈ columns := column.property
          simp only [columns, Finset.mem_map, Finset.mem_univ, true_and] at hmem
          obtain ⟨row, hrow⟩ := hmem
          exact ⟨row, Subtype.ext hrow⟩)
    refine ⟨⟨⟨columns, hcard⟩, matching⟩, ?_⟩
    ext row
    rfl
theorem sourceMatching_sum_eq_embeddings
    {t s : ℕ} {R : Type*} [CommSemiring R]
    (rows : Finset (Fin t)) (weight : Fin t → Fin s → R) :
    (∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard rows.card,
      ∑ matching : rows ≃ columns,
        ∏ row : rows, weight row.val (matching row).val) =
      ∑ embedding : rows ↪ Fin s,
        ∏ row : rows, weight row.val (embedding row) := by
  classical
  let columnSet :=
    (Finset.univ : Finset (Fin s)).powersetCard rows.card
  let dataType := Σ columns : columnSet, rows ≃ columns.val
  calc
    (∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard rows.card,
      ∑ matching : rows ≃ columns,
        ∏ row : rows, weight row.val (matching row).val) =
      ∑ data : dataType,
        ∏ row : rows, weight row.val (data.2 row).val := by
          change
            (∑ columns ∈ columnSet,
              ∑ matching : rows ≃ columns,
                ∏ row : rows, weight row.val (matching row).val) =
              ∑ data : (Σ columns : columnSet, rows ≃ columns.val),
                ∏ row : rows, weight row.val (data.2 row).val
          rw [Fintype.sum_sigma]
          exact (Finset.sum_coe_sort columnSet
            (fun columns => ∑ matching : rows ≃ columns,
              ∏ row : rows, weight row.val (matching row).val)).symm
    _ = ∑ embedding : rows ↪ Fin s,
        ∏ row : rows, weight row.val (embedding row) := by
          exact Fintype.sum_bijective
            (sourceMatchingEmbedding (s := s) rows)
            (sourceMatchingEmbedding_bijective rows)
            _ _ (fun _ => rfl)
theorem minorSum_eq_source_embeddings (t s d : ℕ) :
    minorSum t s d =
      ∑ rows ∈ (Finset.univ : Finset (Fin t)).powersetCard d,
        ∑ embedding : rows ↪ Fin s,
          ∏ row : rows,
            (MvPolynomial.X (row.val, embedding row) :
              MvPolynomial (Fin t × Fin s) ℂ) := by
  classical
  unfold minorSum
  apply Finset.sum_congr rfl
  intro rows hrows
  have hcard : rows.card = d := by
    simpa using hrows
  simpa [hcard] using sourceMatching_sum_eq_embeddings rows
    (fun row column =>
      (MvPolynomial.X (row, column) : MvPolynomial (Fin t × Fin s) ℂ))
noncomputable def sourceFixedEdgeEmbedding
    {t s : ℕ} (rows : Finset (Fin t)) (i : Fin t) (column : Fin s)
    (hrow : i ∈ rows)
    (data : {embedding : rows ↪ Fin s //
      embedding (⟨i, hrow⟩ : rows) = column}) :
    (rows.erase i) ↪ {other : Fin s // other ≠ column} where
  toFun row :=
    ⟨data.val ⟨row.val, Finset.mem_of_mem_erase row.property⟩, by
      intro hcolumn
      have heq :
          data.val ⟨row.val, Finset.mem_of_mem_erase row.property⟩ =
            data.val (⟨i, hrow⟩ : rows) := hcolumn.trans data.property.symm
      have hrows := data.val.injective heq
      exact (Finset.mem_erase.mp row.property).1
        (congrArg (fun r : rows => r.val) hrows)⟩
  inj' := by
    intro left right h
    apply Subtype.ext
    have hvalues :=
      congrArg (fun c : {other : Fin s // other ≠ column} => c.val) h
    have hrows := data.val.injective hvalues
    exact congrArg (fun r : rows => r.val) hrows
theorem sourceFixedEdgeEmbedding_bijective
    {t s : ℕ} (rows : Finset (Fin t)) (i : Fin t) (column : Fin s)
    (hrow : i ∈ rows) :
    Function.Bijective (sourceFixedEdgeEmbedding rows i column hrow) := by
  classical
  constructor
  · intro left right heq
    apply Subtype.ext
    apply DFunLike.ext
    intro row
    by_cases h : row.val = i
    · have hroweq : row = (⟨i, hrow⟩ : rows) := Subtype.ext h
      rw [hroweq, left.property, right.property]
    · let remaining : rows.erase i :=
        ⟨row.val, Finset.mem_erase.mpr ⟨h, row.property⟩⟩
      have hpoint := DFunLike.congr_fun heq remaining
      exact congrArg
        (fun c : {other : Fin s // other ≠ column} => c.val) hpoint
  · intro embedding
    let extend : rows → Fin s := fun row =>
      if h : row.val = i then column
      else (embedding ⟨row.val, Finset.mem_erase.mpr
        ⟨h, row.property⟩⟩).val
    have hinjective : Function.Injective extend := by
      intro left right hvalues
      by_cases hleft : left.val = i
      · by_cases hright : right.val = i
        · exact Subtype.ext (hleft.trans hright.symm)
        · have hnot :=
            (embedding ⟨right.val,
              Finset.mem_erase.mpr ⟨hright, right.property⟩⟩).property
          apply False.elim
          apply hnot
          simpa [extend, hleft, hright] using hvalues.symm
      · by_cases hright : right.val = i
        · have hnot :=
            (embedding ⟨left.val,
              Finset.mem_erase.mpr ⟨hleft, left.property⟩⟩).property
          apply False.elim
          apply hnot
          simpa [extend, hleft, hright] using hvalues
        · have hremaining :
              (embedding ⟨left.val,
                Finset.mem_erase.mpr ⟨hleft, left.property⟩⟩).val =
              (embedding ⟨right.val,
                Finset.mem_erase.mpr ⟨hright, right.property⟩⟩).val := by
              simpa [extend, hleft, hright] using hvalues
          have hembedding := embedding.injective (Subtype.ext hremaining)
          exact Subtype.ext
            (congrArg (fun r : rows.erase i => r.val) hembedding)
    let whole : rows ↪ Fin s := ⟨extend, hinjective⟩
    have hwhole : whole (⟨i, hrow⟩ : rows) = column := by
      simp [whole, extend]
    refine ⟨⟨whole, hwhole⟩, ?_⟩
    apply DFunLike.ext
    intro row
    apply Subtype.ext
    have hnot : row.val ≠ i := (Finset.mem_erase.mp row.property).1
    simp [sourceFixedEdgeEmbedding, whole, extend, hnot]
theorem sourceFixedEdgeEmbedding_prod
    {t s : ℕ} (rows : Finset (Fin t)) (i : Fin t) (column : Fin s)
    (hrow : i ∈ rows) (point : Fin t × Fin s → ℂ)
    (data : {embedding : rows ↪ Fin s //
      embedding (⟨i, hrow⟩ : rows) = column}) :
    (∏ other ∈ (Finset.univ : Finset rows).erase (⟨i, hrow⟩ : rows),
      point (other.val, data.val other)) =
      ∏ other : rows.erase i,
        point (other.val,
          (sourceFixedEdgeEmbedding rows i column hrow data other).val) := by
  classical
  refine Finset.prod_bij
    (fun other hother =>
      (⟨other.val, Finset.mem_erase.mpr
        ⟨by
          intro heq
          apply (Finset.mem_erase.mp hother).1
          exact Subtype.ext heq,
         other.property⟩⟩ : rows.erase i))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro left _ right _ heq
    exact Subtype.ext (congrArg
      (fun row : rows.erase i => row.val) heq)
  · intro other _
    let whole : rows :=
      ⟨other.val, Finset.mem_of_mem_erase other.property⟩
    have hne : whole ≠ (⟨i, hrow⟩ : rows) := by
      intro heq
      exact (Finset.mem_erase.mp other.property).1
        (congrArg (fun row : rows => row.val) heq)
    refine ⟨whole, Finset.mem_erase.mpr
      ⟨hne, Finset.mem_univ whole⟩, ?_⟩
    exact Subtype.ext rfl
  · intro other hother
    rfl
theorem sourceFixedEdgeEmbedding_weighted_sum
    {t s : ℕ} (rows : Finset (Fin t)) (i : Fin t) (column : Fin s)
    (hrow : i ∈ rows) (point : Fin t × Fin s → ℂ) :
    (∑ embedding : rows ↪ Fin s,
      if embedding (⟨i, hrow⟩ : rows) = column then
        ∏ other ∈ (Finset.univ : Finset rows).erase (⟨i, hrow⟩ : rows),
          point (other.val, embedding other)
      else 0) =
      ∑ embedding : (rows.erase i) ↪ {other : Fin s // other ≠ column},
        ∏ other : rows.erase i, point (other.val, (embedding other).val) := by
  classical
  let fixed := {embedding : rows ↪ Fin s //
    embedding (⟨i, hrow⟩ : rows) = column}
  calc
    (∑ embedding : rows ↪ Fin s,
      if embedding (⟨i, hrow⟩ : rows) = column then
        ∏ other ∈ (Finset.univ : Finset rows).erase (⟨i, hrow⟩ : rows),
          point (other.val, embedding other)
      else 0) =
      ∑ data : fixed,
        ∏ other ∈ (Finset.univ : Finset rows).erase (⟨i, hrow⟩ : rows),
          point (other.val, data.val other) := by
            change
              (∑ embedding : rows ↪ Fin s,
                if embedding (⟨i, hrow⟩ : rows) = column then
                  ∏ other ∈ (Finset.univ : Finset rows).erase
                    (⟨i, hrow⟩ : rows),
                    point (other.val, embedding other)
                else 0) =
                ∑ data : {embedding : rows ↪ Fin s //
                    embedding (⟨i, hrow⟩ : rows) = column},
                  ∏ other ∈ (Finset.univ : Finset rows).erase
                    (⟨i, hrow⟩ : rows),
                    point (other.val, data.val other)
            rw [← Finset.sum_filter]
            exact Finset.sum_subtype _ (by simp) _
    _ = ∑ embedding : (rows.erase i) ↪
          {other : Fin s // other ≠ column},
        ∏ other : rows.erase i,
          point (other.val, (embedding other).val) := by
            exact Fintype.sum_bijective
              (sourceFixedEdgeEmbedding rows i column hrow)
              (sourceFixedEdgeEmbedding_bijective rows i column hrow)
              _ _ (sourceFixedEdgeEmbedding_prod rows i column hrow point)
theorem sourceMatching_pderiv_finset_prod
    {ι σ R : Type*} [DecidableEq ι] [CommSemiring R]
    (coordinate : σ) (indices : Finset ι)
    (f : ι → MvPolynomial σ R) :
    MvPolynomial.pderiv coordinate (∏ index ∈ indices, f index) =
      ∑ index ∈ indices,
        MvPolynomial.pderiv coordinate (f index) *
          ∏ other ∈ indices.erase index, f other := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnot ih =>
    rw [Finset.prod_insert hnot, MvPolynomial.pderiv_mul, ih,
      Finset.sum_insert hnot, Finset.mul_sum,
      Finset.erase_insert hnot]
    apply congrArg (fun value : MvPolynomial σ R =>
      MvPolynomial.pderiv coordinate (f index) *
        (∏ other ∈ indices, f other) + value)
    apply Finset.sum_congr rfl
    intro other hother
    have hne : index ≠ other := fun heq => hnot (heq ▸ hother)
    rw [Finset.erase_insert_of_ne hne,
      Finset.prod_insert (fun h => hnot (Finset.mem_of_mem_erase h))]
    ac_rfl
theorem eval_minorSum_pderiv_source_embeddings
    (t s d : ℕ) (point : Fin t × Fin s → ℂ)
    (i : Fin t) (column : Fin s) :
    MvPolynomial.eval point
        (MvPolynomial.pderiv (i, column) (minorSum t s d)) =
      ∑ rows ∈ (Finset.univ : Finset (Fin t)).powersetCard d,
        ∑ embedding : rows ↪ Fin s,
          ∑ row : rows,
            if (row.val, embedding row) = (i, column) then
              ∏ other ∈ (Finset.univ : Finset rows).erase row,
                point (other.val, embedding other)
            else 0 := by
  classical
  rw [minorSum_eq_source_embeddings]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro embedding _
  rw [sourceMatching_pderiv_finset_prod (i, column)
    (Finset.univ : Finset rows)
    (fun row : rows =>
      (MvPolynomial.X (row.val, embedding row) :
        MvPolynomial (Fin t × Fin s) ℂ))]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro row _
  by_cases h : (row.val, embedding row) = (i, column)
  · simp [MvPolynomial.pderiv_X, h]
  · simp [MvPolynomial.pderiv_X, h]
theorem sourceMatching_embedding_edge_sum
    {t s : ℕ} (rows : Finset (Fin t))
    (i : Fin t) (column : Fin s)
    (point : Fin t × Fin s → ℂ) (embedding : rows ↪ Fin s) :
    (∑ row : rows,
      if (row.val, embedding row) = (i, column) then
        ∏ other ∈ (Finset.univ : Finset rows).erase row,
          point (other.val, embedding other)
      else 0) =
      if hrow : i ∈ rows then
        if embedding (⟨i, hrow⟩ : rows) = column then
          ∏ other ∈ (Finset.univ : Finset rows).erase
            (⟨i, hrow⟩ : rows),
            point (other.val, embedding other)
        else 0
      else 0 := by
  classical
  split_ifs with hrow hcolumn
  · rw [Finset.sum_eq_single (⟨i, hrow⟩ : rows)]
    · simp [hcolumn]
    · intro other _ hother
      have hne : other.val ≠ i := by
        intro heq
        exact hother (Subtype.ext heq)
      simp [hne]
    · simp
  · apply Finset.sum_eq_zero
    intro other _
    by_cases hother : other.val = i
    · have heq : other = (⟨i, hrow⟩ : rows) := Subtype.ext hother
      subst other
      simp [hcolumn]
    · simp [hother]
  · apply Finset.sum_eq_zero
    intro other _
    have hne : other.val ≠ i := fun heq => hrow (heq ▸ other.property)
    simp [hne]
theorem sourceMatching_row_derivative_eq_excluded_embeddings
    {t s : ℕ} (rows : Finset (Fin t))
    (i : Fin t) (column : Fin s)
    (point : Fin t × Fin s → ℂ) (hrow : i ∈ rows) :
    (∑ embedding : rows ↪ Fin s,
      ∑ row : rows,
        if (row.val, embedding row) = (i, column) then
          ∏ other ∈ (Finset.univ : Finset rows).erase row,
            point (other.val, embedding other)
        else 0) =
      ∑ embedding : (rows.erase i) ↪ {other : Fin s // other ≠ column},
        ∏ other : rows.erase i,
          point (other.val, (embedding other).val) := by
  classical
  calc
    (∑ embedding : rows ↪ Fin s,
      ∑ row : rows,
        if (row.val, embedding row) = (i, column) then
          ∏ other ∈ (Finset.univ : Finset rows).erase row,
            point (other.val, embedding other)
        else 0) =
      ∑ embedding : rows ↪ Fin s,
        if embedding (⟨i, hrow⟩ : rows) = column then
          ∏ other ∈ (Finset.univ : Finset rows).erase
            (⟨i, hrow⟩ : rows),
            point (other.val, embedding other)
        else 0 := by
          apply Finset.sum_congr rfl
          intro embedding _
          simpa [hrow] using
            sourceMatching_embedding_edge_sum rows i column point embedding
    _ = _ := sourceFixedEdgeEmbedding_weighted_sum
      rows i column hrow point
theorem eval_minorSum_pderiv_eq_excluded_embeddings
    (t s d : ℕ) (hd : 0 < d) (point : Fin t × Fin s → ℂ)
    (i : Fin t) (column : Fin s) :
    MvPolynomial.eval point
        (MvPolynomial.pderiv (i, column) (minorSum t s d)) =
      ∑ rows ∈
          ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
        ∑ embedding : rows ↪ {other : Fin s // other ≠ column},
          ∏ row : rows, point (row.val, (embedding row).val) := by
  classical
  rw [eval_minorSum_pderiv_source_embeddings]
  let sourceRows := (Finset.univ : Finset (Fin t)).powersetCard d
  let validRows := sourceRows.filter (fun rows => i ∈ rows)
  let remainingRows :=
    ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1)
  let edgeWeight : Finset (Fin t) → ℂ := fun rows =>
    ∑ embedding : rows ↪ Fin s,
      ∑ row : rows,
        if (row.val, embedding row) = (i, column) then
          ∏ other ∈ (Finset.univ : Finset rows).erase row,
            point (other.val, embedding other)
        else 0
  let remainingWeight : Finset (Fin t) → ℂ := fun rows =>
    ∑ embedding : rows ↪ {other : Fin s // other ≠ column},
      ∏ row : rows, point (row.val, (embedding row).val)
  change (∑ rows ∈ sourceRows, edgeWeight rows) =
    ∑ rows ∈ remainingRows, remainingWeight rows
  calc
    (∑ rows ∈ sourceRows, edgeWeight rows) =
      ∑ rows ∈ validRows, edgeWeight rows := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro rows hsource hnot
        have hrow : i ∉ rows := by
          intro hmem
          apply hnot
          exact Finset.mem_filter.mpr ⟨hsource, hmem⟩
        change
          (∑ embedding : rows ↪ Fin s,
            ∑ row : rows,
              if (row.val, embedding row) = (i, column) then
                ∏ other ∈ (Finset.univ : Finset rows).erase row,
                  point (other.val, embedding other)
              else 0) = 0
        apply Finset.sum_eq_zero
        intro embedding _
        simpa [hrow] using
          sourceMatching_embedding_edge_sum rows i column point embedding
    _ = ∑ rows ∈ validRows, remainingWeight (rows.erase i) := by
        apply Finset.sum_congr rfl
        intro rows hrows
        have hrow : i ∈ rows := (Finset.mem_filter.mp hrows).2
        exact sourceMatching_row_derivative_eq_excluded_embeddings
          rows i column point hrow
    _ = ∑ rows ∈ remainingRows, remainingWeight rows := by
        refine Finset.sum_bij
          (fun rows _ => rows.erase i) ?_ ?_ ?_ ?_
        · intro rows hrows
          have hmem := Finset.mem_filter.mp hrows
          apply Finset.mem_powersetCard.mpr
          constructor
          · intro row hrow
            exact Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp hrow).1, Finset.mem_univ row⟩
          · have hcard : rows.card = d := by
              simpa [sourceRows] using hmem.1
            rw [Finset.card_erase_of_mem hmem.2, hcard]
        · intro left hleft right hright herase
          have hlefti := (Finset.mem_filter.mp hleft).2
          have hrighti := (Finset.mem_filter.mp hright).2
          calc
            left = insert i (left.erase i) :=
              (Finset.insert_erase hlefti).symm
            _ = insert i (right.erase i) := congrArg (insert i) herase
            _ = right := Finset.insert_erase hrighti
        · intro rows hrows
          have hmem := Finset.mem_powersetCard.mp hrows
          have hnot : i ∉ rows := by
            intro hi
            exact Finset.notMem_erase i Finset.univ (hmem.1 hi)
          let whole := insert i rows
          have hwhole : whole ∈ validRows := by
            apply Finset.mem_filter.mpr
            constructor
            · apply Finset.mem_powersetCard.mpr
              constructor
              · exact Finset.subset_univ whole
              · simp only [whole, Finset.card_insert_of_notMem hnot]
                omega
            · exact Finset.mem_insert_self i rows
          refine ⟨whole, hwhole, ?_⟩
          simp [whole, hnot]
        · intro rows hrows
          rfl
end Standalone_PartitionMatching
section Standalone_PartitionInversion
open scoped BigOperators
theorem partition_empty_eq {α : Type*} [DecidableEq α]
    (partition : Finpartition (∅ : Finset α)) :
    partition = Finpartition.empty (Finset α) := by
  apply Finpartition.ext
  change partition.parts = ∅
  exact Finpartition.parts_eq_empty_iff.mpr rfl
noncomputable def partitionRemovePart {α : Type*} [DecidableEq α]
    {rows : Finset α} (partition : Finpartition rows)
    (block : Finset α) (hblock : block ∈ partition.parts) :
    Finpartition (rows \ block) :=
  partition.ofSubset (Finset.erase_subset block partition.parts) (by
    ext row
    simp only [Finset.mem_sup, id_eq, Finset.mem_erase,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨part, ⟨hne, hpart⟩, hrow⟩
      refine ⟨partition.subset hpart hrow, ?_⟩
      intro hrowblock
      exact Finset.disjoint_left.mp
        (partition.disjoint hpart hblock hne) hrow hrowblock
    · rintro ⟨hrow, hnot⟩
      obtain ⟨part, hpart, hrowpart⟩ := partition.exists_mem hrow
      refine ⟨part, ⟨?_, hpart⟩, hrowpart⟩
      intro heq
      apply hnot
      simpa [heq] using hrowpart)
@[simp] theorem partitionRemovePart_parts {α : Type*} [DecidableEq α]
    {rows : Finset α} (partition : Finpartition rows)
    (block : Finset α) (hblock : block ∈ partition.parts) :
    (partitionRemovePart partition block hblock).parts =
      partition.parts.erase block := by
  rfl
noncomputable def partitionAddPart {α : Type*} [DecidableEq α]
    {rows : Finset α} (block : Finset α)
    (hnonempty : block.Nonempty) (hsubset : block ⊆ rows)
    (partition : Finpartition (rows \ block)) : Finpartition rows :=
  partition.extend hnonempty.ne_empty Finset.sdiff_disjoint (by
    change rows \ block ∪ block = rows
    exact Finset.sdiff_union_of_subset hsubset)
theorem partition_block_not_mem_complement
    {α : Type*} [DecidableEq α] {rows : Finset α}
    (block : Finset α) (hnonempty : block.Nonempty)
    (partition : Finpartition (rows \ block)) :
    block ∉ partition.parts := by
  intro hblock
  obtain ⟨row, hrow⟩ := hnonempty
  exact (Finset.mem_sdiff.mp
    ((partition.subset hblock) hrow)).2 hrow
theorem partition_weight_fiber {α R : Type*}
    [DecidableEq α] [CommSemiring R]
    (weight : Finset α → R) (rows : Finset α)
    (distinguished : α) (hdistinguished : distinguished ∈ rows)
    (selected : Finset α) (hselected : selected ⊆ rows.erase distinguished) :
    (∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition => (partition.part distinguished).erase distinguished =
            selected),
        ∏ block ∈ partition.parts, weight block) =
      weight (insert distinguished selected) *
        ∑ partition : Finpartition (rows \ insert distinguished selected),
          ∏ block ∈ partition.parts, weight block := by
  classical
  let block : Finset α := insert distinguished selected
  have hnonempty : block.Nonempty :=
    ⟨distinguished, Finset.mem_insert_self distinguished selected⟩
  have hsubset : block ⊆ rows := by
    intro row hrow
    rcases Finset.mem_insert.mp hrow with hrow | hrow
    · simpa [hrow] using hdistinguished
    · exact (Finset.mem_erase.mp (hselected hrow)).2
  have hnot : distinguished ∉ selected := by
    intro hmem
    exact Finset.notMem_erase distinguished rows (hselected hmem)
  have hpart (partition : Finpartition rows)
      (hpartition : partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            (partition.part distinguished).erase distinguished = selected)) :
      partition.part distinguished = block := by
    have herase := (Finset.mem_filter.mp hpartition).2
    calc
      partition.part distinguished =
          insert distinguished
            ((partition.part distinguished).erase distinguished) :=
        (Finset.insert_erase
          (partition.mem_part hdistinguished)).symm
      _ = block := by rw [herase]
  have hblock (partition : Finpartition rows)
      (hpartition : partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            (partition.part distinguished).erase distinguished = selected)) :
      block ∈ partition.parts := by
    rw [← hpart partition hpartition]
    exact partition.part_mem.mpr hdistinguished
  rw [Finset.mul_sum]
  change
    (∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition => (partition.part distinguished).erase distinguished =
            selected),
        ∏ part ∈ partition.parts, weight part) =
      ∑ partition : Finpartition (rows \ block),
        weight block * ∏ part ∈ partition.parts, weight part
  refine Finset.sum_bij
    (fun partition hpartition =>
      partitionRemovePart partition block (hblock partition hpartition))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro left hleft right hright heq
    apply Finpartition.ext
    have herase := congrArg Finpartition.parts heq
    change left.parts.erase block = right.parts.erase block at herase
    calc
      left.parts = insert block (left.parts.erase block) :=
        (Finset.insert_erase (hblock left hleft)).symm
      _ = insert block (right.parts.erase block) :=
        congrArg (insert block) herase
      _ = right.parts := Finset.insert_erase (hblock right hright)
  · intro complement _
    let partition : Finpartition rows :=
      partitionAddPart block hnonempty hsubset complement
    have hpart_block : partition.part distinguished = block := by
      apply partition.part_eq_of_mem
      · change block ∈ insert block complement.parts
        exact Finset.mem_insert_self block complement.parts
      · exact Finset.mem_insert_self distinguished selected
    have hfilter : partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            (partition.part distinguished).erase distinguished = selected) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ partition, ?_⟩
      rw [hpart_block]
      simp [block, hnot]
    refine ⟨partition, hfilter, ?_⟩
    apply Finpartition.ext
    change (insert block complement.parts).erase block = complement.parts
    rw [Finset.erase_insert
      (partition_block_not_mem_complement block hnonempty complement)]
  · intro partition hpartition
    rw [partitionRemovePart_parts]
    exact (Finset.mul_prod_erase partition.parts weight
      (hblock partition hpartition)).symm
theorem partition_weight_sum {α R : Type*}
    [DecidableEq α] [CommSemiring R]
    (weight : Finset α → R) (rows : Finset α)
    (distinguished : α) (hdistinguished : distinguished ∈ rows) :
    (∑ partition : Finpartition rows,
      ∏ block ∈ partition.parts, weight block) =
      ∑ selected ∈ (rows.erase distinguished).powerset,
        weight (insert distinguished selected) *
          ∑ partition : Finpartition (rows \ insert distinguished selected),
            ∏ block ∈ partition.parts, weight block := by
  classical
  have hmaps :
      ∀ partition ∈ (Finset.univ : Finset (Finpartition rows)),
        (partition.part distinguished).erase distinguished ∈
          (rows.erase distinguished).powerset := by
    intro partition _
    apply Finset.mem_powerset.mpr
    intro row hrow
    obtain ⟨hne, hpart⟩ := Finset.mem_erase.mp hrow
    exact Finset.mem_erase.mpr
      ⟨hne, partition.part_subset distinguished hpart⟩
  calc
    (∑ partition : Finpartition rows,
        ∏ block ∈ partition.parts, weight block) =
      ∑ selected ∈ (rows.erase distinguished).powerset,
        ∑ partition ∈
            (Finset.univ : Finset (Finpartition rows)).filter
              (fun partition =>
                (partition.part distinguished).erase distinguished = selected),
          ∏ block ∈ partition.parts, weight block :=
        (Finset.sum_fiberwise_of_maps_to hmaps
          (fun partition : Finpartition rows =>
            ∏ block ∈ partition.parts, weight block)).symm
    _ = ∑ selected ∈ (rows.erase distinguished).powerset,
        weight (insert distinguished selected) *
          ∑ partition : Finpartition (rows \ insert distinguished selected),
            ∏ block ∈ partition.parts, weight block := by
      apply Finset.sum_congr rfl
      intro selected hselected
      exact partition_weight_fiber weight rows distinguished hdistinguished
        selected (Finset.mem_powerset.mp hselected)
theorem signed_factorial_powerset {α : Type*}
    [DecidableEq α] (others : Finset α) :
    (∑ selected ∈ others.powerset,
      ((-1 : ℂ) ^ selected.card * (selected.card.factorial : ℂ)) *
        if (others \ selected).card ≤ 1 then (1 : ℂ) else 0) =
      if others.Nonempty then (0 : ℂ) else 1 := by
  classical
  rw [Finset.sum_powerset]
  calc
    (∑ k ∈ Finset.range (others.card + 1),
        ∑ selected ∈ others.powersetCard k,
          ((-1 : ℂ) ^ selected.card *
              (selected.card.factorial : ℂ)) *
            if (others \ selected).card ≤ 1 then (1 : ℂ) else 0) =
      ∑ k ∈ Finset.range (others.card + 1),
        (others.card.choose k : ℂ) *
          (((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
            if others.card - k ≤ 1 then (1 : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          (∑ selected ∈ others.powersetCard k,
              ((-1 : ℂ) ^ selected.card *
                  (selected.card.factorial : ℂ)) *
                if (others \ selected).card ≤ 1 then (1 : ℂ) else 0) =
            ∑ _selected ∈ others.powersetCard k,
              (((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
                if others.card - k ≤ 1 then (1 : ℂ) else 0) := by
              apply Finset.sum_congr rfl
              intro selected hselected
              obtain ⟨hsubset, hcard⟩ :=
                Finset.mem_powersetCard.mp hselected
              rw [Finset.card_sdiff_of_subset hsubset, hcard]
          _ = (others.card.choose k : ℂ) *
                (((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
                  if others.card - k ≤ 1 then (1 : ℂ) else 0) := by
              simp [Finset.card_powersetCard, nsmul_eq_mul]
    _ = if others.Nonempty then (0 : ℂ) else 1 := by
      cases hcard : others.card with
      | zero =>
        have hempty : others = ∅ := Finset.card_eq_zero.mp hcard
        simp [hempty]
      | succ n =>
        have hnonempty : others.Nonempty :=
          Finset.card_pos.mp (by omega)
        simp only [hnonempty, ↓reduceIte]
        have hsubset : ({n, n + 1} : Finset ℕ) ⊆
            Finset.range (others.card + 1) := by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          simp only [Finset.mem_range]
          omega
        have hzero (k : ℕ) (hk : k ∈ Finset.range (others.card + 1))
            (hnot : k ∉ ({n, n + 1} : Finset ℕ)) :
            (others.card.choose k : ℂ) *
              (((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
                if others.card - k ≤ 1 then (1 : ℂ) else 0) = 0 := by
          have hlt : k < others.card + 1 := Finset.mem_range.mp hk
          have hne₁ : k ≠ n := by
            intro heq
            apply hnot
            simp [heq]
          have hne₂ : k ≠ n + 1 := by
            intro heq
            apply hnot
            simp [heq]
          have hlarge : ¬ others.card - k ≤ 1 := by
            omega
          simp [hlarge]
        calc
          (∑ k ∈ Finset.range (n + 1 + 1),
              ((n + 1).choose k : ℂ) *
                (((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
                  if n + 1 - k ≤ 1 then (1 : ℂ) else 0)) =
            ∑ k ∈ ({n, n + 1} : Finset ℕ),
              ((n + 1).choose k : ℂ) *
                (((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
                  if n + 1 - k ≤ 1 then (1 : ℂ) else 0) := by
              simpa [hcard] using
                (Finset.sum_subset hsubset hzero).symm
          _ = 0 := by
            simp [Nat.choose_succ_self_right,
              Nat.factorial_succ, pow_succ]
            split_ifs with h
            · ring
            · omega
theorem partitionMobius_sum {t : ℕ} (rows : Finset (Fin t)) :
    (∑ partition : Finpartition rows, partitionMobius partition) =
      if rows.card ≤ 1 then (1 : ℂ) else 0 := by
  classical
  induction rows using Finset.strongInduction with
  | H rows ih =>
    by_cases hempty : rows = ∅
    · subst rows
      let emptyPartition : Finpartition (∅ : Finset (Fin t)) :=
        Finpartition.empty (Finset (Fin t))
      have huniv :
          (Finset.univ :
            Finset (Finpartition (∅ : Finset (Fin t)))) =
              {emptyPartition} := by
        ext partition
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        change partition = Finpartition.empty (Finset (Fin t))
        exact partition_empty_eq partition
      rw [huniv]
      simp [partitionMobius, emptyPartition, Finpartition.empty]
    · obtain ⟨distinguished, hdistinguished⟩ :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      let weight : Finset (Fin t) → ℂ := fun block =>
        (-1 : ℂ) ^ (block.card - 1) *
          ((block.card - 1).factorial : ℂ)
      calc
        (∑ partition : Finpartition rows,
            partitionMobius partition) =
          ∑ partition : Finpartition rows,
            ∏ block ∈ partition.parts, weight block := by
              simp [partitionMobius, weight]
        _ = ∑ selected ∈ (rows.erase distinguished).powerset,
              weight (insert distinguished selected) *
                ∑ partition :
                    Finpartition (rows \ insert distinguished selected),
                  ∏ block ∈ partition.parts, weight block :=
              partition_weight_sum weight rows
                distinguished hdistinguished
        _ = ∑ selected ∈ (rows.erase distinguished).powerset,
              ((-1 : ℂ) ^ selected.card *
                (selected.card.factorial : ℂ)) *
                if ((rows.erase distinguished) \ selected).card ≤ 1
                  then (1 : ℂ) else 0 := by
              apply Finset.sum_congr rfl
              intro selected hselected
              have hsubset : selected ⊆ rows.erase distinguished :=
                Finset.mem_powerset.mp hselected
              have hnot : distinguished ∉ selected := by
                intro hmem
                exact Finset.notMem_erase distinguished rows (hsubset hmem)
              have hblock : insert distinguished selected ⊆ rows := by
                intro row hrow
                rcases Finset.mem_insert.mp hrow with hrow | hrow
                · simpa [hrow] using hdistinguished
                · exact (Finset.mem_erase.mp (hsubset hrow)).2
              have hnonempty :
                  (insert distinguished selected).Nonempty :=
                ⟨distinguished,
                  Finset.mem_insert_self distinguished selected⟩
              have hcomplement :
                  rows \ insert distinguished selected =
                    (rows.erase distinguished) \ selected := by
                ext row
                simp [Finset.mem_sdiff, Finset.mem_erase,
                  Finset.mem_insert, and_assoc, and_left_comm]
              have hinner :
                  (∑ partition :
                      Finpartition (rows \ insert distinguished selected),
                    ∏ block ∈ partition.parts, weight block) =
                    if (rows \ insert distinguished selected).card ≤ 1
                      then (1 : ℂ) else 0 := by
                calc
                  (∑ partition :
                      Finpartition (rows \ insert distinguished selected),
                    ∏ block ∈ partition.parts, weight block) =
                      ∑ partition :
                          Finpartition (rows \ insert distinguished selected),
                        partitionMobius partition := by
                          simp [partitionMobius, weight]
                  _ = if (rows \ insert distinguished selected).card ≤ 1
                        then (1 : ℂ) else 0 :=
                    ih (rows \ insert distinguished selected)
                      (Finset.sdiff_ssubset hblock hnonempty)
              rw [hinner, hcomplement]
              simp [weight, hnot]
        _ = if (rows.erase distinguished).Nonempty then (0 : ℂ) else 1 :=
              signed_factorial_powerset (rows.erase distinguished)
        _ = if rows.card ≤ 1 then (1 : ℂ) else 0 := by
              have hcard :
                  (rows.erase distinguished).card + 1 = rows.card := by
                rw [Finset.card_erase_of_mem hdistinguished]
                have hpos : 0 < rows.card := Finset.card_pos.mpr
                  ⟨distinguished, hdistinguished⟩
                omega
              by_cases hremaining : (rows.erase distinguished).Nonempty
              · have hnot : ¬ rows.card ≤ 1 := by
                  have hpos := Finset.card_pos.mpr hremaining
                  omega
                simp [hremaining, hnot]
              · have hzero : (rows.erase distinguished).card = 0 := by
                  apply Finset.card_eq_zero.mpr
                  exact Finset.not_nonempty_iff_eq_empty.mp hremaining
                have hsmall : rows.card ≤ 1 := by omega
                simp [hremaining, hsmall]
theorem eval_powerSum_sub_column_monomial (t s : ℕ)
    (point : Fin t × Fin s → ℂ) (column : Fin s)
    (block : Finset (Fin t)) :
    MvPolynomial.eval point (powerSum t s block) -
        ∏ row ∈ block, point (row, column) =
      ∑ other ∈ (Finset.univ : Finset (Fin s)).erase column,
        ∏ row ∈ block, point (row, other) := by
  classical
  simp only [powerSum, map_sum, map_prod, MvPolynomial.eval_X]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin s))
    (fun other => ∏ row ∈ block, point (row, other))
    (Finset.mem_univ column)]
  ring
theorem eval_partitionBlockFactor_excluded_columns (t s : ℕ)
    (point : Fin t × Fin s → ℂ) (column : Fin s)
    {rows : Finset (Fin t)} (partition : Finpartition rows) :
    MvPolynomial.eval (fun row => point (row, column))
        (partitionBlockFactor
          (fun block => MvPolynomial.eval point (powerSum t s block))
          partition) =
      ∏ block ∈ partition.parts,
        ∑ other ∈ (Finset.univ : Finset (Fin s)).erase column,
          ∏ row ∈ block, point (row, other) := by
  classical
  simp only [partitionBlockFactor, map_prod, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.prod_congr rfl
  intro block _
  exact eval_powerSum_sub_column_monomial t s point column block
theorem eval_partitionDerivative_excluded_columns
    (t s d : ℕ) (point : Fin t × Fin s → ℂ)
    (i : Fin t) (column : Fin s) :
    MvPolynomial.eval (fun row => point (row, column))
        (partitionDerivative t d i
          (fun block => MvPolynomial.eval point (powerSum t s block))) =
      ∑ rows ∈
          ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
        ∑ partition : Finpartition rows,
          partitionMobius partition *
            ∏ block ∈ partition.parts,
              ∑ other ∈ (Finset.univ : Finset (Fin s)).erase column,
                ∏ row ∈ block, point (row, other) := by
  classical
  simp only [partitionDerivative, map_sum, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro partition _
  rw [eval_partitionBlockFactor_excluded_columns]
noncomputable def columnAssignmentFiberPartition
    {t s : ℕ} (rows : Finset (Fin t)) (assignment : Fin t → Fin s) :
    Finpartition rows := by
  classical
  exact Finpartition.ofSetSetoid (Setoid.ker assignment) rows
theorem mem_columnAssignmentFiberPartition_part_iff
    {t s : ℕ} (rows : Finset (Fin t)) (assignment : Fin t → Fin s)
    (left right : Fin t) :
    right ∈ (columnAssignmentFiberPartition rows assignment).part left ↔
      left ∈ rows ∧ right ∈ rows ∧ assignment left = assignment right := by
  classical
  change right ∈
      (Finpartition.ofSetSetoid (Setoid.ker assignment) rows).part left ↔
    left ∈ rows ∧ right ∈ rows ∧ assignment left = assignment right
  exact Finpartition.mem_part_ofSetSetoid_iff_rel
    (s := Setoid.ker assignment) rows
theorem columnAssignmentFiberPartition_mobius_product
    {t s : ℕ} (rows : Finset (Fin t)) (assignment : Fin t → Fin s) :
    (∏ block ∈ (columnAssignmentFiberPartition rows assignment).parts,
      ∑ partition : Finpartition block, partitionMobius partition) =
      if Set.InjOn assignment (rows : Set (Fin t)) then (1 : ℂ) else 0 := by
  classical
  let fiber := columnAssignmentFiberPartition rows assignment
  by_cases hinj : Set.InjOn assignment (rows : Set (Fin t))
  · rw [if_pos hinj]
    apply Finset.prod_eq_one
    intro block hblock
    rw [partitionMobius_sum, if_pos]
    apply Finset.card_le_one.mpr
    intro left hleft right hright
    have hleft_rows : left ∈ rows := fiber.subset hblock hleft
    have hright_rows : right ∈ rows := fiber.subset hblock hright
    have hpart : fiber.part left = block :=
      fiber.part_eq_of_mem hblock hleft
    have hsame : assignment left = assignment right :=
      ((mem_columnAssignmentFiberPartition_part_iff
        rows assignment left right).mp (by
          change right ∈ fiber.part left
          rw [hpart]
          exact hright)).2.2
    exact hinj hleft_rows hright_rows hsame
  · rw [if_neg hinj]
    have hcollision : ∃ left ∈ rows, ∃ right ∈ rows,
        left ≠ right ∧ assignment left = assignment right := by
      by_contra hnone
      apply hinj
      intro left hleft right hright heq
      by_contra hne
      apply hnone
      exact ⟨left, hleft, right, hright, hne, heq⟩
    obtain ⟨left, hleft, right, hright, hne, hsame⟩ := hcollision
    let block := fiber.part left
    have hblock : block ∈ fiber.parts := fiber.part_mem.mpr hleft
    apply Finset.prod_eq_zero hblock
    rw [partitionMobius_sum, if_neg]
    intro hsmall
    have hleft_block : left ∈ block := fiber.mem_part hleft
    have hright_block : right ∈ block :=
      (mem_columnAssignmentFiberPartition_part_iff
        rows assignment left right).mpr ⟨hleft, hright, hsame⟩
    exact hne ((Finset.card_le_one.mp hsmall)
      left hleft_block right hright_block)
theorem partition_mem_restrict_of_refinement
    {α : Type*} [DecidableEq α] {rows : Finset α}
    {fine coarse : Finpartition rows} (hrefine : fine ≤ coarse)
    {coarseBlock : Finset α} (hcoarseBlock : coarseBlock ∈ coarse.parts)
    {block : Finset α} :
    block ∈ (fine.restrict (coarse.subset hcoarseBlock)).parts ↔
      block ∈ fine.parts ∧ block ⊆ coarseBlock := by
  change block ∈
    (fine.parts.image (fun part => part ⊓ coarseBlock)).erase ∅ ↔ _
  constructor
  · intro hblock
    obtain ⟨hne, himage⟩ := Finset.mem_erase.mp hblock
    obtain ⟨part, hpart_mem, heq⟩ := Finset.mem_image.mp himage
    obtain ⟨containing, hcontaining, hsubset⟩ := hrefine hpart_mem
    obtain ⟨row, hrow⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hintersection : row ∈ part ⊓ coarseBlock := by
      rw [heq]
      exact hrow
    have hrowpart : row ∈ part :=
      (Finset.mem_inter.mp hintersection).1
    have hrowcoarse : row ∈ coarseBlock :=
      (Finset.mem_inter.mp hintersection).2
    have hcoarse : containing = coarseBlock :=
      coarse.eq_of_mem_parts hcontaining hcoarseBlock
        (hsubset hrowpart) hrowcoarse
    have hpartsubset : part ⊆ coarseBlock := hcoarse ▸ hsubset
    have hpart_eq : part = block := by
      calc
        part = part ⊓ coarseBlock := (inf_eq_left.mpr hpartsubset).symm
        _ = block := heq
    exact ⟨hpart_eq ▸ hpart_mem, hpart_eq ▸ hpartsubset⟩
  · rintro ⟨hblock, hsubset⟩
    refine Finset.mem_erase.mpr ⟨fine.ne_empty hblock, ?_⟩
    exact Finset.mem_image.mpr
      ⟨block, hblock, inf_eq_left.mpr hsubset⟩
theorem partition_bind_refines
    {α : Type*} [DecidableEq α] {rows : Finset α}
    (coarse : Finpartition rows)
    (refinements : ∀ block : coarse.parts, Finpartition block.val) :
    coarse.bind (fun block hblock => refinements ⟨block, hblock⟩) ≤ coarse := by
  intro block hblock
  obtain ⟨containing, hcontaining, hmember⟩ :=
    Finpartition.mem_bind.mp hblock
  exact ⟨containing, hcontaining,
    (refinements ⟨containing, hcontaining⟩).subset hmember⟩
noncomputable def partitionRefinementEquiv
    {α : Type*} [DecidableEq α] {rows : Finset α}
    (coarse : Finpartition rows) :
    {fine : Finpartition rows // fine ≤ coarse} ≃
      (∀ block : coarse.parts, Finpartition block.val) where
  toFun fine block := fine.val.restrict (coarse.subset block.property)
  invFun refinements :=
    ⟨coarse.bind (fun block hblock => refinements ⟨block, hblock⟩),
      partition_bind_refines coarse refinements⟩
  left_inv fine := by
    apply Subtype.ext
    apply Finpartition.ext
    ext block
    change
      block ∈
        (coarse.bind (fun part hpart =>
          fine.val.restrict (coarse.subset hpart))).parts ↔
        block ∈ fine.val.parts
    rw [Finpartition.mem_bind]
    constructor
    · rintro ⟨part, hpart, hblock⟩
      exact (partition_mem_restrict_of_refinement
        fine.property hpart).mp hblock |>.1
    · intro hblock
      obtain ⟨part, hpart, hsubset⟩ := fine.property hblock
      exact ⟨part, hpart,
        (partition_mem_restrict_of_refinement
          fine.property hpart).mpr ⟨hblock, hsubset⟩⟩
  right_inv refinements := by
    funext block
    apply Finpartition.ext
    ext part
    change
      part ∈
        ((coarse.bind (fun other hother =>
          refinements ⟨other, hother⟩)).restrict
            (coarse.subset block.property)).parts ↔
        part ∈ (refinements block).parts
    rw [partition_mem_restrict_of_refinement
      (partition_bind_refines coarse refinements) block.property,
      Finpartition.mem_bind]
    constructor
    · rintro ⟨⟨other, hother, hpart⟩, hsubset⟩
      obtain ⟨row, hrow⟩ :=
        (refinements ⟨other, hother⟩).nonempty_of_mem_parts hpart
      have hrowother : row ∈ other :=
        (refinements ⟨other, hother⟩).subset hpart hrow
      have hrowblock : row ∈ block.val := hsubset hrow
      have heq : other = block.val :=
        coarse.eq_of_mem_parts hother block.property hrowother hrowblock
      subst other
      exact hpart
    · intro hpart
      exact ⟨⟨block.val, block.property, hpart⟩,
        (refinements block).subset hpart⟩
theorem partitionMobius_bind
    {t : ℕ} {rows : Finset (Fin t)} (coarse : Finpartition rows)
    (refinements : ∀ block : coarse.parts, Finpartition block.val) :
    partitionMobius
        (coarse.bind
          (fun block hblock => refinements ⟨block, hblock⟩)) =
      ∏ block : coarse.parts, partitionMobius (refinements block) := by
  classical
  unfold partitionMobius
  rw [Finpartition.bind_parts]
  rw [Finset.prod_biUnion]
  · simp
  · intro left _ right _ hne
    change Disjoint (refinements left).parts (refinements right).parts
    rw [Finset.disjoint_left]
    intro block hleft hright
    have hsubsetleft : block ⊆ left.val :=
      (refinements left).subset hleft
    have hsubsetright : block ⊆ right.val :=
      (refinements right).subset hright
    obtain ⟨row, hrow⟩ :=
      (refinements left).nonempty_of_mem_parts hleft
    have heq : left.val = right.val :=
      coarse.eq_of_mem_parts left.property right.property
        (hsubsetleft hrow) (hsubsetright hrow)
    exact hne (Subtype.ext heq)
theorem partitionMobius_sum_refinements
    {t : ℕ} {rows : Finset (Fin t)} (coarse : Finpartition rows)
    [DecidablePred (fun fine : Finpartition rows => fine ≤ coarse)] :
    (∑ fine : {fine : Finpartition rows // fine ≤ coarse},
      partitionMobius fine.val) =
      ∏ block : coarse.parts,
        ∑ refinement : Finpartition block.val,
          partitionMobius refinement := by
  classical
  calc
    (∑ fine : {fine : Finpartition rows // fine ≤ coarse},
        partitionMobius fine.val) =
      ∑ refinements : ∀ block : coarse.parts, Finpartition block.val,
        partitionMobius
          (coarse.bind
            (fun block hblock => refinements ⟨block, hblock⟩)) := by
        apply Fintype.sum_equiv (partitionRefinementEquiv coarse)
        intro fine
        exact congrArg partitionMobius
          (congrArg Subtype.val
            ((partitionRefinementEquiv coarse).left_inv fine)).symm
    _ = ∑ refinements : ∀ block : coarse.parts, Finpartition block.val,
          ∏ block : coarse.parts, partitionMobius (refinements block) := by
      apply Finset.sum_congr rfl
      intro refinements _
      exact partitionMobius_bind coarse refinements
    _ = ∏ block : coarse.parts,
          ∑ refinement : Finpartition block.val,
            partitionMobius refinement :=
      (Fintype.prod_sum
        (fun block : coarse.parts =>
          fun refinement : Finpartition block.val =>
            partitionMobius refinement)).symm
theorem columnAssignmentFiberPartition_mobius_sum_refinements
    {t s : ℕ} (rows : Finset (Fin t)) (assignment : Fin t → Fin s)
    [DecidablePred (fun fine : Finpartition rows =>
      fine ≤ columnAssignmentFiberPartition rows assignment)] :
    (∑ fine : {fine : Finpartition rows //
        fine ≤ columnAssignmentFiberPartition rows assignment},
      partitionMobius fine.val) =
      if Set.InjOn assignment (rows : Set (Fin t)) then (1 : ℂ) else 0 := by
  classical
  let coarse := columnAssignmentFiberPartition rows assignment
  calc
    (∑ fine : {fine : Finpartition rows //
          fine ≤ columnAssignmentFiberPartition rows assignment},
        partitionMobius fine.val) =
      ∏ block : coarse.parts,
        ∑ refinement : Finpartition block.val,
          partitionMobius refinement :=
      partitionMobius_sum_refinements coarse
    _ = ∏ block ∈ coarse.parts,
          ∑ refinement : Finpartition block,
            partitionMobius refinement :=
      Finset.prod_coe_sort coarse.parts
        (fun block : Finset (Fin t) =>
          ∑ refinement : Finpartition block, partitionMobius refinement)
    _ = if Set.InjOn assignment (rows : Set (Fin t))
          then (1 : ℂ) else 0 :=
      columnAssignmentFiberPartition_mobius_product rows assignment
theorem partition_refines_columnAssignmentFiberPartition_iff
    {t s : ℕ} (rows : Finset (Fin t)) (assignment : Fin t → Fin s)
    (partition : Finpartition rows) :
    partition ≤ columnAssignmentFiberPartition rows assignment ↔
      ∀ block ∈ partition.parts,
        ∀ left ∈ block, ∀ right ∈ block,
          assignment left = assignment right := by
  classical
  let fiber := columnAssignmentFiberPartition rows assignment
  constructor
  · intro hrefine block hblock left hleft right hright
    obtain ⟨containing, hcontaining, hsubset⟩ := hrefine hblock
    have hpart : fiber.part left = containing :=
      fiber.part_eq_of_mem hcontaining (hsubset hleft)
    exact ((mem_columnAssignmentFiberPartition_part_iff
      rows assignment left right).mp (by
        change right ∈ fiber.part left
        rw [hpart]
        exact hsubset hright)).2.2
  · intro hconstant block hblock
    obtain ⟨left, hleft⟩ := partition.nonempty_of_mem_parts hblock
    have hleft_rows : left ∈ rows := partition.subset hblock hleft
    refine ⟨fiber.part left, fiber.part_mem.mpr hleft_rows, ?_⟩
    intro right hright
    have hright_rows : right ∈ rows := partition.subset hblock hright
    exact (mem_columnAssignmentFiberPartition_part_iff
      rows assignment left right).mpr
      ⟨hleft_rows, hright_rows,
        hconstant block hblock left hleft right hright⟩
noncomputable def partitionBlockRepresentative
    {α : Type*} [DecidableEq α] {rows : Finset α}
    (partition : Finpartition rows) (block : partition.parts) : rows :=
  ⟨Classical.choose (partition.nonempty_of_mem_parts block.property),
    partition.subset block.property
      (Classical.choose_spec
        (partition.nonempty_of_mem_parts block.property))⟩
theorem partitionBlockRepresentative_mem
    {α : Type*} [DecidableEq α] {rows : Finset α}
    (partition : Finpartition rows) (block : partition.parts) :
    (partitionBlockRepresentative partition block).val ∈ block.val :=
  Classical.choose_spec (partition.nonempty_of_mem_parts block.property)
noncomputable def partitionBlockAssignmentEquiv
    {α column : Type*} [DecidableEq α] {rows : Finset α}
    (partition : Finpartition rows) :
    (partition.parts → column) ≃
      {assignment : rows → column //
        ∀ (block : Finset α) (hblock : block ∈ partition.parts)
          (left : α) (hleft : left ∈ block)
          (right : α) (hright : right ∈ block),
          assignment ⟨left, partition.subset hblock hleft⟩ =
            assignment ⟨right, partition.subset hblock hright⟩} where
  toFun assignment :=
    ⟨fun row => assignment
      ⟨partition.part row.val, partition.part_mem.mpr row.property⟩, by
      intro block hblock left hleft right hright
      have hleftpart : partition.part left = block :=
        partition.part_eq_of_mem hblock hleft
      have hrightpart : partition.part right = block :=
        partition.part_eq_of_mem hblock hright
      exact congrArg assignment
        (Subtype.ext (hleftpart.trans hrightpart.symm))⟩
  invFun assignment block :=
    assignment.val (partitionBlockRepresentative partition block)
  left_inv assignment := by
    funext block
    change assignment
      ⟨partition.part (partitionBlockRepresentative partition block).val,
        _⟩ = assignment block
    apply congrArg assignment
    exact Subtype.ext
      (partition.part_eq_of_mem block.property
        (partitionBlockRepresentative_mem partition block))
  right_inv assignment := by
    apply Subtype.ext
    funext row
    change assignment.val
      (partitionBlockRepresentative partition
        ⟨partition.part row.val,
          partition.part_mem.mpr row.property⟩) = assignment.val row
    exact assignment.property (partition.part row.val)
      (partition.part_mem.mpr row.property)
      (partitionBlockRepresentative partition
        ⟨partition.part row.val,
          partition.part_mem.mpr row.property⟩).val
      (partitionBlockRepresentative_mem partition
        ⟨partition.part row.val,
          partition.part_mem.mpr row.property⟩)
      row.val (partition.mem_part row.property)
theorem partitionBlockAssignmentEquiv_prod
    {α column R : Type*} [DecidableEq α] [CommMonoid R]
    {rows : Finset α} (partition : Finpartition rows)
    (assignment : partition.parts → column)
    (weight : α → column → R) :
    (∏ block : partition.parts,
      ∏ row : block.val, weight row.val (assignment block)) =
      ∏ row : rows,
        weight row.val
          ((partitionBlockAssignmentEquiv partition assignment).val row) := by
  classical
  calc
    (∏ block : partition.parts,
        ∏ row : block.val, weight row.val (assignment block)) =
      ∏ entry : (Σ block : partition.parts, block.val),
        weight entry.2.val (assignment entry.1) :=
      (Fintype.prod_sigma
        (fun entry : (Σ block : partition.parts, block.val) =>
          weight entry.2.val (assignment entry.1))).symm
    _ = ∏ row : rows,
          weight row.val
            ((partitionBlockAssignmentEquiv partition assignment).val row) := by
      apply Fintype.prod_equiv partition.equivSigmaParts.symm
      intro entry
      change weight entry.2.val (assignment entry.1) =
        weight entry.2.val
          (assignment
            ⟨partition.part entry.2.val, _⟩)
      congr 1
      apply congrArg assignment
      apply Subtype.ext
      exact (partition.part_eq_of_mem entry.1.property
        entry.2.property).symm
theorem partition_block_assignment_sum_comm
    {t : ℕ} {column : Type*} [Fintype column] [DecidableEq column]
    {rows : Finset (Fin t)} (weight : Fin t → column → ℂ) :
    (∑ partition : Finpartition rows,
      partitionMobius partition *
        ∑ assignment : partition.parts → column,
          ∏ block : partition.parts,
            ∏ row : block.val, weight row.val (assignment block)) =
      ∑ assignment : rows → column,
        (∏ row : rows, weight row.val (assignment row)) *
          ∑ partition ∈
              (Finset.univ : Finset (Finpartition rows)).filter
                (fun partition =>
                  ∀ (block : Finset (Fin t))
                    (hblock : block ∈ partition.parts)
                    (left : Fin t) (hleft : left ∈ block)
                    (right : Fin t) (hright : right ∈ block),
                    assignment ⟨left, partition.subset hblock hleft⟩ =
                      assignment ⟨right, partition.subset hblock hright⟩),
            partitionMobius partition := by
  classical
  let compatible (partition : Finpartition rows)
      (assignment : rows → column) : Prop :=
    ∀ (block : Finset (Fin t)) (hblock : block ∈ partition.parts)
      (left : Fin t) (hleft : left ∈ block)
      (right : Fin t) (hright : right ∈ block),
      assignment ⟨left, partition.subset hblock hleft⟩ =
        assignment ⟨right, partition.subset hblock hright⟩
  calc
    (∑ partition : Finpartition rows,
      partitionMobius partition *
        ∑ assignment : partition.parts → column,
          ∏ block : partition.parts,
            ∏ row : block.val, weight row.val (assignment block)) =
      ∑ partition : Finpartition rows,
        ∑ assignment : partition.parts → column,
          partitionMobius partition *
            ∏ block : partition.parts,
              ∏ row : block.val, weight row.val (assignment block) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ partition : Finpartition rows,
          ∑ assignment : {assignment : rows → column //
            compatible partition assignment},
            partitionMobius partition *
              ∏ row : rows, weight row.val (assignment.val row) := by
        apply Finset.sum_congr rfl
        intro partition _
        apply Fintype.sum_equiv (partitionBlockAssignmentEquiv partition)
        intro assignment
        congr 1
        exact partitionBlockAssignmentEquiv_prod
          partition assignment weight
    _ = ∑ partition : Finpartition rows,
          ∑ assignment : rows → column,
            if compatible partition assignment then
              partitionMobius partition *
                ∏ row : rows, weight row.val (assignment row)
            else 0 := by
        apply Finset.sum_congr rfl
        intro partition _
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype
          ((Finset.univ : Finset (rows → column)).filter
            (compatible partition))
          (by simp)
          (fun assignment : rows → column =>
            partitionMobius partition *
              ∏ row : rows, weight row.val (assignment row))).symm
    _ = ∑ assignment : rows → column,
          ∑ partition : Finpartition rows,
            if compatible partition assignment then
              partitionMobius partition *
                ∏ row : rows, weight row.val (assignment row)
            else 0 := Finset.sum_comm
    _ = ∑ assignment : rows → column,
          (∏ row : rows, weight row.val (assignment row)) *
            ∑ partition ∈
                (Finset.univ : Finset (Finpartition rows)).filter
                  (compatible · assignment),
              partitionMobius partition := by
        apply Finset.sum_congr rfl
        intro assignment _
        rw [Finset.mul_sum, ← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro partition _
        ac_rfl
    _ = _ := rfl
noncomputable def selectedRowAssignmentExtend
    {t s : ℕ} (rows : Finset (Fin t))
    (assignment : rows → Fin s) (defaultColumn : Fin s) : Fin t → Fin s :=
  fun row => if hrow : row ∈ rows then assignment ⟨row, hrow⟩ else defaultColumn
@[simp] theorem selectedRowAssignmentExtend_apply
    {t s : ℕ} (rows : Finset (Fin t))
    (assignment : rows → Fin s) (defaultColumn : Fin s) (row : rows) :
    selectedRowAssignmentExtend rows assignment defaultColumn row.val =
      assignment row := by
  classical
  simp [selectedRowAssignmentExtend, row.property]
theorem selectedRowAssignmentExtend_injOn_iff
    {t s : ℕ} (rows : Finset (Fin t))
    (assignment : rows → Fin s) (defaultColumn : Fin s) :
    Set.InjOn (selectedRowAssignmentExtend rows assignment defaultColumn)
        (rows : Set (Fin t)) ↔
      Function.Injective assignment := by
  classical
  constructor
  · intro hinj left right heq
    apply Subtype.ext
    apply hinj left.property right.property
    simpa only [selectedRowAssignmentExtend_apply] using heq
  · intro hinj left hleft right hright heq
    have hvalues :
        assignment ⟨left, hleft⟩ = assignment ⟨right, hright⟩ := by
      calc
        assignment ⟨left, hleft⟩ =
            selectedRowAssignmentExtend rows assignment defaultColumn left :=
          (selectedRowAssignmentExtend_apply rows assignment
            defaultColumn ⟨left, hleft⟩).symm
        _ = selectedRowAssignmentExtend rows assignment
            defaultColumn right := heq
        _ = assignment ⟨right, hright⟩ :=
          selectedRowAssignmentExtend_apply rows assignment
            defaultColumn ⟨right, hright⟩
    exact congrArg Subtype.val (hinj hvalues)
theorem selectedRowAssignment_mobius_sum_refinements
    {t s : ℕ} (rows : Finset (Fin t))
    (assignment : rows → Fin s) (defaultColumn : Fin s)
    [DecidablePred (fun fine : Finpartition rows =>
      fine ≤ columnAssignmentFiberPartition rows
        (selectedRowAssignmentExtend rows assignment defaultColumn))] :
    (∑ fine : {fine : Finpartition rows //
        fine ≤ columnAssignmentFiberPartition rows
          (selectedRowAssignmentExtend rows assignment defaultColumn)},
      partitionMobius fine.val) =
      if Function.Injective assignment then (1 : ℂ) else 0 := by
  classical
  rw [columnAssignmentFiberPartition_mobius_sum_refinements]
  by_cases hinj : Function.Injective assignment
  · rw [if_pos hinj, if_pos
      ((selectedRowAssignmentExtend_injOn_iff
        rows assignment defaultColumn).mpr hinj)]
  · rw [if_neg hinj, if_neg]
    intro hextend
    exact hinj ((selectedRowAssignmentExtend_injOn_iff
      rows assignment defaultColumn).mp hextend)
theorem selectedRowAssignment_partitionMobius_filter_sum
    {t s : ℕ} (rows : Finset (Fin t))
    (assignment : rows → Fin s) (defaultColumn : Fin s) :
    (∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            ∀ (block : Finset (Fin t))
              (hblock : block ∈ partition.parts)
              (left : Fin t) (hleft : left ∈ block)
              (right : Fin t) (hright : right ∈ block),
              assignment ⟨left, partition.subset hblock hleft⟩ =
                assignment ⟨right, partition.subset hblock hright⟩),
      partitionMobius partition) =
      if Function.Injective assignment then (1 : ℂ) else 0 := by
  classical
  let extended := selectedRowAssignmentExtend rows assignment defaultColumn
  let fiber := columnAssignmentFiberPartition rows extended
  have hcompatible (partition : Finpartition rows) :
      (∀ (block : Finset (Fin t)) (hblock : block ∈ partition.parts)
        (left : Fin t) (hleft : left ∈ block)
        (right : Fin t) (hright : right ∈ block),
        assignment ⟨left, partition.subset hblock hleft⟩ =
          assignment ⟨right, partition.subset hblock hright⟩) ↔
        partition ≤ fiber := by
    rw [partition_refines_columnAssignmentFiberPartition_iff]
    constructor
    · intro hconstant block hblock left hleft right hright
      have hleft_rows := partition.subset hblock hleft
      have hright_rows := partition.subset hblock hright
      change extended left = extended right
      change
        selectedRowAssignmentExtend rows assignment defaultColumn left =
          selectedRowAssignmentExtend rows assignment defaultColumn right
      rw [selectedRowAssignmentExtend_apply rows assignment
        defaultColumn ⟨left, hleft_rows⟩,
        selectedRowAssignmentExtend_apply rows assignment
          defaultColumn ⟨right, hright_rows⟩]
      exact hconstant block hblock left hleft right hright
    · intro hconstant block hblock left hleft right hright
      have hleft_rows := partition.subset hblock hleft
      have hright_rows := partition.subset hblock hright
      have heq := hconstant block hblock left hleft right hright
      change extended left = extended right at heq
      change
        selectedRowAssignmentExtend rows assignment defaultColumn left =
          selectedRowAssignmentExtend rows assignment defaultColumn right
        at heq
      rw [selectedRowAssignmentExtend_apply rows assignment
        defaultColumn ⟨left, hleft_rows⟩,
        selectedRowAssignmentExtend_apply rows assignment
          defaultColumn ⟨right, hright_rows⟩] at heq
      exact heq
  calc
    (∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            ∀ (block : Finset (Fin t))
              (hblock : block ∈ partition.parts)
              (left : Fin t) (hleft : left ∈ block)
              (right : Fin t) (hright : right ∈ block),
              assignment ⟨left, partition.subset hblock hleft⟩ =
                assignment ⟨right, partition.subset hblock hright⟩),
      partitionMobius partition) =
      ∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition => partition ≤ fiber),
        partitionMobius partition := by
        apply Finset.sum_congr
        · ext partition
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hcompatible partition
        · intro partition _
          rfl
    _ = ∑ partition : {partition : Finpartition rows // partition ≤ fiber},
        partitionMobius partition.val := by
      apply Finset.sum_subtype
      intro partition
      simp
    _ = if Function.Injective assignment then (1 : ℂ) else 0 :=
      selectedRowAssignment_mobius_sum_refinements
        rows assignment defaultColumn
theorem excludedColumnAssignment_partitionMobius_filter_sum
    {t s : ℕ} (rows : Finset (Fin t)) (excluded : Fin s)
    (assignment : rows → {column : Fin s // column ≠ excluded}) :
    (∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            ∀ (block : Finset (Fin t))
              (hblock : block ∈ partition.parts)
              (left : Fin t) (hleft : left ∈ block)
              (right : Fin t) (hright : right ∈ block),
              assignment ⟨left, partition.subset hblock hleft⟩ =
                assignment ⟨right, partition.subset hblock hright⟩),
      partitionMobius partition) =
      if Function.Injective assignment then (1 : ℂ) else 0 := by
  classical
  let raw : rows → Fin s := fun row => (assignment row).val
  have hinj : Function.Injective raw ↔ Function.Injective assignment := by
    constructor
    · intro hraw left right heq
      apply hraw
      exact congrArg Subtype.val heq
    · intro hassignment left right heq
      apply hassignment
      exact Subtype.ext heq
  calc
    (∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            ∀ (block : Finset (Fin t))
              (hblock : block ∈ partition.parts)
              (left : Fin t) (hleft : left ∈ block)
              (right : Fin t) (hright : right ∈ block),
              assignment ⟨left, partition.subset hblock hleft⟩ =
                assignment ⟨right, partition.subset hblock hright⟩),
      partitionMobius partition) =
      ∑ partition ∈
        (Finset.univ : Finset (Finpartition rows)).filter
          (fun partition =>
            ∀ (block : Finset (Fin t))
              (hblock : block ∈ partition.parts)
              (left : Fin t) (hleft : left ∈ block)
              (right : Fin t) (hright : right ∈ block),
              raw ⟨left, partition.subset hblock hleft⟩ =
                raw ⟨right, partition.subset hblock hright⟩),
        partitionMobius partition := by
          apply Finset.sum_congr
          · ext partition
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hconstant block hblock left hleft right hright
              exact congrArg Subtype.val
                (hconstant block hblock left hleft right hright)
            · intro hconstant block hblock left hleft right hright
              exact Subtype.ext
                (hconstant block hblock left hleft right hright)
          · intro partition _
            rfl
    _ = if Function.Injective raw then (1 : ℂ) else 0 :=
      selectedRowAssignment_partitionMobius_filter_sum
        rows raw excluded
    _ = if Function.Injective assignment then (1 : ℂ) else 0 := by
      by_cases hassignment : Function.Injective assignment
      · rw [if_pos hassignment, if_pos (hinj.mpr hassignment)]
      · rw [if_neg hassignment, if_neg]
        exact fun hraw => hassignment (hinj.mp hraw)
theorem partitionMobius_excluded_columns_eq_embeddings
    (t s : ℕ) (point : Fin t × Fin s → ℂ) (excluded : Fin s)
    (rows : Finset (Fin t)) :
    (∑ partition : Finpartition rows,
      partitionMobius partition *
        ∏ block ∈ partition.parts,
          ∑ other ∈ (Finset.univ : Finset (Fin s)).erase excluded,
            ∏ row ∈ block, point (row, other)) =
      ∑ embedding : rows ↪ {column : Fin s // column ≠ excluded},
        ∏ row : rows, point (row.val, (embedding row).val) := by
  classical
  let column := {column : Fin s // column ≠ excluded}
  let weight : Fin t → column → ℂ :=
    fun row other => point (row, other.val)
  have hblock (block : Finset (Fin t)) :
      (∑ other ∈ (Finset.univ : Finset (Fin s)).erase excluded,
        ∏ row ∈ block, point (row, other)) =
      ∑ other : column,
        ∏ row : block, weight row.val other := by
    calc
      (∑ other ∈ (Finset.univ : Finset (Fin s)).erase excluded,
        ∏ row ∈ block, point (row, other)) =
        ∑ other ∈ (Finset.univ : Finset (Fin s)).erase excluded,
          ∏ row : block, point (row.val, other) := by
          apply Finset.sum_congr rfl
          intro other _
          exact (Finset.prod_coe_sort block
            (fun row => point (row, other))).symm
      _ = ∑ other : column,
          ∏ row : block, weight row.val other := by
        apply Finset.sum_subtype
        intro other
        simp [ne_comm]
  calc
    (∑ partition : Finpartition rows,
      partitionMobius partition *
        ∏ block ∈ partition.parts,
          ∑ other ∈ (Finset.univ : Finset (Fin s)).erase excluded,
            ∏ row ∈ block, point (row, other)) =
      ∑ partition : Finpartition rows,
        partitionMobius partition *
          ∑ assignment : partition.parts → column,
            ∏ block : partition.parts,
              ∏ row : block.val,
                weight row.val (assignment block) := by
        apply Finset.sum_congr rfl
        intro partition _
        congr 1
        calc
          (∏ block ∈ partition.parts,
            ∑ other ∈ (Finset.univ : Finset (Fin s)).erase excluded,
              ∏ row ∈ block, point (row, other)) =
            ∏ block : partition.parts,
              ∑ other ∈ (Finset.univ : Finset (Fin s)).erase excluded,
                ∏ row ∈ block.val, point (row, other) :=
              (Finset.prod_coe_sort partition.parts
                (fun block =>
                  ∑ other ∈
                    (Finset.univ : Finset (Fin s)).erase excluded,
                    ∏ row ∈ block, point (row, other))).symm
          _ = ∏ block : partition.parts,
                ∑ other : column,
                  ∏ row : block.val, weight row.val other := by
              apply Finset.prod_congr rfl
              intro block _
              exact hblock block.val
          _ = ∑ assignment : partition.parts → column,
                ∏ block : partition.parts,
                  ∏ row : block.val,
                    weight row.val (assignment block) :=
              Fintype.prod_sum
                (fun block : partition.parts =>
                  fun other : column =>
                    ∏ row : block.val, weight row.val other)
    _ = ∑ assignment : rows → column,
          (∏ row : rows, weight row.val (assignment row)) *
            ∑ partition ∈
                (Finset.univ : Finset (Finpartition rows)).filter
                  (fun partition =>
                    ∀ (block : Finset (Fin t))
                      (hblock : block ∈ partition.parts)
                      (left : Fin t) (hleft : left ∈ block)
                      (right : Fin t) (hright : right ∈ block),
                      assignment
                          ⟨left, partition.subset hblock hleft⟩ =
                        assignment
                          ⟨right, partition.subset hblock hright⟩),
              partitionMobius partition :=
      partition_block_assignment_sum_comm weight
    _ = ∑ assignment : rows → column,
          (∏ row : rows, weight row.val (assignment row)) *
            if Function.Injective assignment then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro assignment _
        congr 1
        exact excludedColumnAssignment_partitionMobius_filter_sum
          rows excluded assignment
    _ = ∑ assignment ∈
            (Finset.univ : Finset (rows → column)).filter
              Function.Injective,
          ∏ row : rows, weight row.val (assignment row) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro assignment _
        split <;> simp
    _ = ∑ assignment : {assignment : rows → column //
            Function.Injective assignment},
          ∏ row : rows, weight row.val (assignment.val row) := by
        apply Finset.sum_subtype
        intro assignment
        simp
    _ = ∑ embedding : rows ↪ column,
          ∏ row : rows, weight row.val (embedding row) := by
        apply Fintype.sum_equiv
          (Equiv.subtypeInjectiveEquivEmbedding rows column)
        intro assignment
        rfl
    _ = _ := rfl
theorem eval_partitionDerivative_eq_excluded_embeddings
    (t s d : ℕ) (point : Fin t × Fin s → ℂ)
    (i : Fin t) (excluded : Fin s) :
    MvPolynomial.eval (fun row => point (row, excluded))
        (partitionDerivative t d i
          (fun block => MvPolynomial.eval point (powerSum t s block))) =
      ∑ rows ∈
          ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
        ∑ embedding : rows ↪ {column : Fin s // column ≠ excluded},
          ∏ row : rows, point (row.val, (embedding row).val) := by
  classical
  rw [eval_partitionDerivative_excluded_columns]
  apply Finset.sum_congr rfl
  intro rows _
  exact partitionMobius_excluded_columns_eq_embeddings
    t s point excluded rows
theorem eval_minorSum_pderiv_eq_partitionDerivative
    (t s d : ℕ) (hd : 0 < d)
    (point : Fin t × Fin s → ℂ) (i : Fin t) (column : Fin s) :
    MvPolynomial.eval point
        (MvPolynomial.pderiv (i, column) (minorSum t s d)) =
      MvPolynomial.eval (fun row => point (row, column))
        (partitionDerivative t d i
          (fun block => MvPolynomial.eval point (powerSum t s block))) := by
  calc
    MvPolynomial.eval point
        (MvPolynomial.pderiv (i, column) (minorSum t s d)) =
      ∑ rows ∈
          ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
        ∑ embedding : rows ↪ {other : Fin s // other ≠ column},
          ∏ row : rows, point (row.val, (embedding row).val) :=
      eval_minorSum_pderiv_eq_excluded_embeddings t s d hd point i column
    _ = MvPolynomial.eval (fun row => point (row, column))
          (partitionDerivative t d i
            (fun block => MvPolynomial.eval point (powerSum t s block))) :=
      (eval_partitionDerivative_eq_excluded_embeddings
        t s d point i column).symm
end Standalone_PartitionInversion
section Standalone_Incidence
open scoped BigOperators
abbrev IncidenceRowBlock (t : ℕ) :=
  {block : Finset (Fin t) // block.Nonempty}
abbrev IncidenceParameter (t : ℕ) := IncidenceRowBlock t → ℂ
abbrev IncidenceColumns (t s : ℕ) := Fin s → Fin t → ℂ
noncomputable def incidenceParameterExtend {t : ℕ}
    (p : IncidenceParameter t) (block : Finset (Fin t)) : ℂ :=
  if h : block.Nonempty then p ⟨block, h⟩ else 0
@[simp] theorem incidenceParameterExtend_nonempty {t : ℕ}
    (p : IncidenceParameter t) (block : Finset (Fin t))
    (hblock : block.Nonempty) :
    incidenceParameterExtend p block = p ⟨block, hblock⟩ := by
  simp [incidenceParameterExtend, hblock]
theorem incidence_partitionBlockFactor_congr_of_nonempty {t : ℕ}
    (p q : Finset (Fin t) → ℂ)
    (h : ∀ block : Finset (Fin t), block.Nonempty → p block = q block)
    {rows : Finset (Fin t)} (partition : Finpartition rows) :
    partitionBlockFactor p partition = partitionBlockFactor q partition := by
  classical
  unfold partitionBlockFactor
  apply Finset.prod_congr rfl
  intro block hblock
  rw [h block (partition.nonempty_of_mem_parts hblock)]
theorem incidence_partitionDerivative_congr_of_nonempty
    (t d : ℕ) (i : Fin t) (p q : Finset (Fin t) → ℂ)
    (h : ∀ block : Finset (Fin t), block.Nonempty → p block = q block) :
    partitionDerivative t d i p = partitionDerivative t d i q := by
  classical
  unfold partitionDerivative
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro partition _
  rw [incidence_partitionBlockFactor_congr_of_nonempty p q h partition]
noncomputable def partitionFiberCoordinateEsymmPolynomial
    (t q : ℕ) : MvPolynomial (Fin t) ℂ :=
  MvPolynomial.esymm (Fin t) ℂ q
noncomputable def minorSumPowerParameters (t s : ℕ)
    (x : Fin t × Fin s → ℂ) : IncidenceParameter t :=
  fun block => MvPolynomial.eval x (powerSum t s block.1)
theorem partitionDerivative_incidencePowerParameters
    (t s d : ℕ) (x : Fin t × Fin s → ℂ) (i : Fin t) :
    partitionDerivative t d i
        (incidenceParameterExtend (minorSumPowerParameters t s x)) =
      partitionDerivative t d i
        (fun block => MvPolynomial.eval x (powerSum t s block)) := by
  apply incidence_partitionDerivative_congr_of_nonempty
  intro block hblock
  simp [incidenceParameterExtend, minorSumPowerParameters, hblock]
theorem eval_minorSum_pderiv_eq_incidencePartitionDerivative
    (t s d : ℕ) (hd : 0 < d)
    (x : Fin t × Fin s → ℂ) (i : Fin t) (a : Fin s) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv (i, a) (minorSum t s d)) =
      MvPolynomial.eval (fun j => x (j, a))
        (partitionDerivative t d i
          (incidenceParameterExtend (minorSumPowerParameters t s x))) := by
  rw [eval_minorSum_pderiv_eq_partitionDerivative t s d hd x i a]
  rw [partitionDerivative_incidencePowerParameters]
def minorSumColumns (t s : ℕ)
    (x : Fin t × Fin s → ℂ) : IncidenceColumns t s :=
  fun a i => x (i, a)
abbrev IncidenceCoordinate (t s : ℕ) :=
  IncidenceRowBlock t ⊕ (Fin s × Fin t)
def incidenceCoordinatePoint (t s : ℕ)
    (p : IncidenceParameter t) (columns : IncidenceColumns t s) :
    IncidenceCoordinate t s → ℂ :=
  Sum.elim p (fun coordinate => columns coordinate.1 coordinate.2)
noncomputable def partitionIncidenceEquation (t s d : ℕ)
    (a : Fin s) (i : Fin t) : MvPolynomial (IncidenceCoordinate t s) ℂ :=
  ∑ rows ∈ ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
    ∑ partition : Finpartition rows,
      MvPolynomial.C (partitionMobius partition) *
        ∏ block ∈ partition.parts.attach,
          (MvPolynomial.X
              (Sum.inl ⟨block.1,
                partition.nonempty_of_mem_parts block.2⟩) -
            ∏ row ∈ block.1,
              MvPolynomial.X (Sum.inr (a, row)))
theorem eval_partitionIncidenceEquation (t s d : ℕ)
    (p : IncidenceParameter t) (columns : IncidenceColumns t s)
    (a : Fin s) (i : Fin t) :
    MvPolynomial.eval (incidenceCoordinatePoint t s p columns)
        (partitionIncidenceEquation t s d a i) =
      MvPolynomial.eval (columns a)
        (partitionDerivative t d i (incidenceParameterExtend p)) := by
  classical
  simp only [partitionIncidenceEquation, partitionDerivative,
    partitionBlockFactor, map_sum, map_mul, map_prod, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X,
    incidenceCoordinatePoint]
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro partition _
  congr 1
  calc
    (∏ block ∈ partition.parts.attach,
        (p ⟨block.1, partition.nonempty_of_mem_parts block.2⟩ -
          ∏ row ∈ block.1, columns a row)) =
        ∏ block ∈ partition.parts.attach,
          (incidenceParameterExtend p block.1 -
            ∏ row ∈ block.1, columns a row) := by
      apply Finset.prod_congr rfl
      intro block _
      rw [incidenceParameterExtend_nonempty p block.1
        (partition.nonempty_of_mem_parts block.2)]
    _ = ∏ block ∈ partition.parts,
          (incidenceParameterExtend p block -
            ∏ row ∈ block, columns a row) :=
      Finset.prod_attach partition.parts
        (fun block => incidenceParameterExtend p block -
          ∏ row ∈ block, columns a row)
noncomputable def partitionIncidenceIdeal (t s d : ℕ) :
    Ideal (MvPolynomial (IncidenceCoordinate t s) ℂ) :=
  Ideal.span
    (Set.range fun coordinate : Fin s × Fin t =>
      partitionIncidenceEquation t s d coordinate.1 coordinate.2)
abbrev PartitionIncidenceCoordinateRing (t s d : ℕ) :=
  MvPolynomial (IncidenceCoordinate t s) ℂ ⧸
    partitionIncidenceIdeal t s d
noncomputable def partitionIncidenceGlobalBaseProjection
    (t s d : ℕ) :
    MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ →ₐ[ℂ]
      PartitionIncidenceCoordinateRing t s d :=
  MvPolynomial.aeval (Sum.elim
    (fun block =>
      Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
        (MvPolynomial.X (Sum.inl block)))
    (fun coordinate =>
      Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
        (MvPolynomial.rename
          (fun row : Fin t => Sum.inr (coordinate.1, row))
          (partitionFiberCoordinateEsymmPolynomial t
            (coordinate.2.val + 1)))))
noncomputable abbrev partitionIncidenceGlobalBaseAlgebra
    (t s d : ℕ) :
    Algebra
      (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)
      (PartitionIncidenceCoordinateRing t s d) :=
  (partitionIncidenceGlobalBaseProjection t s d).toRingHom.toAlgebra
noncomputable def partitionIncidenceGlobalColumnLift
    (t s d : ℕ) :
    MvPolynomial (IncidenceCoordinate t s) ℂ →+*
      MvPolynomial (Fin s × Fin t)
        (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C :
      MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ →+*
        MvPolynomial (Fin s × Fin t)
          (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)).comp
      (MvPolynomial.C : ℂ →+*
        MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ))
    (Sum.elim
      (fun block : IncidenceRowBlock t =>
        MvPolynomial.C (MvPolynomial.X (Sum.inl block)))
      (fun coordinate : Fin s × Fin t => MvPolynomial.X coordinate))
noncomputable def partitionIncidenceGlobalPowerRemainder
    (t s d : ℕ) (coordinate : Fin s × Fin t) :
    MvPolynomial (Fin s × Fin t)
      (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ) :=
  let q := d - 1
  let k : ℂ := ((t - q : ℕ) : ℂ)
  let a : ℂ := (-1 : ℂ) ^ q * (q.factorial : ℂ)
  let embed : Fin t → IncidenceCoordinate t s :=
    fun row => Sum.inr (coordinate.1, row)
  let R : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ := fun row =>
    partitionIncidenceEquation t s d coordinate.1 row -
      MvPolynomial.C a *
        MvPolynomial.rename embed
          (deletedCoordinateEsymmPolynomial t q row)
  let low : MvPolynomial (Fin s × Fin t)
      (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ) :=
    ∑ j : Fin (d - 2),
      (-MvPolynomial.X coordinate) ^ (q - (j.val + 1)) *
        MvPolynomial.C (MvPolynomial.X (Sum.inr (coordinate.1, j)))
  MvPolynomial.C
      (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) *
    (MvPolynomial.C (MvPolynomial.C (k * a)) * low +
      MvPolynomial.C (MvPolynomial.C k) *
        partitionIncidenceGlobalColumnLift t s d (R coordinate.2) -
      ∑ row : Fin t,
        partitionIncidenceGlobalColumnLift t s d (R row))
noncomputable def incidenceUniversalPartitionBlockFactor
    {t : ℕ} {ι B : Type*} [CommRing B]
    (parameter : Finset (Fin t) → B) (index : Fin t → ι)
    {rows : Finset (Fin t)} (partition : Finpartition rows) :
    MvPolynomial ι B :=
  ∏ block ∈ partition.parts,
    (MvPolynomial.C (parameter block) -
      ∏ row ∈ block, MvPolynomial.X (index row))
noncomputable def incidenceUniversalPartitionDerivative
    {t : ℕ} {ι B : Type*} [CommRing B] [Algebra ℂ B]
    (d : ℕ) (i : Fin t)
    (parameter : Finset (Fin t) → B) (index : Fin t → ι) :
    MvPolynomial ι B :=
  ∑ rows ∈ ((Finset.univ : Finset (Fin t)).erase i).powersetCard (d - 1),
    ∑ partition : Finpartition rows,
      MvPolynomial.C (algebraMap ℂ B (partitionMobius partition)) *
        incidenceUniversalPartitionBlockFactor parameter index partition
noncomputable def partitionIncidenceGlobalUniversalParameter
    (t s d : ℕ) (block : Finset (Fin t)) :
    (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ) :=
  if h : block.Nonempty then
    MvPolynomial.X (Sum.inl ⟨block, h⟩)
  else 0
noncomputable def partitionIncidenceGlobalEquationRemainder
    (t s d : ℕ) (a : Fin s) (i : Fin t) :
    MvPolynomial (IncidenceCoordinate t s) ℂ :=
  partitionIncidenceEquation t s d a i -
    MvPolynomial.C
      (((-1 : ℂ) ^ (d - 1)) * ((d - 1).factorial : ℂ)) *
      MvPolynomial.rename
        (fun row : Fin t => (Sum.inr (a, row) : IncidenceCoordinate t s))
        (deletedCoordinateEsymmPolynomial t (d - 1) i)
noncomputable def minorSumGraphPullback
    (t s : ℕ) :
    MvPolynomial (IncidenceCoordinate t s) ℂ →ₐ[ℂ]
      MvPolynomial (Fin t × Fin s) ℂ :=
  MvPolynomial.aeval <| Sum.elim
    (fun block : IncidenceRowBlock t => powerSum t s block.1)
    (fun coordinate : Fin s × Fin t =>
      MvPolynomial.X (coordinate.2, coordinate.1))
theorem minorSumGraphPullback_eval
    (t s : ℕ) (point : Fin t × Fin s → ℂ)
    (f : MvPolynomial (IncidenceCoordinate t s) ℂ) :
    MvPolynomial.eval point
        (minorSumGraphPullback t s f) =
      MvPolynomial.eval
        (incidenceCoordinatePoint t s
          (minorSumPowerParameters t s point)
          (minorSumColumns t s point)) f := by
  change
    MvPolynomial.aeval point
      (MvPolynomial.aeval
        (Sum.elim
          (fun block : IncidenceRowBlock t => powerSum t s block.1)
          (fun coordinate : Fin s × Fin t =>
            MvPolynomial.X (coordinate.2, coordinate.1))) f) =
      MvPolynomial.aeval
        (incidenceCoordinatePoint t s
          (minorSumPowerParameters t s point)
          (minorSumColumns t s point)) f
  have hcoordinates :
      (fun coordinate : IncidenceCoordinate t s =>
        MvPolynomial.aeval point
          (Sum.elim
            (fun block : IncidenceRowBlock t => powerSum t s block.1)
            (fun coordinate : Fin s × Fin t =>
              MvPolynomial.X (coordinate.2, coordinate.1)) coordinate)) =
        incidenceCoordinatePoint t s
          (minorSumPowerParameters t s point)
          (minorSumColumns t s point) := by
    funext coordinate
    cases coordinate with
    | inl block =>
        simp [incidenceCoordinatePoint, minorSumPowerParameters,
          MvPolynomial.aeval_def]
    | inr coordinate =>
        simp [incidenceCoordinatePoint, minorSumColumns]
  rw [MvPolynomial.comp_aeval_apply, hcoordinates]
theorem minorSumGraphPullback_incidenceEquation
    (t s d : ℕ) (hd : 0 < d) (column : Fin s) (row : Fin t) :
    minorSumGraphPullback t s
        (partitionIncidenceEquation t s d column row) =
      MvPolynomial.pderiv (row, column) (minorSum t s d) := by
  apply MvPolynomial.funext
  intro point
  rw [minorSumGraphPullback_eval,
    eval_partitionIncidenceEquation]
  exact (eval_minorSum_pderiv_eq_incidencePartitionDerivative
    t s d hd point row column).symm
abbrev BlockIncidenceCoordinate (b t s : ℕ) :=
  Fin b × IncidenceCoordinate t s
abbrev BlockIncidenceColumn (b t s : ℕ) :=
  Fin b × (Fin s × Fin t)
abbrev BlockIncidenceBaseIndex (b t s d : ℕ) :=
  Fin b × (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2)))
noncomputable def blockIncidenceEquation (b t s d : ℕ)
    (coordinate : BlockIncidenceColumn b t s) :
    MvPolynomial (BlockIncidenceCoordinate b t s) ℂ :=
  MvPolynomial.rename
    (fun z : IncidenceCoordinate t s => (coordinate.1, z))
    (partitionIncidenceEquation t s d coordinate.2.1 coordinate.2.2)
noncomputable abbrev blockIncidenceIdeal (b t s d : ℕ) :
    Ideal (MvPolynomial (BlockIncidenceCoordinate b t s) ℂ) :=
  Ideal.span (Set.range (blockIncidenceEquation b t s d))
noncomputable abbrev BlockIncidenceCoordinateRing (b t s d : ℕ) :=
  MvPolynomial (BlockIncidenceCoordinate b t s) ℂ ⧸
    blockIncidenceIdeal b t s d
noncomputable def blockIncidenceBaseProjection (b t s d : ℕ) :
    MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ →ₐ[ℂ]
      BlockIncidenceCoordinateRing b t s d :=
  MvPolynomial.aeval fun coordinate =>
    match coordinate.2 with
    | Sum.inl block =>
        Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (coordinate.1, Sum.inl block))
    | Sum.inr column =>
        Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.rename
            (fun row : Fin t => (coordinate.1, Sum.inr (column.1, row)))
            (partitionFiberCoordinateEsymmPolynomial t
              (column.2.val + 1)))
noncomputable abbrev blockIncidenceBaseAlgebra (b t s d : ℕ) :
    Algebra (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
      (BlockIncidenceCoordinateRing b t s d) :=
  (blockIncidenceBaseProjection b t s d).toRingHom.toAlgebra
noncomputable def blockIncidenceBaseRename
    (b t s d : ℕ) (block : Fin b) :
    MvPolynomial
        (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ →+*
      (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ) :=
  (MvPolynomial.rename
    (fun coordinate : IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2)) =>
      (block, coordinate))).toRingHom
noncomputable def blockIncidencePowerRemainder
    (b t s d : ℕ)
    (coordinate : Fin b × (Fin s × Fin t)) :
    MvPolynomial (Fin b × (Fin s × Fin t))
      ((MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)) :=
  MvPolynomial.rename
    (fun row : Fin s × Fin t => (coordinate.1, row))
    (MvPolynomial.map
      (blockIncidenceBaseRename b t s d coordinate.1)
      (partitionIncidenceGlobalPowerRemainder t s d coordinate.2))
noncomputable def blockIncidenceSingleBlockInclusion
    (b t s d : ℕ) (block : Fin b) :
    PartitionIncidenceCoordinateRing t s d →ₐ[ℂ]
      BlockIncidenceCoordinateRing b t s d :=
  Ideal.Quotient.liftₐ (partitionIncidenceIdeal t s d)
    ((Ideal.Quotient.mkₐ ℂ
      (blockIncidenceIdeal b t s d)).comp
      (MvPolynomial.rename
        (fun z : IncidenceCoordinate t s => (block, z))))
    (by
      intro f hf
      rw [partitionIncidenceIdeal,
        Ideal.mem_span_range_iff_exists_fun] at hf
      obtain ⟨coefficients, hcoefficients⟩ := hf
      rw [← hcoefficients, map_sum]
      apply Finset.sum_eq_zero
      intro coordinate _
      rw [map_mul]
      have hgenerator :
          MvPolynomial.rename
            (fun z : IncidenceCoordinate t s => (block, z))
            (partitionIncidenceEquation t s d
              coordinate.1 coordinate.2) ∈
            blockIncidenceIdeal b t s d := by
        exact Ideal.subset_span
          ⟨(block, coordinate), rfl⟩
      have hzero :
          Ideal.Quotient.mk
            (blockIncidenceIdeal b t s d)
            (MvPolynomial.rename
              (fun z : IncidenceCoordinate t s => (block, z))
              (partitionIncidenceEquation t s d
                coordinate.1 coordinate.2)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hgenerator
      change _ *
        Ideal.Quotient.mk
          (blockIncidenceIdeal b t s d)
          (MvPolynomial.rename
            (fun z : IncidenceCoordinate t s => (block, z))
            (partitionIncidenceEquation t s d
              coordinate.1 coordinate.2)) = 0
      rw [hzero, mul_zero])
end Standalone_Incidence
section Standalone_SourceCircuitBridge
open scoped BigOperators
noncomputable section
noncomputable def sourceSlicedGradientLinearInput {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (j : Fin m) : FreeAffineInput (Fin k) where
  constant := 0
  inputCoefficients :=
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin k)).symm
      (fun i => W (Pi.single i 1) j)
noncomputable def sourceFreeAffineFormFiniteLinearCombination
    {ι α : Type*} [Fintype α]
    (coefficient : α → ℂ) (form : α → FreeAffineForm ι) :
    FreeAffineForm ι where
  constant := ∑ j, coefficient j * (form j).constant
  inputCoefficients := ∑ j, coefficient j • (form j).inputCoefficients
  gateCoefficients := ∑ j, coefficient j • (form j).gateCoefficients
noncomputable def sourceSlicedGradientReverseOutputForm
    {k m : ℕ}
    (circuit : FreeAffineCircuit (Fin m))
    (output : FreeAffineForm (Fin m))
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (i : Fin k) : FreeAffineForm (Fin k) :=
  sourceFreeAffineFormFiniteLinearCombination
    (fun j : Fin m => (A (Pi.single j 1)) i)
    (fun j : Fin m =>
      (((ReverseAdjoint.CircuitAdjoint.run circuit output).inputAdjoints j).substituteInputs
        (sourceSlicedGradientLinearInput W)))
noncomputable def freeAffineCircuitSquareFamily
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k)) (target : Fin k → ℂ) :
    Fin (Fintype.card (Fin k ⊕ Fin circuit.program.length)) →
      MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ :=
  fun i =>
    Fin.append
      (freeAffineCircuitInstructionEquation circuit)
      (fun j : Fin k =>
        freeAffineExtendedForm
          (n := circuit.program.length) (output j) -
          MvPolynomial.C (target j))
      (Fin.cast (by simp [Nat.add_comm]) i)
end
end Standalone_SourceCircuitBridge
section Standalone_TreeCoefficients
open scoped BigOperators
noncomputable def treeBlockVector {r : ℕ}
    (block : Finset (Fin r)) : Fin r → ℂ :=
  fun row => if row ∈ block then 1 else 0
noncomputable def treeQuotientLinearForm {r : ℕ}
    (vector : Fin r → ℂ) : SquareZeroAlgebra r :=
  ∑ row : Fin r,
    algebraMap ℂ (SquareZeroAlgebra r) (vector row) *
      squareZeroVariable r row
noncomputable def treeNodeVector {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (left right : BlockTree ι) (ζ : ℂ) (j : ℕ) : Fin r → ℂ :=
  fun row =>
    (∑ i ∈ left.leaves, treeBlockVector (blocks i) row) +
      (2 * ζ ^ j) *
        (∑ i ∈ right.leaves, treeBlockVector (blocks i) row)
noncomputable def treeLinearFormVectors {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (t d : ℕ) (ζ : ℂ) : BlockTree ι → List (Fin r → ℂ)
  | .leaf i => List.replicate (t - d) (treeBlockVector (blocks i))
  | .branch left right =>
      treeLinearFormVectors blocks t d ζ left ++
        treeLinearFormVectors blocks t d ζ right ++
          List.ofFn (fun j : Fin d =>
            treeNodeVector blocks left right ζ j)
theorem tree_leafList_length_pos {ι : Type*} (tree : BlockTree ι) :
    0 < tree.leafList.length := by
  induction tree with
  | leaf i => simp [BlockTree.leafList]
  | branch left right ihleft ihright =>
      simp only [BlockTree.leafList, List.length_append]
      omega
theorem treeLinearFormVectors_length {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (t d : ℕ) (hd : d ≤ t) (ζ : ℂ) (tree : BlockTree ι) :
    (treeLinearFormVectors blocks t d ζ tree).length =
      tree.leafList.length * t - d := by
  induction tree with
  | leaf i => simp [treeLinearFormVectors, BlockTree.leafList]
  | branch left right ihleft ihright =>
      have hleftone : 1 ≤ left.leafList.length :=
        tree_leafList_length_pos left
      have hrightone : 1 ≤ right.leafList.length :=
        tree_leafList_length_pos right
      have hleft : d ≤ left.leafList.length * t :=
        le_trans hd (by simpa using Nat.mul_le_mul_right t hleftone)
      have hright : d ≤ right.leafList.length * t :=
        le_trans hd (by simpa using Nat.mul_le_mul_right t hrightone)
      simp only [treeLinearFormVectors, List.length_append,
        List.length_ofFn, BlockTree.leafList, List.length_append,
        ihleft, ihright, Nat.add_mul]
      omega
noncomputable def treeLinearFormMatrix {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (t d : ℕ) (ζ : ℂ) (tree : BlockTree ι) :
    Matrix (Fin r)
      (Fin (treeLinearFormVectors blocks t d ζ tree).length) ℂ :=
  fun row column =>
    (treeLinearFormVectors blocks t d ζ tree).get column row
noncomputable def sourceRowBlock (b t : ℕ) (h : Fin b) :
    Finset (Fin (b * t)) :=
  (Finset.univ : Finset (Fin t)).image
    (fun j => (finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)) (h, j))
theorem mem_sourceRowBlock {b t : ℕ} (h : Fin b)
    (row : Fin (b * t)) :
    row ∈ sourceRowBlock b t h ↔
      ((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm row).1 = h := by
  classical
  constructor
  · intro hrow
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hrow
    subst row
    simp
  · intro hrow
    let e : Fin b × Fin t ≃ Fin (b * t) := finProdFinEquiv
    refine Finset.mem_image.mpr
      ⟨(e.symm row).2, Finset.mem_univ _, ?_⟩
    change e (h, (e.symm row).2) = row
    calc
      e (h, (e.symm row).2) =
          e ((e.symm row).1, (e.symm row).2) := by rw [hrow]
      _ = e (e.symm row) := by rw [Prod.eta]
      _ = row := e.apply_symm_apply row
theorem sourceRowBlock_disjoint {b t : ℕ} {left right : Fin b}
    (hne : left ≠ right) :
    Disjoint (sourceRowBlock b t left) (sourceRowBlock b t right) := by
  rw [Finset.disjoint_left]
  intro row hleft hright
  exact hne ((mem_sourceRowBlock left row).mp hleft |>.symm.trans
    ((mem_sourceRowBlock right row).mp hright))
theorem sourceTree_leafList_length (b : ℕ)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    tree.leafList.length = b := by
  classical
  have hset : tree.leafList.toFinset = tree.leaves := by
    ext i
    simp [BlockTree.mem_leaves_iff]
  calc
    tree.leafList.length = tree.leafList.toFinset.card :=
      (List.toFinset_card_of_nodup hnodup).symm
    _ = tree.leaves.card := congrArg Finset.card hset
    _ = b := by simp [hleaves]
theorem sourceTreeLinearFormVectors_length
    (b t d : ℕ) (hd : d ≤ t) (ζ : ℂ)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    (treeLinearFormVectors (sourceRowBlock b t) t d ζ tree).length =
      b * t - d := by
  rw [treeLinearFormVectors_length (sourceRowBlock b t)
    t d hd ζ tree, sourceTree_leafList_length b tree hnodup hleaves]
noncomputable def sourceTreeMatrix (b t d : ℕ) (hd : d ≤ t)
    (ζ : ℂ) (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    Matrix (Fin (b * t)) (Fin (b * t - d)) ℂ :=
  fun row column =>
    treeLinearFormMatrix (sourceRowBlock b t) t d ζ tree row
      ((finCongr
        (sourceTreeLinearFormVectors_length
          b t d hd ζ tree hnodup hleaves).symm) column)
noncomputable def sourceComplementRowEquiv
    (r d : ℕ) (omitted : Finset (Fin r))
    (homitted : omitted.card = d) :
    Fin (r - d) ≃ {row : Fin r // row ∉ omitted} :=
  Fintype.equivOfCardEq (by
    classical
    rw [Fintype.card_fin,
      Fintype.card_subtype_compl
        (fun row : Fin r => row ∈ omitted),
      Fintype.card_fin, Fintype.card_coe, homitted])
noncomputable def sourceComplementSquareFreeRowEquiv
    (r d : ℕ) (omitted : Finset (Fin r))
    (homitted : omitted.card = d) :
    Fin (r - d) ≃
      {row : Fin r // row ∈ (Finset.univ : Finset (Fin r)) \ omitted} :=
  (sourceComplementRowEquiv r d omitted homitted).trans
    (Equiv.subtypeEquivRight (fun row => by simp))
noncomputable def sourceRowBlockMinorSum
    {R : Type*} [CommSemiring R] (b t s d : ℕ)
    (X : Matrix (Fin (b * t)) (Fin s) R) (h : Fin b) : R :=
  ∑ omitted ∈ (sourceRowBlock b t h).powersetCard d,
    ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
      sourceBlockMinor (b * t) s X omitted columns
noncomputable def sourceRowBlockEmbedding
    (b t : ℕ) (h : Fin b) : Fin t ↪ Fin (b * t) where
  toFun row :=
    (finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)) (h, row)
  inj' := by
    intro left right heq
    exact congrArg Prod.snd
      ((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).injective heq)
theorem sourceRowBlock_eq_map
    (b t : ℕ) (h : Fin b) :
    sourceRowBlock b t h =
      (Finset.univ : Finset (Fin t)).map
        (sourceRowBlockEmbedding b t h) := by
  classical
  ext row
  change
    row ∈ (Finset.univ : Finset (Fin t)).image
      (fun localRow =>
        (finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t))
          (h, localRow)) ↔
      row ∈ (Finset.univ : Finset (Fin t)).map
        (sourceRowBlockEmbedding b t h)
  constructor
  · intro hrow
    obtain ⟨localRow, _, rfl⟩ := Finset.mem_image.mp hrow
    exact Finset.mem_map.mpr
      ⟨localRow, Finset.mem_univ _, rfl⟩
  · intro hrow
    obtain ⟨localRow, _, rfl⟩ := Finset.mem_map.mp hrow
    exact Finset.mem_image.mpr
      ⟨localRow, Finset.mem_univ _, rfl⟩
noncomputable def sourceRowBlockVariableEmbedding
    (b t s : ℕ) (h : Fin b) :
    (Fin t × Fin s) ↪ (Fin (b * t) × Fin s) where
  toFun entry :=
    (sourceRowBlockEmbedding b t h entry.1, entry.2)
  inj' := by
    intro left right heq
    have hfirst :
        sourceRowBlockEmbedding b t h left.1 =
          sourceRowBlockEmbedding b t h right.1 :=
      congrArg (fun entry : Fin (b * t) × Fin s => entry.1) heq
    have hsecond : left.2 = right.2 :=
      congrArg (fun entry : Fin (b * t) × Fin s => entry.2) heq
    exact Prod.ext
      ((sourceRowBlockEmbedding b t h).injective hfirst) hsecond
theorem sourceRowBlockVariableEmbedding_disjoint
    (b t s : ℕ) {left right : Fin b} (hne : left ≠ right) :
    Disjoint
      (Set.range (sourceRowBlockVariableEmbedding b t s left))
      (Set.range (sourceRowBlockVariableEmbedding b t s right)) := by
  classical
  rw [Set.disjoint_left]
  rintro entry ⟨leftVariable, hleft⟩ ⟨rightVariable, hright⟩
  have hrows :
      sourceRowBlockEmbedding b t left leftVariable.1 =
        sourceRowBlockEmbedding b t right rightVariable.1 :=
    congrArg Prod.fst (hleft.trans hright.symm)
  have hleftmem :
      sourceRowBlockEmbedding b t left leftVariable.1 ∈
        sourceRowBlock b t left := by
    rw [sourceRowBlock_eq_map]
    exact Finset.mem_map.mpr
      ⟨leftVariable.1, Finset.mem_univ _, rfl⟩
  have hrightmem :
      sourceRowBlockEmbedding b t left leftVariable.1 ∈
        sourceRowBlock b t right := by
    rw [hrows, sourceRowBlock_eq_map]
    exact Finset.mem_map.mpr
      ⟨rightVariable.1, Finset.mem_univ _, rfl⟩
  exact (Finset.disjoint_left.mp (sourceRowBlock_disjoint hne))
    hleftmem hrightmem
end Standalone_TreeCoefficients
section Standalone_SourcePermanentSpecialization
open scoped BigOperators
noncomputable section
def sourceBlockAffineInput
    {r s d : ℕ}
    (U : Matrix (Fin r) (Fin (r - d)) ℂ) :
    (Fin r ⊕ Fin (s - d)) →
      (Fin s ⊕ Fin (r - d)) → FreeAffineInput (Fin (r * s))
  | .inl row, .inl column =>
      ⟨0, Finsupp.single
        ((finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
          (row, column)) 1⟩
  | .inl row, .inr column => ⟨U row column, 0⟩
  | .inr _, .inl _ => ⟨1, 0⟩
  | .inr _, .inr _ => ⟨0, 0⟩
theorem sourceBlock_floor_reindex_sizes
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) :
    blockRows n d + (blockColumns n d - d) = n ∧
      blockColumns n d + (blockRows n d - d) = n := by
  have hr := degree_le_blockRows hd hn
  have hs := degree_le_blockColumns n d
  have hsize := block_size_identity n d
  omega
def sourceBlockRowEquiv
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) :
    Fin n ≃ Fin (blockRows n d) ⊕ Fin (blockColumns n d - d) :=
  (finCongr (sourceBlock_floor_reindex_sizes hd hn).1.symm).trans
    (finSumFinEquiv :
      Fin (blockRows n d) ⊕ Fin (blockColumns n d - d) ≃
        Fin (blockRows n d + (blockColumns n d - d))).symm
def sourceBlockColumnEquiv
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) :
    Fin n ≃ Fin (blockColumns n d) ⊕ Fin (blockRows n d - d) :=
  (finCongr (sourceBlock_floor_reindex_sizes hd hn).2.symm).trans
    (finSumFinEquiv :
      Fin (blockColumns n d) ⊕ Fin (blockRows n d - d) ≃
        Fin (blockColumns n d + (blockRows n d - d))).symm
def sourceTreeBlockCommonFactor (b t s d : ℕ) : ℂ :=
  (((s - d).factorial : ℕ) : ℂ) *
    (((t - d).factorial : ℕ) : ℂ) *
    ((((t.factorial : ℕ) : ℂ) ^ (b - 1)))
def sourceTreeSeparatedMinorSum
    (b t s d : ℕ) (tree : BlockTree (Fin b)) :
    MvPolynomial (Fin (b * t) × Fin s) ℂ :=
  ∑ h : Fin b,
    MvPolynomial.C
      (subtreeCoefficient
        (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h) *
      MvPolynomial.rename
        (sourceRowBlockVariableEmbedding b t s h)
        (minorSum t s d)
end
end Standalone_SourcePermanentSpecialization
section Standalone_MainReduction
open scoped BigOperators
noncomputable section
def separatedBlockMinorSum (b t s d : ℕ) (weight : Fin b → ℂ) :
    MvPolynomial (Fin (b * t) × Fin s) ℂ :=
  ∑ h : Fin b,
    MvPolynomial.C (weight h) *
      MvPolynomial.rename (sourceRowBlockVariableEmbedding b t s h)
        (minorSum t s d)
theorem separatedBlockMinorSum_offBlock_pderiv
    (b t s d : ℕ) {h j : Fin b} (hne : h ≠ j)
    (i : Fin t) (a : Fin s) :
    MvPolynomial.pderiv
        (sourceRowBlockVariableEmbedding b t s h (i, a))
        (MvPolynomial.rename (sourceRowBlockVariableEmbedding b t s j)
          (minorSum t s d)) = 0 := by
  classical
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  have himage := MvPolynomial.vars_rename
    (sourceRowBlockVariableEmbedding b t s j)
    (minorSum t s d) hmem
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp himage
  exact Set.disjoint_left.mp
    (sourceRowBlockVariableEmbedding_disjoint b t s hne)
    ⟨(i, a), rfl⟩ ⟨entry, hentry⟩
theorem separatedBlockMinorSum_pderiv
    (b t s d : ℕ) (weight : Fin b → ℂ)
    (h : Fin b) (i : Fin t) (a : Fin s) :
    MvPolynomial.pderiv
        (sourceRowBlockVariableEmbedding b t s h (i, a))
        (separatedBlockMinorSum b t s d weight) =
      MvPolynomial.C (weight h) *
        MvPolynomial.rename (sourceRowBlockVariableEmbedding b t s h)
          (MvPolynomial.pderiv (i, a) (minorSum t s d)) := by
  classical
  unfold separatedBlockMinorSum
  rw [map_sum]
  rw [Finset.sum_eq_single h]
  · rw [MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_rename
        (sourceRowBlockVariableEmbedding b t s h).injective]
  · intro j _ hj
    rw [MvPolynomial.pderiv_C_mul,
      separatedBlockMinorSum_offBlock_pderiv
        b t s d hj.symm i a, mul_zero]
  · simp
def blockMinorGraphPullback (b t s : ℕ) :
    MvPolynomial (BlockIncidenceCoordinate b t s) ℂ →ₐ[ℂ]
      MvPolynomial (Fin (b * t) × Fin s) ℂ :=
  MvPolynomial.aeval fun coordinate =>
    match coordinate.2 with
    | Sum.inl block =>
        MvPolynomial.rename
          (sourceRowBlockVariableEmbedding b t s coordinate.1)
          (powerSum t s block.1)
    | Sum.inr column =>
        MvPolynomial.X
          (sourceRowBlockVariableEmbedding b t s coordinate.1
            (column.2, column.1))
theorem blockMinorGraphPullback_rename
    (b t s : ℕ) (h : Fin b)
    (f : MvPolynomial (IncidenceCoordinate t s) ℂ) :
    blockMinorGraphPullback b t s
        (MvPolynomial.rename
          (fun coordinate : IncidenceCoordinate t s => (h, coordinate)) f) =
      MvPolynomial.rename (sourceRowBlockVariableEmbedding b t s h)
        (minorSumGraphPullback t s f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp [blockMinorGraphPullback, minorSumGraphPullback]
  | add f g hf hg =>
      simp [map_add, hf, hg]
  | mul_X f coordinate hf =>
      rw [map_mul, map_mul, map_mul, hf]
      cases coordinate with
      | inl block =>
          simp [blockMinorGraphPullback, minorSumGraphPullback]
      | inr column =>
          simp [blockMinorGraphPullback, minorSumGraphPullback]
theorem blockMinorGraphPullback_equation
    (b t s d : ℕ) (hd : 0 < d)
    (coordinate : BlockIncidenceColumn b t s) :
    blockMinorGraphPullback b t s
        (blockIncidenceEquation b t s d coordinate) =
      MvPolynomial.rename
        (sourceRowBlockVariableEmbedding b t s coordinate.1)
        (MvPolynomial.pderiv (coordinate.2.2, coordinate.2.1)
          (minorSum t s d)) := by
  unfold blockIncidenceEquation
  rw [blockMinorGraphPullback_rename,
    minorSumGraphPullback_incidenceEquation t s d hd]
abbrev separatedBlockGradientIdeal
    (b t s d : ℕ) (weight : Fin b → ℂ) :
    Ideal (MvPolynomial (Fin (b * t) × Fin s) ℂ) :=
  homogeneousMapIdeal
    (fun coordinate : Fin (b * t) × Fin s =>
      MvPolynomial.pderiv coordinate
        (separatedBlockMinorSum b t s d weight))
abbrev SeparatedBlockCriticalCoordinateRing
    (b t s d : ℕ) (weight : Fin b → ℂ) :=
  MvPolynomial (Fin (b * t) × Fin s) ℂ ⧸
    separatedBlockGradientIdeal b t s d weight
theorem blockMinorGraphPullback_equation_mem_gradient
    (b t s d : ℕ) (weight : Fin b → ℂ)
    (hw : ∀ h, weight h ≠ 0) (hd : 0 < d)
    (coordinate : BlockIncidenceColumn b t s) :
    blockMinorGraphPullback b t s
        (blockIncidenceEquation b t s d coordinate) ∈
      separatedBlockGradientIdeal b t s d weight := by
  classical
  rw [blockMinorGraphPullback_equation b t s d hd]
  let z : Fin (b * t) × Fin s :=
    sourceRowBlockVariableEmbedding b t s coordinate.1
      (coordinate.2.2, coordinate.2.1)
  have hderiv :
      MvPolynomial.pderiv z
          (separatedBlockMinorSum b t s d weight) =
        MvPolynomial.C (weight coordinate.1) *
          MvPolynomial.rename
            (sourceRowBlockVariableEmbedding b t s coordinate.1)
            (MvPolynomial.pderiv (coordinate.2.2, coordinate.2.1)
              (minorSum t s d)) :=
    separatedBlockMinorSum_pderiv
      b t s d weight coordinate.1 coordinate.2.2 coordinate.2.1
  have hmember :
      MvPolynomial.pderiv z
          (separatedBlockMinorSum b t s d weight) ∈
        separatedBlockGradientIdeal b t s d weight :=
    Ideal.subset_span ⟨z, rfl⟩
  have hscaled :=
    (separatedBlockGradientIdeal b t s d weight).mul_mem_left
      (MvPolynomial.C ((weight coordinate.1)⁻¹)) hmember
  rw [hderiv, ← mul_assoc, ← MvPolynomial.C_mul,
    inv_mul_cancel₀ (hw coordinate.1), MvPolynomial.C_1, one_mul]
    at hscaled
  exact hscaled
def blockIncidenceWeightedCriticalGraph
    (b t s d : ℕ) (weight : Fin b → ℂ)
    (hw : ∀ h, weight h ≠ 0) (hd : 0 < d) :
    BlockIncidenceCoordinateRing b t s d →ₐ[ℂ]
      SeparatedBlockCriticalCoordinateRing b t s d weight := by
  let J := separatedBlockGradientIdeal b t s d weight
  let φ : MvPolynomial (BlockIncidenceCoordinate b t s) ℂ →ₐ[ℂ]
      SeparatedBlockCriticalCoordinateRing b t s d weight :=
    (Ideal.Quotient.mkₐ ℂ J).comp
      (blockMinorGraphPullback b t s)
  apply Ideal.Quotient.liftₐ (blockIncidenceIdeal b t s d) φ
  intro f hf
  have hker : blockIncidenceIdeal b t s d ≤
      RingHom.ker φ.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨coordinate, rfl⟩
    change Ideal.Quotient.mk J
      (blockMinorGraphPullback b t s
        (blockIncidenceEquation b t s d coordinate)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact blockMinorGraphPullback_equation_mem_gradient
      b t s d weight hw hd coordinate
  exact hker hf
def blockMinorMatrixCoordinateLift (b t s : ℕ) :
    (Fin (b * t) × Fin s) → BlockIncidenceCoordinate b t s :=
  fun coordinate =>
    (((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm
        coordinate.1).1,
      Sum.inr (coordinate.2,
        ((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm
          coordinate.1).2))
def flattenedSeparatedBlockMinorSum
    (b t s d : ℕ) (weight : Fin b → ℂ) :
    MvPolynomial (Fin ((b * t) * s)) ℂ :=
  MvPolynomial.rename
    (finProdFinEquiv : Fin (b * t) × Fin s ≃ Fin ((b * t) * s))
    (separatedBlockMinorSum b t s d weight)
theorem separatedBlockGradientIdeal_map_flatten
    (b t s d : ℕ) (weight : Fin b → ℂ) :
    (separatedBlockGradientIdeal b t s d weight).map
      (MvPolynomial.renameEquiv ℂ
        (finProdFinEquiv :
          Fin (b * t) × Fin s ≃ Fin ((b * t) * s))).toRingHom =
      homogeneousMapIdeal
        (fun j : Fin ((b * t) * s) =>
          MvPolynomial.pderiv j
            (flattenedSeparatedBlockMinorSum b t s d weight)) := by
  classical
  let e : Fin (b * t) × Fin s ≃ Fin ((b * t) * s) :=
    finProdFinEquiv
  change
    (Ideal.span (Set.range fun j : Fin (b * t) × Fin s =>
      MvPolynomial.pderiv j
        (separatedBlockMinorSum b t s d weight))).map
      (MvPolynomial.renameEquiv ℂ e).toRingHom =
    Ideal.span (Set.range fun j : Fin ((b * t) * s) =>
      MvPolynomial.pderiv j
        (MvPolynomial.rename e
          (separatedBlockMinorSum b t s d weight)))
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change
      MvPolynomial.rename e
        (MvPolynomial.pderiv j
          (separatedBlockMinorSum b t s d weight)) ∈
        Ideal.span (Set.range fun k : Fin ((b * t) * s) =>
          MvPolynomial.pderiv k
            (MvPolynomial.rename e
              (separatedBlockMinorSum b t s d weight)))
    rw [← MvPolynomial.pderiv_rename e.injective]
    exact Ideal.subset_span ⟨e j, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hrename := MvPolynomial.pderiv_rename e.injective
      (e.symm j) (separatedBlockMinorSum b t s d weight)
    rw [e.apply_symm_apply] at hrename
    change
      MvPolynomial.pderiv j
        (MvPolynomial.rename e
          (separatedBlockMinorSum b t s d weight)) ∈ _
    rw [hrename]
    apply Ideal.subset_span
    exact ⟨MvPolynomial.pderiv (e.symm j)
      (separatedBlockMinorSum b t s d weight),
      ⟨e.symm j, rfl⟩, rfl⟩
def separatedBlockCriticalFlattenEquiv
    (b t s d : ℕ) (weight : Fin b → ℂ) :
    SeparatedBlockCriticalCoordinateRing b t s d weight ≃ₐ[ℂ]
      criticalCoordinateRing
        (flattenedSeparatedBlockMinorSum b t s d weight) :=
  Ideal.quotientEquivAlg
    (separatedBlockGradientIdeal b t s d weight)
    (homogeneousMapIdeal
      (fun j : Fin ((b * t) * s) =>
        MvPolynomial.pderiv j
          (flattenedSeparatedBlockMinorSum b t s d weight)))
    (MvPolynomial.renameEquiv ℂ
      (finProdFinEquiv :
        Fin (b * t) × Fin s ≃ Fin ((b * t) * s)))
    (separatedBlockGradientIdeal_map_flatten
      b t s d weight).symm
def sourceTreeBlockWeight (b d : ℕ) (tree : BlockTree (Fin b)) :
    Fin b → ℂ :=
  fun h => subtreeCoefficient
    (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h
def sourceSeparatedBlockMinorSum
    (n d : ℕ) (weight : Fin (blockCount n d) → ℂ) :
    MvPolynomial (Fin (blockVariables n d)) ℂ :=
  flattenedSeparatedBlockMinorSum
    (blockCount n d) (blockWidth d) (blockColumns n d) d weight
structure CircuitPrefix (ι : Type) where
  program : List (Instruction ι)
  valid : ∀ position : Fin program.length,
    (program.get position).referencesBounded position.val
namespace CircuitPrefix
def values {ι : Type} (state : CircuitPrefix ι) :
    Array (MvPolynomial ι ℂ) :=
  state.program.foldl
    (fun values instruction => values.push (instruction.eval values)) #[]
def empty (ι : Type) : CircuitPrefix ι where
  program := []
  valid position := Fin.elim0 position
def append {ι : Type} (state : CircuitPrefix ι)
    (instruction : Instruction ι)
    (hvalid : instruction.referencesBounded state.program.length) :
    CircuitPrefix ι where
  program := state.program ++ [instruction]
  valid := by
    intro position
    by_cases hposition : position.val < state.program.length
    · change
        ((state.program ++ [instruction])[position.val]).referencesBounded
          position.val
      rw [List.getElem_append_left hposition]
      exact state.valid ⟨position.val, hposition⟩
    · have hlast : position.val = state.program.length := by
        have hlt := position.isLt
        simp only [List.length_append, List.length_singleton] at hlt
        omega
      change
        ((state.program ++ [instruction])[position.val]).referencesBounded
          position.val
      rw [List.getElem_append_right (by omega)]
      simpa [hlast] using hvalid
end CircuitPrefix
namespace ArithmeticCircuit
end ArithmeticCircuit
open scoped LinearAlgebra.Projectivization
end
end Standalone_MainReduction
end PermanentRollout
namespace PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace TranscendenceBounds
end TranscendenceBounds
inductive Formula (ι : Type u) (R : Type v) where
  | var : ι → Formula ι R
  | const : R → Formula ι R
  | add : Formula ι R → Formula ι R → Formula ι R
  | sub : Formula ι R → Formula ι R → Formula ι R
  | mul : Formula ι R → Formula ι R → Formula ι R
namespace Formula
variable {ι : Type u} {R : Type v}
noncomputable def eval [CommRing R] : Formula ι R → MvPolynomial ι R
  | .var i => MvPolynomial.X i
  | .const c => MvPolynomial.C c
  | .add f g => eval f + eval g
  | .sub f g => eval f - eval g
  | .mul f g => eval f * eval g
def leafCount : Formula ι R → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add f g => leafCount f + leafCount g
  | .sub f g => leafCount f + leafCount g
  | .mul f g => leafCount f + leafCount g
def variableLeaves : Formula ι R → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add f g => variableLeaves f + variableLeaves g
  | .sub f g => variableLeaves f + variableLeaves g
  | .mul f g => variableLeaves f + variableLeaves g
def blockLeaves [DecidableEq ι] (s : Finset ι) : Formula ι R → ℕ
  | .var i => if i ∈ s then 1 else 0
  | .const _ => 0
  | .add f g => blockLeaves s f + blockLeaves s g
  | .sub f g => blockLeaves s f + blockLeaves s g
  | .mul f g => blockLeaves s f + blockLeaves s g
def internalGateCount : Formula ι R → ℕ
  | .var _ => 0
  | .const _ => 0
  | .add f g => internalGateCount f + internalGateCount g + 1
  | .sub f g => internalGateCount f + internalGateCount g + 1
  | .mul f g => internalGateCount f + internalGateCount g + 1
def vertexCount : Formula ι R → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add f g => vertexCount f + vertexCount g + 1
  | .sub f g => vertexCount f + vertexCount g + 1
  | .mul f g => vertexCount f + vertexCount g + 1
end Formula
inductive RationalFormula (ι : Type u) (R : Type v) where
  | var : ι → RationalFormula ι R
  | const : R → RationalFormula ι R
  | add : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R
  | sub : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R
  | mul : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R
  | div : RationalFormula ι R → RationalFormula ι R → RationalFormula ι R
namespace RationalFormula
variable {ι : Type u} {R : Type v}
noncomputable def eval [Field R] :
    RationalFormula ι R → FractionRing (MvPolynomial ι R)
  | .var i =>
      algebraMap (MvPolynomial ι R) (FractionRing (MvPolynomial ι R))
        (MvPolynomial.X i)
  | .const c =>
      algebraMap (MvPolynomial ι R) (FractionRing (MvPolynomial ι R))
        (MvPolynomial.C c)
  | .add f g => eval f + eval g
  | .sub f g => eval f - eval g
  | .mul f g => eval f * eval g
  | .div f g => eval f / eval g
inductive Valid [Field R] : RationalFormula ι R → Prop where
  | var (i : ι) : Valid (.var i)
  | const (c : R) : Valid (.const c)
  | add {f g : RationalFormula ι R} : Valid f → Valid g → Valid (.add f g)
  | sub {f g : RationalFormula ι R} : Valid f → Valid g → Valid (.sub f g)
  | mul {f g : RationalFormula ι R} : Valid f → Valid g → Valid (.mul f g)
  | div {f g : RationalFormula ι R} :
      Valid f → Valid g → eval g ≠ 0 → Valid (.div f g)
def leafCount : RationalFormula ι R → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add f g => leafCount f + leafCount g
  | .sub f g => leafCount f + leafCount g
  | .mul f g => leafCount f + leafCount g
  | .div f g => leafCount f + leafCount g
def variableLeaves : RationalFormula ι R → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add f g => variableLeaves f + variableLeaves g
  | .sub f g => variableLeaves f + variableLeaves g
  | .mul f g => variableLeaves f + variableLeaves g
  | .div f g => variableLeaves f + variableLeaves g
def blockLeaves [DecidableEq ι] (s : Finset ι) : RationalFormula ι R → ℕ
  | .var i => if i ∈ s then 1 else 0
  | .const _ => 0
  | .add f g => blockLeaves s f + blockLeaves s g
  | .sub f g => blockLeaves s f + blockLeaves s g
  | .mul f g => blockLeaves s f + blockLeaves s g
  | .div f g => blockLeaves s f + blockLeaves s g
def internalGateCount : RationalFormula ι R → ℕ
  | .var _ => 0
  | .const _ => 0
  | .add f g => internalGateCount f + internalGateCount g + 1
  | .sub f g => internalGateCount f + internalGateCount g + 1
  | .mul f g => internalGateCount f + internalGateCount g + 1
  | .div f g => internalGateCount f + internalGateCount g + 1
def vertexCount : RationalFormula ι R → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add f g => vertexCount f + vertexCount g + 1
  | .sub f g => vertexCount f + vertexCount g + 1
  | .mul f g => vertexCount f + vertexCount g + 1
  | .div f g => vertexCount f + vertexCount g + 1
end RationalFormula
namespace RationalFormula
noncomputable section RationalSkeletonInduction
variable {Y Z F : Type*}
def yLeafCount : RationalFormula (Y ⊕ Z) F → ℕ
  | .var (.inl _) => 1
  | .var (.inr _) => 0
  | .const _ => 0
  | .add f g => yLeafCount f + yLeafCount g
  | .sub f g => yLeafCount f + yLeafCount g
  | .mul f g => yLeafCount f + yLeafCount g
  | .div f g => yLeafCount f + yLeafCount g
abbrev rationalCoefficientField (Z F : Type*) [Field F] :=
  FractionRing (MvPolynomial Z F)
abbrev rationalSplitField (Y Z F : Type*) [Field F] :=
  FractionRing (MvPolynomial Y (rationalCoefficientField Z F))
def splitPolynomialHom [Field F] :
    MvPolynomial (Y ⊕ Z) F →+* rationalSplitField Y Z F :=
  (algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F)).comp
      ((MvPolynomial.map (σ := Y)
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F))).comp
          (MvPolynomial.sumAlgEquiv F Y Z).toRingEquiv.toRingHom)
theorem splitPolynomialHom_injective [Field F] :
    Function.Injective (splitPolynomialHom (Y := Y) (Z := Z) (F := F)) := by
  unfold splitPolynomialHom
  exact
    (IsFractionRing.injective
      (MvPolynomial Y (rationalCoefficientField Z F))
      (rationalSplitField Y Z F)).comp
      ((MvPolynomial.map_injective
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F))
        (IsFractionRing.injective
          (MvPolynomial Z F) (rationalCoefficientField Z F))).comp
            (MvPolynomial.sumAlgEquiv F Y Z).injective)
def splitFractionHom [Field F] :
    FractionRing (MvPolynomial (Y ⊕ Z) F) →+* rationalSplitField Y Z F :=
  IsFractionRing.lift
    (splitPolynomialHom_injective (Y := Y) (Z := Z) (F := F))
def splitEval [Field F] (f : RationalFormula (Y ⊕ Z) F) :
    rationalSplitField Y Z F :=
  splitFractionHom (Y := Y) (Z := Z) (F := F) (eval f)
def splitCoefficientHom [Field F] :
    rationalCoefficientField Z F →+* rationalSplitField Y Z F :=
  (algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F)).comp MvPolynomial.C
theorem splitCoefficientHom_eq_algebraMap [Field F] :
    splitCoefficientHom (Y := Y) (Z := Z) (F := F) =
      algebraMap (rationalCoefficientField Z F)
        (rationalSplitField Y Z F) := by
  ext c
  exact (IsScalarTower.algebraMap_apply
    (rationalCoefficientField Z F)
    (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F) c).symm
@[simp] theorem splitFractionHom_algebraMap [Field F]
    (p : MvPolynomial (Y ⊕ Z) F) :
    splitFractionHom (Y := Y) (Z := Z) (F := F)
        (algebraMap (MvPolynomial (Y ⊕ Z) F)
          (FractionRing (MvPolynomial (Y ⊕ Z) F)) p) =
      splitPolynomialHom (Y := Y) (Z := Z) (F := F) p := by
  exact IsFractionRing.lift_algebraMap
    (splitPolynomialHom_injective (Y := Y) (Z := Z) (F := F)) p
@[simp] theorem splitEval_var_inl [Field F] (i : Y) :
    splitEval (Z := Z) (F := F) (.var (.inl i)) =
      algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
        (rationalSplitField Y Z F) (MvPolynomial.X i) := by
  simp [splitEval, eval, splitPolynomialHom]
@[simp] theorem splitEval_var_inr [Field F] (j : Z) :
    splitEval (Y := Y) (F := F) (.var (.inr j)) =
      splitCoefficientHom (Y := Y) (Z := Z) (F := F)
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F)
          (MvPolynomial.X j)) := by
  simp [splitEval, eval, splitPolynomialHom, splitCoefficientHom]
@[simp] theorem splitEval_const [Field F] (c : F) :
    splitEval (Y := Y) (Z := Z) (.const c) =
      splitCoefficientHom (Y := Y) (Z := Z) (F := F)
        (algebraMap (MvPolynomial Z F) (rationalCoefficientField Z F)
          (MvPolynomial.C c)) := by
  simp [splitEval, eval, splitPolynomialHom, splitCoefficientHom]
@[simp] theorem splitEval_add [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.add f g) = splitEval f + splitEval g := by
  simp [splitEval, eval]
@[simp] theorem splitEval_sub [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.sub f g) = splitEval f - splitEval g := by
  simp [splitEval, eval]
@[simp] theorem splitEval_mul [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.mul f g) = splitEval f * splitEval g := by
  simp [splitEval, eval]
@[simp] theorem splitEval_div [Field F]
    (f g : RationalFormula (Y ⊕ Z) F) :
    splitEval (.div f g) = splitEval f / splitEval g := by
  simp [splitEval, eval, map_div₀]
theorem exists_splitEval_eq_coefficient_of_yLeafCount_eq_zero [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (h : yLeafCount f = 0) :
    ∃ c : rationalCoefficientField Z F,
      splitEval f = splitCoefficientHom (Y := Y) (Z := Z) (F := F) c := by
  induction f with
  | var i =>
      cases i with
      | inl i => simp [yLeafCount] at h
      | inr j =>
          exact ⟨algebraMap (MvPolynomial Z F)
            (rationalCoefficientField Z F) (MvPolynomial.X j),
              splitEval_var_inr j⟩
  | const c =>
      exact ⟨algebraMap (MvPolynomial Z F)
        (rationalCoefficientField Z F) (MvPolynomial.C c),
          splitEval_const c⟩
  | add f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a + b, ?_⟩
      rw [splitEval_add, ha, hb, map_add]
  | sub f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a - b, ?_⟩
      rw [splitEval_sub, ha, hb, map_sub]
  | mul f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a * b, ?_⟩
      rw [splitEval_mul, ha, hb, map_mul]
  | div f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨a, ha⟩ := hf hfzero
      obtain ⟨b, hb⟩ := hg hgzero
      refine ⟨a / b, ?_⟩
      rw [splitEval_div, ha, hb, map_div₀]
def rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F)) :
    IntermediateField F (rationalSplitField Y Z F) :=
  IntermediateField.adjoin F
    (Set.range (fun i : Y =>
      algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
        (rationalSplitField Y Z F) (MvPolynomial.X i)) ∪
      (splitCoefficientHom (Y := Y) (Z := Z) (F := F)) ''
        (s : Set (rationalCoefficientField Z F)))
theorem marked_variable_mem_rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F)) (i : Y) :
    algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
        (rationalSplitField Y Z F) (MvPolynomial.X i) ∈
      rationalSkeletonField (Y := Y) s := by
  apply IntermediateField.subset_adjoin F _
  exact Or.inl ⟨i, rfl⟩
theorem coefficient_parameter_mem_rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F))
    (c : rationalCoefficientField Z F) (hc : c ∈ s) :
    splitCoefficientHom (Y := Y) (Z := Z) (F := F) c ∈
      rationalSkeletonField (Y := Y) s := by
  apply IntermediateField.subset_adjoin F _
  exact Or.inr ⟨c, hc, rfl⟩
theorem coefficient_adjoin_mem_rationalSkeletonField [Field F]
    (s : Finset (rationalCoefficientField Z F))
    (c : rationalCoefficientField Z F)
    (hc : c ∈ IntermediateField.adjoin F
      (s : Set (rationalCoefficientField Z F))) :
    splitCoefficientHom (Y := Y) (Z := Z) (F := F) c ∈
      rationalSkeletonField (Y := Y) s := by
  refine IntermediateField.adjoin_induction F
    (p := fun x _ =>
      splitCoefficientHom (Y := Y) (Z := Z) (F := F) x ∈
        rationalSkeletonField (Y := Y) s)
    ?_ ?_ ?_ ?_ ?_ hc
  · intro x hx
    exact coefficient_parameter_mem_rationalSkeletonField s x hx
  · intro x
    rw [splitCoefficientHom_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply F
        (rationalCoefficientField Z F) (rationalSplitField Y Z F)]
    exact (rationalSkeletonField (Y := Y) s).algebraMap_mem x
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro x _ hx
    rw [map_inv₀]
    exact inv_mem hx
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy
theorem rationalSkeletonField_mono [Field F]
    {s t : Finset (rationalCoefficientField Z F)} (h : s ⊆ t) :
    rationalSkeletonField (Y := Y) s ≤ rationalSkeletonField (Y := Y) t := by
  apply IntermediateField.adjoin.mono
  intro x hx
  rcases hx with hx | ⟨c, hc, rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨c, h hc, rfl⟩
end RationalSkeletonInduction
end RationalFormula
noncomputable def permanentPolynomial (n : ℕ) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).permanent
namespace Formula
end Formula
def matchingBlockRow {n k : ℕ} (hk : 0 < k)
    (j : Fin (n / k)) (r : Fin k) : Fin n :=
  ⟨(j : ℕ) * k + (r : ℕ), by
    have hupper : ((j : ℕ) + 1) * k ≤ n :=
      (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt j.isLt)
    have hupper' : (j : ℕ) * k + k ≤ n := by
      simpa [Nat.add_mul] using hupper
    exact (Nat.add_lt_add_left r.isLt ((j : ℕ) * k)).trans_le hupper'⟩
theorem matchingBlockRow_injective {n k : ℕ} (hk : 0 < k) :
    Function.Injective
      (fun jr : Fin (n / k) × Fin k =>
        matchingBlockRow hk jr.1 jr.2) := by
  intro x y h
  rcases x with ⟨j, r⟩
  rcases y with ⟨j', r'⟩
  have hval :
      (j : ℕ) * k + (r : ℕ) =
        (j' : ℕ) * k + (r' : ℕ) :=
    congrArg Fin.val h
  have hr : (r : ℕ) = (r' : ℕ) := by
    have hmod := congrArg (fun z : ℕ => z % k) hval
    simpa [Nat.add_mod, Nat.mod_eq_of_lt r.isLt,
      Nat.mod_eq_of_lt r'.isLt] using hmod
  have hmul : (j : ℕ) * k = (j' : ℕ) * k := by
    omega
  have hj : (j : ℕ) = (j' : ℕ) :=
    Nat.eq_of_mul_eq_mul_right hk hmul
  apply Prod.ext
  · exact Fin.ext hj
  · exact Fin.ext hr
def cyclicMatchingBlock {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    Finset (Fin n × Fin n) := by
  classical
  letI : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (t : ℕ)).trans_lt t.isLt)⟩
  exact Finset.univ.image fun r : Fin k =>
    let i := matchingBlockRow hk j r
    (i, i + t)
theorem card_cyclicMatchingBlock {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    (cyclicMatchingBlock hk t j).card = k := by
  classical
  unfold cyclicMatchingBlock
  rw [Finset.card_image_of_injective]
  · simp
  · intro r r' heq
    have hrows : matchingBlockRow hk j r = matchingBlockRow hk j r' :=
      congrArg Prod.fst heq
    exact congrArg Prod.snd
      (matchingBlockRow_injective hk
        (a₁ := (j, r)) (a₂ := (j, r')) hrows)
namespace Formula
end Formula
namespace RationalFormula
end RationalFormula
namespace Formula
end Formula
namespace RationalFormula
end RationalFormula
section Coefficients
variable {Y : Type u} {Z : Type v} {F : Type w} [Field F]
noncomputable def coefficientPolynomial
    (f : MvPolynomial (Y ⊕ Z) F) (α : Y →₀ ℕ) : MvPolynomial Z F :=
  MvPolynomial.coeff α (MvPolynomial.sumAlgEquiv F Y Z f)
noncomputable def coefficientField (f : MvPolynomial (Y ⊕ Z) F) :
    IntermediateField F (FractionRing (MvPolynomial Z F)) :=
  IntermediateField.adjoin F
    (Set.range fun α : Y →₀ ℕ =>
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (coefficientPolynomial f α))
noncomputable def coefficientTranscendenceDegree
    (f : MvPolynomial (Y ⊕ Z) F) : Cardinal :=
  Algebra.trdeg F ↥(coefficientField f)
end Coefficients
section Jacobian
variable {ι : Type u} {κ : Type v} {F : Type w}
noncomputable def jacobianMinor [CommSemiring F]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) :
    Matrix ι ι (MvPolynomial κ F) :=
  fun i j => MvPolynomial.pderiv (cols j) (g i)
noncomputable def evaluatedJacobianMinor [CommSemiring F]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) (x : κ → F) :
    Matrix ι ι F :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (cols j) (g i))
end Jacobian
noncomputable section PolynomialIntersection
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
def polynomialCoefficientProjection (φ : E →ₗ[K] K) :
    MvPolynomial ι E →ₗ[K] MvPolynomial ι K :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap φ).comp
      (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)
end PolynomialIntersection
noncomputable section RationalCoefficientExtraction
variable {F E Y : Type*} [Field F] [Field E] [Algebra F E]
def coefficientPolynomialEmbedding (K : IntermediateField F E) :
    MvPolynomial Y K →ₐ[F] FractionRing (MvPolynomial Y E) :=
  (IsScalarTower.toAlgHom F (MvPolynomial Y E)
    (FractionRing (MvPolynomial Y E))).comp
      (MvPolynomial.mapAlgHom K.val)
theorem coefficientPolynomialEmbedding_injective
    (K : IntermediateField F E) :
    Function.Injective (coefficientPolynomialEmbedding (Y := Y) K) := by
  unfold coefficientPolynomialEmbedding
  exact
    (IsFractionRing.injective (MvPolynomial Y E)
      (FractionRing (MvPolynomial Y E))).comp
      (MvPolynomial.map_injective (algebraMap K E)
        (RingHom.injective (algebraMap K E)))
def coefficientFractionEmbedding (K : IntermediateField F E) :
    FractionRing (MvPolynomial Y K) →ₐ[F]
      FractionRing (MvPolynomial Y E) :=
  IsFractionRing.liftAlgHom (coefficientPolynomialEmbedding_injective
    (Y := Y) K)
@[simp] theorem coefficientFractionEmbedding_algebraMap
    (K : IntermediateField F E) (p : MvPolynomial Y K) :
    coefficientFractionEmbedding (Y := Y) K
      (algebraMap (MvPolynomial Y K)
        (FractionRing (MvPolynomial Y K)) p) =
      coefficientPolynomialEmbedding (Y := Y) K p := by
  exact IsFractionRing.lift_algebraMap
    (coefficientPolynomialEmbedding_injective (Y := Y) K) p
def coefficientRationalField (s : Finset E) :
    IntermediateField F (FractionRing (MvPolynomial Y E)) :=
  IntermediateField.adjoin F
    (Set.range (fun i : Y =>
      algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E))
        (MvPolynomial.X i)) ∪
      (algebraMap E (FractionRing (MvPolynomial Y E))) '' (s : Set E))
end RationalCoefficientExtraction
noncomputable section RationalSkeleton
variable {E L : Type*} [Field E] [Field L] [Algebra E L]
def fractionalNumerator (M : Matrix (Fin 2) (Fin 2) E) (q : L) : L :=
  algebraMap E L (M 0 0) * q + algebraMap E L (M 0 1)
def fractionalDenominator (M : Matrix (Fin 2) (Fin 2) E) (q : L) : L :=
  algebraMap E L (M 1 0) * q + algebraMap E L (M 1 1)
def fractionalApply (M : Matrix (Fin 2) (Fin 2) E) (q : L) : L :=
  fractionalNumerator M q / fractionalDenominator M q
theorem fractionalNumerator_mul
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalNumerator (M * N) q =
      algebraMap E L (M 0 0) * fractionalNumerator N q +
        algebraMap E L (M 0 1) * fractionalDenominator N q := by
  obtain ⟨h₀₀, h₀₁, _, _⟩ := Matrix.two_mul_expl M N
  simp only [fractionalNumerator, fractionalDenominator]
  rw [h₀₀, h₀₁]
  simp only [map_add, map_mul]
  ring
theorem fractionalDenominator_mul
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalDenominator (M * N) q =
      algebraMap E L (M 1 0) * fractionalNumerator N q +
        algebraMap E L (M 1 1) * fractionalDenominator N q := by
  obtain ⟨_, _, h₁₀, h₁₁⟩ := Matrix.two_mul_expl M N
  simp only [fractionalNumerator, fractionalDenominator]
  rw [h₁₀, h₁₁]
  simp only [map_add, map_mul]
  ring
theorem fractionalNumerator_mul_factor
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0) :
    fractionalNumerator (M * N) q =
      fractionalDenominator N q *
        fractionalNumerator M (fractionalApply N q) := by
  rw [fractionalNumerator_mul]
  change
    algebraMap E L (M 0 0) * fractionalNumerator N q +
        algebraMap E L (M 0 1) * fractionalDenominator N q =
      fractionalDenominator N q *
        (algebraMap E L (M 0 0) *
          (fractionalNumerator N q / fractionalDenominator N q) +
            algebraMap E L (M 0 1))
  field_simp [hN]
theorem fractionalDenominator_mul_factor
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0) :
    fractionalDenominator (M * N) q =
      fractionalDenominator N q *
        fractionalDenominator M (fractionalApply N q) := by
  rw [fractionalDenominator_mul]
  change
    algebraMap E L (M 1 0) * fractionalNumerator N q +
        algebraMap E L (M 1 1) * fractionalDenominator N q =
      fractionalDenominator N q *
        (algebraMap E L (M 1 0) *
          (fractionalNumerator N q / fractionalDenominator N q) +
            algebraMap E L (M 1 1))
  field_simp [hN]
theorem fractionalDenominator_mul_ne_zero
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0)
    (hM : fractionalDenominator M (fractionalApply N q) ≠ 0) :
    fractionalDenominator (M * N) q ≠ 0 := by
  rw [fractionalDenominator_mul_factor M N q hN]
  exact mul_ne_zero hN hM
theorem fractionalApply_mul
    (M N : Matrix (Fin 2) (Fin 2) E) (q : L)
    (hN : fractionalDenominator N q ≠ 0) :
    fractionalApply (M * N) q =
      fractionalApply M (fractionalApply N q) := by
  unfold fractionalApply
  rw [fractionalNumerator_mul_factor M N q hN,
    fractionalDenominator_mul_factor M N q hN]
  exact mul_div_mul_left _ _ hN
theorem matrix_ne_zero_of_fractionalDenominator_ne_zero
    (M : Matrix (Fin 2) (Fin 2) E) (q : L)
    (h : fractionalDenominator M q ≠ 0) : M ≠ 0 := by
  intro hM
  apply h
  simp [fractionalDenominator, hM]
def normalizedFractionalMatrix
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2) :
    Matrix (Fin 2) (Fin 2) E :=
  (M ij.1 ij.2)⁻¹ • M
theorem normalizedFractionalMatrix_pivot
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2)
    (h : M ij.1 ij.2 ≠ 0) :
    normalizedFractionalMatrix M ij ij.1 ij.2 = 1 := by
  simp [normalizedFractionalMatrix, Matrix.smul_apply, smul_eq_mul, h]
theorem fractionalNumerator_smul
    (c : E) (M : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalNumerator (c • M) q =
      algebraMap E L c * fractionalNumerator M q := by
  simp [fractionalNumerator, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring
theorem fractionalDenominator_smul
    (c : E) (M : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalDenominator (c • M) q =
      algebraMap E L c * fractionalDenominator M q := by
  simp [fractionalDenominator, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring
theorem fractionalApply_smul
    (c : E) (hc : c ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) E) (q : L) :
    fractionalApply (c • M) q = fractionalApply M q := by
  have hc' : algebraMap E L c ≠ 0 :=
    (map_ne_zero_iff (algebraMap E L)
      (RingHom.injective (algebraMap E L))).mpr hc
  simp only [fractionalApply, fractionalNumerator_smul,
    fractionalDenominator_smul]
  exact mul_div_mul_left _ _ hc'
theorem fractionalApply_normalizedFractionalMatrix
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2)
    (h : M ij.1 ij.2 ≠ 0) (q : L) :
    fractionalApply (normalizedFractionalMatrix M ij) q =
      fractionalApply M q := by
  unfold normalizedFractionalMatrix
  exact fractionalApply_smul _ (inv_ne_zero h) M q
def projectiveMatrixGenerators
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2) : Finset E := by
  classical
  exact (Finset.univ.erase ij).image
    (fun ab => normalizedFractionalMatrix M ij ab.1 ab.2)
theorem card_projectiveMatrixGenerators_le_three
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2) :
    (projectiveMatrixGenerators M ij).card ≤ 3 := by
  classical
  unfold projectiveMatrixGenerators
  calc
    ((Finset.univ.erase ij).image
      (fun ab => normalizedFractionalMatrix M ij ab.1 ab.2)).card ≤
        (Finset.univ.erase ij).card := Finset.card_image_le
    _ = 3 := by simp
theorem normalizedFractionalMatrix_entry_mem_adjoin
    {F : Type*} [Field F] [Algebra F E]
    (M : Matrix (Fin 2) (Fin 2) E) (ij : Fin 2 × Fin 2)
    (h : M ij.1 ij.2 ≠ 0) (a b : Fin 2) :
    normalizedFractionalMatrix M ij a b ∈
      IntermediateField.adjoin F
        (projectiveMatrixGenerators M ij : Set E) := by
  classical
  by_cases hab : (a, b) = ij
  · have ha : a = ij.1 := congrArg Prod.fst hab
    have hb : b = ij.2 := congrArg Prod.snd hab
    rw [ha, hb, normalizedFractionalMatrix_pivot M ij h]
    exact one_mem _
  · apply IntermediateField.subset_adjoin F
      (projectiveMatrixGenerators M ij : Set E)
    change normalizedFractionalMatrix M ij a b ∈
      projectiveMatrixGenerators M ij
    change normalizedFractionalMatrix M ij a b ∈
      (Finset.univ.erase ij).image
        (fun ab => normalizedFractionalMatrix M ij ab.1 ab.2)
    exact Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_erase.mpr ⟨hab, Finset.mem_univ _⟩, rfl⟩
end RationalSkeleton
namespace RationalFormula
noncomputable section RationalSkeletonContraction
variable {Y Z F : Type*}
section MarkedPathGates
variable {E L : Type*} [Field E] [Field L] [Algebra E L]
def rationalAddPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![1, c; 0, 1]
def rationalSubPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![1, -c; 0, 1]
def rationalReverseSubPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![-1, c; 0, 1]
def rationalMulPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![c, 0; 0, 1]
def rationalDivPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![1, 0; 0, c]
def rationalReverseDivPathMatrix (c : E) : Matrix (Fin 2) (Fin 2) E :=
  !![0, c; 1, 0]
@[simp] theorem fractionalDenominator_rationalAddPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalAddPathMatrix c) q = 1 := by
  simp [rationalAddPathMatrix, fractionalDenominator]
@[simp] theorem fractionalApply_rationalAddPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalAddPathMatrix c) q =
      q + algebraMap E L c := by
  simp [rationalAddPathMatrix, fractionalApply, fractionalNumerator,
    fractionalDenominator]
@[simp] theorem fractionalDenominator_rationalSubPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalSubPathMatrix c) q = 1 := by
  simp [rationalSubPathMatrix, fractionalDenominator]
@[simp] theorem fractionalApply_rationalSubPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalSubPathMatrix c) q =
      q - algebraMap E L c := by
  simp [rationalSubPathMatrix, fractionalApply, fractionalNumerator,
    fractionalDenominator, sub_eq_add_neg]
@[simp] theorem fractionalDenominator_rationalReverseSubPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalReverseSubPathMatrix c) q = 1 := by
  simp [rationalReverseSubPathMatrix, fractionalDenominator]
@[simp] theorem fractionalApply_rationalReverseSubPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalReverseSubPathMatrix c) q =
      algebraMap E L c - q := by
  simp [rationalReverseSubPathMatrix, fractionalApply, fractionalNumerator,
    fractionalDenominator, sub_eq_add_neg, add_comm]
@[simp] theorem fractionalDenominator_rationalMulPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalMulPathMatrix c) q = 1 := by
  simp [rationalMulPathMatrix, fractionalDenominator]
@[simp] theorem fractionalApply_rationalMulPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalMulPathMatrix c) q =
      algebraMap E L c * q := by
  simp [rationalMulPathMatrix, fractionalApply, fractionalNumerator,
    fractionalDenominator]
@[simp] theorem fractionalDenominator_rationalDivPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalDivPathMatrix c) q =
      algebraMap E L c := by
  simp [rationalDivPathMatrix, fractionalDenominator]
@[simp] theorem fractionalApply_rationalDivPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalDivPathMatrix c) q =
      q / algebraMap E L c := by
  simp [rationalDivPathMatrix, fractionalApply, fractionalNumerator,
    fractionalDenominator]
@[simp] theorem fractionalDenominator_rationalReverseDivPathMatrix
    (c : E) (q : L) :
    fractionalDenominator (rationalReverseDivPathMatrix c) q = q := by
  simp [rationalReverseDivPathMatrix, fractionalDenominator]
@[simp] theorem fractionalApply_rationalReverseDivPathMatrix
    (c : E) (q : L) :
    fractionalApply (rationalReverseDivPathMatrix c) q =
      algebraMap E L c / q := by
  simp [rationalReverseDivPathMatrix, fractionalApply, fractionalNumerator,
    fractionalDenominator]
end MarkedPathGates
structure ContractedRationalSkeleton [Field F]
    (f : RationalFormula (Y ⊕ Z) F) where
  generators : Finset (rationalCoefficientField Z F)
  matrix : Matrix (Fin 2) (Fin 2) (rationalCoefficientField Z F)
  core : rationalSplitField Y Z F
  core_mem : core ∈ rationalSkeletonField (Y := Y) generators
  denominator_ne : fractionalDenominator matrix core ≠ 0
  split_eq : splitEval f = fractionalApply matrix core
  generator_card : generators.card ≤ 6 * yLeafCount f - 6
noncomputable def contractedRationalSkeletonVar [Field F] (i : Y) :
    ContractedRationalSkeleton (Z := Z) (F := F) (.var (.inl i)) where
  generators := ∅
  matrix := 1
  core := algebraMap (MvPolynomial Y (rationalCoefficientField Z F))
    (rationalSplitField Y Z F) (MvPolynomial.X i)
  core_mem := marked_variable_mem_rationalSkeletonField ∅ i
  denominator_ne := by simp [fractionalDenominator]
  split_eq := by
    simp [splitEval_var_inl, fractionalApply, fractionalNumerator,
      fractionalDenominator]
  generator_card := by simp [yLeafCount]
noncomputable def contractedRationalSkeletonCompose [Field F]
    {f h : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f)
    (P : Matrix (Fin 2) (Fin 2) (rationalCoefficientField Z F))
    (heval : splitEval h = fractionalApply P (splitEval f))
    (hden : fractionalDenominator P (splitEval f) ≠ 0)
    (hleaves : yLeafCount h = yLeafCount f) :
    ContractedRationalSkeleton h where
  generators := w.generators
  matrix := P * w.matrix
  core := w.core
  core_mem := w.core_mem
  denominator_ne := by
    apply fractionalDenominator_mul_ne_zero P w.matrix w.core w.denominator_ne
    rwa [← w.split_eq]
  split_eq := by
    calc
      splitEval h = fractionalApply P (splitEval f) := heval
      _ = fractionalApply P (fractionalApply w.matrix w.core) :=
        congrArg (fractionalApply P) w.split_eq
      _ = fractionalApply (P * w.matrix) w.core :=
        (fractionalApply_mul P w.matrix w.core w.denominator_ne).symm
  generator_card := by
    simpa [hleaves] using w.generator_card
namespace ContractedRationalSkeleton
theorem exists_pivot [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    ∃ ij : Fin 2 × Fin 2, w.matrix ij.1 ij.2 ≠ 0 := by
  classical
  by_contra h
  have hzero : w.matrix = 0 := by
    apply Matrix.ext
    intro i j
    have hij : w.matrix i j = 0 := by
      by_contra hentry
      exact h ⟨(i, j), hentry⟩
    simpa using hij
  exact (matrix_ne_zero_of_fractionalDenominator_ne_zero
    w.matrix w.core w.denominator_ne) hzero
noncomputable def pivot [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) : Fin 2 × Fin 2 :=
  (exists_pivot w).choose
theorem pivot_ne [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    w.matrix (pivot w).1 (pivot w).2 ≠ 0 :=
  (exists_pivot w).choose_spec
noncomputable def extendedGenerators [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    Finset (rationalCoefficientField Z F) := by
  classical
  exact w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)
theorem splitEval_mem_extended [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) :
    splitEval f ∈ rationalSkeletonField (Y := Y) (extendedGenerators w) := by
  classical
  let s : Finset (rationalCoefficientField Z F) :=
    extendedGenerators w
  have hgenerators : w.generators ⊆ s := by
    intro c hc
    change c ∈ w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)
    exact Finset.mem_union_left _ hc
  have hcore : w.core ∈ rationalSkeletonField (Y := Y) s :=
    rationalSkeletonField_mono hgenerators w.core_mem
  have hentry (a b : Fin 2) :
      algebraMap (rationalCoefficientField Z F)
        (rationalSplitField Y Z F)
        (normalizedFractionalMatrix w.matrix (pivot w) a b) ∈
          rationalSkeletonField (Y := Y) s := by
    have hsmall := normalizedFractionalMatrix_entry_mem_adjoin
      (F := F) w.matrix (pivot w) (pivot_ne w) a b
    have hlarge :
        normalizedFractionalMatrix w.matrix (pivot w) a b ∈
          IntermediateField.adjoin F
            (s : Set (rationalCoefficientField Z F)) := by
      have hmono :
          IntermediateField.adjoin F
              (projectiveMatrixGenerators w.matrix (pivot w) :
                Set (rationalCoefficientField Z F)) ≤
            IntermediateField.adjoin F
              (s : Set (rationalCoefficientField Z F)) := by
        apply IntermediateField.adjoin.mono
        intro c hc
        change c ∈ projectiveMatrixGenerators w.matrix (pivot w) at hc
        change c ∈ s
        change c ∈
          w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)
        exact Finset.mem_union_right _ hc
      exact hmono hsmall
    rw [← splitCoefficientHom_eq_algebraMap]
    exact coefficient_adjoin_mem_rationalSkeletonField s _ hlarge
  change splitEval f ∈ rationalSkeletonField (Y := Y) s
  rw [w.split_eq, ← fractionalApply_normalizedFractionalMatrix
    w.matrix (pivot w) (pivot_ne w) w.core]
  unfold fractionalApply fractionalNumerator fractionalDenominator
  apply div_mem
  · exact add_mem (mul_mem (hentry 0 0) hcore) (hentry 0 1)
  · exact add_mem (mul_mem (hentry 1 0) hcore) (hentry 1 1)
theorem extendedGenerators_card_le [Field F]
    {f : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hmarked : 0 < yLeafCount f) :
    (extendedGenerators w).card ≤ 6 * yLeafCount f - 3 := by
  classical
  change
    (w.generators ∪ projectiveMatrixGenerators w.matrix (pivot w)).card ≤
      6 * yLeafCount f - 3
  have hunion := Finset.card_union_le w.generators
    (projectiveMatrixGenerators w.matrix (pivot w))
  have hmatrix := card_projectiveMatrixGenerators_le_three
    w.matrix (pivot w)
  have hgenerators := w.generator_card
  omega
end ContractedRationalSkeleton
noncomputable def contractedRationalSkeletonMerge [Field F]
    {f g h : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g)
    (op : rationalSplitField Y Z F → rationalSplitField Y Z F →
      rationalSplitField Y Z F)
    (hclosed : ∀ (K : IntermediateField F (rationalSplitField Y Z F))
      (x y : rationalSplitField Y Z F),
        x ∈ K → y ∈ K → op x y ∈ K)
    (heval : splitEval h = op (splitEval f) (splitEval g))
    (hleaves : yLeafCount h = yLeafCount f + yLeafCount g) :
    ContractedRationalSkeleton h := by
  classical
  let s : Finset (rationalCoefficientField Z F) :=
    ContractedRationalSkeleton.extendedGenerators wf ∪
      ContractedRationalSkeleton.extendedGenerators wg
  have hleft : ContractedRationalSkeleton.extendedGenerators wf ⊆ s := by
    intro c hc
    exact Finset.mem_union_left _ hc
  have hright : ContractedRationalSkeleton.extendedGenerators wg ⊆ s := by
    intro c hc
    exact Finset.mem_union_right _ hc
  refine
    { generators := s
      matrix := 1
      core := op (splitEval f) (splitEval g)
      core_mem := ?_
      denominator_ne := ?_
      split_eq := ?_
      generator_card := ?_ }
  · apply hclosed (rationalSkeletonField (Y := Y) s)
    · exact rationalSkeletonField_mono hleft
        (ContractedRationalSkeleton.splitEval_mem_extended wf)
    · exact rationalSkeletonField_mono hright
        (ContractedRationalSkeleton.splitEval_mem_extended wg)
  · simp [fractionalDenominator]
  · simpa [fractionalApply, fractionalNumerator, fractionalDenominator]
      using heval
  · have hunion := Finset.card_union_le
      (ContractedRationalSkeleton.extendedGenerators wf)
      (ContractedRationalSkeleton.extendedGenerators wg)
    have hcardf := ContractedRationalSkeleton.extendedGenerators_card_le wf hf
    have hcardg := ContractedRationalSkeleton.extendedGenerators_card_le wg hg
    change s.card ≤ 6 * yLeafCount h - 6
    change
      (ContractedRationalSkeleton.extendedGenerators wf ∪
        ContractedRationalSkeleton.extendedGenerators wg).card ≤
        6 * yLeafCount h - 6
    omega
theorem exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (h : yLeafCount f = 0) :
    ∃ c : rationalCoefficientField Z F,
      splitEval f =
        algebraMap (rationalCoefficientField Z F)
          (rationalSplitField Y Z F) c := by
  obtain ⟨c, hc⟩ :=
    exists_splitEval_eq_coefficient_of_yLeafCount_eq_zero f h
  refine ⟨c, ?_⟩
  rwa [splitCoefficientHom_eq_algebraMap] at hc
noncomputable def contractedRationalSkeletonAddLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0) :
    ContractedRationalSkeleton (.add f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalAddPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_add, fractionalApply_rationalAddPathMatrix, hc]
  · rw [fractionalDenominator_rationalAddPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]
noncomputable def contractedRationalSkeletonAddRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0) :
    ContractedRationalSkeleton (.add f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w (rationalAddPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_add, fractionalApply_rationalAddPathMatrix, hc, add_comm]
  · rw [fractionalDenominator_rationalAddPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]
noncomputable def contractedRationalSkeletonSubLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0) :
    ContractedRationalSkeleton (.sub f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalSubPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_sub, fractionalApply_rationalSubPathMatrix, hc]
  · rw [fractionalDenominator_rationalSubPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]
noncomputable def contractedRationalSkeletonSubRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0) :
    ContractedRationalSkeleton (.sub f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w (rationalReverseSubPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_sub, fractionalApply_rationalReverseSubPathMatrix, hc]
  · rw [fractionalDenominator_rationalReverseSubPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]
noncomputable def contractedRationalSkeletonMulLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0) :
    ContractedRationalSkeleton (.mul f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalMulPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_mul, fractionalApply_rationalMulPathMatrix, hc, mul_comm]
  · rw [fractionalDenominator_rationalMulPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]
noncomputable def contractedRationalSkeletonMulRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0) :
    ContractedRationalSkeleton (.mul f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w (rationalMulPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_mul, fractionalApply_rationalMulPathMatrix, hc]
  · rw [fractionalDenominator_rationalMulPathMatrix]
    exact one_ne_zero
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]
noncomputable def contractedRationalSkeletonDivLeft [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton f) (hg : yLeafCount g = 0)
    (hden : splitEval g ≠ 0) :
    ContractedRationalSkeleton (.div f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero g hg).choose_spec
  refine contractedRationalSkeletonCompose w (rationalDivPathMatrix c)
    ?_ ?_ ?_
  · rw [splitEval_div, fractionalApply_rationalDivPathMatrix, hc]
  · rw [fractionalDenominator_rationalDivPathMatrix]
    rw [hc] at hden
    exact hden
  · change yLeafCount f + yLeafCount g = yLeafCount f
    rw [hg, Nat.add_zero]
noncomputable def contractedRationalSkeletonDivRight [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (w : ContractedRationalSkeleton g) (hf : yLeafCount f = 0)
    (hden : splitEval g ≠ 0) :
    ContractedRationalSkeleton (.div f g) := by
  let c := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose
  have hc := (exists_splitEval_eq_algebraMap_of_yLeafCount_eq_zero f hf).choose_spec
  refine contractedRationalSkeletonCompose w
    (rationalReverseDivPathMatrix c) ?_ ?_ ?_
  · rw [splitEval_div, fractionalApply_rationalReverseDivPathMatrix, hc]
  · rwa [fractionalDenominator_rationalReverseDivPathMatrix]
  · change yLeafCount f + yLeafCount g = yLeafCount g
    rw [hf, Nat.zero_add]
noncomputable def contractedRationalSkeletonAddBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.add f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· + ·)
    (fun K _ _ hx hy => K.add_mem hx hy)
    (splitEval_add f g) rfl
noncomputable def contractedRationalSkeletonSubBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.sub f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· - ·)
    (fun K _ _ hx hy => K.sub_mem hx hy)
    (splitEval_sub f g) rfl
noncomputable def contractedRationalSkeletonMulBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.mul f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· * ·)
    (fun K _ _ hx hy => K.mul_mem hx hy)
    (splitEval_mul f g) rfl
noncomputable def contractedRationalSkeletonDivBinary [Field F]
    {f g : RationalFormula (Y ⊕ Z) F}
    (wf : ContractedRationalSkeleton f)
    (wg : ContractedRationalSkeleton g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedRationalSkeleton (.div f g) :=
  contractedRationalSkeletonMerge wf wg hf hg (· / ·)
    (fun K _ _ hx hy => K.div_mem hx hy)
    (splitEval_div f g) rfl
end RationalSkeletonContraction
end RationalFormula
abbrev matchingOutside {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) :=
  {z : Fin n × Fin n // z ∉ Set.range d}
noncomputable def matchingVariableEquiv {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) :
    Y ⊕ matchingOutside d ≃ Fin n × Fin n := by
  classical
  exact
    (Equiv.sumCongr (Equiv.ofInjective d d.injective)
      (Equiv.refl (matchingOutside d))).trans
        (Equiv.Set.sumCompl (Set.range d))
@[simp] theorem matchingVariableEquiv_inl {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (y : Y) :
    matchingVariableEquiv d (.inl y) = d y := by
  classical
  change
    (Equiv.Set.sumCompl (Set.range d))
      (.inl ((Equiv.ofInjective d d.injective) y)) = d y
  exact Equiv.Set.sumCompl_apply_inl (Set.range d)
    ((Equiv.ofInjective d d.injective) y)
@[simp] theorem matchingVariableEquiv_inr {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (z : matchingOutside d) :
    matchingVariableEquiv d (.inr z) = z.1 := by
  classical
  change (Equiv.Set.sumCompl (Set.range d)) (.inr z) = z.1
  exact Equiv.Set.sumCompl_apply_inr (Set.range d) z
noncomputable def matchingMarkedPermanent {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) :
    MvPolynomial (Y ⊕ matchingOutside d) ℂ :=
  MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm
    (permanentPolynomial n)
noncomputable def matchingSquarefreeMonomial {Y : Type u}
    (S : Finset Y) : Y →₀ ℕ :=
  ∑ y ∈ S, Finsupp.single y 1
@[simp] theorem matchingSquarefreeMonomial_apply {Y : Type u}
    [DecidableEq Y]
    (S : Finset Y) (y : Y) :
    matchingSquarefreeMonomial S y = if y ∈ S then 1 else 0 := by
  classical
  simp [matchingSquarefreeMonomial, Finsupp.finsetSum_apply,
    Finsupp.single_apply, Finset.sum_ite_eq']
noncomputable def matchingPermutationExponent {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (σ : Equiv.Perm (Fin n)) : Y →₀ ℕ :=
  ∑ i : Fin n,
    match (matchingVariableEquiv d).symm (i, σ i) with
    | .inl y => Finsupp.single y 1
    | .inr _ => 0
noncomputable def matchingPermutationOutsideProduct
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) : MvPolynomial (matchingOutside d) ℂ :=
  ∏ i : Fin n,
    match (matchingVariableEquiv d).symm (i, σ i) with
    | .inl _ => 1
    | .inr z => MvPolynomial.X z
noncomputable def matchingPermutationOutsideFactor
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    MvPolynomial (matchingOutside d) ℂ :=
  match (matchingVariableEquiv d).symm (i, σ i) with
  | .inl _ => 1
  | .inr z => MvPolynomial.X z
noncomputable def matchingBlockIndexEquiv (ell m : ℕ) :
    ((Fin ell ⊕ Fin ell) ⊕ Fin m) ≃ Fin ((ell + ell) + m) :=
  (Equiv.sumCongr
    (finSumFinEquiv : Fin ell ⊕ Fin ell ≃ Fin (ell + ell))
    (Equiv.refl (Fin m))).trans finSumFinEquiv
noncomputable def matchingDiagonalEmbedding (ell m : ℕ) :
    (Fin ell ⊕ Fin ell) ↪
      Fin ((ell + ell) + m) × Fin ((ell + ell) + m) where
  toFun y :=
    (matchingBlockIndexEquiv ell m (.inl y),
      matchingBlockIndexEquiv ell m (.inl y))
  inj' := by
    intro x y h
    exact Sum.inl_injective
      ((matchingBlockIndexEquiv ell m).injective
        (congrArg Prod.fst h))
noncomputable def matchingExternalEntry
    (ell m : ℕ) (a b : Fin m) :
    matchingOutside (matchingDiagonalEmbedding ell m) := by
  refine ⟨(matchingBlockIndexEquiv ell m (.inr a),
    matchingBlockIndexEquiv ell m (.inr b)), ?_⟩
  rintro ⟨y, hy⟩
  have hrow := congrArg Prod.fst hy
  have hsum :
      (Sum.inl y : (Fin ell ⊕ Fin ell) ⊕ Fin m) = .inr a :=
    (matchingBlockIndexEquiv ell m).injective hrow
  cases hsum
noncomputable def matchingPermanentSpecialization
    {ell m : ℕ} (p q : Fin m → ℂ) :
    matchingOutside (matchingDiagonalEmbedding ell m) → ℂ :=
  fun z =>
    match (matchingBlockIndexEquiv ell m).symm z.1.1,
        (matchingBlockIndexEquiv ell m).symm z.1.2 with
    | .inl _, .inl _ => 0
    | .inl (.inl u), .inr b => p b ^ (2 ^ (u : ℕ))
    | .inl (.inr _), .inr _ => 1
    | .inr _, .inl (.inl _) => 1
    | .inr a, .inl (.inr v) => q a ^ (2 ^ (v : ℕ))
    | .inr _, .inr _ => 1
structure MatchingCrossData (T A B : Type*) where
  rows : T ↪ B
  cols : T ↪ A
  remainder :
    {a : A // a ∉ Set.range cols} ≃
      {b : B // b ∉ Set.range rows}
noncomputable def MatchingCrossData.assemble
    {T A B : Type*} (c : MatchingCrossData T A B) :
    T ⊕ A ≃ T ⊕ B := by
  classical
  let ce : T ≃ Set.range c.cols :=
    Equiv.ofInjective c.cols c.cols.injective
  let re : T ≃ Set.range c.rows :=
    Equiv.ofInjective c.rows c.rows.injective
  let splitA : A ≃ T ⊕ {a : A // a ∉ Set.range c.cols} :=
    (Equiv.Set.sumCompl (Set.range c.cols)).symm.trans
      (Equiv.sumCongr ce.symm (Equiv.refl _))
  let mergeB : T ⊕ {b : B // b ∉ Set.range c.rows} ≃ B :=
    (Equiv.sumCongr re (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range c.rows))
  exact
    (Equiv.sumCongr (Equiv.refl T) splitA).trans
      ((Equiv.sumAssoc T T _).symm.trans
        ((Equiv.sumCongr (Equiv.sumComm T T) (Equiv.refl _)).trans
          ((Equiv.sumAssoc T T _).trans
            (Equiv.sumCongr (Equiv.refl T)
              ((Equiv.sumCongr (Equiv.refl T) c.remainder).trans
                mergeB)))))
@[simp] theorem MatchingCrossData.assemble_inl
    {T A B : Type*} (c : MatchingCrossData T A B) (t : T) :
    c.assemble (.inl t) = .inr (c.rows t) := by
  classical
  change
    Sum.inr ((Equiv.Set.sumCompl (Set.range c.rows))
      (.inl ((Equiv.ofInjective c.rows c.rows.injective) t))) =
        Sum.inr (c.rows t)
  rfl
@[simp] theorem MatchingCrossData.assemble_cols
    {T A B : Type*} (c : MatchingCrossData T A B) (t : T) :
    c.assemble (.inr (c.cols t)) = .inl t := by
  classical
  simp [MatchingCrossData.assemble,
    Equiv.Set.sumCompl_symm_apply_of_mem]
@[simp] theorem MatchingCrossData.assemble_remainder
    {T A B : Type*} (c : MatchingCrossData T A B)
    (a : {a : A // a ∉ Set.range c.cols}) :
    c.assemble (.inr a.1) = .inr (c.remainder a).1 := by
  classical
  simp only [MatchingCrossData.assemble, Equiv.trans_apply,
    Equiv.sumCongr_apply, Equiv.coe_refl, Equiv.coe_trans, Sum.map_inr,
    Function.comp_apply,
    Equiv.Set.sumCompl_symm_apply_of_notMem a.property,
    Subtype.coe_eta, id_eq, Equiv.sumAssoc_symm_apply_inr_inr,
    Equiv.sumComm_apply, Equiv.sumAssoc_apply_inr, Sum.inr.injEq]
  exact Equiv.Set.sumCompl_apply_inr (Set.range c.rows)
    (c.remainder a)
theorem matching_card_compl_range
    {T A : Type*} [Fintype T] [Fintype A] [DecidableEq A]
    (f : T ↪ A) :
    Fintype.card {a : A // a ∉ Set.range f} =
      Fintype.card A - Fintype.card T := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_range]
abbrev MatchingCrossPermutation (T A B : Type*) :=
  {σ : T ⊕ A ≃ T ⊕ B //
    ∀ t : T, ∃ b : B, σ (.inl t) = .inr b}
noncomputable def matchingCrossRows {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) : T ↪ B where
  toFun t := Classical.choose (σ.property t)
  inj' := by
    intro x y h
    apply Sum.inl_injective
    apply σ.1.injective
    calc
      σ.1 (.inl x) = .inr (Classical.choose (σ.property x)) :=
        Classical.choose_spec (σ.property x)
      _ = .inr (Classical.choose (σ.property y)) :=
        congrArg Sum.inr h
      _ = σ.1 (.inl y) :=
        (Classical.choose_spec (σ.property y)).symm
theorem matchingCrossRows_spec {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) (t : T) :
    σ.1 (.inl t) = .inr (matchingCrossRows σ t) :=
  Classical.choose_spec (σ.property t)
theorem matchingCrossCols_exists {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) (t : T) :
    ∃ a : A, σ.1.symm (.inl t) = .inr a := by
  classical
  cases h : σ.1.symm (.inl t) with
  | inl u =>
      obtain ⟨b, hb⟩ := σ.property u
      have hu : σ.1 (.inl u) = .inl t := by
        calc
          σ.1 (.inl u) = σ.1 (σ.1.symm (.inl t)) := by rw [h]
          _ = .inl t := σ.1.apply_symm_apply _
      rw [hu] at hb
      cases hb
  | inr a => exact ⟨a, rfl⟩
noncomputable def matchingCrossCols {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) : T ↪ A where
  toFun t := Classical.choose (matchingCrossCols_exists σ t)
  inj' := by
    intro x y h
    apply Sum.inl_injective
    apply σ.1.symm.injective
    calc
      σ.1.symm (.inl x) =
        .inr (Classical.choose (matchingCrossCols_exists σ x)) :=
          Classical.choose_spec (matchingCrossCols_exists σ x)
      _ = .inr (Classical.choose (matchingCrossCols_exists σ y)) := by
        exact congrArg Sum.inr h
      _ = σ.1.symm (.inl y) :=
        (Classical.choose_spec (matchingCrossCols_exists σ y)).symm
theorem matchingCrossCols_spec {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) (t : T) :
    σ.1.symm (.inl t) = .inr (matchingCrossCols σ t) :=
  Classical.choose_spec (matchingCrossCols_exists σ t)
theorem matchingCrossResidual_exists {T A B : Type*}
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    ∃ b : {b : B // b ∉ Set.range (matchingCrossRows σ)},
      σ.1 (.inr a.1) = .inr b.1 := by
  classical
  cases h : σ.1 (.inr a.1) with
  | inl t =>
      have hsym := congrArg σ.1.symm h
      rw [σ.1.symm_apply_apply, matchingCrossCols_spec] at hsym
      have ha : a.1 = matchingCrossCols σ t :=
        Sum.inr_injective hsym
      exact False.elim (a.property ⟨t, ha.symm⟩)
  | inr b =>
      have hb : b ∉ Set.range (matchingCrossRows σ) := by
        rintro ⟨t, ht⟩
        have hsame : σ.1 (.inr a.1) = σ.1 (.inl t) := by
          rw [h, matchingCrossRows_spec, ht]
        have hbad :
            (Sum.inr a.1 : T ⊕ A) = .inl t :=
          σ.1.injective hsame
        cases hbad
      exact ⟨⟨b, hb⟩, rfl⟩
noncomputable def matchingCrossResidualValue {T A B : Type*}
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    {b : B // b ∉ Set.range (matchingCrossRows σ)} :=
  Classical.choose (matchingCrossResidual_exists σ a)
theorem matchingCrossResidualValue_spec {T A B : Type*}
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    σ.1 (.inr a.1) = .inr (matchingCrossResidualValue σ a).1 :=
  Classical.choose_spec (matchingCrossResidual_exists σ a)
noncomputable def matchingCrossResidualEmbedding {T A B : Type*}
    (σ : MatchingCrossPermutation T A B) :
    {a : A // a ∉ Set.range (matchingCrossCols σ)} ↪
      {b : B // b ∉ Set.range (matchingCrossRows σ)} where
  toFun := matchingCrossResidualValue σ
  inj' := by
    intro a a' h
    apply Subtype.ext
    apply Sum.inr_injective
    apply σ.1.injective
    rw [matchingCrossResidualValue_spec,
      matchingCrossResidualValue_spec, h]
theorem matchingCrossPermutation_external_card
    {T A B : Type*} [Finite T] [Fintype A] [Fintype B]
    (σ : MatchingCrossPermutation T A B) :
    Fintype.card A = Fintype.card B := by
  letI := Fintype.ofFinite T
  have h := Fintype.card_congr σ.1
  simpa using h
noncomputable def matchingCrossResidualEquiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B) :
    {a : A // a ∉ Set.range (matchingCrossCols σ)} ≃
      {b : B // b ∉ Set.range (matchingCrossRows σ)} := by
  let e := matchingCrossResidualEmbedding σ
  refine Equiv.ofBijective e
    ((Fintype.bijective_iff_injective_and_card e).2
      ⟨e.injective, ?_⟩)
  rw [matching_card_compl_range, matching_card_compl_range,
    matchingCrossPermutation_external_card σ]
noncomputable def MatchingCrossData.ofPermutation
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B) :
    MatchingCrossData T A B where
  rows := matchingCrossRows σ
  cols := matchingCrossCols σ
  remainder := matchingCrossResidualEquiv σ
theorem MatchingCrossData.ofPermutation_remainder_spec
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B)
    (a : {a : A // a ∉ Set.range (matchingCrossCols σ)}) :
    σ.1 (.inr a.1) =
      .inr ((MatchingCrossData.ofPermutation σ).remainder a).1 :=
  matchingCrossResidualValue_spec σ a
@[simp] theorem MatchingCrossData.assemble_symm_inl
    {T A B : Type*} (c : MatchingCrossData T A B) (t : T) :
    c.assemble.symm (.inl t) = .inr (c.cols t) := by
  apply c.assemble.injective
  rw [Equiv.apply_symm_apply, MatchingCrossData.assemble_cols]
theorem MatchingCrossData.assemble_ofPermutation
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (σ : MatchingCrossPermutation T A B) :
    (MatchingCrossData.ofPermutation σ).assemble = σ.1 := by
  classical
  apply Equiv.ext
  intro x
  cases x with
  | inl t =>
      rw [MatchingCrossData.assemble_inl]
      exact (matchingCrossRows_spec σ t).symm
  | inr a =>
      by_cases ha : a ∈ Set.range (matchingCrossCols σ)
      · obtain ⟨t, ht⟩ := ha
        subst a
        have hleft :
            (MatchingCrossData.ofPermutation σ).assemble
              (.inr (matchingCrossCols σ t)) = .inl t :=
          MatchingCrossData.assemble_cols
            (MatchingCrossData.ofPermutation σ) t
        rw [hleft]
        simpa using congrArg σ.1 (matchingCrossCols_spec σ t)
      · have hx := MatchingCrossData.ofPermutation_remainder_spec
          σ (⟨a, ha⟩ : {a : A // a ∉ Set.range (matchingCrossCols σ)})
        rw [MatchingCrossData.assemble_remainder
          (MatchingCrossData.ofPermutation σ)
            (⟨a, ha⟩ : {a : A // a ∉ Set.range (matchingCrossCols σ)})]
        exact hx.symm
theorem MatchingCrossData.assemble_injective
    {T A B : Type*} :
    Function.Injective
      (MatchingCrossData.assemble (T := T) (A := A) (B := B)) := by
  classical
  intro c d h
  have hrows : c.rows = d.rows := by
    apply Function.Embedding.ext
    intro t
    apply Sum.inr_injective
    calc
      Sum.inr (c.rows t) = c.assemble (.inl t) :=
        (MatchingCrossData.assemble_inl c t).symm
      _ = d.assemble (.inl t) := DFunLike.congr_fun h (.inl t)
      _ = Sum.inr (d.rows t) :=
        MatchingCrossData.assemble_inl d t
  have hcols : c.cols = d.cols := by
    apply Function.Embedding.ext
    intro t
    apply Sum.inr_injective
    calc
      Sum.inr (c.cols t) = c.assemble.symm (.inl t) :=
        (MatchingCrossData.assemble_symm_inl c t).symm
      _ = d.assemble.symm (.inl t) := by rw [h]
      _ = Sum.inr (d.cols t) :=
        MatchingCrossData.assemble_symm_inl d t
  cases c with
  | mk cr cc ce =>
      cases d with
      | mk dr dc de =>
          change cr = dr at hrows
          subst dr
          change cc = dc at hcols
          subst dc
          congr 1
          apply Equiv.ext
          intro a
          apply Subtype.ext
          apply Sum.inr_injective
          calc
            Sum.inr (ce a).1 =
                (MatchingCrossData.mk cr cc ce).assemble (.inr a.1) :=
              (MatchingCrossData.assemble_remainder
                (MatchingCrossData.mk cr cc ce) a).symm
            _ = (MatchingCrossData.mk cr cc de).assemble (.inr a.1) :=
              DFunLike.congr_fun h (.inr a.1)
            _ = Sum.inr (de a).1 :=
              MatchingCrossData.assemble_remainder
                (MatchingCrossData.mk cr cc de) a
noncomputable def MatchingCrossData.toPermutation
    {T A B : Type*} (c : MatchingCrossData T A B) :
    MatchingCrossPermutation T A B :=
  ⟨c.assemble, fun t => ⟨c.rows t, c.assemble_inl t⟩⟩
noncomputable def matchingCrossPermutationEquiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    MatchingCrossPermutation T A B ≃ MatchingCrossData T A B where
  toFun := MatchingCrossData.ofPermutation
  invFun := MatchingCrossData.toPermutation
  left_inv σ := by
    apply Subtype.ext
    exact MatchingCrossData.assemble_ofPermutation σ
  right_inv c := by
    apply MatchingCrossData.assemble_injective
    exact MatchingCrossData.assemble_ofPermutation
      (MatchingCrossData.toPermutation c)
noncomputable def matchingCrossDataSigmaEquiv (T A B : Type*) :
    MatchingCrossData T A B ≃
      (Σ rows : (T ↪ B), Σ cols : (T ↪ A),
        {a : A // a ∉ Set.range cols} ≃
          {b : B // b ∉ Set.range rows}) where
  toFun c := ⟨c.rows, c.cols, c.remainder⟩
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv c := by cases c; rfl
  right_inv z := by rcases z with ⟨rows, cols, remainder⟩; rfl
noncomputable def matchingCrossPermutationSigmaEquiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    MatchingCrossPermutation T A B ≃
      (Σ rows : (T ↪ B), Σ cols : (T ↪ A),
        {a : A // a ∉ Set.range cols} ≃
          {b : B // b ∉ Set.range rows}) :=
  matchingCrossPermutationEquiv.trans
    (matchingCrossDataSigmaEquiv T A B)
noncomputable instance matchingCrossPermutationFintype
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    Fintype (MatchingCrossPermutation T A B) := by
  classical
  exact Fintype.ofEquiv _
    (matchingCrossPermutationSigmaEquiv
      (T := T) (A := A) (B := B)).symm
@[simp] theorem matchingCrossRows_toPermutation
    {T A B : Type*} (c : MatchingCrossData T A B) :
    matchingCrossRows c.toPermutation = c.rows := by
  apply Function.Embedding.ext
  intro t
  apply Sum.inr_injective
  calc
    Sum.inr (matchingCrossRows c.toPermutation t) =
        c.toPermutation.1 (.inl t) :=
      (matchingCrossRows_spec c.toPermutation t).symm
    _ = Sum.inr (c.rows t) := c.assemble_inl t
@[simp] theorem matchingCrossCols_toPermutation
    {T A B : Type*} (c : MatchingCrossData T A B) :
    matchingCrossCols c.toPermutation = c.cols := by
  apply Function.Embedding.ext
  intro t
  apply Sum.inr_injective
  calc
    Sum.inr (matchingCrossCols c.toPermutation t) =
        c.toPermutation.1.symm (.inl t) :=
      (matchingCrossCols_spec c.toPermutation t).symm
    _ = c.assemble.symm (.inl t) := rfl
    _ = Sum.inr (c.cols t) := c.assemble_symm_inl t
def matchingBinaryDegree {ell : ℕ} (P : Finset (Fin ell)) : ℕ :=
  ∑ u ∈ P, 2 ^ (u : ℕ)
noncomputable def matchingInjectionSum {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) : F := by
  classical
  exact ∑ rho : (↥P ↪ Fin m), ∏ u : ↥P, p (rho u) ^ (2 ^ (u.1 : ℕ))
noncomputable def matchingPolynomial {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) : Polynomial F :=
  if hP : P.Nonempty then
    Polynomial.C (matchingInjectionSum p P) -
      ∑ u : ↥P,
        (Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
          matchingPolynomial p (P.erase u.1)
  else
    1
termination_by P.card
decreasing_by
  exact Finset.card_erase_lt_of_mem u.property
@[simp] theorem matchingPolynomial_empty {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) :
    matchingPolynomial (ell := ell) p ∅ = 1 := by
  simp [matchingPolynomial]
@[simp] theorem matchingBinaryDegree_empty (ell : ℕ) :
    matchingBinaryDegree (ell := ell) ∅ = 0 := by
  simp [matchingBinaryDegree]
def matchingEraseEmbedding {ell m : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) (b : Fin m)
    (rho : ↥P ↪ Fin m) (hrho : rho u = b) :
    ↥(P.erase u.1) ↪ {j : Fin m // j ≠ b} where
  toFun v :=
    ⟨rho ⟨v.1, (Finset.mem_erase.mp v.property).2⟩, by
      intro hv
      have hsame := rho.injective (hv.trans hrho.symm)
      exact (Finset.mem_erase.mp v.property).1
        (congrArg Subtype.val hsame)⟩
  inj' := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun x : ↥P => x.1)
      (rho.injective (congrArg Subtype.val h))
def matchingInsertEmbedding {ell m : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) (b : Fin m)
    (rho : ↥(P.erase u.1) ↪ {j : Fin m // j ≠ b}) :
    ↥P ↪ Fin m where
  toFun v :=
    if hv : v.1 = u.1 then b
    else (rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).1
  inj' := by
    intro v w h
    by_cases hv : v.1 = u.1
    · by_cases hw : w.1 = u.1
      · exact Subtype.ext (hv.trans hw.symm)
      · exfalso
        have heq :
            (rho ⟨w.1, Finset.mem_erase.mpr ⟨hw, w.property⟩⟩).1 = b := by
          simpa [hv, hw] using h.symm
        exact (rho ⟨w.1, Finset.mem_erase.mpr ⟨hw, w.property⟩⟩).property heq
    · by_cases hw : w.1 = u.1
      · exfalso
        have heq :
            (rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).1 = b := by
          simpa [hv, hw] using h
        exact (rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).property heq
      · apply Subtype.ext
        have himage :
            rho ⟨v.1, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩ =
              rho ⟨w.1, Finset.mem_erase.mpr ⟨hw, w.property⟩⟩ := by
          apply Subtype.ext
          simpa [hv, hw] using h
        exact congrArg (fun x : ↥(P.erase u.1) => x.1)
          (rho.injective himage)
noncomputable def matchingHitEmbeddingEquiv {ell m : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) (b : Fin m) :
    {rho : ↥P ↪ Fin m // rho u = b} ≃
      (↥(P.erase u.1) ↪ {j : Fin m // j ≠ b}) where
  toFun rho := matchingEraseEmbedding u b rho.1 rho.2
  invFun rho :=
    ⟨matchingInsertEmbedding u b rho, by
      simp [matchingInsertEmbedding]⟩
  left_inv rho := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro v
    by_cases hv : v = u
    · subst v
      simpa [matchingInsertEmbedding] using rho.property.symm
    · have hv' : v.1 ≠ u.1 := fun h => hv (Subtype.ext h)
      change
        (if h : v.1 = u.1 then b
          else (matchingEraseEmbedding u b rho.1 rho.2
            ⟨v.1, Finset.mem_erase.mpr ⟨h, v.property⟩⟩).1) = rho.1 v
      rw [dif_neg hv']
      rfl
  right_inv rho := by
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    have hv : v.1 ≠ u.1 := (Finset.mem_erase.mp v.property).1
    have hv' :
        (⟨v.1, (Finset.mem_erase.mp v.property).2⟩ : ↥P) ≠ u := by
      intro h
      exact hv (congrArg Subtype.val h)
    simp [matchingEraseEmbedding, matchingInsertEmbedding, hv']
noncomputable def matchingAvoidingInjectionSum {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) (b : Fin m) : F := by
  classical
  exact ∑ rho : (↥P ↪ {j : Fin m // j ≠ b}),
    ∏ u : ↥P, p (rho u).1 ^ (2 ^ (u.1 : ℕ))
def matchingEraseIndexEquiv {ell : ℕ}
    {P : Finset (Fin ell)} (u : ↥P) :
    {v : ↥P // v ≠ u} ≃ ↥(P.erase u.1) where
  toFun v :=
    ⟨v.1.1, Finset.mem_erase.mpr
      ⟨fun h => v.2 (Subtype.ext h), v.1.2⟩⟩
  invFun v :=
    ⟨⟨v.1, (Finset.mem_erase.mp v.2).2⟩, by
      intro h
      exact (Finset.mem_erase.mp v.2).1 (congrArg Subtype.val h)⟩
  left_inv _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv _ := by
    apply Subtype.ext
    rfl
def matchingAvoidingEmbeddingEquiv {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m) :
    {rho : ↥P ↪ Fin m // ∀ u, rho u ≠ b} ≃
      (↥P ↪ {j : Fin m // j ≠ b}) where
  toFun rho :=
    { toFun := fun u => ⟨rho.1 u, rho.2 u⟩
      inj' := by
        intro u v h
        exact rho.1.injective (congrArg Subtype.val h) }
  invFun rho :=
    ⟨{ toFun := fun u => (rho u).1
       inj' := by
         intro u v h
         exact rho.injective (Subtype.ext h) },
      fun u => (rho u).2⟩
  left_inv _ := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro _
    rfl
  right_inv _ := by
    apply Function.Embedding.ext
    intro _
    rfl
theorem matching_exists_hit {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m)
    (rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b}) :
    ∃ u : ↥P, rho.1 u = b := by
  classical
  by_contra h
  apply rho.property
  intro u hu
  exact h ⟨u, hu⟩
noncomputable def matchingHitIndex {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m)
    (rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b}) : ↥P :=
  Classical.choose (matching_exists_hit b rho)
theorem matchingHitIndex_spec {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m)
    (rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b}) :
    rho.1 (matchingHitIndex b rho) = b :=
  Classical.choose_spec (matching_exists_hit b rho)
noncomputable def matchingHitSigmaEquiv {ell m : ℕ}
    {P : Finset (Fin ell)} (b : Fin m) :
    {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b} ≃
      Σ u : ↥P, {rho : ↥P ↪ Fin m // rho u = b} where
  toFun rho :=
    ⟨matchingHitIndex b rho, ⟨rho.1, matchingHitIndex_spec b rho⟩⟩
  invFun rho :=
    ⟨rho.2.1, by
      intro h
      exact h rho.1 rho.2.2⟩
  left_inv _ := by
    apply Subtype.ext
    rfl
  right_inv rho := by
    rcases rho with ⟨u, rho⟩
    have hindex :
        matchingHitIndex b
          (⟨rho.1, fun h => h u rho.2⟩ :
            {f : ↥P ↪ Fin m // ¬ ∀ v, f v ≠ b}) = u :=
      rho.1.injective
        ((matchingHitIndex_spec b
          ⟨rho.1, fun h => h u rho.2⟩).trans rho.2.symm)
    refine Sigma.ext hindex ?_
    exact (Subtype.heq_iff_coe_eq (fun f => by
      change
        f (matchingHitIndex b
          (⟨rho.1, fun h => h u rho.2⟩ :
            {g : ↥P ↪ Fin m // ¬ ∀ v, g v ≠ b})) = b ↔ f u = b
      rw [hindex])).2 rfl
@[simp] theorem matchingAvoidingInjectionSum_empty
    {F : Type*} [CommSemiring F] {ell m : ℕ}
    (p : Fin m → F) (b : Fin m) :
    matchingAvoidingInjectionSum (ell := ell) p ∅ b = 1 := by
  classical
  simp [matchingAvoidingInjectionSum]
noncomputable def matchingPolynomialEvaluationMatrix
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p : Fin m → F) (P : Fin m → Finset (Fin ell)) :
    Matrix (Fin m) (Fin m) F :=
  fun b d => (matchingPolynomial p (P d)).eval (p b)
def matchingBitSubset (ell d : ℕ) : Finset (Fin ell) := by
  classical
  exact Finset.univ.filter (fun u : Fin ell => (u : ℕ) ∈ d.bitIndices)
noncomputable def matchingBivariateEvaluationMatrix
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) F :=
  fun de ab =>
    (matchingPolynomial p (P de.1)).eval (p ab.2) *
      (matchingPolynomial q (Q de.2)).eval (q ab.1)
def matchingJacobianWeight (m r s : ℕ) : ℕ :=
  (m - 1 - r - s).factorial *
    (m - 1 - r).descFactorial s *
      (m - 1 - s).descFactorial r
noncomputable def matchingWeightedBivariateEvaluationMatrix
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) F :=
  fun de ab =>
    (matchingJacobianWeight m (P de.1).card (Q de.2).card : F) *
      matchingBivariateEvaluationMatrix p q P Q de ab
noncomputable def matchingBitCoefficientSet (ell m : ℕ)
    (de : Fin m × Fin m) : Finset (Fin ell ⊕ Fin ell) := by
  classical
  exact Finset.univ.filter fun y =>
    match y with
    | .inl u => u ∉ matchingBitSubset ell (de.1 : ℕ)
    | .inr v => v ∉ matchingBitSubset ell (de.2 : ℕ)
@[simp] theorem matchingBitCoefficientSet_mem_inl (ell m : ℕ)
    (de : Fin m × Fin m) (u : Fin ell) :
    Sum.inl u ∈ matchingBitCoefficientSet ell m de ↔
      u ∉ matchingBitSubset ell (de.1 : ℕ) := by
  classical
  simp [matchingBitCoefficientSet]
@[simp] theorem matchingBitCoefficientSet_mem_inr (ell m : ℕ)
    (de : Fin m × Fin m) (v : Fin ell) :
    Sum.inr v ∈ matchingBitCoefficientSet ell m de ↔
      v ∉ matchingBitSubset ell (de.2 : ℕ) := by
  classical
  simp [matchingBitCoefficientSet]
noncomputable def matchingPermanentJacobian
    {ell m : ℕ} (p q : Fin m → ℂ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
  evaluatedJacobianMinor
    (fun de : Fin m × Fin m =>
      coefficientPolynomial
        (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
        (matchingSquarefreeMonomial
          (matchingBitCoefficientSet ell m de)))
    (fun ab : Fin m × Fin m =>
      matchingExternalEntry ell m ab.1 ab.2)
    (matchingPermanentSpecialization p q)
noncomputable def matchingCrossWeight
    {F : Type*} [CommMonoid F] {ell m : ℕ}
    (p q : Fin m → F) (P Q : Finset (Fin ell)) (a b : Fin m)
    (σ : MatchingCrossPermutation (↥P ⊕ ↥Q)
      {j : Fin m // j ≠ a} {j : Fin m // j ≠ b}) : F :=
  (∏ u : ↥P,
    p ((matchingCrossRows σ) (.inl u)).1 ^ (2 ^ (u.1 : ℕ))) *
  (∏ v : ↥Q,
    q ((matchingCrossCols σ) (.inr v)).1 ^ (2 ^ (v.1 : ℕ)))
@[simp] theorem matchingVariableEquiv_symm_marked
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n) (y : Y) :
    (matchingVariableEquiv d).symm (d y) = .inl y := by
  apply (matchingVariableEquiv d).injective
  simp
theorem matchingPermutationExponent_apply
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (y : Y) :
    matchingPermutationExponent d σ y =
      if σ (d y).1 = (d y).2 then 1 else 0 := by
  classical
  have hterm (i : Fin n) :
      (match (matchingVariableEquiv d).symm (i, σ i) with
        | .inl y' => Finsupp.single y' 1
        | .inr _ => (0 : Y →₀ ℕ)) y =
          if (i, σ i) = d y then 1 else 0 := by
    cases h : (matchingVariableEquiv d).symm (i, σ i) with
    | inl y' =>
        have hpair : (i, σ i) = d y' := by
          have heq := congrArg (matchingVariableEquiv d) h
          simpa using heq
        simp [Finsupp.single_apply, hpair, d.injective.eq_iff]
    | inr z =>
        have hne : (i, σ i) ≠ d y := by
          intro heq
          have himage := congrArg (matchingVariableEquiv d).symm heq
          rw [h, matchingVariableEquiv_symm_marked] at himage
          cases himage
        simp [hne]
  calc
    matchingPermutationExponent d σ y =
        ∑ i : Fin n, if (i, σ i) = d y then 1 else 0 := by
          unfold matchingPermutationExponent
          rw [Finsupp.finsetSum_apply]
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = if σ (d y).1 = (d y).2 then 1 else 0 := by
      by_cases hfix : σ (d y).1 = (d y).2
      · have hi (i : Fin n) :
            (i, σ i) = d y ↔ i = (d y).1 := by
          constructor
          · exact congrArg Prod.fst
          · intro heq
            subst i
            exact Prod.ext rfl hfix
        simp_rw [hi]
        simp [hfix]
      · have hi (i : Fin n) : (i, σ i) ≠ d y := by
          intro heq
          have hrow := congrArg Prod.fst heq
          have hcol := congrArg Prod.snd heq
          exact hfix (hrow ▸ hcol)
        simp [hi, hfix]
theorem matchingPermutationExponent_eq_squarefree_iff
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (S : Finset Y) :
    matchingPermutationExponent d σ = matchingSquarefreeMonomial S ↔
      ∀ y : Y, σ (d y).1 = (d y).2 ↔ y ∈ S := by
  classical
  constructor
  · intro h y
    have hy := DFunLike.congr_fun h y
    rw [matchingPermutationExponent_apply,
      matchingSquarefreeMonomial_apply] at hy
    by_cases hfix : σ (d y).1 = (d y).2 <;>
      by_cases hmem : y ∈ S <;> simp_all
  · intro h
    apply Finsupp.ext
    intro y
    rw [matchingPermutationExponent_apply,
      matchingSquarefreeMonomial_apply]
    by_cases hy : y ∈ S <;> simp [hy, (h y).2,
      mt (h y).1]
noncomputable def matchingRestrictComplement
    {α β D : Type*} (e : α ≃ β)
    (r : D ↪ α) (c : D ↪ β)
    (h : ∀ d : D, e (r d) = c d) :
    {x : α // x ∉ Set.range r} ≃
      {y : β // y ∉ Set.range c} := by
  classical
  apply e.subtypeEquiv
  intro x
  apply not_congr
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, (h d).symm⟩
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    apply e.injective
    exact (h d).trans hd
noncomputable def matchingDeletedIndexEmbedding
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) : (↥S ⊕ Unit) ↪ I where
  toFun
    | .inl y => e (.inl y.1)
    | .inr _ => e (.inr a)
  inj' := by
    rintro (x | x) (y | y) h
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Sum.inl_injective (e.injective h)
    · have hbad := e.injective h
      cases hbad
    · have hbad := e.injective h
      cases hbad
    · exact congrArg Sum.inr (Subsingleton.elim x y)
noncomputable def matchingRemainingIndexEmbedding
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    ({y : Y // y ∉ S} ⊕ {j : E // j ≠ a}) ↪ I where
  toFun
    | .inl y => e (.inl y.1)
    | .inr j => e (.inr j.1)
  inj' := by
    rintro (x | x) (y | y) h
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Sum.inl_injective (e.injective h)
    · have hbad := e.injective h
      cases hbad
    · have hbad := e.injective h
      cases hbad
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact Sum.inr_injective (e.injective h)
theorem matchingRemainingIndexEmbedding_range
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    Set.range (matchingRemainingIndexEmbedding e S a) =
      (Set.range (matchingDeletedIndexEmbedding e S a))ᶜ := by
  classical
  ext i
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hxy :
        matchingRemainingIndexEmbedding e S a x =
          matchingDeletedIndexEmbedding e S a y :=
      hx.trans hy.symm
    rcases x with x | x <;> rcases y with y | y
    · have h := e.injective hxy
      have heq : x.1 = y.1 := Sum.inl_injective h
      exact x.property (heq ▸ y.property)
    · cases e.injective hxy
    · cases e.injective hxy
    · have h := e.injective hxy
      exact x.property (Sum.inr_injective h)
  · intro hi
    cases h : e.symm i with
    | inl y =>
        have hyi : e (.inl y) = i := by
          simpa [h] using e.apply_symm_apply i
        have hy : y ∉ S := by
          intro hmem
          exact hi ⟨.inl ⟨y, hmem⟩, hyi⟩
        exact ⟨.inl ⟨y, hy⟩, hyi⟩
    | inr j =>
        have hji : e (.inr j) = i := by
          simpa [h] using e.apply_symm_apply i
        have hj : j ≠ a := by
          intro heq
          subst j
          exact hi ⟨.inr (), hji⟩
        exact ⟨.inr ⟨j, hj⟩, hji⟩
noncomputable def matchingRemainingIndexEquiv
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    ({y : Y // y ∉ S} ⊕ {j : E // j ≠ a}) ≃
      {i : I // i ∉ Set.range (matchingDeletedIndexEmbedding e S a)} :=
  (Equiv.ofInjective
    (matchingRemainingIndexEmbedding e S a)
    (matchingRemainingIndexEmbedding e S a).injective).trans
      (Equiv.setCongr (matchingRemainingIndexEmbedding_range e S a))
noncomputable def matchingReducedEquiv
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (hfix : ∀ y ∈ S,
      σ (matchingBlockIndexEquiv ell m (.inl y)) =
        matchingBlockIndexEquiv ell m (.inl y))
    (hab :
      σ (matchingBlockIndexEquiv ell m (.inr a)) =
        matchingBlockIndexEquiv ell m (.inr b)) :
    ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ a}) ≃
        ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
          {j : Fin m // j ≠ b}) := by
  let e := matchingBlockIndexEquiv ell m
  let r := matchingDeletedIndexEmbedding e S a
  let c := matchingDeletedIndexEmbedding e S b
  have hdel : ∀ d : ↥S ⊕ Unit, σ (r d) = c d := by
    rintro (y | y)
    · exact hfix y.1 y.property
    · exact hab
  exact
    (matchingRemainingIndexEquiv e S a).trans
      ((matchingRestrictComplement σ r c hdel).trans
        (matchingRemainingIndexEquiv e S b).symm)
theorem matchingReducedEquiv_eq_iff
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (hfix : ∀ y ∈ S,
      σ (matchingBlockIndexEquiv ell m (.inl y)) =
        matchingBlockIndexEquiv ell m (.inl y))
    (hab :
      σ (matchingBlockIndexEquiv ell m (.inr a)) =
        matchingBlockIndexEquiv ell m (.inr b))
    (x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ a})
    (y : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ b}) :
    matchingReducedEquiv S a b σ hfix hab x = y ↔
      σ (matchingRemainingIndexEmbedding
        (matchingBlockIndexEquiv ell m) S a x) =
          matchingRemainingIndexEmbedding
            (matchingBlockIndexEquiv ell m) S b y := by
  unfold matchingReducedEquiv
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq, Subtype.ext_iff]
  rfl
noncomputable def matchingBitSurvivorEquiv
    (ell m : ℕ) (de : Fin m × Fin m) :
    (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ≃
        {y : Fin ell ⊕ Fin ell //
          y ∉ matchingBitCoefficientSet ell m de} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro (u | v)
    · exact ⟨.inl u.1, by
        simpa only [matchingBitCoefficientSet_mem_inl,
          not_not] using u.property⟩
    · exact ⟨.inr v.1, by
        simpa only [matchingBitCoefficientSet_mem_inr,
          not_not] using v.property⟩
  · intro y
    cases hy : y.1 with
    | inl u =>
        refine .inl ⟨u, ?_⟩
        have hnot : Sum.inl u ∉ matchingBitCoefficientSet ell m de := by
          simpa [hy] using y.property
        simpa only [matchingBitCoefficientSet_mem_inl, not_not]
          using hnot
    | inr v =>
        refine .inr ⟨v, ?_⟩
        have hnot : Sum.inr v ∉ matchingBitCoefficientSet ell m de := by
          simpa [hy] using y.property
        simpa only [matchingBitCoefficientSet_mem_inr, not_not]
          using hnot
  · rintro (u | v) <;> rfl
  · rintro ⟨y, hy⟩
    cases y <;> rfl
abbrev MatchingBitSelectedPermutation
    (ell m : ℕ) (de ab : Fin m × Fin m) :=
  {σ : Equiv.Perm (Fin ((ell + ell) + m)) //
    matchingPermutationExponent (matchingDiagonalEmbedding ell m) σ =
        matchingSquarefreeMonomial (matchingBitCoefficientSet ell m de) ∧
      σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
        (matchingExternalEntry ell m ab.1 ab.2).1.2}
theorem matchingBitSelectedPermutation_fixed
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitSelectedPermutation ell m de ab)
    (y : Fin ell ⊕ Fin ell)
    (hy : y ∈ matchingBitCoefficientSet ell m de) :
    σ.1 (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y) := by
  have h :=
    (matchingPermutationExponent_eq_squarefree_iff
      (matchingDiagonalEmbedding ell m) σ.1
      (matchingBitCoefficientSet ell m de)).mp σ.property.1 y
  exact h.mpr hy
theorem matchingBitSelectedPermutation_external
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitSelectedPermutation ell m de ab) :
    σ.1 (matchingBlockIndexEquiv ell m (.inr ab.1)) =
      matchingBlockIndexEquiv ell m (.inr ab.2) :=
  σ.property.2
noncomputable def matchingBitReducedEquiv
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitSelectedPermutation ell m de ab) :
    ((↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
        {j : Fin m // j ≠ ab.1}) ≃
      ((↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
          {j : Fin m // j ≠ ab.2}) :=
  (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
    (Equiv.refl _)).trans
      ((matchingReducedEquiv
        (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1
        (matchingBitSelectedPermutation_fixed σ)
        (matchingBitSelectedPermutation_external σ)).trans
          (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
            (Equiv.refl _)))
noncomputable def matchingDeletedRemainingEquiv
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) :
    ((↥S ⊕ Unit) ⊕
      ({y : Y // y ∉ S} ⊕ {j : E // j ≠ a})) ≃ I := by
  classical
  exact
    (Equiv.sumCongr
      (Equiv.ofInjective (matchingDeletedIndexEmbedding e S a)
        (matchingDeletedIndexEmbedding e S a).injective)
      (matchingRemainingIndexEquiv e S a)).trans
        (Equiv.Set.sumCompl
          (Set.range (matchingDeletedIndexEmbedding e S a)))
@[simp] theorem matchingDeletedRemainingEquiv_inl
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E) (x : ↥S ⊕ Unit) :
    matchingDeletedRemainingEquiv e S a (.inl x) =
      matchingDeletedIndexEmbedding e S a x := by
  rfl
@[simp] theorem matchingDeletedRemainingEquiv_inr
    {Y E I : Type*} (e : Y ⊕ E ≃ I)
    (S : Finset Y) (a : E)
    (x : {y : Y // y ∉ S} ⊕ {j : E // j ≠ a}) :
    matchingDeletedRemainingEquiv e S a (.inr x) =
      matchingRemainingIndexEmbedding e S a x := by
  rfl
noncomputable def matchingExtendReducedEquiv
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b})) :
    Equiv.Perm (Fin ((ell + ell) + m)) :=
  (matchingDeletedRemainingEquiv
    (matchingBlockIndexEquiv ell m) S a).symm.trans
      ((Equiv.sumCongr
        (Equiv.refl (↥S ⊕ Unit)) τ).trans
          (matchingDeletedRemainingEquiv
            (matchingBlockIndexEquiv ell m) S b))
theorem matchingExtendReducedEquiv_deleted
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b}))
    (x : ↥S ⊕ Unit) :
    matchingExtendReducedEquiv S a b τ
        (matchingDeletedIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingDeletedIndexEmbedding
        (matchingBlockIndexEquiv ell m) S b x := by
  calc
    matchingExtendReducedEquiv S a b τ
        (matchingDeletedIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingExtendReducedEquiv S a b τ
        (matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S a (.inl x)) := by
            rw [matchingDeletedRemainingEquiv_inl]
    _ = matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S b (.inl x) := by
            simp only [matchingExtendReducedEquiv, Equiv.trans_apply,
              Equiv.symm_apply_apply, Equiv.sumCongr_apply,
              Equiv.refl_apply, Sum.map_inl]
    _ = matchingDeletedIndexEmbedding
          (matchingBlockIndexEquiv ell m) S b x :=
            matchingDeletedRemainingEquiv_inl _ _ _ _
theorem matchingExtendReducedEquiv_remaining
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b}))
    (x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
      {j : Fin m // j ≠ a}) :
    matchingExtendReducedEquiv S a b τ
        (matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingRemainingIndexEmbedding
        (matchingBlockIndexEquiv ell m) S b (τ x) := by
  calc
    matchingExtendReducedEquiv S a b τ
        (matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m) S a x) =
      matchingExtendReducedEquiv S a b τ
        (matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S a (.inr x)) := by
            rw [matchingDeletedRemainingEquiv_inr]
    _ = matchingDeletedRemainingEquiv
          (matchingBlockIndexEquiv ell m) S b (.inr (τ x)) := by
            simp only [matchingExtendReducedEquiv, Equiv.trans_apply,
              Equiv.symm_apply_apply, Equiv.sumCongr_apply,
              Sum.map_inr]
    _ = matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m) S b (τ x) :=
            matchingDeletedRemainingEquiv_inr _ _ _ _
theorem matchingExtendReducedEquiv_fixed
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b}))
    (y : Fin ell ⊕ Fin ell) (hy : y ∈ S) :
    matchingExtendReducedEquiv S a b τ
        (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y) :=
  matchingExtendReducedEquiv_deleted S a b τ
    (.inl ⟨y, hy⟩)
theorem matchingExtendReducedEquiv_external
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b})) :
    matchingExtendReducedEquiv S a b τ
        (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inr b) :=
  matchingExtendReducedEquiv_deleted S a b τ (.inr ())
theorem matchingReducedEquiv_extend
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (τ :
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ a}) ≃
      ({y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
        {j : Fin m // j ≠ b})) :
    matchingReducedEquiv S a b
      (matchingExtendReducedEquiv S a b τ)
      (matchingExtendReducedEquiv_fixed S a b τ)
      (matchingExtendReducedEquiv_external S a b τ) = τ := by
  apply Equiv.ext
  intro x
  apply (matchingReducedEquiv_eq_iff S a b
    (matchingExtendReducedEquiv S a b τ)
    (matchingExtendReducedEquiv_fixed S a b τ)
    (matchingExtendReducedEquiv_external S a b τ)
    x (τ x)).2
  exact matchingExtendReducedEquiv_remaining S a b τ x
theorem matchingExtendReducedEquiv_reduced
    {ell m : ℕ} (S : Finset (Fin ell ⊕ Fin ell))
    (a b : Fin m)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (hfix : ∀ y ∈ S,
      σ (matchingBlockIndexEquiv ell m (.inl y)) =
        matchingBlockIndexEquiv ell m (.inl y))
    (hab :
      σ (matchingBlockIndexEquiv ell m (.inr a)) =
        matchingBlockIndexEquiv ell m (.inr b)) :
    matchingExtendReducedEquiv S a b
      (matchingReducedEquiv S a b σ hfix hab) = σ := by
  apply Equiv.ext
  intro i
  obtain ⟨x, rfl⟩ := (matchingBlockIndexEquiv ell m).surjective i
  cases x with
  | inl y =>
      by_cases hy : y ∈ S
      · rw [matchingExtendReducedEquiv_fixed S a b _ y hy,
          hfix y hy]
      · let x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
            {j : Fin m // j ≠ a} := .inl ⟨y, hy⟩
        have hext := matchingExtendReducedEquiv_remaining
          S a b (matchingReducedEquiv S a b σ hfix hab) x
        have hred :=
          (matchingReducedEquiv_eq_iff S a b σ hfix hab x
            (matchingReducedEquiv S a b σ hfix hab x)).mp rfl
        exact hext.trans hred.symm
  | inr j =>
      by_cases hj : j = a
      · subst j
        rw [matchingExtendReducedEquiv_external S a b _, hab]
      · let x : {y : Fin ell ⊕ Fin ell // y ∉ S} ⊕
            {j : Fin m // j ≠ a} := .inr ⟨j, hj⟩
        have hext := matchingExtendReducedEquiv_remaining
          S a b (matchingReducedEquiv S a b σ hfix hab) x
        have hred :=
          (matchingReducedEquiv_eq_iff S a b σ hfix hab x
            (matchingReducedEquiv S a b σ hfix hab x)).mp rfl
        exact hext.trans hred.symm
abbrev MatchingBitCrossSelectedPermutation
    (ell m : ℕ) (de ab : Fin m × Fin m) :=
  {σ : MatchingBitSelectedPermutation ell m de ab //
    ∀ y : {y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de},
      ∃ j : Fin m,
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
          matchingBlockIndexEquiv ell m (.inr j)}
theorem matchingBitCrossSelectedPermutation_external_ne
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (y : {y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de})
    (j : Fin m)
    (himage :
      σ.1.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
        matchingBlockIndexEquiv ell m (.inr j)) :
    j ≠ ab.2 := by
  intro hj
  subst j
  have hsame :
      σ.1.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
        σ.1.1 (matchingBlockIndexEquiv ell m (.inr ab.1)) :=
    himage.trans (matchingBitSelectedPermutation_external σ.1).symm
  have hbad :=
    (matchingBlockIndexEquiv ell m).injective
      (σ.1.1.injective hsame)
  cases hbad
noncomputable def matchingBitCrossSelectedToCross
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2} := by
  refine ⟨matchingBitReducedEquiv σ.1, ?_⟩
  intro t
  let y := matchingBitSurvivorEquiv ell m de t
  obtain ⟨j, hj⟩ := σ.property y
  have hne := matchingBitCrossSelectedPermutation_external_ne σ y j hj
  refine ⟨⟨j, hne⟩, ?_⟩
  have hred :=
    (matchingReducedEquiv_eq_iff
      (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
      (matchingBitSelectedPermutation_fixed σ.1)
      (matchingBitSelectedPermutation_external σ.1)
      (.inl y) (.inr ⟨j, hne⟩)).2 hj
  unfold matchingBitReducedEquiv
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inl]
  rw [hred]
  rfl
noncomputable def matchingBitUnreduceCrossEquiv
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2}) :
    ({y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de} ⊕
        {j : Fin m // j ≠ ab.1}) ≃
      ({y : Fin ell ⊕ Fin ell //
        y ∉ matchingBitCoefficientSet ell m de} ⊕
          {j : Fin m // j ≠ ab.2}) :=
  (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
    (Equiv.refl _)).trans
      (τ.1.trans
        (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
          (Equiv.refl _)))
theorem matchingBitUnreduceCrossEquiv_internal
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2})
    (y : {y : Fin ell ⊕ Fin ell //
      y ∉ matchingBitCoefficientSet ell m de}) :
    ∃ j : {j : Fin m // j ≠ ab.2},
      matchingBitUnreduceCrossEquiv τ (.inl y) = .inr j := by
  obtain ⟨j, hj⟩ :=
    τ.property ((matchingBitSurvivorEquiv ell m de).symm y)
  refine ⟨j, ?_⟩
  unfold matchingBitUnreduceCrossEquiv
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inl]
  rw [hj]
  rfl
noncomputable def matchingBitCrossToSelected
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2}) :
    MatchingBitCrossSelectedPermutation ell m de ab := by
  let S := matchingBitCoefficientSet ell m de
  let r := matchingBitUnreduceCrossEquiv τ
  let σ := matchingExtendReducedEquiv S ab.1 ab.2 r
  have hfixed :
      matchingPermutationExponent (matchingDiagonalEmbedding ell m) σ =
        matchingSquarefreeMonomial S := by
    apply
      (matchingPermutationExponent_eq_squarefree_iff
        (matchingDiagonalEmbedding ell m) σ S).2
    intro y
    constructor
    · intro hfix
      by_contra hy
      let yy : {y : Fin ell ⊕ Fin ell // y ∉ S} := ⟨y, hy⟩
      obtain ⟨j, hj⟩ := matchingBitUnreduceCrossEquiv_internal τ yy
      have hmove := matchingExtendReducedEquiv_remaining
        S ab.1 ab.2 r (.inl yy)
      rw [hj] at hmove
      have hbad :
          (Sum.inl y : (Fin ell ⊕ Fin ell) ⊕ Fin m) =
            .inr j.1 := by
        apply (matchingBlockIndexEquiv ell m).injective
        exact hfix.symm.trans hmove
      cases hbad
    · intro hy
      exact matchingExtendReducedEquiv_fixed
        S ab.1 ab.2 r y hy
  have hexternal :
      σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
        (matchingExternalEntry ell m ab.1 ab.2).1.2 :=
    matchingExtendReducedEquiv_external S ab.1 ab.2 r
  refine ⟨⟨σ, hfixed, hexternal⟩, ?_⟩
  intro y
  obtain ⟨j, hj⟩ := matchingBitUnreduceCrossEquiv_internal τ y
  refine ⟨j.1, ?_⟩
  have hmove := matchingExtendReducedEquiv_remaining
    S ab.1 ab.2 r (.inl y)
  rw [hj] at hmove
  exact hmove
theorem matchingBitUnreduceCrossEquiv_toCross
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    matchingBitUnreduceCrossEquiv
      (matchingBitCrossSelectedToCross σ) =
        matchingReducedEquiv
          (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
          (matchingBitSelectedPermutation_fixed σ.1)
          (matchingBitSelectedPermutation_external σ.1) := by
  apply Equiv.ext
  intro x
  unfold matchingBitUnreduceCrossEquiv
  change
    ((Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
      (Equiv.refl _)).trans
      ((matchingBitReducedEquiv σ.1).trans
        (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
          (Equiv.refl _)))) x = _
  unfold matchingBitReducedEquiv
  simp [Equiv.trans_apply, Equiv.sumCongr_apply]
theorem matchingBitCrossSelectedToCross_toSelected
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (τ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2}) :
    matchingBitCrossSelectedToCross
      (matchingBitCrossToSelected τ) = τ := by
  apply Subtype.ext
  change
    (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
      (Equiv.refl _)).trans
      ((matchingReducedEquiv
        (matchingBitCoefficientSet ell m de) ab.1 ab.2
        (matchingExtendReducedEquiv
          (matchingBitCoefficientSet ell m de) ab.1 ab.2
          (matchingBitUnreduceCrossEquiv τ)) _ _).trans
        (Equiv.sumCongr (matchingBitSurvivorEquiv ell m de).symm
          (Equiv.refl _))) = τ.1
  rw [matchingReducedEquiv_extend]
  apply Equiv.ext
  intro x
  unfold matchingBitUnreduceCrossEquiv
  simp [Equiv.trans_apply, Equiv.sumCongr_apply]
theorem matchingBitCrossToSelected_toCross
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    matchingBitCrossToSelected
      (matchingBitCrossSelectedToCross σ) = σ := by
  apply Subtype.ext
  apply Subtype.ext
  change
    matchingExtendReducedEquiv
      (matchingBitCoefficientSet ell m de) ab.1 ab.2
      (matchingBitUnreduceCrossEquiv
        (matchingBitCrossSelectedToCross σ)) = σ.1.1
  rw [matchingBitUnreduceCrossEquiv_toCross]
  exact matchingExtendReducedEquiv_reduced
    (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
    (matchingBitSelectedPermutation_fixed σ.1)
    (matchingBitSelectedPermutation_external σ.1)
noncomputable def matchingBitCrossSelectedEquiv
    (ell m : ℕ) (de ab : Fin m × Fin m) :
    MatchingBitCrossSelectedPermutation ell m de ab ≃
      MatchingCrossPermutation
        (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
          ↥(matchingBitSubset ell (de.2 : ℕ)))
        {j : Fin m // j ≠ ab.1}
        {j : Fin m // j ≠ ab.2} where
  toFun := matchingBitCrossSelectedToCross
  invFun := matchingBitCrossToSelected
  left_inv := matchingBitCrossToSelected_toCross
  right_inv := matchingBitCrossSelectedToCross_toSelected
theorem matchingBitCrossSelected_reduced_eq_iff
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (x : (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
        {j : Fin m // j ≠ ab.1})
    (z : (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ⊕
        {j : Fin m // j ≠ ab.2}) :
    (matchingBitCrossSelectedToCross σ).1 x = z ↔
      σ.1.1
        (matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m)
          (matchingBitCoefficientSet ell m de) ab.1
          ((Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
            (Equiv.refl _)) x)) =
        matchingRemainingIndexEmbedding
          (matchingBlockIndexEquiv ell m)
          (matchingBitCoefficientSet ell m de) ab.2
          ((Equiv.sumCongr (matchingBitSurvivorEquiv ell m de)
            (Equiv.refl _)) z) := by
  change matchingBitReducedEquiv σ.1 x = z ↔ _
  unfold matchingBitReducedEquiv
  simp only [Equiv.trans_apply]
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  exact matchingReducedEquiv_eq_iff
    (matchingBitCoefficientSet ell m de) ab.1 ab.2 σ.1.1
    (matchingBitSelectedPermutation_fixed σ.1)
    (matchingBitSelectedPermutation_external σ.1) _ _
theorem matchingBitCrossSelected_full_rows_spec
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) :
    σ.1.1
        (matchingBlockIndexEquiv ell m
          (.inl (matchingBitSurvivorEquiv ell m de t).1)) =
      matchingBlockIndexEquiv ell m
        (.inr (matchingCrossRows
          (matchingBitCrossSelectedToCross σ) t).1) := by
  have h :=
    (matchingBitCrossSelected_reduced_eq_iff σ
      (.inl t)
      (.inr (matchingCrossRows
        (matchingBitCrossSelectedToCross σ) t))).mp
      (matchingCrossRows_spec
        (matchingBitCrossSelectedToCross σ) t)
  exact h
noncomputable def matchingBitCrossSelectedSupportEmbedding
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) ↪
        Fin ((ell + ell) + m) where
  toFun
    | .inl u =>
        matchingBlockIndexEquiv ell m (.inl (.inl u.1))
    | .inr v =>
        σ.1.1.symm
          (matchingBlockIndexEquiv ell m (.inl (.inr v.1)))
  inj' := by
    rintro (u | v) (u' | v') h
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Sum.inl_injective
        (Sum.inl_injective
          ((matchingBlockIndexEquiv ell m).injective h))
    · have hact := congrArg σ.1.1 h
      rw [Equiv.apply_symm_apply] at hact
      have hrow := matchingBitCrossSelected_full_rows_spec σ (.inl u)
      change
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl (.inl u.1))) =
          matchingBlockIndexEquiv ell m
            (.inr (matchingCrossRows
              (matchingBitCrossSelectedToCross σ) (.inl u)).1)
        at hrow
      rw [hrow] at hact
      cases (matchingBlockIndexEquiv ell m).injective hact
    · have hact := congrArg σ.1.1 h.symm
      rw [Equiv.apply_symm_apply] at hact
      have hrow := matchingBitCrossSelected_full_rows_spec σ (.inl u')
      change
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl (.inl u'.1))) =
          matchingBlockIndexEquiv ell m
            (.inr (matchingCrossRows
              (matchingBitCrossSelectedToCross σ) (.inl u')).1)
        at hrow
      rw [hrow] at hact
      cases (matchingBlockIndexEquiv ell m).injective hact
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact Sum.inr_injective
        (Sum.inl_injective
          ((matchingBlockIndexEquiv ell m).injective
            (σ.1.1.symm.injective h)))
namespace Formula
variable {Y : Type u} {Z : Type v} {F : Type w}
def yLeafCount : Formula (Y ⊕ Z) F → ℕ
  | .var (.inl _) => 1
  | .var (.inr _) => 0
  | .const _ => 0
  | .add f g => yLeafCount f + yLeafCount g
  | .sub f g => yLeafCount f + yLeafCount g
  | .mul f g => yLeafCount f + yLeafCount g
noncomputable def splitEval [Field F]
    (f : Formula (Y ⊕ Z) F) : MvPolynomial Y (MvPolynomial Z F) :=
  MvPolynomial.sumAlgEquiv F Y Z (eval f)
@[simp] theorem splitEval_var_inl [Field F] (i : Y) :
    splitEval (Z := Z) (F := F) (.var (.inl i)) = MvPolynomial.X i := by
  simp [splitEval, eval]
@[simp] theorem splitEval_var_inr [Field F] (j : Z) :
    splitEval (Y := Y) (F := F) (.var (.inr j)) =
      MvPolynomial.C (MvPolynomial.X j) := by
  simp [splitEval, eval]
@[simp] theorem splitEval_const [Field F] (c : F) :
    splitEval (Y := Y) (Z := Z) (.const c) =
      MvPolynomial.C (MvPolynomial.C c) := by
  simp [splitEval, eval]
@[simp] theorem splitEval_add [Field F]
    (f g : Formula (Y ⊕ Z) F) :
    splitEval (.add f g) = splitEval f + splitEval g := by
  simp [splitEval, eval]
@[simp] theorem splitEval_sub [Field F]
    (f g : Formula (Y ⊕ Z) F) :
    splitEval (.sub f g) = splitEval f - splitEval g := by
  simp [splitEval, eval]
@[simp] theorem splitEval_mul [Field F]
    (f g : Formula (Y ⊕ Z) F) :
    splitEval (.mul f g) = splitEval f * splitEval g := by
  simp [splitEval, eval]
theorem exists_splitEval_eq_C_of_yLeafCount_eq_zero [Field F]
    (f : Formula (Y ⊕ Z) F) (h : yLeafCount f = 0) :
    ∃ q : MvPolynomial Z F, splitEval f = MvPolynomial.C q := by
  induction f with
  | var i =>
      cases i with
      | inl i => simp [yLeafCount] at h
      | inr i => exact ⟨MvPolynomial.X i, splitEval_var_inr i⟩
  | const c => exact ⟨MvPolynomial.C c, splitEval_const c⟩
  | add f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨qf, hqf⟩ := hf hfzero
      obtain ⟨qg, hqg⟩ := hg hgzero
      refine ⟨qf + qg, ?_⟩
      rw [splitEval_add, hqf, hqg, map_add]
  | sub f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨qf, hqf⟩ := hf hfzero
      obtain ⟨qg, hqg⟩ := hg hgzero
      refine ⟨qf - qg, ?_⟩
      rw [splitEval_sub, hqf, hqg, map_sub]
  | mul f g hf hg =>
      have hfzero : yLeafCount f = 0 := by
        simp only [yLeafCount] at h
        omega
      have hgzero : yLeafCount g = 0 := by
        simp only [yLeafCount] at h
        omega
      obtain ⟨qf, hqf⟩ := hf hfzero
      obtain ⟨qg, hqg⟩ := hg hgzero
      refine ⟨qf * qg, ?_⟩
      rw [splitEval_mul, hqf, hqg, map_mul]
section CoefficientFields
variable [Field F]
theorem coeff_mem_intermediateField_add
    (S : IntermediateField F (FractionRing (MvPolynomial Z F)))
    (p q : MvPolynomial Y (MvPolynomial Z F))
    (hp : ∀ α : Y →₀ ℕ,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α p) ∈ S)
    (hq : ∀ α : Y →₀ ℕ,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α q) ∈ S) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (p + q)) ∈ S := by
  simpa only [map_add, MvPolynomial.coeff_add] using
    S.add_mem (hp α) (hq α)
theorem coeff_mem_intermediateField_sub
    (S : IntermediateField F (FractionRing (MvPolynomial Z F)))
    (p q : MvPolynomial Y (MvPolynomial Z F))
    (hp : ∀ α : Y →₀ ℕ,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α p) ∈ S)
    (hq : ∀ α : Y →₀ ℕ,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α q) ∈ S) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (p - q)) ∈ S := by
  simpa only [map_sub, MvPolynomial.coeff_sub] using
    S.sub_mem (hp α) (hq α)
theorem coeff_mem_intermediateField_mul
    (S : IntermediateField F (FractionRing (MvPolynomial Z F)))
    (p q : MvPolynomial Y (MvPolynomial Z F))
    (hp : ∀ α : Y →₀ ℕ,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α p) ∈ S)
    (hq : ∀ α : Y →₀ ℕ,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α q) ∈ S) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (p * q)) ∈ S := by
  classical
  rw [MvPolynomial.coeff_mul, map_sum]
  apply S.sum_mem
  intro a ha
  rw [map_mul]
  exact S.mul_mem (hp a.1) (hq a.2)
theorem coeff_mem_intermediateField_C
    (S : IntermediateField F (FractionRing (MvPolynomial Z F)))
    (a : MvPolynomial Z F)
    (ha : algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F)) a ∈ S)
    (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (MvPolynomial.C a)) ∈ S := by
  classical
  by_cases hα : α = 0
  · subst α
    simpa using ha
  · rw [MvPolynomial.coeff_C_of_ne_zero hα, map_zero]
    exact S.zero_mem
theorem coeff_mem_intermediateField_X
    (S : IntermediateField F (FractionRing (MvPolynomial Z F)))
    (i : Y) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (MvPolynomial.X i)) ∈ S := by
  classical
  rw [MvPolynomial.coeff_X]
  split <;> simp [S.zero_mem, S.one_mem]
structure ContractedSkeleton (f : Formula (Y ⊕ Z) F) where
  generators : Finset (FractionRing (MvPolynomial Z F))
  slope : MvPolynomial Z F
  intercept : MvPolynomial Z F
  core : MvPolynomial Y (MvPolynomial Z F)
  split_eq : splitEval f = MvPolynomial.C slope * core + MvPolynomial.C intercept
  core_coeff_mem : ∀ α : Y →₀ ℕ,
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
      (MvPolynomial.coeff α core) ∈
        IntermediateField.adjoin F (generators : Set _)
  generator_card : generators.card ≤ 4 * yLeafCount f - 4
noncomputable def contractedSkeletonAffine
    {f h : Formula (Y ⊕ Z) F}
    (w : ContractedSkeleton f) (A B : MvPolynomial Z F)
    (haffine : splitEval h =
      MvPolynomial.C A * splitEval f + MvPolynomial.C B)
    (hleaves : yLeafCount h = yLeafCount f) :
    ContractedSkeleton h := by
  refine
    { generators := w.generators
      slope := A * w.slope
      intercept := A * w.intercept + B
      core := w.core
      split_eq := ?_
      core_coeff_mem := w.core_coeff_mem
      generator_card := ?_ }
  · rw [haffine, w.split_eq]
    simp only [map_mul, map_add]
    ring
  · simpa [hleaves] using w.generator_card
noncomputable def contractedSkeletonBinaryExtras
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g) :
    Finset (FractionRing (MvPolynomial Z F)) := by
  classical
  exact
    {algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F)) wf.slope,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F)) wf.intercept,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F)) wg.slope,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F)) wg.intercept}
noncomputable def contractedSkeletonBinaryGenerators
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g) :
    Finset (FractionRing (MvPolynomial Z F)) := by
  classical
  exact contractedSkeletonBinaryExtras wf wg ∪
    (wf.generators ∪ wg.generators)
theorem contractedSkeletonBinaryGenerators_left_le
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g) :
    IntermediateField.adjoin F (wf.generators : Set _) ≤
      IntermediateField.adjoin F
        (↑(contractedSkeletonBinaryGenerators wf wg) :
          Set (FractionRing (MvPolynomial Z F))) := by
  classical
  apply IntermediateField.adjoin.mono
  intro x hx
  change x ∈ wf.generators at hx
  change x ∈ contractedSkeletonBinaryGenerators wf wg
  unfold contractedSkeletonBinaryGenerators
  exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)
theorem contractedSkeletonBinaryGenerators_right_le
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g) :
    IntermediateField.adjoin F (wg.generators : Set _) ≤
      IntermediateField.adjoin F
        (↑(contractedSkeletonBinaryGenerators wf wg) :
          Set (FractionRing (MvPolynomial Z F))) := by
  classical
  apply IntermediateField.adjoin.mono
  intro x hx
  change x ∈ wg.generators at hx
  change x ∈ contractedSkeletonBinaryGenerators wf wg
  unfold contractedSkeletonBinaryGenerators
  exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)
theorem contractedSkeletonBinaryGenerators_parameter_mem
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g)
    {a : FractionRing (MvPolynomial Z F)}
    (ha : a ∈ contractedSkeletonBinaryExtras wf wg) :
    a ∈ IntermediateField.adjoin F
      (↑(contractedSkeletonBinaryGenerators wf wg) :
        Set (FractionRing (MvPolynomial Z F))) := by
  classical
  apply IntermediateField.subset_adjoin F
    (↑(contractedSkeletonBinaryGenerators wf wg) :
      Set (FractionRing (MvPolynomial Z F)))
  change a ∈ contractedSkeletonBinaryGenerators wf wg
  unfold contractedSkeletonBinaryGenerators
  exact Finset.mem_union_left _ ha
theorem contractedSkeletonBinaryGenerators_card_le
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g) :
    (contractedSkeletonBinaryGenerators wf wg).card ≤
      wf.generators.card + wg.generators.card + 4 := by
  classical
  have hextra : (contractedSkeletonBinaryExtras wf wg).card ≤ 4 := by
    unfold contractedSkeletonBinaryExtras
    exact Finset.card_le_four
  have hunion := Finset.card_union_le
    (contractedSkeletonBinaryExtras wf wg) (wf.generators ∪ wg.generators)
  have hinherited := Finset.card_union_le wf.generators wg.generators
  change ((contractedSkeletonBinaryExtras wf wg) ∪
    (wf.generators ∪ wg.generators)).card ≤
    wf.generators.card + wg.generators.card + 4
  omega
theorem contractedSkeletonBinaryGenerators_coeff_mem_left
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g)
    (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (splitEval f)) ∈
      IntermediateField.adjoin F
        (↑(contractedSkeletonBinaryGenerators wf wg) :
          Set (FractionRing (MvPolynomial Z F))) := by
  classical
  let S : IntermediateField F (FractionRing (MvPolynomial Z F)) :=
    IntermediateField.adjoin F
      (↑(contractedSkeletonBinaryGenerators wf wg) :
        Set (FractionRing (MvPolynomial Z F)))
  change algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
    (MvPolynomial.coeff α (splitEval f)) ∈ S
  rw [wf.split_eq]
  apply coeff_mem_intermediateField_add S
  · intro β
    apply coeff_mem_intermediateField_mul S
    · apply coeff_mem_intermediateField_C S
      exact contractedSkeletonBinaryGenerators_parameter_mem wf wg
        (Finset.mem_insert_self _ _)
    · intro γ
      exact contractedSkeletonBinaryGenerators_left_le wf wg
        (wf.core_coeff_mem γ)
  · apply coeff_mem_intermediateField_C S
    exact contractedSkeletonBinaryGenerators_parameter_mem wf wg
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
theorem contractedSkeletonBinaryGenerators_coeff_mem_right
    {f g : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g)
    (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (splitEval g)) ∈
      IntermediateField.adjoin F
        (↑(contractedSkeletonBinaryGenerators wf wg) :
          Set (FractionRing (MvPolynomial Z F))) := by
  classical
  let S : IntermediateField F (FractionRing (MvPolynomial Z F)) :=
    IntermediateField.adjoin F
      (↑(contractedSkeletonBinaryGenerators wf wg) :
        Set (FractionRing (MvPolynomial Z F)))
  change algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
    (MvPolynomial.coeff α (splitEval g)) ∈ S
  rw [wg.split_eq]
  apply coeff_mem_intermediateField_add S
  · intro β
    apply coeff_mem_intermediateField_mul S
    · apply coeff_mem_intermediateField_C S
      exact contractedSkeletonBinaryGenerators_parameter_mem wf wg
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    · intro γ
      exact contractedSkeletonBinaryGenerators_right_le wf wg
        (wg.core_coeff_mem γ)
  · apply coeff_mem_intermediateField_C S
    exact contractedSkeletonBinaryGenerators_parameter_mem wf wg
      (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
noncomputable def contractedSkeletonBinary
    {f g h : Formula (Y ⊕ Z) F}
    (wf : ContractedSkeleton f) (wg : ContractedSkeleton g)
    (op : MvPolynomial Y (MvPolynomial Z F) →
      MvPolynomial Y (MvPolynomial Z F) → MvPolynomial Y (MvPolynomial Z F))
    (hop : ∀ (S : IntermediateField F (FractionRing (MvPolynomial Z F)))
      (p q : MvPolynomial Y (MvPolynomial Z F)),
      (∀ α : Y →₀ ℕ,
        algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
          (MvPolynomial.coeff α p) ∈ S) →
      (∀ α : Y →₀ ℕ,
        algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
          (MvPolynomial.coeff α q) ∈ S) →
      ∀ α : Y →₀ ℕ,
        algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
          (MvPolynomial.coeff α (op p q)) ∈ S)
    (hsplit : splitEval h = op (splitEval f) (splitEval g))
    (hleaves : yLeafCount h = yLeafCount f + yLeafCount g)
    (hf : 0 < yLeafCount f) (hg : 0 < yLeafCount g) :
    ContractedSkeleton h := by
  refine
    { generators := contractedSkeletonBinaryGenerators wf wg
      slope := 1
      intercept := 0
      core := op (splitEval f) (splitEval g)
      split_eq := ?_
      core_coeff_mem := ?_
      generator_card := ?_ }
  · simpa using hsplit
  · exact hop _ (splitEval f) (splitEval g)
      (contractedSkeletonBinaryGenerators_coeff_mem_left wf wg)
      (contractedSkeletonBinaryGenerators_coeff_mem_right wf wg)
  · have hbound := contractedSkeletonBinaryGenerators_card_le wf wg
    have hcard_f := wf.generator_card
    have hcard_g := wg.generator_card
    rw [hleaves]
    omega
noncomputable def contractedSkeletonAdd
    (f g : Formula (Y ⊕ Z) F)
    (wf : (0 < yLeafCount f) → ContractedSkeleton f)
    (wg : (0 < yLeafCount g) → ContractedSkeleton g)
    (hmarked : 0 < yLeafCount (.add f g)) :
    ContractedSkeleton (.add f g) := by
  classical
  by_cases hfzero : yLeafCount f = 0
  · have hgpos : 0 < yLeafCount g := by
      simp only [yLeafCount] at hmarked
      omega
    let q := Classical.choose
      (exists_splitEval_eq_C_of_yLeafCount_eq_zero f hfzero)
    have hq : splitEval f = MvPolynomial.C q :=
      Classical.choose_spec
        (exists_splitEval_eq_C_of_yLeafCount_eq_zero f hfzero)
    apply contractedSkeletonAffine (wg hgpos) 1 q
    · rw [splitEval_add, hq]
      simp [add_comm]
    · simp [yLeafCount, hfzero]
  · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
    by_cases hgzero : yLeafCount g = 0
    · let q := Classical.choose
        (exists_splitEval_eq_C_of_yLeafCount_eq_zero g hgzero)
      have hq : splitEval g = MvPolynomial.C q :=
        Classical.choose_spec
          (exists_splitEval_eq_C_of_yLeafCount_eq_zero g hgzero)
      apply contractedSkeletonAffine (wf hfpos) 1 q
      · rw [splitEval_add, hq]
        simp
      · simp [yLeafCount, hgzero]
    · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
      exact contractedSkeletonBinary (wf hfpos) (wg hgpos) (· + ·)
        (fun S p q hp hq α => coeff_mem_intermediateField_add S p q hp hq α)
        (splitEval_add f g) rfl hfpos hgpos
noncomputable def contractedSkeletonSub
    (f g : Formula (Y ⊕ Z) F)
    (wf : (0 < yLeafCount f) → ContractedSkeleton f)
    (wg : (0 < yLeafCount g) → ContractedSkeleton g)
    (hmarked : 0 < yLeafCount (.sub f g)) :
    ContractedSkeleton (.sub f g) := by
  classical
  by_cases hfzero : yLeafCount f = 0
  · have hgpos : 0 < yLeafCount g := by
      simp only [yLeafCount] at hmarked
      omega
    let q := Classical.choose
      (exists_splitEval_eq_C_of_yLeafCount_eq_zero f hfzero)
    have hq : splitEval f = MvPolynomial.C q :=
      Classical.choose_spec
        (exists_splitEval_eq_C_of_yLeafCount_eq_zero f hfzero)
    apply contractedSkeletonAffine (wg hgpos) (-1) q
    · rw [splitEval_sub, hq]
      simp only [map_neg, map_one]
      ring
    · simp [yLeafCount, hfzero]
  · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
    by_cases hgzero : yLeafCount g = 0
    · let q := Classical.choose
        (exists_splitEval_eq_C_of_yLeafCount_eq_zero g hgzero)
      have hq : splitEval g = MvPolynomial.C q :=
        Classical.choose_spec
          (exists_splitEval_eq_C_of_yLeafCount_eq_zero g hgzero)
      apply contractedSkeletonAffine (wf hfpos) 1 (-q)
      · rw [splitEval_sub, hq]
        simp only [map_neg, map_one]
        ring
      · simp [yLeafCount, hgzero]
    · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
      exact contractedSkeletonBinary (wf hfpos) (wg hgpos) (· - ·)
        (fun S p q hp hq α => coeff_mem_intermediateField_sub S p q hp hq α)
        (splitEval_sub f g) rfl hfpos hgpos
noncomputable def contractedSkeletonMul
    (f g : Formula (Y ⊕ Z) F)
    (wf : (0 < yLeafCount f) → ContractedSkeleton f)
    (wg : (0 < yLeafCount g) → ContractedSkeleton g)
    (hmarked : 0 < yLeafCount (.mul f g)) :
    ContractedSkeleton (.mul f g) := by
  classical
  by_cases hfzero : yLeafCount f = 0
  · have hgpos : 0 < yLeafCount g := by
      simp only [yLeafCount] at hmarked
      omega
    let q := Classical.choose
      (exists_splitEval_eq_C_of_yLeafCount_eq_zero f hfzero)
    have hq : splitEval f = MvPolynomial.C q :=
      Classical.choose_spec
        (exists_splitEval_eq_C_of_yLeafCount_eq_zero f hfzero)
    apply contractedSkeletonAffine (wg hgpos) q 0
    · rw [splitEval_mul, hq]
      simp
    · simp [yLeafCount, hfzero]
  · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
    by_cases hgzero : yLeafCount g = 0
    · let q := Classical.choose
        (exists_splitEval_eq_C_of_yLeafCount_eq_zero g hgzero)
      have hq : splitEval g = MvPolynomial.C q :=
        Classical.choose_spec
          (exists_splitEval_eq_C_of_yLeafCount_eq_zero g hgzero)
      apply contractedSkeletonAffine (wf hfpos) q 0
      · rw [splitEval_mul, hq]
        simp [mul_comm]
      · simp [yLeafCount, hgzero]
    · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
      exact contractedSkeletonBinary (wf hfpos) (wg hgpos) (· * ·)
        (fun S p q hp hq α => coeff_mem_intermediateField_mul S p q hp hq α)
        (splitEval_mul f g) rfl hfpos hgpos
noncomputable def contractedSkeleton
    (f : Formula (Y ⊕ Z) F) (hmarked : 0 < yLeafCount f) :
    ContractedSkeleton f := by
  induction f with
  | var i =>
      cases i with
      | inl i =>
          refine
            { generators := ∅
              slope := 1
              intercept := 0
              core := MvPolynomial.X i
              split_eq := ?_
              core_coeff_mem := ?_
              generator_card := ?_ }
          · simp
          · exact coeff_mem_intermediateField_X _ i
          · simp [yLeafCount]
      | inr i => simp [yLeafCount] at hmarked
  | const c => simp [yLeafCount] at hmarked
  | add f g hf hg =>
      exact contractedSkeletonAdd f g hf hg hmarked
  | sub f g hf hg =>
      exact contractedSkeletonSub f g hf hg hmarked
  | mul f g hf hg =>
      exact contractedSkeletonMul f g hf hg hmarked
noncomputable def contractedSkeletonRootExtras
    {f : Formula (Y ⊕ Z) F}
    (w : ContractedSkeleton f) :
    Finset (FractionRing (MvPolynomial Z F)) := by
  classical
  exact
    {algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F)) w.slope,
      algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F)) w.intercept}
noncomputable def contractedSkeletonRootGenerators
    {f : Formula (Y ⊕ Z) F}
    (w : ContractedSkeleton f) :
    Finset (FractionRing (MvPolynomial Z F)) := by
  classical
  exact contractedSkeletonRootExtras w ∪ w.generators
end CoefficientFields
end Formula
noncomputable def matchingMarkedFinset {n : ℕ} {Y : Type u} [Fintype Y]
    (d : Y ↪ Fin n × Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.image d
@[simp] theorem mem_matchingMarkedFinset {n : ℕ} {Y : Type u} [Fintype Y]
    (d : Y ↪ Fin n × Fin n) (i : Fin n × Fin n) :
    i ∈ matchingMarkedFinset d ↔ ∃ y : Y, d y = i := by
  classical
  simp [matchingMarkedFinset]
namespace Formula
variable {ι : Type u} {κ : Type v} {R : Type w}
def rename (e : ι ≃ κ) : Formula ι R → Formula κ R
  | .var i => .var (e i)
  | .const c => .const c
  | .add f g => .add (rename e f) (rename e g)
  | .sub f g => .sub (rename e f) (rename e g)
  | .mul f g => .mul (rename e f) (rename e g)
end Formula
namespace RationalFormula
variable {ι : Type u} {κ : Type v} {R : Type w}
def rename (e : ι ≃ κ) : RationalFormula ι R → RationalFormula κ R
  | .var i => .var (e i)
  | .const c => .const c
  | .add f g => .add (rename e f) (rename e g)
  | .sub f g => .sub (rename e f) (rename e g)
  | .mul f g => .mul (rename e f) (rename e g)
  | .div f g => .div (rename e f) (rename e g)
noncomputable def renameFractionEquiv [Field R] (e : ι ≃ κ) :
    FractionRing (MvPolynomial ι R) ≃+*
      FractionRing (MvPolynomial κ R) :=
  IsFractionRing.ringEquivOfRingEquiv
    (MvPolynomial.renameEquiv R e).toRingEquiv
@[simp] theorem renameFractionEquiv_algebraMap [Field R]
    (e : ι ≃ κ) (p : MvPolynomial ι R) :
    renameFractionEquiv e
        (algebraMap (MvPolynomial ι R)
          (FractionRing (MvPolynomial ι R)) p) =
      algebraMap (MvPolynomial κ R)
        (FractionRing (MvPolynomial κ R))
        (MvPolynomial.renameEquiv R e p) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (MvPolynomial.renameEquiv R e).toRingEquiv p
end RationalFormula
noncomputable def matchingCanonicalComplexPoints (m : ℕ) : Fin m → ℂ :=
  fun i => (i.1 : ℂ)
noncomputable def matchingEmbeddingPermutation
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq β] (f g : α ↪ β) : Equiv.Perm β :=
  Classical.choose
    (Equiv.Perm.exists_extending_pair
      (f : α → β) (g : α → β) f.injective g.injective)
@[simp] theorem matchingEmbeddingPermutation_apply
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq β] (f g : α ↪ β) (a : α) :
    matchingEmbeddingPermutation f g (f a) = g a :=
  Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (f : α → β) (g : α → β) f.injective g.injective) a
noncomputable def matchingOutsideRelabelEquiv
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (e : Equiv.Perm (Fin n × Fin n))
    (he : ∀ y : Y, e (d₀ y) = d y) :
    matchingOutside d₀ ≃ matchingOutside d := by
  classical
  apply e.subtypeEquiv
  intro x
  apply not_congr
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (he y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, e.injective ?_⟩
    exact (he y).trans hy
@[simp] theorem matchingOutsideRelabelEquiv_apply_val
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (e : Equiv.Perm (Fin n × Fin n))
    (he : ∀ y : Y, e (d₀ y) = d y)
    (z : matchingOutside d₀) :
    (matchingOutsideRelabelEquiv d₀ d e he z).1 = e z.1 := by
  rfl
noncomputable def matchingCyclicBlockIndexEquiv
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    (Fin ell ⊕ Fin ell) ≃ ↥(cyclicMatchingBlock hk t j) := by
  apply Fintype.equivOfCardEq
  simp [card_cyclicMatchingBlock, two_mul]
noncomputable def matchingCyclicDiagonalEmbedding
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    (Fin ell ⊕ Fin ell) ↪ Fin n × Fin n where
  toFun y := (matchingCyclicBlockIndexEquiv hk t j y).1
  inj' := fun _ _ h =>
    (matchingCyclicBlockIndexEquiv hk t j).injective (Subtype.ext h)
namespace Formula
end Formula
namespace RationalFormula
end RationalFormula
end PermanentFormulaLowerBound



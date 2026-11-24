-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:12.39181+00:00
-- url     : https://prove2.me/theorems/6b9dd36b-4dcf-4a69-a2ed-cf7bad504946
-- title:
--   Standard Lattice Vec Indep
-- statement:
--   Definitions and structural lemmas for Standard Lattice Vec Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StandardLatticeVecIndep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open NumberField TensorProduct MeasureTheory Filter Topology Asymptotics
noncomputable section
section Had
variable {K : Type} [Field K] [NumberField K]
def embMean (f : (K →+* ℂ) → ℝ) : ℝ := (∑ σ : K →+* ℂ, f σ) / Module.finrank ℚ K
def degN (E : HermitianBundle.{0} K) : ℝ := HermitianBundle.normDegree E ⊤
abbrev rk (E : HermitianBundle.{0} K) : ℕ := Module.finrank (𝓞 K) E.carrier
structure SmallFamily (E : HermitianBundle.{0} K) (lam : (K →+* ℂ) → ℝ) where

  vec : Fin (rk E) → E.carrier

  indep : LinearIndependent (𝓞 K) vec

  norm_le : ∀ (σ : K →+* ℂ) (i : Fin (rk E)), ‖fibreVec E.metric σ (vec i)‖ ≤ lam σ
structure Had.Data (K : Type) [Field K] [NumberField K] where

  source : HermitianBundle.{0} K

  target : HermitianBundle.{0} K

  map : source.carrier →ₗ[𝓞 K] target.carrier
  map_injective : Function.Injective map

  A : (K →+* ℂ) → ℝ
  A_pos : ∀ σ, 0 < A σ

  map_le : ∀ (σ : K →+* ℂ) (x : Fibre σ source.carrier),
    ‖FibreSpace.equiv target.metric σ (LinearMap.lTensor (ComplexAt σ) map x)‖ ≤
      A σ * ‖FibreSpace.equiv source.metric σ x‖

  lam : (K →+* ℂ) → ℝ
  lam_pos : ∀ σ, 0 < lam σ

  family : SmallFamily target lam
def Had.Statement : Prop :=
  (∀ (K : Type) [Field K] [NumberField K] (d : Had.Data K),
    degN d.source ≤ degN d.target + (rk d.source : ℝ) * embMean (fun σ ↦ Real.log (d.A σ)) +
      ((rk d.target : ℝ) - rk d.source) * embMean (fun σ ↦ Real.log (d.lam σ))) ∧
  (∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (lam : (K →+* ℂ) → ℝ), (∀ σ, 0 < lam σ) → SmallFamily E lam →
    -((rk E : ℝ) * embMean (fun σ ↦ Real.log (lam σ))) ≤ degN E)
end Had
section HadExamples
variable (K : Type) [Field K] [NumberField K]
theorem rk_standard (n : ℕ) : rk (HermitianBundle.standard.{0} K n) = n :=
  Module.finrank_fin_fun (𝓞 K)
def standardVec (n : ℕ) : Fin (rk (HermitianBundle.standard.{0} K n)) →
    (HermitianBundle.standard.{0} K n).carrier :=
  fun i ↦ (Pi.single (Fin.cast (rk_standard K n) i) 1 : Fin n → 𝓞 K)
theorem standardVec_indep (n : ℕ) : LinearIndependent (𝓞 K) (standardVec K n) := by
  have h : LinearIndependent (𝓞 K) (fun j : Fin n ↦ (Pi.single j 1 : Fin n → 𝓞 K)) := by
    have e : ⇑(Pi.basisFun (𝓞 K) (Fin n)) = fun j : Fin n ↦ (Pi.single j 1 : Fin n → 𝓞 K) := by
      funext j; exact Pi.basisFun_apply (𝓞 K) (Fin n) j
    rw [← e]; exact (Pi.basisFun (𝓞 K) (Fin n)).linearIndependent
  exact h.comp (Fin.cast (rk_standard K n)) (Fin.cast_injective _)
theorem standardVec_norm (n : ℕ) (σ : K →+* ℂ) (i : Fin (rk (HermitianBundle.standard.{0} K n))) :
    ‖fibreVec (HermitianBundle.standard.{0} K n).metric σ (standardVec K n i)‖ = 1 := by
  have h := norm_fibreVec_sq (HermitianBundle.standard.{0} K n).metric σ (standardVec K n i)
  have h1 := HermitianMetric.standard_inner_single K n σ (Fin.cast (rk_standard K n) i)
  have h1' : ((HermitianBundle.standard.{0} K n).metric.form σ).inner
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] standardVec K n i) (1 ⊗ₜ[𝓞 K] standardVec K n i) = 1 := h1
  have h2 : ‖fibreVec (HermitianBundle.standard.{0} K n).metric σ (standardVec K n i)‖ ^ 2 = 1 := by
    rw [h, h1', Complex.one_re]
  have h3 := norm_nonneg (fibreVec (HermitianBundle.standard.{0} K n).metric σ (standardVec K n i))
  nlinarith [sq_nonneg (‖fibreVec (HermitianBundle.standard.{0} K n).metric σ
    (standardVec K n i)‖ - 1)]
def SmallFamily.standard (n : ℕ) :
    SmallFamily (HermitianBundle.standard.{0} K n) (fun _ ↦ 1) where
  vec := standardVec K n
  indep := standardVec_indep K n
  norm_le σ i := (standardVec_norm K n σ i).le
def Had.Data.identity (n : ℕ) : Had.Data K where
  source := HermitianBundle.standard.{0} K n
  target := HermitianBundle.standard.{0} K n
  map := LinearMap.id
  map_injective := Function.injective_id
  A _ := 1
  A_pos _ := one_pos
  map_le σ x := by rw [LinearMap.lTensor_id, LinearMap.id_apply, one_mul]
  lam _ := 1
  lam_pos _ := one_pos
  family := SmallFamily.standard K n
example : Had.Data ℚ := Had.Data.identity ℚ 2
example : Had.Data GaussianField := Had.Data.identity GaussianField 2
end HadExamples
def unitBallVolume (R : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin R)) 1)).toReal
structure EuclidLattice (R : ℕ) where

  carrier : Submodule ℤ (EuclideanSpace ℝ (Fin R))
  [discrete : DiscreteTopology carrier]
  [full : IsZLattice ℝ carrier]
attribute [instance] EuclidLattice.discrete EuclidLattice.full
def EuclidLattice.covol {R : ℕ} (La : EuclidLattice R) : ℝ := ZLattice.covolume La.carrier
def EuclidLattice.count {R : ℕ} (La : EuclidLattice R) (b : ℝ) : ℕ :=
  Nat.card {x : La.carrier // ‖(x : EuclideanSpace ℝ (Fin R))‖ ≤ b}
structure LatticeCount.Data (R : ℕ) where

  lattice : EuclidLattice R

  c : ℝ

  vec : Fin R → lattice.carrier
  indep : LinearIndependent ℤ vec
  norm_le : ∀ i, ‖(vec i : EuclideanSpace ℝ (Fin R))‖ ≤ c
def LatticeCount.Statement : Prop :=
  ∀ (R : ℕ) (d : LatticeCount.Data R) (b : ℝ), 0 ≤ b →
    (d.lattice.count b : ℝ) * d.lattice.covol ≤ unitBallVolume R * (b + R * d.c) ^ R
def MinkowskiCount.Statement : Prop :=
  (∀ (R : ℕ) (La : EuclidLattice R) (ρ : ℝ), 0 < ρ →
    Real.log (unitBallVolume R) + R * Real.log ρ - Real.log La.covol ≤
      Real.log (La.count (2 * ρ))) ∧
  (∀ R : ℕ, (2 / Real.sqrt R) ^ R ≤ unitBallVolume R)
def SmallBallVolume.Statement : Prop :=
  ∀ R : ℕ, unitBallVolume R ≤ 6
section LatticeExamples
def EuclidLattice.standard (R : ℕ) : EuclidLattice R where
  carrier := Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin R) ℝ).toBasis)
def standardLatticeVec (R : ℕ) : Fin R → (EuclidLattice.standard R).carrier :=
  fun i ↦ ⟨(EuclideanSpace.basisFun (Fin R) ℝ).toBasis i, Submodule.subset_span ⟨i, rfl⟩⟩
theorem standardLatticeVec_indep (R : ℕ) : LinearIndependent ℤ (standardLatticeVec R) := by
  apply LinearIndependent.of_comp (EuclidLattice.standard R).carrier.subtype
  exact ((EuclideanSpace.basisFun (Fin R) ℝ).toBasis.linearIndependent).restrict_scalars'
    (R := ℤ)
def LatticeCount.Data.standard (R : ℕ) : LatticeCount.Data R where
  lattice := EuclidLattice.standard R
  c := 1
  vec := standardLatticeVec R
  indep := standardLatticeVec_indep R
  norm_le i := by
    simp [standardLatticeVec, OrthonormalBasis.coe_toBasis]
example : LatticeCount.Data 3 := LatticeCount.Data.standard 3
end LatticeExamples
structure Packing.Data (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] where

  lattice : Submodule ℤ V
  [discrete : DiscreteTopology lattice]
  [finite : Module.Finite ℤ lattice]

  points : Finset V
  mem : ∀ x ∈ points, x ∈ lattice
  norm_le : ∀ x ∈ points, ‖x‖ ≤ 1

  b : ℝ
  b_nonneg : 0 ≤ b
  sep : ∀ x ∈ points, ∀ y ∈ points, x ≠ y → Real.exp (-b) ≤ ‖x - y‖
def Packing.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : Packing.Data V),
    Real.log d.points.card ≤ Module.finrank ℤ d.lattice * (d.b + Real.log 3)
def Packing.Data.integers : Packing.Data ℝ where
  lattice := Submodule.span ℤ (Set.range (Module.Basis.singleton (Fin 1) ℝ))
  points := {-1, 0, 1}
  mem x hx := by
    have h1 : (1 : ℝ) ∈ Submodule.span ℤ (Set.range (Module.Basis.singleton (Fin 1) ℝ)) :=
      Submodule.subset_span ⟨0, by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Submodule.neg_mem _ h1
    · exact Submodule.zero_mem _
    · exact h1
  norm_le x hx := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  b := 0
  b_nonneg := le_rfl
  sep x hx y hy hxy := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rw [neg_zero, Real.exp_zero]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact absurd rfl hxy | norm_num
structure Halving.Data where

  a : ℕ → ℝ
  bounded : ∃ C, ∀ n, |a n| ≤ C
  halve : Tendsto (fun n ↦ a (2 * n) - a n / 2) atTop (𝓝 0)
  step : Tendsto (fun n ↦ a (n + 1) - a n) atTop (𝓝 0)
def Halving.Statement : Prop :=
  ∀ d : Halving.Data, Tendsto d.a atTop (𝓝 0)
theorem tendsto_inv_succ : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
def Halving.Data.inv : Halving.Data where
  a n := 1 / ((n : ℝ) + 1)
  bounded := ⟨1, fun n ↦ by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  halve := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 / ((2 * n : ℕ) + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_inv_succ.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    have h2 := tendsto_inv_succ.div_const (2 : ℝ)
    simpa using h1.sub h2
  step := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_inv_succ.comp (tendsto_add_atTop_nat 1)
    simpa using h1.sub tendsto_inv_succ
def BetaSum.Statement : Prop :=
  ∀ D i : ℕ, i ≤ D →
    ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) = 1 / ((D : ℝ) + 1)
def GridSum.Statement : Prop :=
  ∀ D i : ℕ, i ≤ D →
    (fun n : ℕ ↦ (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n - 1),
        (p.1 : ℝ) ^ i * (p.2 : ℝ) ^ (D - i) / ((i.factorial : ℝ) * (D - i).factorial)) -
        (n : ℝ) ^ (D + 1) / (D + 1).factorial) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ D)
def entryDeriv {m : ℕ} (G : ℝ → Matrix (Fin m) (Fin m) ℂ) (t : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j ↦ deriv (fun s ↦ G s i j) t
open scoped ComplexOrder in

structure PosDefFamily (m : ℕ) where

  G : ℝ → Matrix (Fin m) (Fin m) ℂ

  smooth : ∀ i j, ContDiff ℝ 1 (fun t ↦ G t i j)

  posDef : ∀ t, (G t).PosDef
def LogDetDerivative.Statement : Prop :=
  ∀ (m : ℕ) (F : PosDefFamily m) (t : ℝ),
    HasDerivAt (fun s ↦ -(1 / 2) * Real.log (F.G s).det.re)
      (-(1 / 2) * ((F.G t)⁻¹ * entryDeriv F.G t).trace.re) t
open scoped ComplexOrder in

def PosDefFamily.expScalar : PosDefFamily 2 where
  G t := ((Real.exp t : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  smooth i j := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    exact (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul contDiff_const
  posDef t := Matrix.PosDef.one.smul (by
    have := Real.exp_pos t
    exact_mod_cast this)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel



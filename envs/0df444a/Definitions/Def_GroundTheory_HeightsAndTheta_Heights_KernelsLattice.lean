-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
-- name    : GroundTheory_HeightsAndTheta_Heights_KernelsLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:24.61448+00:00
-- url     : https://prove2.me/theorems/f7983a68-7459-4159-bbb1-874a8cde9166
-- title:
--   Kernels Lattice
-- statement:
--   Definitions and structural lemmas for Kernels Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KernelsLattice.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding Matrix Real
open scoped ComplexOrder nonZeroDivisors
noncomputable section
def genIndex {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : ℝ :=
  (B.relIndex A : ℝ) / (A.relIndex B : ℝ)
variable {K : Type*} [Field K]
def embVec (σ : K →+* ℂ) {n : ℕ} (v : Fin n → K) : Fin n → ℂ := fun j => σ (v j)
def gramAt {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} (u : ι → Fin n → K) :
    Matrix ι ι ℂ :=
  fun a b => star (embVec σ (u a)) ⬝ᵥ (h *ᵥ embVec σ (u b))
variable [NumberField K]
structure HermLattice (K : Type*) [Field K] [NumberField K] (n : ℕ) where

  lattice : Submodule (𝓞 K) (Fin n → K)
  fg : lattice.FG
  span_eq : Submodule.span K (lattice : Set (Fin n → K)) = ⊤

  metric : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ
  posDef : ∀ σ, (metric σ).PosDef
  conj : ∀ σ, metric (conjugate σ) = (metric σ).map (starRingEnd ℂ)
def subDegree {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (h : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) : ℝ :=
  log (genIndex (L ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup) -
    1 / 2 * ∑ σ : K →+* ℂ, log (gramAt (h σ) σ u).det.re
def quotDegree {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (h : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (b : ι → Fin n → K) (c : κ → Fin n → K) : ℝ :=
  log (genIndex (L ⊔ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range c) ⊔
        (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)).toAddSubgroup) -
    1 / 2 * ∑ σ : K →+* ℂ,
      (log (gramAt (h σ) σ (Sum.elim b c)).det.re - log (gramAt (h σ) σ b).det.re)
variable (K) in

def normalise (x : ℝ) : ℝ := x / Module.finrank ℚ K
namespace HermLattice
variable {n : ℕ}
def degree (F : HermLattice K n) : ℝ :=
  subDegree F.lattice F.metric (fun j : Fin n => (Pi.single j 1 : Fin n → K))
def slope (F : HermLattice K n) : ℝ := normalise K F.degree / n
def lineDegree (F : HermLattice K n) (K' : Type*) [Field K'] [NumberField K'] [Algebra K K']
    (v : Fin n → K') : ℝ :=
  normalise K' (subDegree
    (Submodule.span (𝓞 K') ((fun w : Fin n → K => fun j => algebraMap K K' (w j)) '' F.lattice))
    (fun σ' => F.metric (σ'.comp (algebraMap K K'))) (fun _ : Fin 1 => v))
end HermLattice
def idealLattice {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.pi Set.univ fun x => (a x : Submodule (𝓞 K) K)
def diagMetric {n : ℕ} (d : (K →+* ℂ) → Fin n → ℝ) : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => Matrix.diagonal fun x => (d σ x : ℂ)
def OrthogonalLines.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ),
    (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) → (∀ σ x, d (conjugate σ) x = d σ x) → ∀ μ : ℝ,
    (∀ x, μ ≤ normalise K (subDegree (idealLattice a) (diagMetric d)
      (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)))) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
      LinearIndependent K (Sum.elim b c) → m + k = n →
      k * μ ≤ normalise K (quotDegree (idealLattice a) (diagMetric d) b c)
def LineOfLargeDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ), 1 ≤ i → ∀ (F : HermLattice K i) (ε : ℝ), 0 < ε →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
      v ≠ 0 ∧ F.slope - 1 / 2 * log i - ε ≤ F.lineDegree K' v
def HermLattice.standard (K : Type*) [Field K] [NumberField K] (n : ℕ) : HermLattice K n where
  lattice := Submodule.span (𝓞 K) (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    rw [Submodule.span_span_of_tower]
    have h : (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K)) =
        Set.range (Pi.basisFun K (Fin n)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun K (Fin n)).span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp
example : 1 ≤ 2 ∧ (0 : ℝ) < 1 ∧ (HermLattice.standard ℚ 2).metric = fun _ => 1 :=
  ⟨by norm_num, one_pos, rfl⟩
example :
    let a : Fin 2 → FractionalIdeal (𝓞 ℚ)⁰ ℚ := fun _ => 1
    let d : (ℚ →+* ℂ) → Fin 2 → ℝ := fun _ _ => 1
    let deg : Fin 2 → ℝ := fun x => normalise ℚ (subDegree (idealLattice a) (diagMetric d)
      (fun _ : Fin 1 => (Pi.single x 1 : Fin 2 → ℚ)))
    (∀ x, a x ≠ 0) ∧ (∀ σ x, 0 < d σ x) ∧ (∀ σ x, d (conjugate σ) x = d σ x) ∧
      ∀ x, min (deg 0) (deg 1) ≤ deg x := by
  intro a d deg
  refine ⟨fun _ => one_ne_zero, fun _ _ => one_pos, fun _ _ => rfl, ?_⟩
  intro x
  fin_cases x
  · exact min_le_left _ _
  · exact min_le_right _ _
end
end GroundTheory.Heights₂.Heights



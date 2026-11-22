-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_StatementD
-- name    : Formalism_MahlerMeasure_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:12.80426+00:00
-- url     : https://prove2.me/theorems/ba99284e-61ee-447d-8987-9baf9fe7cef6
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/StatementD.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Finset Polynomial
noncomputable def gaussR {K : Type} [NormedField K] (ρ : NNReal) (P : K[X]) : NNReal :=
  P.support.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k)
def GaussMulRad : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ρ : NNReal) (P Q : K[X]), 0 < ρ →
    gaussR ρ (P * Q) = gaussR ρ P * gaussR ρ Q
noncomputable def binK (K : Type) [Field K] (k : ℕ) : K[X] :=
  Polynomial.C (((k.factorial : K))⁻¹) * descPochhammer K k
def MahlerK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] (h k : ℕ) (t₀ : ℤ), k ≤ p ^ h →
    ∀ m : ℕ, ‖((binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))).coeff m‖ ≤ 1
def SmithZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ_[p]),
    ∃ (U V : Matrix (Fin n) (Fin n) ℤ_[p]) (d : Fin n → ℤ_[p]),
      IsUnit U.det ∧ IsUnit V.det ∧ M = U * Matrix.diagonal d * V
noncomputable def binMatK (K : Type) [Field K] {n : ℕ} (del₀ : ℕ) (c : Fin n → Fin n → ℕ → K) :
    Matrix (Fin n) (Fin n) K[X] :=
  fun i j => ∑ k ∈ range (del₀ + 1), Polynomial.C (c i j k) * binK K k
open Classical in

def ValuationWindowLowerBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h → lead ≠ 0 →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    ((univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)
open Classical in

def WindowFull : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ : ℤ) (Y₀ : ℕ)
    (La₀ : ℝ) (U V : ℤ → Matrix (Fin n) (Fin n) K) (d : ℤ → Fin n → K),
    0 < Y₀ → Y₀ ≤ p ^ h → del₀ ≤ p ^ h → 0 < E → lead ≠ 0 → (∀ i j k, ‖c i j k‖ ≤ 1) →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (∀ t ∈ Ico t₀ (t₀ + Y₀), (∀ i j, ‖U t i j‖ ≤ 1) ∧ (∀ i j, ‖V t i j‖ ≤ 1) ∧
      ‖(U t).det‖ = 1 ∧ ‖(V t).det‖ = 1 ∧
      (binMatK K del₀ c).map (Polynomial.eval (t : K)) = U t * Matrix.diagonal (d t) * V t) →
    -Real.logb p ‖lead‖ + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La₀ →
    (∑ t ∈ Ico t₀ (t₀ + Y₀), ((univ.filter (fun i => ‖d t i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) / (Y₀ : ℝ) ≤
      (n : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)
end Formalism.GM



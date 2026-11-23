-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementC
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:00:53.094865+00:00
-- url     : https://prove2.me/theorems/51fa2967-92b3-4817-84b8-da0c3d98f820
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/StatementC.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_DetIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
def CoeffCauchy : Prop :=
  ∀ (V : Type) [Fintype V] (G : MvPolynomial V ℂ) (ρ : V → ℝ) (S : ℝ) (μ : V →₀ ℕ), (∀ v, 0 < ρ v) →
    (∀ z : V → ℂ, (∀ v, ‖z v‖ ≤ ρ v) → ‖MvPolynomial.eval z G‖ ≤ S) →
    ‖MvPolynomial.coeff μ G‖ * ∏ v, ρ v ^ μ v ≤ S
def LamEnd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (NN : MLine K) (cf : K) (S : (K →+* ℂ) → ℝ) (B : ℝ),
    NN.Good → cf ≠ 0 → cf ∈ NN.I → (∀ σ, 0 < S σ) → 0 < B → (∀ σ, NN.len σ cf ≤ S σ * B) →
    - NN.deg - (Module.finrank ℚ K : ℝ) * Real.log B ≤ ∑ σ : K →+* ℂ, Real.log (S σ)
def pDeg (logOm : ℝ) : ℝ := (1 + |logOm|) / 2
def lineNN {K : Type} [Field K] [NumberField K] {g : ℕ} {V : Type} [Fintype V] (de : MLine K) (ℓ : Fin g → MLine K)
    (c : V → Fin g) (μ : V → ℕ) (n : ℕ) : MLine K :=
  (de.pow n).tensor (MLine.prodPow (fun v => ℓ (c v)) μ).dual
def CMNumbers {K : Type} [Field K] [NumberField K] {g : ℕ} (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ) : Prop :=
  Lie.Good ∧ (∀ j, (ℓ j).Good) ∧ de.Good ∧ LinearIndependent K u ∧ (∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ Lie.M) ∧ 1 ≤ La ∧
  (∀ σ j, Lie.sq σ (u j) ≤ (La * (ℓ j).n σ) ^ 2) ∧ (∀ j, (ℓ j).ndeg = logOm / 2) ∧
  de.ndeg ≤ (1 / 2) * Lie.detLine.dual.ndeg + (g : ℝ) / 4 * Real.log (2 * Real.pi)
def DegDe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ), CMNumbers Lie ℓ u de La logOm →
    de.ndeg ≤ (g : ℝ) * (pDeg logOm + (1 / 2) * Real.log La)
def DegNN : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin g) (μ : V → ℕ) (n : ℕ),
    CMNumbers Lie ℓ u de La logOm →
    (lineNN de ℓ c μ n).Good ∧
    (lineNN de ℓ c μ n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)
def LamNumber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ)
    (S : (K →+* ℂ) → ℝ) (Rr : ℝ),
    CMNumbers Lie ℓ u de La logOm → MvPolynomial.coeff μ G ≠ 0 → MvPolynomial.coeff μ G ∈ (lineNN de ℓ c μ n).I →
    (∀ σ, 0 < S σ) → 0 < Rr →
    (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * de.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) →
    - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤
      (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)
end Formalism.L2.LamCM



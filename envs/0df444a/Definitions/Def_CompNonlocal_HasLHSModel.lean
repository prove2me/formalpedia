-- Prove2me | Definitions.Def_CompNonlocal_HasLHSModel
-- name    : CompNonlocal_HasLHSModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:37.911277+00:00
-- url     : https://prove2.me/theorems/f5e7e669-66dd-4e86-afae-f2608973bc94
-- title:
--   Local hidden-state (LHS) models
-- statement:
--   A two-qubit state $\omega$ has an **LHS model** if there are a probability space $(\Lambda,\mu)$ and a measurable family of qubit density matrices $\omega_\lambda$ such that for every finite-outcome POVM $\{M_a\}$ on Alice's qubit there is a measurable response $q(\lambda,a)\in[0,1]$, $\sum_aq(\lambda,a)=1$, with
--   $$\operatorname{Tr}\big((M_a\otimes N)\,\omega\big)=\int q(\lambda,a)\,\operatorname{Tr}(N\omega_\lambda)\,d\mu(\lambda)$$
--   for every effect $N$ on Bob's qubit (Eq. (8)). The hidden distribution and the ensemble are common to all measurements.
--
--   **Formalization Note** Each measurement setting of Alice is one POVM, and each outcome of a Bob POVM is an effect, so this is Eq. (8) for all measurement families.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 3, p.20

import Mathlib
import Definitions.Def_CompNonlocal_IsEffect
import Definitions.Def_QAlgorithms_Defs_Information

set_option autoImplicit false

open MeasureTheory
open scoped Kronecker ComplexOrder

namespace CompNonlocal

/-- Local hidden-state (LHS) models for qubit measurements on Alice's side. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), Definition 3, p.20: "For a state ω_AB we say it has a local
hidden-state (LHS) model (is unsteerable) if for every A, B who perform any POVM measurements
{M_{a|x}} and {M_{b|y}} respectively, it holds that for every x, y, a, b
Pr[a, b | x, y] = ∫ dλ Pr[a | x, λ] Tr(M_{b|y} ω_λ), (8) where the hidden distribution and the
ensemble {ω_λ}_λ are common to the entire measurement family and independent of x, y."

**Formalization Note** For a two-qubit `ω` (Alice's qubit first): there are a probability space
`(Λ, µ)` and a measurable family of qubit density matrices `ω_λ` such that for every finite-outcome
POVM `{M_a}` on Alice's qubit there is a measurable response `q(λ, a) ∈ [0, 1]`, summing to `1` over
`a`, with `Tr((M_a ⊗ N) ω) = ∫ q(λ, a) Tr(N ω_λ) dµ` for every effect `N` on Bob's qubit. Each
measurement setting `x` is a POVM, so quantifying over single POVMs covers every family `{M_{a|x}}`;
each outcome of a Bob POVM is an effect. Alice's POVMs are finite-outcome, the measurements an
efficient Alice can make. -/
def HasLHSModel (ω : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Prop :=
  ∃ (Λ : Type) (_ : MeasurableSpace Λ) (μ : Measure Λ), IsProbabilityMeasure μ ∧
    ∃ ωh : Λ → Matrix Bool Bool ℂ, (∀ l, QAlgorithms.IsDensityMatrix (ωh l)) ∧
      (∀ i j, Measurable fun l => ωh l i j) ∧
      ∀ (Out : Type) [Fintype Out] (M : Out → Matrix Bool Bool ℂ),
        (∀ a, (M a).PosSemidef) → ∑ a, M a = 1 →
        ∃ q : Λ → Out → ℝ, (∀ l a, 0 ≤ q l a) ∧ (∀ l, ∑ a, q l a = 1) ∧
          (∀ a, Measurable fun l => q l a) ∧
          ∀ a (N : Matrix Bool Bool ℂ), IsEffect N →
            ((M a ⊗ₖ N) * ω).trace.re = ∫ l, q l a * (N * ωh l).trace.re ∂μ

end CompNonlocal



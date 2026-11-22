-- Prove2me | Definitions.Def_Formalism_SuccessiveMinima_StatementNP
-- name    : Formalism_SuccessiveMinima_StatementNP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:05.744549+00:00
-- url     : https://prove2.me/theorems/b8829ffd-1148-49dd-82ae-9e7ae98653d9
-- title:
--   Statement NP
-- statement:
--   Definitions and structural lemmas for Statement NP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/StatementNP.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace Formalism.FN
variable {K : Type*} [NormedField K]
def ConvOn (a : ℕ → K) (r : ℝ) : Prop :=
  Tendsto (fun k : ℕ => ‖a k‖ * r ^ k) atTop (𝓝 0)
def gNorm (a : ℕ → K) (r : ℝ) : ℝ := ⨆ k : ℕ, ‖a k‖ * r ^ k
def wdeg (a : ℕ → K) (r : ℝ) : ℕ := sSup {k : ℕ | ‖a k‖ * r ^ k = gNorm a r}
def evalS (a : ℕ → K) (x : K) : K := ∑' k : ℕ, a k * x ^ k
def NewtonSlope : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] (a : ℕ → K) (r₁ r₂ : ℝ),
    0 < r₁ → r₁ < r₂ → ConvOn a r₂ → a ≠ 0 →
      gNorm a r₁ * (r₂ / r₁) ^ wdeg a r₁ ≤ gNorm a r₂
def Strassmann : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (a : ℕ → K) (r : ℝ), 0 < r → ConvOn a r → a ≠ 0 →
      ∀ s : Finset K, (∀ x ∈ s, ‖x‖ ≤ r ∧ evalS a x = 0) → s.card ≤ wdeg a r
def WeierstrassPrep : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (a : ℕ → K) (r : ℝ), 0 < r → ConvOn a r → a ≠ 0 →
      ∃ P : Polynomial K, P.Monic ∧ P.natDegree = wdeg a r ∧
        (∀ j : ℕ, ‖P.coeff j‖ * r ^ j ≤ r ^ wdeg a r) ∧
        ∃ b : ℕ → K, ConvOn b r ∧ ∀ x : K, ‖x‖ ≤ r →
          evalS a x = P.eval x * evalS b x ∧ ‖evalS b x‖ = gNorm a r / r ^ wdeg a r
def ZeroFormula : Prop :=
  ∀ {K L : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    (a : ℕ → K) (r : ℝ), 0 < r → ConvOn a r → a ≠ 0 →
      ∃ Z : Multiset L, Multiset.card Z = wdeg a r ∧ (∀ ζ ∈ Z, ‖ζ‖ ≤ r) ∧
        ∀ x : K, ‖x‖ ≤ r →
          ‖evalS a x‖ = gNorm a r / r ^ wdeg a r * (Z.map fun ζ => ‖algebraMap K L x - ζ‖).prod
example (p : ℕ) [Fact p.Prime] : IsAlgClosed (PadicAlgCl p) := inferInstance
example (p : ℕ) [Fact p.Prime] : NormedAlgebra ℚ_[p] (PadicAlgCl p) := inferInstance
example (p : ℕ) [Fact p.Prime] : IsUltrametricDist (PadicAlgCl p) := inferInstance
example (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℚ_[p] := inferInstance
example (p : ℕ) [Fact p.Prime] : CompleteSpace ℚ_[p] := inferInstance
end Formalism.FN



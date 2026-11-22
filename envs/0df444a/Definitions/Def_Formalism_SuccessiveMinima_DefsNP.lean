-- Prove2me | Definitions.Def_Formalism_SuccessiveMinima_DefsNP
-- name    : Formalism_SuccessiveMinima_DefsNP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:06.719907+00:00
-- url     : https://prove2.me/theorems/197ba1af-4d35-46f1-8a77-69987d41b64d
-- title:
--   Defs NP
-- statement:
--   Definitions and structural lemmas for Defs NP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/DefsNP.lean

import Definitions.Def_Formalism_SuccessiveMinima_StatementNP
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
def cmul {K : Type*} [NormedField K] (a b : ℕ → K) : ℕ → K :=
  fun n => ∑ i ∈ Finset.range (n + 1), a i * b (n - i)
def GaussMul : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] (a b : ℕ → K) (r : ℝ),
    0 < r → ConvOn a r → ConvOn b r → a ≠ 0 → b ≠ 0 →
      ConvOn (cmul a b) r ∧ gNorm (cmul a b) r = gNorm a r * gNorm b r ∧
        wdeg (cmul a b) r = wdeg a r + wdeg b r
def EvalMul : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (a b : ℕ → K) (r : ℝ), 0 < r → ConvOn a r → ConvOn b r →
      ∀ x : K, ‖x‖ ≤ r → evalS (cmul a b) x = evalS a x * evalS b x
def WDivision : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (f g : ℕ → K) (r : ℝ), 0 < r → ConvOn f r → ConvOn g r → g ≠ 0 →
      ∃ q : ℕ → K, ConvOn q r ∧ ∃ R : Polynomial K, R.degree < (wdeg g r : WithBot ℕ) ∧
        (∀ j : ℕ, ‖R.coeff j‖ * r ^ j ≤ gNorm f r) ∧ ∀ n : ℕ, f n = cmul q g n + R.coeff n
def UnitFacts : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ), 0 < r → ConvOn b r → b ≠ 0 → wdeg b r = 0 →
      (∀ x : K, ‖x‖ ≤ r → ‖evalS b x‖ = gNorm b r) ∧
      ∃ u : ℕ → K, ConvOn u r ∧ cmul b u = fun n => if n = 0 then 1 else 0
end Formalism.FN



-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementC
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_StatementC
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:42.634036+00:00
-- url     : https://prove2.me/theorems/506b19eb-cade-4474-8270-446d46d4d3c0
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/StatementC.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_GoodModelAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.CM (HasCMBy)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer)
open Formalism.L2.Th1.G (linSub sqSum betaPair)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)
def ShapeOrthD : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n]
    (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
    (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(dK : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun _ => (1 : ℂ_[p]))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ‖Formalism.L2.Th1.C.jet (logSer (curveL p L ι)) (phC p L ι) 2‖ ≤ ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧
      linSub A (thetaZ p L ι ω₀ r s) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curveL p L ι)) (phC p L ι) 2)) • betaPair H N0 N1 u) * sg
def ThmBOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n]
    (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
    (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(dK : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun _ => (1 : ℂ_[p]))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) ℂ_[p]), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) → (∀ τ, size τ = ∑ c, ht τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) ℂ_[p])) (ht τ) (hht τ) (I τ))
          (linSub A (thetaZ p L ι ω₀ r s))‖ ≤
        ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
def ThmBGaussOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n]
    (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
    (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun _ => (1 : ℂ_[p]))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) →
      (∀ τ, size τ = ∑ c, ht τ c) →
    ∀ nn : ((Bool × H) × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff nn (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (linSub A (thetaZ p L ι ω₀ r s)))‖ ≤
        ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
def IntOpOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (n : Type) [Fintype n],
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (thetaZ p L ι ω₀ r s) ∧
    ∀ P : MvPolynomial n ℂ_[p], (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (thetaZ p L ι ω₀ r s)‖ ≤ 1
end Formalism.L2.Th1.Top



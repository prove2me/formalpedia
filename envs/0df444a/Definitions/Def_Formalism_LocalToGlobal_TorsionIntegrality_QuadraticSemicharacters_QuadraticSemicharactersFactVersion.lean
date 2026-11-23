-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:31:26.929539+00:00
-- url     : https://prove2.me/theorems/168bff18-157d-429b-86e4-a3e4572ca733
-- title:
--   Quadratic Semicharacters Fact Version
-- statement:
--   Definitions and structural lemmas for Quadratic Semicharacters Fact Version, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/QuadraticSemicharactersFactVersion.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
def TransInt (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ω₀ : ℂ) (lg ph : PowerSeries ℂ_[l]) :
    Prop :=
  ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
    Formalism.L2.Th1.E.IntS ((mvExp ph : PowerSeries ℂ_[l]) *
      (PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst lg)
def thetaU {K : Type} [Field K] (ι : ℂ →+* K) (lg : PowerSeries K) {n : Type} [Fintype n] [DecidableEq n]
    (B' : Matrix n n K) (θ : (n → ℂ) → ℂ) : MvPowerSeries n K :=
  MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (B' i j) * Formalism.InvariantFactorPaths.G7.at1 j lg)
    (MvPowerSeries.map ι (taylorMv θ))
def quadraticSemicharacterIdentityReformulated₂ : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), StdData L ω₀ h Λ α β g →
    ∀ (ε : ℂ) (θ : (n → ℂ) → ℂ), tens4 θ = ε • kernel4 L ω₀ Λ β g →
    ∀ (S : Finset (Fin 4 × n → ℂ)),
      IsReps (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) S →
    ∀ (t : n → ℂ) (y : Fin 4 × n → ℂ),
      tens4 (opU (matH h) t θ) (g.symm y)
        = ∑ x ∈ S, (ε * ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
              (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ * β x
            * Complex.exp (-(Real.pi : ℂ) * Complex.I
                * (altE (stdH L (Fin 4 × n)) (g fun w => t w.2) x : ℂ)))
          * ∏ w, Formalism.L2.Th1.F.opU L (g (fun w => t w.2) w + x w) (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) (y w)
def quadraticSemicharacterIdentity : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ω₀ : ℂ) (lg linv ph : PowerSeries ℂ_[l]),
    Formalism.L2.Th1.C.IsLogPair lg linv → PowerSeries.constantCoeff ph = 0 → TransInt l L ι ω₀ lg ph →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
      (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), StdData L ω₀ h Λ α β g →
    ¬ l ∣ relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ ε : ℂ, ‖ι ε‖ ≤ 1 → ∀ θ ∈ Th (matH h) α Λ, tens4 θ = ε • kernel4 L ω₀ Λ β g →
    ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
    ∀ (O : Type) [Semiring O] (τ : O →+* ℂ_[l]) (γ : Matrix (Fin 4 × n) (Fin 4 × n) O)
      (B' : Matrix n n ℂ_[l]),
      (∀ (a : Fin 4) (i : n) (w : Fin 4 × n),
        ∑ j, B' i j * τ (γ (a, j) w) = ι (g.symm (Pi.single w 1) (a, i))) →
      Formalism.L2.Th1.E.ThetaFourthTensorPowerProductShape lg linv ph τ
        (thetaU (ι : ℂ →+* ℂ_[l]) lg B' (opU (matH h) t θ)) γ
def ThetaIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ω₀ : ℂ) (lg linv ph : PowerSeries ℂ_[l])
    (R : Subring ℂ_[l]), (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → Formalism.L2.Th1.C.Frame R lg linv ph →
    TransInt l L ι ω₀ lg ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* ℂ_[l]),
    (∀ a, Formalism.L2.Th1.C.EndInt R lg linv (τ a)) →
    (∀ z : O, star z = z → Formalism.L2.Th1.C.IsBinomScalar R (τ z)) →
    Formalism.L2.Th1.C.F1 R lg linv ph →
    (∀ a : O, Formalism.L2.Th1.C.PhNormAt R lg linv ph (τ a) (τ (star a))) →
    (∀ a : O, Formalism.L2.Th1.C.AdjAt R lg linv ph (τ a) (τ (star a))) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
      (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), StdData L ω₀ h Λ α β g →
    ¬ l ∣ relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ ε : ℂ, ‖ι ε‖ ≤ 1 → ∀ θ ∈ Th (matH h) α Λ, tens4 θ = ε • kernel4 L ω₀ Λ β g →
    ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
    ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) O) (B' : Matrix n n ℂ_[l]), γ.conjTranspose * γ = 1 →
      (∀ (a : Fin 4) (i : n) (w : Fin 4 × n),
        ∑ j, B' i j * τ (γ (a, j) w) = ι (g.symm (Pi.single w 1) (a, i))) →
      Integral (mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[l]) *
        thetaU (ι : ℂ →+* ℂ_[l]) lg B' (opU (matH h) t θ))
end Formalism.L2.Th1.H



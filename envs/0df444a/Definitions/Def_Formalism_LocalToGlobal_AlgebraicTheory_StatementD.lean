-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementD
-- name    : Formalism_LocalToGlobal_AlgebraicTheory_StatementD
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:43.234693+00:00
-- url     : https://prove2.me/theorems/d5ee5bb5-bcd2-5297-a971-dfcd67adef4a
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AlgebraicTheory/StatementD.lean

import Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
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
namespace Formalism.L2.AlgTh
open Formalism.L2.Th1.H (cmL CmOK matH Sesq altE IsSelfDual IsHerm IsPosDef IsLat IsReps imgLat Th alphaQ opU taylorMv)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.G (linSub)
open Formalism.L2.Th1.GD (LocNorm InMul frameM)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
section Defs
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def cLat (c : ℂ) (Λ : AddSubgroup V) : AddSubgroup V := imgLat (c • (LinearMap.id : V →ₗ[ℂ] V)) Λ
def xiHat (H : Sesq V) (q : ℕ) (Ψ : V → ℂ) (Sb : Finset V) (a : V) : ℂ :=
  ((q : ℂ))⁻¹ * ∑ b ∈ Sb, Ψ b * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H b a : ℂ))
def xiG (H : Sesq V) (α : V → ℂ) (θ : V → ℂ) (q : ℕ) (Ψ : V → ℂ) (Sa Sb : Finset V) (z : V) : ℂ :=
  ∑ a ∈ Sa, xiHat H q Ψ Sb a * α a * opU H a θ z
end Defs
def serLin {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n ν κ : Type} [Fintype n] [DecidableEq n] [Fintype ν] [Fintype κ]
    (h : Matrix n n ℂ) (F : (n → ℂ) → ℂ) (r : κ → ℂ) (t : κ → n → ℂ) (Mat : n → ν → ℂ_[p]) : MvPowerSeries ν ℂ_[p] :=
  linSub Mat (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => ∑ k, r k * opU (matH h) (t k) F z))
def XiEt : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ →
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ π : ℂ, IsQInt dK π → π * conj π = (p : ℂ) → ‖ι (conj π)‖ < 1 →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ Ψ : (n → ℂ) → ℂ, (∀ b ∈ Sb, ‖ι (Ψ b)‖ ≤ 1) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖ι (r k)‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ ‖(p : ℂ_[p])‖) →
    JetsIntegral (MvPowerSeries.C ((p : ℂ_[p]) ^ Fintype.card n) *
      serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t
        (frameM (ι : ℂ →+* ℂ_[p]) v A))
def ScalarConst : Prop :=
  ∀ (dK : ℕ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ → IsSelfDual (matH h) Λ →
    Formalism.L2.Th1.H.IsSemiChar (matH h) Λ (alphaQ (Real.sqrt dK / 2) (matH h)) →
    Formalism.L2.Th1.H.AtMostLine (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ →
  ∀ (p : ℕ), p.Prime → ∀ π : ℂ, π * conj π = (p : ℂ) → conj π ≠ π →
    (∀ x ∈ Λ, π • x ∈ Λ) → (∀ x ∈ Λ, conj π • x ∈ Λ) → (∃ u w : ℂ, (∀ x ∈ Λ, u • x ∈ Λ) ∧ (∀ x ∈ Λ, w • x ∈ Λ) ∧ u * π + w * conj π = 1) →
  ∀ Sa : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ, θ ≠ 0 →
    Sa.card = p ^ Fintype.card n ∧
    ∃ c : ℂ, c ^ 8 = (conj π / π) ^ (4 * Fintype.card n) ∧
      ∀ z, θ ((π / conj π) • z) =
        c * ((Real.sqrt ((p : ℝ) ^ Fintype.card n) : ℝ) : ℂ)⁻¹ *
          ∑ a ∈ Sa, alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z
def XiSwap : Prop :=
  ∀ (dK : ℕ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsSelfDual (matH h) Λ →
    Formalism.L2.Th1.H.IsSemiChar (matH h) Λ (alphaQ (Real.sqrt dK / 2) (matH h)) →
  ∀ (q : ℕ), 0 < q → ∀ π : ℂ, π ≠ 0 → (∀ x ∈ Λ, π • x ∈ Λ) → (∀ x ∈ Λ, conj π • x ∈ Λ) →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ, ∀ C' : ℂ, C' ≠ 0 →
    (∀ z, θ ((π / conj π) • z) = C' * ∑ a ∈ Sa, alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z) →
  ∀ (Ψ : (n → ℂ) → ℂ) (z : n → ℂ),
    xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ q Ψ Sa Sb z =
      (C' * (q : ℂ))⁻¹ * ∑ b ∈ Sb, Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b *
        opU (matH h) ((π / conj π) • b) θ ((π / conj π) • z)
def XiConn : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ →
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ π : ℂ, IsQInt dK π → π * conj π = (p : ℂ) → ‖ι (conj π)‖ = 1 →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ Ψ : (n → ℂ) → ℂ, (∀ b ∈ Sb, ‖ι (Ψ b)‖ ≤ 1) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖ι (r k)‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) →
    JetsIntegral (serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t
      (frameM (ι : ℂ →+* ℂ_[p]) v A))
def SelfDualLatticeThetaPadicIntegrality : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ →
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ π : ℂ, IsQInt dK π → π * conj π = (p : ℂ) →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ Ψ : (n → ℂ) → ℂ, (∀ b ∈ Sb, ‖ι (Ψ b)‖ ≤ 1) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖ι (r k)‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ ‖ι (conj π)‖) →
    JetsIntegral (MvPowerSeries.C ((p : ℂ_[p]) ^ Fintype.card n) *
      serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t
        (frameM (ι : ℂ →+* ℂ_[p]) v A))
end Formalism.L2.AlgTh



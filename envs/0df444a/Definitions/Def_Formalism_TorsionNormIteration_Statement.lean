-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_Statement
-- name    : Formalism_TorsionNormIteration_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:36.360512+00:00
-- url     : https://prove2.me/theorems/89e0d1ae-04ae-4a1e-bdf4-ef266c785cb9
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/Statement.lean

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
namespace Formalism.LT
open Formalism.G
def LTSetting (K : Type u) [NormedField K] (p q : ℕ) (π : K) : Prop :=
  p.Prime ∧ (∃ h : ℕ, 0 < h ∧ q = p ^ h) ∧ 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ‖(p : K)‖ ≤ ‖π‖ ∧
    ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ ≤ ‖π‖
def IsLTSeries {K : Type u} [NormedField K] (q : ℕ) (π : K) (e : PowerSeries K) : Prop :=
  IntegralPS e ∧ constantCoeff e = 0 ∧ coeff 1 e = π ∧ DivBy π (e - X ^ q)
abbrev toK {K : Type u} [NormedField K] [IsUltrametricDist K] (F : FormalGroup (unitBall K)) :
    FormalGroup K :=
  F.map (unitBall K).subtype
def LubinTateGroup : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p q : ℕ) (π : K), LTSetting K p q π →
    ∀ e : PowerSeries K, IsLTSeries q π e →
      ∃ F : FormalGroup (unitBall K), F.IsComm ∧ IsHom (toK F) (toK F) e ∧
        (∀ F' : FormalGroup (unitBall K), IsHom (toK F') (toK F') e → F' = F) ∧
        ∃ end_ : K → PowerSeries K,
          end_ π = e ∧
          (∀ a : K, ‖a‖ ≤ 1 →
            IntegralPS (end_ a) ∧ coeff 1 (end_ a) = a ∧ IsHom (toK F) (toK F) (end_ a) ∧
              (end_ a).subst e = e.subst (end_ a)) ∧
          (∀ a : K, ‖a‖ ≤ 1 → ∀ φ : PowerSeries K, IntegralPS φ → coeff 1 φ = a →
            IsHom (toK F) (toK F) φ → φ.subst e = e.subst φ → φ = end_ a) ∧
          (∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
            end_ (a * b) = (end_ a).subst (end_ b) ∧
            end_ (a + b) = (toK F).toPowerSeries.subst ![end_ a, end_ b])
def LubinTateIso : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p q : ℕ) (π : K), LTSetting K p q π →
    ∀ e e' : PowerSeries K, IsLTSeries q π e → IsLTSeries q π e' →
      ∀ a : K, ‖a‖ ≤ 1 →
        ∃ θ : PowerSeries K, IntegralPS θ ∧ constantCoeff θ = 0 ∧ coeff 1 θ = a ∧
          e'.subst θ = θ.subst e ∧
          (∀ θ' : PowerSeries K, constantCoeff θ' = 0 → coeff 1 θ' = a →
            e'.subst θ' = θ'.subst e → θ' = θ) ∧
          (∀ F F' : FormalGroup (unitBall K), IsHom (toK F) (toK F) e →
            IsHom (toK F') (toK F') e' → IsHom (toK F) (toK F') θ)
def IsLTPoly {K : Type u} [NormedField K] (q : ℕ) (π : K) (e : Polynomial K) : Prop :=
  e.coeff 0 = 0 ∧ e.coeff 1 = π ∧ ‖e.coeff q‖ = 1 ∧ ∀ i : ℕ, i ≠ 1 → i ≠ q → ‖e.coeff i‖ ≤ ‖π‖
def TorsionNorm : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (π : K) (q : ℕ), 0 < ‖π‖ → ‖π‖ < 1 →
    2 ≤ q → ∀ e : Polynomial K, IsLTPoly q π e →
      ∀ x : K, x ≠ 0 → ‖x‖ < 1 → e.eval x = 0 → ‖x‖ ^ (q - 1) = ‖π‖
def TorsionNormIter : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (π : K) (q : ℕ), 0 < ‖π‖ → ‖π‖ < 1 →
    2 ≤ q → ∀ e : Polynomial K, IsLTPoly q π e →
      ∀ (n : ℕ) (x : K), 1 ≤ n → ‖x‖ < 1 →
        (fun y => e.eval y)^[n] x = 0 → (fun y => e.eval y)^[n - 1] x ≠ 0 →
          ‖x‖ ^ (q ^ (n - 1) * (q - 1)) = ‖π‖
def TorsionExample : Prop :=
  IsLTPoly 2 (2 : ℚ_[2]) (Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2) ∧
    ((Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ_[2]).eval (-2) = 0) ∧
    ‖(-2 : ℚ_[2])‖ < 1 ∧ (-2 : ℚ_[2]) ≠ 0
def ExpIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ < 1 → ∀ c : K, ‖c‖ ^ (p - 1) ≤ ‖(p : K)‖ →
      ∀ n : ℕ, ‖c ^ n / (n.factorial : K)‖ ≤ 1
def QuasiLogShift : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p : ℕ), p.Prime → ‖(p : K)‖ < 1 →
    ∀ z : PowerSeries K, constantCoeff z = 0 → IntegralPS (PowerSeries.derivative K z) →
      DivByMv (p : K)
        (z.subst (MvPowerSeries.X (0 : Fin 2) + (p : K) • MvPowerSeries.X (1 : Fin 2)) - atX z)
end Formalism.LT



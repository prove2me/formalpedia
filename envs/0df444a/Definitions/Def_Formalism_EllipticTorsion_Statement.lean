-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_Statement
-- name    : Formalism_EllipticTorsion_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:19.178067+00:00
-- url     : https://prove2.me/theorems/b6ff553a-7d63-4459-a900-14307ad41fde
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/Statement.lean

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
open Formalism.G
def legendre {K : Type u} [CommRing K] (l : K) : WeierstrassCurve K :=
  ⟨0, -(1 + l), 0, l, 0⟩
def deuring {K : Type u} [CommRing K] (a : K) : WeierstrassCurve K :=
  ⟨a, 0, 1, 0, 0⟩
def IntegralModel {K : Type u} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1
def LegendreInv : Prop :=
  ∀ (K : Type u) [CommRing K] (l : K),
    (legendre l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 ∧ (legendre l).c₄ = 16 * (l ^ 2 - l + 1)
def DeuringInv : Prop :=
  ∀ (K : Type u) [CommRing K] (a : K),
    (deuring a).Δ = a ^ 3 - 27 ∧ (deuring a).c₄ = a * (a ^ 3 - 24)
def ModelLegendre : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K],
    ‖(2 : K)‖ = 1 → ∀ j : K, ‖j‖ ≤ 1 →
      ∃ l : K, ‖l‖ = 1 ∧ ‖l - 1‖ = 1 ∧
        (legendre l).c₄ ^ 3 = j * (legendre l).Δ ∧ ‖(legendre l).Δ‖ = 1
def ModelDeuring : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K],
    ‖(3 : K)‖ = 1 → ∀ j : K, ‖j‖ ≤ 1 →
      ∃ a : K, ‖a‖ ≤ 1 ∧
        (deuring a).c₄ ^ 3 = j * (deuring a).Δ ∧ ‖(deuring a).Δ‖ = 1
def ModelUnit : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (j : K), ‖j‖ ≤ 1 →
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j
def IntValuedZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [NormedAlgebra ℚ_[p] K]
    (P : Polynomial K), (∀ n : ℕ, ‖P.eval (n : K)‖ ≤ 1) →
      ∀ b : ℤ_[p], ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1
def PadicMult : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K]
    [NormedAlgebra ℚ_[p] K] (F : FormalGroup (unitBall K)) (l e : PowerSeries K),
    IsLog (F.map (unitBall K).subtype) l →
    constantCoeff e = 0 → e.subst l = X → l.subst e = X →
      ∀ b : ℤ_[p], IntegralPS (e.subst (algebraMap ℚ_[p] K (b : ℚ_[p]) • l))
section Cong
variable {K : Type u} [NormedField K] [CharZero K] {σ : Type}
def logOnePlus (f : MvPowerSeries σ K) : MvPowerSeries σ K := (PowerSeries.log K).subst f
def InN (G : MvPowerSeries σ K) : Prop :=
  ∃ f : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 ∧ IntegralMv f ∧ G = logOnePlus f
def Cong (G H : MvPowerSeries σ K) : Prop := InN (G - H)
end Cong
def NAddSubgroup : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (σ : Type),
    InN (0 : MvPowerSeries σ K) ∧
    (∀ G H : MvPowerSeries σ K, InN G → InN H → InN (G + H)) ∧
    (∀ G : MvPowerSeries σ K, InN G → InN (-G))
def NZpSmul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CharZero K] [NormedAlgebra ℚ_[p] K] (σ : Type) (G : MvPowerSeries σ K), InN G →
      ∀ b : ℤ_[p], InN (algebraMap ℚ_[p] K (b : ℚ_[p]) • G)
def NPderiv : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (σ : Type)
    (G : MvPowerSeries σ K), InN G → ∀ i : σ, IntegralMv (MvPowerSeries.pderiv K i G)
end Formalism.ELL



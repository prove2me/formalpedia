-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
-- name    : Formalism_PeriodIntegrals_JetsPhW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:07.68613+00:00
-- url     : https://prove2.me/theorems/23f00ce9-aefb-4286-be5a-d231b1488e44
-- title:
--   Jets Ph W
-- statement:
--   Definitions and structural lemmas for Jets Ph W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/JetsPhW.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.JetsPhW
def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1
def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)
def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])
def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i
def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f
def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3
def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹
def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n
section Ops
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
def add (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex
def sub (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l - PowerSeries.subst b l) ex
def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex
def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph
def be (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b
end Ops
def jet {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst ex ph : PowerSeries ℂ_[p])
def cubeE {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
    phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
    phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)
def High : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (cubeE (flog W wq) ex ph) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)
def One : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X → p ≠ 2 →
    Simeq (phAt ph (mulBy (flog W wq) ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)
def Two : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (be (flog W wq) ex ph (mulBy (flog W wq) ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be (flog W wq) ex ph (Xv 0) (mulBy (flog W wq) ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)
def Target : Prop := High ∧ One ∧ Two
def LogOk {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX l = 1
def InvOmega : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX (flog W wq) = 1
def HighG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    Simeq (cubeE l ex ph) 0 → ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)
def OneG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex → p ≠ 2 →
    Simeq (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)
def TwoG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]), LogOk l ex →
    Simeq (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)
def Glue : Prop := InvOmega → HighG → OneG → TwoG → Target
end PI.JetsPhW



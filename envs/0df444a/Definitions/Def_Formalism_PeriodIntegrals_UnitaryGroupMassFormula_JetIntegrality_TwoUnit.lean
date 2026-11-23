-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:32.950051+00:00
-- url     : https://prove2.me/theorems/e7129ff2-8d23-43ab-88e2-e9523191da8a
-- title:
--   Two Unit
-- statement:
--   Definitions and structural lemmas for Two Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/TwoUnit.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.JetsPhW.W
open PI.JetsPhW
def Dv {p : ℕ} [Fact p.Prime] {σ : Type*} (v : PowerSeries ℂ_[p]) (i : σ)
    (f : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v * MvPowerSeries.pderiv ℂ_[p] i f
def psi {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.subst ex ph
def IntP {p : ℕ} [Fact p.Prime] (g : PowerSeries ℂ_[p]) : Prop :=
  ∀ n, IsIntP (PowerSeries.coeff n g)
def Chain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst s g) =
      MvPowerSeries.pderiv ℂ_[p] i s * PowerSeries.subst s (dX g)
def DChain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (l v g : PowerSeries ℂ_[p]) (s : MvPowerSeries σ ℂ_[p])
    (c : ℂ_[p]), v * dX l = 1 → MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv ℂ_[p] i s =
      MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX l) →
    Dv v i (PowerSeries.subst s g) = MvPowerSeries.C c * PowerSeries.subst s (dX g)
def PdSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX g)
def PdNe : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i j : σ) (g : PowerSeries ℂ_[p]), j ≠ i →
    MvPowerSeries.pderiv ℂ_[p] i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) g) = 0
def DSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v g : PowerSeries ℂ_[p]),
    Dv v i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (v * dX g)
def Ev0 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.constantCoeff (PowerSeries.subst s g) = PowerSeries.constantCoeff g
def Coef1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a g : PowerSeries ℂ_[p]), PowerSeries.constantCoeff a = 0 →
    PowerSeries.coeff 1 (PowerSeries.subst a g : PowerSeries ℂ_[p]) =
      PowerSeries.coeff 1 g * PowerSeries.coeff 1 a
def JetD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (n : ℕ),
    jet ex ph n = PowerSeries.constantCoeff ((dX (A := ℂ_[p]))^[n] (psi ex ph))
def LogDer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → MvPowerSeries.constantCoeff f = 0 → IntegralMv (expMv f) → IntegralMv (Dv v i f)
def Dint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → IntegralMv f → IntegralMv (Dv v i f)
def RwAdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
    phAt ph (add l ex a b) = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) (psi ex ph)
def RwMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (l ex ph : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    MvPowerSeries.constantCoeff a = 0 →
    phAt ph (mulBy l ex c a) = PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) (psi ex ph)
abbrev lX {p : ℕ} [Fact p.Prime] {σ : Type*} (l : PowerSeries ℂ_[p]) (j : σ) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) l
def Rw3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    cubeE l ex ph =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)
def Rw1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    (phAt ph (mulBy l ex (-1) (Xv ())) - phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.C (-1) * lX l () : MvPowerSeries Unit ℂ_[p]) (psi ex ph) -
        phAt ph (Xv ())
def Rw2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]), LogOk l ex →
    (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) - be l ex ph (Xv 0) (mulBy l ex b (Xv 1)) :
      MvPowerSeries (Fin 2) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.C a * lX l 0 + lX l 1 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (MvPowerSeries.C a * lX l 0 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph) -
        phAt ph (Xv 1) -
        PowerSeries.subst (lX l 0 + MvPowerSeries.C b * lX l 1 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) +
        PowerSeries.subst (MvPowerSeries.C b * lX l 1 : MvPowerSeries (Fin 2) ℂ_[p]) (psi ex ph)
def TwoUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ‖(2 : ℂ_[p])‖ = 1
end PI.JetsPhW.W



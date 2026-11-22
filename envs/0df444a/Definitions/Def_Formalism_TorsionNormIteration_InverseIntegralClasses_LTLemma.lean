-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:45.837673+00:00
-- url     : https://prove2.me/theorems/ad2e9747-cd52-474d-853a-2385f85712ea
-- title:
--   LTLemma
-- statement:
--   Definitions and structural lemmas for LTLemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
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
namespace Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
section Near
variable {K : Type u} [NormedField K] {ι : Type*}
def Near (k : ℕ) (A B : MvPowerSeries ι K) : Prop := Low k A ∧ Low k B ∧ Low (k + 1) (A - B)
end Near
section Master
variable {K : Type u} [NormedField K] {ι : Type*}
def Ep (e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) x
def Ldef (e e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  Ep e' x - e.subst x
end Master
section Cong
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
def Cong (c : K) (A B : MvPowerSeries ι K) : Prop :=
  IntegralMv A ∧ IntegralMv B ∧ DivByMv c (A - B)
end Cong
section FrobPi
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
def piO (π : K) (hπ : ‖π‖ ≤ 1) : unitBall K := ⟨π, hπ⟩
end FrobPi
section Defect
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
end Defect
section Constr
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
def lin (a : ι → K) : MvPowerSeries ι K := ∑ i, a i • MvPowerSeries.X i
def corr (e e' : PowerSeries K) (π : K) (N : ℕ) (P : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun d => if d.degree = N + 1 then MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1)) else 0
def seq (e e' : PowerSeries K) (π : K) (a : ι → K) : ℕ → MvPowerSeries ι K
  | 0 => 0
  | 1 => lin a
  | (N + 2) => seq e e' π a (N + 1) + corr e e' π (N + 1) (seq e e' π a (N + 1))
def Inv (e e' : PowerSeries K) (a : ι → K) (k : ℕ) (P : MvPowerSeries ι K) : Prop :=
  MvPowerSeries.constantCoeff P = 0 ∧ IntegralMv P ∧
    (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) P = a i) ∧ Low (k + 1) (Ldef e e' P)
variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}
def lim (e e' : PowerSeries K) (π : K) (a : ι → K) : MvPowerSeries ι K :=
  fun d => MvPowerSeries.coeff d (seq e e' π a (d.degree + 1))
end Constr
end Formalism.LT.LTL
namespace Formalism.LT
open Formalism.G Formalism.LT.LTL
end Formalism.LT



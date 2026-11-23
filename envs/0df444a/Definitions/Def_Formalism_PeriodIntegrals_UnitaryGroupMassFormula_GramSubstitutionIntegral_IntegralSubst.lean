-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:33.27713+00:00
-- url     : https://prove2.me/theorems/615b18f9-c6d6-4c55-b5bb-39aa9f1ce05e
-- title:
--   Integral Subst
-- statement:
--   Definitions and structural lemmas for Integral Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
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
namespace PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
def Good {σ : Type*} (a : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff a = 0 ∧ IntegralMv a
structure Hyps (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])) : Prop where
  data : Data l ex ph
  swap : ∀ α ∈ S, α.swap ∈ S
  intMul : ∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])
  intAdd : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
  norm : ∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))
  conj : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))
  biadd : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))
section Calc
open PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
end Calc
def GoodAdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]), Good a → Good b → Good (add l ex a b)
def GoodMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (α : ℂ_[p] × ℂ_[p]), α ∈ S → ∀ a : MvPowerSeries σ ℂ_[p], Good a → Good (mulBy l ex α.1 a)
def BiaddSub : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (a b c : MvPowerSeries σ ℂ_[p]), Good a → Good b → Good c →
      Simeq (be l ex ph (add l ex a b) c) (be l ex ph a c + be l ex ph b c)
def NormSub : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (α : ℂ_[p] × ℂ_[p]), α ∈ S → ∀ a : MvPowerSeries σ ℂ_[p], Good a →
      Simeq (phAt ph (mulBy l ex α.1 a)) (MvPowerSeries.C (α.1 * α.2) * phAt ph a)
def MoveSub : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (α α' : ℂ_[p] × ℂ_[p]), α ∈ S → α' ∈ S → ∀ a b : MvPowerSeries σ ℂ_[p], Good a → Good b →
      Simeq (be l ex ph (mulBy l ex α.1 a) (mulBy l ex α'.1 b)) (be l ex ph (mulBy l ex (α'.2 * α.1) a) b)
def Expand : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ : Type) (m : ℕ) (a : Fin m → MvPowerSeries σ ℂ_[p]), (∀ j, Good (a j)) →
      Simeq (phAt ph (pt ex (∑ j, lg l (a j))))
        (∑ j, phAt ph (a j) + ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (a j) (a j'))
def SumFirst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ∀ (σ ι : Type) (s : Finset ι) (e : ι → ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]), Good a → Good b →
      (∀ i ∈ s, Good (mulBy l ex (e i) a)) →
      Simeq (∑ i ∈ s, be l ex ph (mulBy l ex (e i) a) b) (be l ex ph (mulBy l ex (∑ i ∈ s, e i) a) b)
def ColumnFor (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])) : Prop :=
  ∀ (k : ℕ) (c d : Fin k → ℂ_[p]), (∀ j, (c j, d j) ∈ S) →
    Simeq (phAt ph (lin l ex c (fun j => (Xv j : MvPowerSeries (Fin k) ℂ_[p]))))
      (∑ j, MvPowerSeries.C (c j * d j) * phAt ph (Xv j) +
        ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
          be l ex ph (mulBy l ex (d j' * c j) (Xv j)) (Xv j'))
def Column : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ColumnFor l ex ph S
def Gather : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyps l ex ph S →
    ColumnFor l ex ph S →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A)
end PI.UnitaryGroupMassFormula.PhGram



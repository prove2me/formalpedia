-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SDiffGram
-- name    : Formalism_PeriodIntegrals_SDiffGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:07.057706+00:00
-- url     : https://prove2.me/theorems/dd820119-b81d-4e82-a145-ab3b9224edf3
-- title:
--   SDiff Gram
-- statement:
--   Definitions and structural lemmas for SDiff Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SDiffGram.lean

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
namespace PI.SDiffGram
open Classical
def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1
def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)
def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])
def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
def hP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap
abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i
def zc {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) : ℂ_[p] := algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])
section FG
variable {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {σ : Type*}
def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l
def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex
def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)
def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  pt ex (MvPowerSeries.C c * lg l a)
def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  pt ex (∑ j, MvPowerSeries.C (c j) * lg l (a j))
def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a ph
def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b
end FG
section SD
variable {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p])
def PhOn {κ ι : Type*} [Fintype κ] [Fintype ι] (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (b e k).1) (fun e => Xv e))
def PhV {κ ι σ : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) (w : ι → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (b e k).1) w)
def sdL {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  PhOn l ex ph (Sum.elim a a') - PhV l ex ph a (fun e => Xv (Sum.inl e)) - PhV l ex ph a' (fun e => Xv (Sum.inr e))
def sdR {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (mulBy l ex (hP (a f) (a' f')).1 (Xv (Sum.inl f))) (Xv (Sum.inr f'))
def sdR' {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (Xv (Sum.inl f)) (mulBy l ex (hP (a f) (a' f')).2 (Xv (Sum.inr f')))
end SD
def SDiffGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), PowerSeries.constantCoeff l = 0 → PowerSeries.constantCoeff ex = 0 →
    PowerSeries.subst ex l = PowerSeries.X → PowerSeries.constantCoeff ph = 0 →
    ∀ (S : Set (ℂ_[p] × ℂ_[p])),
    (0 : ℂ_[p] × ℂ_[p]) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * phAt ph (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (mulBy l ex (hP (A j) (A j')).1 (Xv j)) (Xv j'))) →
    (∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))) →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]),
      (∀ e k, a e k ∈ S) → (∀ e k, a' e k ∈ S) →
      Simeq (sdL l ex ph a a') (sdR l ex ph a a') ∧ Simeq (sdL l ex ph a a') (sdR' l ex ph a a')
end PI.SDiffGram



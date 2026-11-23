-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FglGram
-- name    : Formalism_PeriodIntegrals_FglGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:26.050079+00:00
-- url     : https://prove2.me/theorems/edb40311-016e-4f51-bae4-8d7ef7e9ffea
-- title:
--   Fgl Gram
-- statement:
--   Definitions and structural lemmas for Fgl Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FglGram.lean

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
namespace PI.FglGram
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
def DualIso {p : ℕ} [Fact p.Prime] {κ ι : Type*} [Fintype κ] (b b' : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e e', hP (b e) (b e') = 0) ∧ (∀ e e', hP (b' e) (b' e') = 0) ∧
    ∀ e e', hP (b e) (b' e') = if e = e' then 1 else 0
section
variable {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {σ : Type*}
def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l
def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex
def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)
def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)
def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  pt ex (MvPowerSeries.C c * lg l a)
def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  pt ex (∑ j, MvPowerSeries.C (c j) * lg l (a j))
def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a ph
def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b
end
def PhOn {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (b e k).1) (fun e => Xv e))
def beSum {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (ι : Type*) [Fintype ι] :
    MvPowerSeries (ι ⊕ ι) ℂ_[p] :=
  ∑ e : ι, be l ex ph (Xv (Sum.inl e)) (Xv (Sum.inr e))
def GramRhs {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {κ : Type*} [Fintype κ] {k : ℕ}
    (A : Fin k → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (Fin k) ℂ_[p] :=
  ∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * phAt ph (Xv j) +
    ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (mulBy l ex (hP (A j) (A j')).1 (Xv j)) (Xv j')
def Data {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧ PowerSeries.constantCoeff ph = 0
def CubeRelationOfParallelogram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    Simeq (phAt ph (add l ex (Xv 0) (Xv 1)) + phAt ph (sub l ex (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * phAt ph (Xv 0) + 2 * phAt ph (Xv 1)) →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) + phAt ph (sub l ex (Xv 0) (Xv 1)) +
        phAt ph (sub l ex (Xv 1) (Xv 2)) + phAt ph (sub l ex (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2))) →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
        phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0
def PhGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Data l ex ph →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    (∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))) →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A)
def GramUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    ∀ (n : ℕ) (de : Fin n → Fin n → ℂ_[p] × ℂ_[p]), (∀ i j, hP (de i) (de j) = if i = j then 1 else 0) →
      GramRhs l ex ph de = ∑ j, phAt ph (Xv j)
def GramIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (b : Fin r → κ → ℂ_[p] × ℂ_[p]), (∀ e e', hP (b e) (b e') = 0) →
      GramRhs l ex ph b = 0
def PhDualGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Data l ex ph →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A)) →
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → ℂ_[p] × ℂ_[p]), (∀ e k, b e k ∈ S) →
      (∀ e k, b' e k ∈ S) → DualIso b b' →
      Simeq (PhOn l ex ph (Sum.elim b b')) (beSum l ex ph ι)
end PI.FglGram



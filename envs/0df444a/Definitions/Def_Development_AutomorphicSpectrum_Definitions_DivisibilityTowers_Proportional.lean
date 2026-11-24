-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
-- name    : Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:01.075284+00:00
-- url     : https://prove2.me/theorems/d76281fc-a75a-4d96-9000-aeccea84e0ac
-- title:
--   Proportional
-- statement:
--   Definitions and structural lemmas for Proportional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/Proportional.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
namespace GlobalTheory.CompanionTheory.Ar.Top
structure RootTower (Ψ : Type) [Fintype Ψ] (N : ℕ) where

  j : ℕ
  j_pos : 1 ≤ j
  j_lt : j < N

  Comp : Type
  [finC : Fintype Comp]
  [neC : Nonempty Comp]

  bad : Finset ℕ
  two_mem : 2 ∈ bad

  nu : Wt Ψ N
  nu_rat : IsRatWt nu

  M : ℕ → Comp → RootModel Ψ N
attribute [instance] RootTower.finC RootTower.neC
def scale (s : ℝ) : ℝ := Real.exp (-(s ^ 2)⁻¹)
namespace RootTower
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N) (II : IntersectionSystem)
def InS (B p : ℕ) : Prop := p.Prime ∧ (p ≤ B ∨ p ∈ T.bad)
def lamS (lam : Wt Ψ N) (s : ℝ) : Wt Ψ N := lam - s • T.nu
def vol (c : T.Comp) : ℝ :=
  (T.M 2 c).geoFun (toA (linRoot (rhoWt : Wt Ψ N) ^ dimFl Ψ N)) / flagDeg (rhoWt : Wt Ψ N)
def volT : ℝ := ∑ c, T.vol c
def PPc (B : ℕ) (c : T.Comp) (F : RP Ψ N) : ℝ := (T.M B c).PP II (toA F)
def PPt (B : ℕ) (F : RP Ψ N) : ℝ := ∑ c, T.PPc II B c F
def PBs (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ := (T.M B c).PP II (linA lam s ^ (dimFl Ψ N + 1))
def PB (B : ℕ) (lam : Wt Ψ N) : ℝ := T.PPt II B (linRoot lam ^ (dimFl Ψ N + 1))
def mbarTop (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ :=
  (T.M B c).arFun II (scale s) (linA (T.lamS lam s) s ^ (dimFl Ψ N + 1))
def mDeg (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ :=
  (T.M B c).geoFun (linA (T.lamS lam s) s ^ dimFl Ψ N)
def mbarHt (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) (W : Ideal (MRing (T.M B c).ι)) : ℝ :=
  (T.M B c).ht II (scale s) (T.lamS lam s) s W
def slope (B : ℕ) (c : T.Comp) (u : Wt Ψ N) : ℝ :=
  T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)) / (((dimFl Ψ N : ℝ) + 1) * (T.vol c * flagDeg u))
def Conv : Prop := ∀ B c, (T.M B c).Converges II
def Proportional : Prop :=
  (∀ c, 0 < T.vol c) ∧ (∀ B c (F : RP Ψ N), (T.M B c).geoFun (toA F) = T.vol c * degFl F) ∧
    ∀ B B' c, (T.M B c).geoFun = (T.M B' c).geoFun
def I1 : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c m, |(T.M B c).PP II (monomial m 1)| ≤ C * Real.log B
def I2 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → |T.mbarTop II B c lam s - T.PBs II B c (T.lamS lam s) s| ≤ C * s
def A1 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → (T.M B c).Semipos (scale s) (T.lamS lam s) s
def ModelNefStatement : Prop := ∀ B c p, T.InS B p → ∀ mu : Wt Ψ N, Dominant mu → (T.M B c).NefAt p mu 0
def M2 : Prop :=
  ∀ B c (p : ℕ), p.Prime → ¬ T.InS B p → ∀ mu : Wt Ψ N, Dominant mu → NefThreshold T.j p mu → (T.M B c).NefAt p mu 0
def ANef : Prop := ∀ B c, (T.M B c).NefFib 0 1
def I3 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) →
      (T.M B c).NefFib (T.lamS lam s) s ∧ (T.M B c).Semipos (scale s) (T.lamS lam s) s
def I5 : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam →
    ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam →
      ∀ W, (T.M B c).IsPt W → -(C * Real.log (B / (s : ℝ))) ≤ T.mbarHt II B c lam s W
def I6 : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam →
    ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam →
      ∃ F : Set (Ideal (MRing (T.M B c).ι)), IsZariskiDense (T.M B c).P F ∧
        ∀ W ∈ F, (T.M B c).IsPt W ∧ T.mbarHt II B c lam s W ≤ C * Real.log B
def I7 : Prop :=
  ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 ∧ (T.M B c).EffDiff T.nu
def I8 (hh : RP Ψ N → ℝ) : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ c τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) ≠ T.j → ∀ lam : Wt Ψ N,
    T.PPc II B c (linRoot (swapWt τ a b lam) ^ (dimFl Ψ N + 1)) -
        T.vol c * hh (linRoot (swapWt τ a b lam) ^ (dimFl Ψ N + 1)) =
      -(T.PPc II B c (linRoot lam ^ (dimFl Ψ N + 1)) - T.vol c * hh (linRoot lam ^ (dimFl Ψ N + 1)))
def Prop6 (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) : Prop :=
  ∀ B₀ B : ℕ, 2 ≤ B₀ → B₀ ≤ B → ∀ c τ (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
    T.PPc II B₀ c (pk τ k * Q) = T.PPc II B c (pk τ k * Q) +
      T.vol c * ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad), deltaTerm T.j p τ (frob p τ) k Q
def PropA : Prop :=
  ∃ Γ : Subgroup (Equiv.Perm Ψ), (∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') ∧ ∀ σ ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∀ F : RP Ψ N,
    T.PPt II B (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = T.PPt II B F
def PropF (C rd Lval : ℝ) : Prop :=
  ∃ h : ℕ → T.Comp → Ψ → ℝ,
    (∀ B : ℕ, 2 ≤ B → ∀ c τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) →
      T.PPc II B c (pk τ 1 * Q) = h B c τ * (T.vol c * degFl Q)) ∧
    ∀ B : ℕ, 128 ≤ B → T.bad.card ≤ B → ∀ c τ, |h B c τ| ≤ C * N * bigLam B rd Lval
def VolEq : Prop := ∀ c c', T.vol c = T.vol c'
end RootTower
def I9 {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (hh : RP Ψ N → ℝ) : Prop :=
  (∀ lam : Wt Ψ N, Dominant lam → (∃ τ, ∃ a b : Fin N, (b : ℕ) = a + 1 ∧ lam τ a = lam τ b) →
      hh (linRoot lam ^ (dimFl Ψ N + 1)) = 0) ∧
    (∀ lam : Wt Ψ N, Dominant lam → 0 ≤ hh (linRoot lam ^ (dimFl Ψ N + 1))) ∧
    ∀ τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) → hh (pk τ 1 * Q) = 0
end GlobalTheory.CompanionTheory.Ar.Top



-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:57:27.506803+00:00
-- url     : https://prove2.me/theorems/08d68bb7-876b-56f3-b043-43c9b61441fc
-- title:
--   PNTDens St
-- statement:
--   Definitions and structural lemmas for PNTDens St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensSt.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
def qd (M : ℕ) (T : ℝ) : ℕ := ⌈(M : ℝ) * T⌉₊
def pYd (M : ℕ) (T : ℝ) : ℕ := qd M T ^ 3
def pJd (M : ℕ) (T : ℝ) : ℕ := 8 * (Nat.log 2 (qd M T) + 1)
def pNd (M : ℕ) (T : ℝ) : ℕ := 2 ^ pJd M T
def blkD (Y N U : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc U (2 * U), mco Y N n * f n * (n : ℂ) ^ (-s)
def DivSq : Prop :=
  ∀ x : ℕ, 1 ≤ x → ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ (x : ℝ) * (1 + Real.log x) ^ 3
def CoefficientBlockBound : Prop :=
  ∀ (Y N U : ℕ) (σ : ℝ), 1 ≤ U → 0 ≤ σ →
    ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3
def PairCross : Prop :=
  ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), ψ ≠ 1 → ∀ w : ℂ, 0 ≤ w.re → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), ψ (n : ZMod M) * (n : ℂ) ^ (-w)‖ ≤ 4 * ((M : ℝ) + 1) * (1 + ‖w‖)
def PairSame : Prop :=
  ∀ (M : ℕ) [NeZero M] (w : ℂ), 0 ≤ w.re → w.re ≤ 1 → w.im ≠ 0 → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w)‖ ≤
      4 * (U : ℝ) ^ (1 - w.re) / |w.im| + 4 * ((M : ℝ) + 1) * (1 + ‖w‖)
def Spacing : Prop :=
  ∀ (P : Finset ℝ) (T : ℝ), 0 ≤ T → (∀ x ∈ P, |x| ≤ T) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ |x - y|) →
    (P.card : ℝ) ≤ 2 * T + 1 ∧ ∀ t ∈ P, ∑ x ∈ P.erase t, 1 / |t - x| ≤ 2 * (1 + Real.log (2 * T + 1))
def Triv : Prop :=
  ∀ (M : ℕ) [NeZero M] (T : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 0 ≤ T →
    (∀ p ∈ S, |p.2.im| ≤ T) → (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ (M : ℝ) * (2 * T + 1)
def Offdiag : Prop :=
  ∀ (M : ℕ) [NeZero M] (S : Finset (DirichletCharacter ℂ M × ℂ)) (σ T : ℝ) (U : ℕ), 1 ≤ U → 2 ≤ T →
    1 / 2 ≤ σ → (∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (U : ℝ) * (9 + 8 * Real.log (2 * T + 1)) + (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T))
def BlockCnt : Prop :=
  ∀ {α : Type} (S : Finset α) (f : α → ℕ → ℂ) (ρ : α → ℂ) (Y N U : ℕ) (σ θ G K : ℝ), 1 ≤ U → 0 < θ →
    0 ≤ σ → 0 ≤ G → 0 ≤ K →
    (∀ p ∈ S, ∀ n : ℕ, ‖f p n‖ ≤ 1) → (∀ p ∈ S, σ ≤ (ρ p).re) →
    (∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ))))‖ ≤ (U : ℝ) * G + (S.card : ℝ) * K) →
    (∀ p ∈ S, θ ≤ ‖blkD Y N U (f p) (ρ p)‖) →
    2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 * K ≤ θ ^ 2 / 2 →
    (S.card : ℝ) ≤ 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 * G / θ ^ 2
def EtaPartial : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ N : ℕ, 1 ≤ N →
    ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s -
        (∑ n ∈ Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s))‖ ≤
      4 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re)
def PrincipalZeta : Prop :=
  ∀ (M : ℕ) [NeZero M] (s : ℂ), 0 < s.re → IsLZero (1 : DirichletCharacter ℂ M) s → riemannZeta s = 0
def Detect1 : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → 3 ≤ M →
    ∀ ρ : ℂ, 3 / 4 ≤ ρ.re → |ρ.im| ≤ T → DirichletCharacter.LFunction χ ρ = 0 →
      ∃ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) ≤
        ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖
def Detect0 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T : ℝ), 2 ≤ T → 3 ≤ M → q₀ ≤ qd M T →
    ∀ ρ : ℂ, 3 / 4 ≤ ρ.re → |ρ.im| ≤ T → IsLZero (1 : DirichletCharacter ℂ M) ρ →
      ∃ i ∈ range 2, ∃ j ∈ range (pJd M T + 1),
        c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
          ‖blkD (pYd M T) (2 ^ i * pNd M T) (pYd M T * 2 ^ j)
            (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ‖
def Count1 : Prop :=
  ∃ C : ℝ, ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 3 / 4 ≤ σ → q₀ ≤ qd M T →
    (∀ p ∈ S, p.1 ≠ 1 ∧ σ ≤ p.2.re ∧ p.2.re < 1 ∧ |p.2.im| ≤ T ∧ DirichletCharacter.LFunction p.1 p.2 = 0) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (24 * (1 - σ)) * Real.log ((M : ℝ) * T) ^ 10
def Count0 : Prop :=
  ∃ C : ℝ, ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 3 / 4 ≤ σ → q₀ ≤ qd M T →
    (∀ p ∈ S, p.1 = 1 ∧ σ ≤ p.2.re ∧ p.2.re < 1 ∧ |p.2.im| ≤ T ∧ IsLZero p.1 p.2) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (24 * (1 - σ)) * Real.log ((M : ℝ) * T) ^ 10
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens



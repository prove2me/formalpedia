-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
-- name    : Formalism_PolynomialDimension_DigitClassSize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:20.513948+00:00
-- url     : https://prove2.me/theorems/a1e993b3-f146-482e-832f-66bcebbefd1a
-- title:
--   Digit Class Size
-- statement:
--   Definitions and structural lemmas for Digit Class Size, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/DigitClassSize.lean

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_PolynomialDimension_WeylDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.CountingSumsFrames
def dimPol (k' A : ℕ) : ℕ := (A + k').choose k'
def dimHar (k' al be : ℕ) : ℕ :=
  dimPol k' al * dimPol k' be - (if al = 0 ∨ be = 0 then 0 else dimPol k' (al - 1) * dimPol k' (be - 1))
def hwt (m : ℕ) (A B : ℕ) : Fin (m + 2) → ℤ := Fin.cons (A : ℤ) (Fin.snoc (fun _ : Fin m => (0 : ℤ)) (-(B : ℤ)))
def cwt (m : ℕ) (A c B : ℕ) (cl : Fin m → ℤ) : Fin (m + 2) → ℤ :=
  Fin.cons ((A : ℤ) + c) (Fin.snoc cl (-(B : ℤ)))
def LemmaS : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (C Cp R R'' : Type) [AddCommGroup C] [Module O C] [Module.Free O C] [Module.Finite O C]
      [AddCommGroup Cp] [Module O Cp] [Module.Free O Cp] [Module.Finite O Cp]
      [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
      [AddCommGroup R''] [Module O R''] [Module.Free O R''] [Module.Finite O R'']
      (io : C →ₗ[O] Cp) (ph : Cp →ₗ[O] R) (ps : R →ₗ[O] R'') (D ρp σ np : ℕ),
      Formalism.G0.GoodRank π (ps ∘ₗ ph) ρp D →
      Formalism.G0.GoodRank π (ph ∘ₗ io) σ D →
      (∀ n, Formalism.G0.GoodRank π ph n (2 * D) → n ≤ np) →
      Formalism.G0.GoodRank π (ps ∘ₗ ph ∘ₗ io) (σ + ρp - np) (2 * D)
def CountB : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (π : O), Irreducible π →
    ∀ (M : ℕ) (Rl CC : Fin M → Submodule O V) (n E c : ℕ), E < c →
      (∀ e e', e ≠ e' → ∀ x ∈ CC e, ∃ y ∈ Rl e', x = π ^ c • y) →
      (∀ e, ∃ h : CC e ≤ Rl e, Formalism.G0.GoodRank π (Submodule.inclusion h) n E) →
      M * n ≤ Module.finrank K V
def LevelCount : Prop :=
  ∀ k' A B : ℕ, ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B
def LevelTail : Prop :=
  ∀ k' A B J : ℕ, J ≤ min A B →
    (∑ j ∈ Icc J (min A B), dimHar k' (A - j) (B - j) = dimPol k' (A - J) * dimPol k' (B - J)) ∧
    ((dimPol k' (A - J) * dimPol k' (B - J) : ℕ) : ℝ) ≤
      (1 - (J : ℝ) / (B + k' + 1)) ^ k' * ((dimPol k' A * dimPol k' B : ℕ) : ℝ)
def LevelTailExp : Prop :=
  ∀ (k' A B J : ℕ) (La b' : ℝ), 2 ≤ k' → 0 < b' → 0 ≤ La → La * b' / (k' + 1) ≤ J →
    (B : ℝ) + k' + 1 ≤ 2 * b' →
    ((∑ j ∈ Icc J (min A B), dimHar k' (A - j) (B - j) : ℕ) : ℝ) ≤
      Real.exp (-La / 3) * ((dimPol k' A * dimPol k' B : ℕ) : ℝ)
def HarLower : Prop :=
  ∀ k' al be : ℕ, ((dimPol k' al * dimPol k' be : ℕ) : ℝ) * k' / (be + k') ≤ (dimHar k' al be : ℝ)
def BinomRatio : Prop :=
  ∀ k' al j : ℕ, 0 < al → 1 - (k' : ℝ) * j / al ≤ (dimPol k' al : ℝ) / dimPol k' (al + j)
def BinomSeries : Prop :=
  ∀ k' be : ℕ, 2 ≤ k' →
    HasSum (fun j : ℕ => (dimPol k' be : ℝ) / dimPol k' (be + j)) (((be : ℝ) + k') / ((k' : ℝ) - 1))
def BinomTail : Prop :=
  ∀ (k' be J : ℕ) (La b' : ℝ), 5 ≤ k' → 0 < b' → 0 ≤ La → La * b' / (k' + 1) ≤ J →
    (be : ℝ) + J + k' + 1 ≤ 2 * b' →
    ∑' j : ℕ, (dimPol k' be : ℝ) / dimPol k' (be + J + j) ≤
      Real.exp (-La / 3) * (((be : ℝ) + k') / ((k' : ℝ) - 1))
def DensityLower : Prop :=
  ∀ (k' al be : ℕ) (La b' : ℝ), 5 ≤ k' → 0 < al → 0 < b' → 0 ≤ La →
    (be : ℝ) + (⌊La * b' / (k' + 1)⌋₊ + 1 : ℕ) + k' + 1 ≤ 2 * b' →
    (1 - (k' : ℝ) * (La * b' / (k' + 1)) / al) * (1 - Real.exp (-La / 3)) ≤
      ∑ j ∈ range (⌊La * b' / (k' + 1)⌋₊ + 1),
        (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j))
def CloudDims : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N m c : ℕ) (A B : Fin N → ℕ) (cl : Fin N → Fin m → ℤ) (b' : ℝ),
    (∀ s, Antitone (cl s)) → (∀ s i, 0 ≤ cl s i ∧ cl s i ≤ c) → 0 < b' →
    (∀ s, b' ≤ 4 * A s ∧ b' ≤ 4 * B s) → (N : ℝ) * (m + 2) * c ≤ b' →
    (1 - C * N * (m + 2) * c / b') * ((∏ s, weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℚ) : ℝ) ≤
        (((∏ s, weylDim m (cl s)) * ∏ s, weylDim (m + 2) (hwt m (A s) (B s)) : ℚ) : ℝ) ∧
      ((∏ s, weylDim (m + 2) (hwt m (A s + c) (B s + c)) : ℚ) : ℝ) ≤
        (1 + C * N * (m + 2) * c / b') * ((∏ s, weylDim (m + 2) (hwt m (A s) (B s)) : ℚ) : ℝ)
def CloudShare : Prop :=
  ∀ (ρ dcl dH dHp dlam κH κHp x : ℝ), 0 < dlam → 0 ≤ dH → 0 ≤ dHp → 0 ≤ dcl →
    0 ≤ κH → κH ≤ 1 → 0 ≤ κHp → 0 ≤ x → x ≤ 1 →
    dcl * ((1 - κH) * dH - κHp * dHp) ≤ ρ →
    (1 - x) * dlam ≤ dcl * dH → dHp ≤ (1 + x) * dH → dcl * dH ≤ dlam →
    1 - ρ / dlam ≤ κH + 2 * κHp + x
def HockeyStick : Prop :=
  ∀ m B : ℕ, ∑ j ∈ range (B + 1), dimPol m (B - j) = dimPol (m + 1) B
def DigitClassCount : Prop :=
  ∀ m P g : ℕ, 0 < P →
    ((univ : Finset (Fin (m + 1) → Fin P)).filter (fun ρ => (∑ i, (ρ i : ℕ)) % P = g % P)).card = P ^ m
def DigitClassSize : Prop :=
  ∀ m P g e : ℕ, 0 < P → 0 < g → (g : ℝ) / P - (m + 1) ≤ e →
    (1 - ((m : ℝ) + 1) ^ 2 * P / g) * dimPol m g ≤ (P : ℝ) ^ m * dimPol m e
end Formalism.CountingSumsFrames



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_ConductorExponents
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_ConductorExponents
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:41:28.126856+00:00
-- url     : https://prove2.me/theorems/9540f72c-de9a-4c50-82d3-586f4d9305c4
-- title:
--   Conductor Exponents
-- statement:
--   Definitions and structural lemmas for Conductor Exponents, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/ConductorExponents.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents
open PowerSeries GlobalTheory.BK
def eW (N r : ℕ) : ℕ := 2 * (N - 1) * r
def eL (N η : ℕ) : ℕ := (N + 1) * η
def c₁ (η r : ℕ) : ℕ := η * (r + 1)
def c₂ (N η r : ℕ) : ℕ := c₁ η r + eW N r
def kExp (N η r : ℕ) : ℕ := c₂ N η r + η + eL N η + eW N r
structure Numerics (l e N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig
  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N
  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H
  large : 40 * (H * N ^ 2 + N ^ 3) < l
section
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι₀ ι₁ ι₂ : Type} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁]
  [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {η H : ℕ}
  {D₀ : BKDat O K l e a ι₀ η H} {D₁ : BKDat O K l e a ι₁ η H} {D₂ : BKDat O K l e a ι₂ η H}
def Hyp (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop :=
  IsExactTriple F.toHom G.toHom ∧ Numerics l e N η H Sig U ∧
    D₁.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) ∧ ∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))
def Lifts (G : BKHom D₁ D₂) (k : ℕ) (y₂' m₂ : Vec K a ι₂) : Prop :=
  ∃ y' ∈ D₁.Y', ∃ m ∈ D₁.Minv, D₁.Mon (y' + D₁.phi m) = 0 ∧
    G.app (y' + D₁.phi m) = (l : K) ^ k • (y₂' + D₂.phi m₂)
def Steps (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N r : ℕ) (y₂' m₂ : Vec K a ι₂) : Prop :=
  ∃ y₁' ∈ D₁.Y', ∃ m₁ ∈ D₁.Minv,

    G.app y₁' = (l : K) ^ eW N r • y₂' ∧ G.app m₁ = (l : K) ^ eW N r • m₂ ∧

    (l : K) ^ c₁ η r • D₁.Mon (y₁' + D₁.phi m₁) ∈ D₁.Z ∧

    (∃ w ∈ D₀.Z, F.onPol w = (l : K) ^ c₂ N η r • D₁.Mon (y₁' + D₁.phi m₁)) ∧
    (∃ w ∈ D₀.Zl, F.onPol (D₀.Lc w) = D₁.Mon (y₁' + D₁.phi m₁)) ∧

    (∃ y ∈ D₀.Y', F.onPol (D₀.Lc (D₀.cls y)) =
      (l : K) ^ (c₂ N η r + η + eL N η) • D₁.Mon (y₁' + D₁.phi m₁)) ∧

    ∃ y₀ ∈ D₀.Y', F.onPol (D₀.Mon y₀) =
        (l : K) ^ (c₂ N η r + η + eL N η) • D₁.Mon (y₁' + D₁.phi m₁) ∧

      D₁.Mon ((l : K) ^ (c₂ N η r + η + eL N η) • (y₁' + D₁.phi m₁) - F.app y₀) = 0 ∧
      G.app ((l : K) ^ (c₂ N η r + η + eL N η) • (y₁' + D₁.phi m₁) - F.app y₀) =
        (l : K) ^ kExp N η r • (y₂' + D₂.phi m₂)
end
def Lifting : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] [CompleteSpace K] (ι₀ ι₁ ι₂ : Type) [Fintype ι₀] [DecidableEq ι₀]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (η H : ℕ)
    (D₀ : BKDat O K l e a ι₀ η H) (D₁ : BKDat O K l e a ι₁ η H) (D₂ : BKDat O K l e a ι₂ η H)
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ),
    Hyp F G N Sig U → ∀ y₂' ∈ D₂.Y', ∀ m₂ ∈ D₂.Minv, D₂.Mon (y₂' + D₂.phi m₂) = 0 →
      Lifts G (kExp N η (maxPeriod l Sig)) y₂' m₂
def LiftingSteps : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] [CompleteSpace K] (ι₀ ι₁ ι₂ : Type) [Fintype ι₀] [DecidableEq ι₀]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (η H : ℕ)
    (D₀ : BKDat O K l e a ι₀ η H) (D₁ : BKDat O K l e a ι₁ η H) (D₂ : BKDat O K l e a ι₂ η H)
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ),
    Hyp F G N Sig U → ∀ y₂' ∈ D₂.Y', ∀ m₂ ∈ D₂.Minv, D₂.Mon (y₂' + D₂.phi m₂) = 0 →
      Steps F G N (maxPeriod l Sig) y₂' m₂
example : kExp 2 1 1 = 10 := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents



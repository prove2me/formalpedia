-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:15.861289+00:00
-- url     : https://prove2.me/theorems/5bc9692c-a769-4f2d-a522-5926aa1a5995
-- title:
--   Analytic
-- statement:
--   Definitions and structural lemmas for Analytic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HC
namespace An
abbrev abelian₂ (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)
def logDerivativeAtOne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1
def G (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0) -
    y * (Real.log y - 1 - Real.eulerMascheroniConstant)
def sumLamChi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (y / n - 1) 0 : ℝ) : ℂ)
open Classical in

def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ
def Induces {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  χ.IsPrimitive ∧ ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a
end An
namespace Frame
variable (φ : Frame)
abbrev Char : Type := φ.GG →* ℂˣ
def psC : φ.Char := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp φ.chQ
def TrivialOnFirstFactor {φ : Frame} (θ : φ.Char) : Prop := ∀ s ∈ φ.A0, θ (φ.tau1 s) = 1
def Chat : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1 ∧ θ φ.cc = 1}
def Xp : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1}
def Xm : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = -1}
end Frame
namespace HostRaw
variable {φ : Frame} (H : HostRaw φ)
def dir (θ : φ.Char) : DirichletCharacter ℂ H.condN := MulChar.ofUnitHom (θ.comp H.art)
def dirAt (θ : φ.Char) (a : ℕ) : ℂ := H.dir θ (a : ZMod H.condN)
def IsPrimOf (θ : φ.Char) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := An.Induces χ (H.dirAt θ) H.condN
def prim (θ : φ.Char) : PChar := PChar.of (H.dir θ)
def IsCharE {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := ∃ θ : φ.Char, H.IsPrimOf θ χ
def Kept (S : Finset PChar) (θ : φ.Char) : Prop := ∃ ψ ∈ S, H.IsPrimOf θ ψ.χ
def Bounded (S : Finset PChar) : Set φ.Char := {θ | (θ ∈ φ.Xp ∧ ¬ H.Kept S θ) ∨ θ ∈ φ.Xm}
def KeptInXp (S : Finset PChar) : Prop := ∀ ψ ∈ S, ∃ θ ∈ φ.Xp, H.IsPrimOf θ ψ.χ
def KeptEqChat (S : Finset PChar) : Prop :=
  (∀ ψ ∈ S, ∃ θ ∈ φ.Chat, H.IsPrimOf θ ψ.χ) ∧ ∀ θ ∈ φ.Chat, H.Kept S θ
def KeptEqXp (S : Finset PChar) : Prop := H.KeptInXp S ∧ ∀ θ ∈ φ.Xp, H.Kept S θ
def ChebyshevCharacterBound (x eps c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsCharE χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖An.gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))
def LogDerivativeBound (S : Finset PChar) (X x eps C : ℝ) : Prop :=
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf φ.chC χ → ‖An.logDerivativeAtOne χ‖ ≤ x ^ eps) ∧
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.logDerivativeAtOne χ‖ ≤ C * Real.log X
def BoundedCharsPointwise (S : Finset PChar) (x eps : ℝ) : Prop :=
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps)
def ExceptionalCharacterKept (S : Finset PChar) (psK : Option PChar) : Prop :=
  (∀ ψ, psK = some ψ → H.IsPrimOf φ.psC ψ.χ) ∧ (psK = none → ¬ H.Kept S φ.psC)
end HostRaw
structure HostConditions (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostRaw φ) : Prop where
  kept : H.KeptInXp T.KEPT
  a : H.ChebyshevCharacterBound x T.eps κ.c
  b : H.LogDerivativeBound T.KEPT X x T.eps κ.C
  c1 : H.BoundedCharsPointwise T.KEPT x T.eps
  e : H.ExceptionalCharacterKept T.KEPT T.psK
structure PreHostAn (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostAx φ) (rr rr' : ℕ) : Prop
    extends PreHost T κ X x H rr rr' where
  ha10 : HostConditions T κ X x H.toHostRaw
end Formalism.HC
end



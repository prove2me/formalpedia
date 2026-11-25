-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
-- name    : Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:44:34.874135+00:00
-- url     : https://prove2.me/theorems/7101278f-1cf3-479e-a808-334cfba6c2f2
-- title:
--   Core At H
-- statement:
--   Definitions and structural lemmas for Core At H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_RecH
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Window
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace UpperTheory.Comparison₂
open Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
def chr (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) : φ.Char := (ψ.toMonoidHom.comp (toE φ)).toHomUnits
variable {φ : Frame}
def HostAddCharCompatible (H : HostRaw φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ) : Prop :=
  ∀ ψ : AddChar (E0 × φ.A) ℂ, ψ ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    (∀ n : ℕ, n ≠ 0 → χ (n : ZMod N) = primVal (arith H) ψ n) → ell ψ = An.logDerivativeAtOne χ
open Classical in

def keptA (Λ : Level) (H : HostRaw φ) : Finset (AddChar (E0 × φ.A) ℂ) :=
  Finset.univ.filter fun ψ => H.Kept Λ.KEPT (chr φ ψ)
def koOf (Λ : Level) : ℝ := ∑ ψ ∈ Λ.KEPT, ‖An.logDerivativeAtOne ψ.χ‖
def CoreAtH (H : HostRaw φ) (TT : Finset φ.A) (eD eL K cHH eK eps x : ℝ) : Prop :=
  ∃ (U0 : Type) (_ : Fintype U0) (tr : U0 → φ.A)
    (W : U0 → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (Top : Type) (_ : Fintype Top)
    (m f : ℕ) (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (ell : AddChar (E0 × φ.A) ℂ → ℂ) (N : ℕ) (T2 : Finset φ.A) (a : φ.A → ℝ)
    (w : φ.A → Fin m → E0 × φ.A → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := φ.A)) (η X' θ : ℝ),
    HostAddCharCompatible H ell ∧ Dd.x = x ∧ Dd.ε = eps ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    (∀ s ∈ φ.A0, ∃ u, tr u = s) ∧ IdentU Dd tr (arith H) N ell TT a w eT eP ∧
    Formalism.LFunctionChainParameters.LChain.SizeData₂ Dd C Xpp ∧ ErrWindows Dd C Xpp eK K ∧ BNBoundsU Dd T2 ∧
    SizesA φ.A0 TT T2 a w N x Dd.b Dd.b' η X' θ ∧ ThinScales (arith H) ell X' θ ∧
    CostWindows x (fPl φ.A) Dd.b η θ ∧
    RestSize eps x (Fintype.card φ.A) TT.card T2.card m Dd.b Dd.k Dd.a ∧
    ∀ s ∈ T2, s ∈ φ.A0
def pcOf (ψ : PChar) : Deduction.PC := ⟨ψ.N, ψ.χ, ψ.prim⟩
def pcTo (ξ : Deduction.PC) : PChar := ⟨ξ.N, ξ.χ, ξ.prim⟩
def pcEquiv : PChar ≃ Deduction.PC := ⟨pcOf, pcTo, fun _ => rfl, fun _ => rfl⟩
end UpperTheory.Comparison₂
end



-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
-- name    : Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:07:23.795386+00:00
-- url     : https://prove2.me/theorems/99d58248-a0b7-4e2d-b2bc-7acfc43a7086
-- title:
--   Split Inertia
-- statement:
--   Definitions and structural lemmas for Split Inertia, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_RunBaseDimensionLeRankAddGenusTerm
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Deduction.CH
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
structure HostFactsS (D : ArithData H) (S : Finset ℕ) : Prop where
  d_prime : D.d.Prime
  two_mem : 2 ∈ S
  q1_mem : D.q1 ∈ S
  d_not_mem : D.d ∉ S
  unram : ∀ p : ℕ, p.Prime → p ∉ S → p ≠ D.d → D.inertia p = ⊥
  split_inertia : ∀ p ∈ S, ∀ x ∈ D.inertia p, InPhi x
  split_frob : ∀ p ∈ S, InPhi (D.frob p)
  inertia_d : ∀ x, x ∈ D.inertia D.d ↔ x = 0 ∨ x = sgc0
open Classical in

def PsiA (A0 : AddSubgroup H) : Finset (AddChar (E0 × H) ℂ) := univ.filter fun ψ => ∀ s ∈ A0, ψ (0, s) = 1
open Classical in

def wtA (c : ℝ) (ψ : AddChar (E0 × H) ℂ) : ℝ := if ∀ h : H, ψ (0, h) = 1 then 1 else c
open Classical in

def GmA (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Kp : Finset (AddChar (E0 × H) ℂ)) (c y : ℝ) : ℝ :=
  ∑ ψ ∈ Kp, wtA c ψ * (GPsi D ell ψ y).re
open Classical in

def SigA (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (y : ℝ) : ℝ :=
  ∑ ψ ∈ PsiA A0 \ Kp, ‖GPsi D ell ψ y‖
def SizesA (A0 : AddSubgroup H) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (N : ℕ)
    (x b b' η X' θ : ℝ) : Prop :=
  0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  (∀ u0 ∈ A0, ∀ j ρ, InPhi ρ → 0 < w u0 j ρ) ∧
  (∀ u0 ∈ A0, ∀ j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + η + 1) ∧
  (∀ u0 ∈ A0, ∀ j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w u0 j ρ ≤ 2 * b') ∧
  (∀ u0 ∈ A0, ∀ j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N)
def gapA (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (u0 : H) : ℝ :=
  ∑ t ∈ TT, ∑ j : Fin m, (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)
open Classical in

def CharsA (ell : AddChar (E0 × H) ℂ → ℂ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (TT : Finset H)
    (c M Ko CE ε x : ℝ) : Prop :=
  0 ∈ Kp ∧ (∀ ψ ∈ Kp, ψ ∈ PsiA A0 ∧ ψ sgc0 = 1) ∧ ((PsiA A0).card : ℝ) ≤ M ∧
  (∀ ψ ∈ Kp, (¬ ∀ h : H, ψ (0, h) = 1) →
    ‖(∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)‖ ≤ M * x ^ (-1 + ε) * (TT.card : ℝ)) ∧
  (∀ ψ ∈ Kp, ψ ≠ 0 → ‖ell ψ‖ ≤ Ko) ∧
  (∀ ψ ∈ PsiA A0, ψ ∉ Kp → ‖ell ψ‖ ≤ CE * Real.log x)
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}
def IdentU (Dd : Data U0 W Top m f) (tr : U0 → H) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) : Prop :=
  (∀ τ, Dd.aT τ = a (eT τ)) ∧ (∀ u j ρ, Dd.w u j ρ = w (tr u) j (eP ρ)) ∧
  Dd.gam = Real.eulerMascheroniConstant ∧ Dd.LpL = (ell chC).re ∧
  (∀ u, Dd.ASK u = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w (tr u) j))
def BNBoundsU (Dd : Data U0 W Top m f) (T2 : Finset H) : Prop :=
  Dd.B0 ≤ (2 * (Fintype.card H : ℝ)) * m * Dd.b * Dd.x ^ Dd.ε ∧
  Dd.Nc ≤ (T2.card : ℝ) * Dd.k * Dd.b * Dd.x ^ Dd.ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * Dd.x ^ (-Dd.ε)))
open Classical in

def ReadsKept (T : DType) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Kp : Finset (AddChar (E0 × H) ℂ)) : Prop :=
  ∃ rd : PC → AddChar (E0 × H) ℂ, Set.InjOn rd T.KEPT ∧ Kp = T.KEPT.image rd ∧
    ∀ ξ ∈ T.KEPT, (∀ n : ℕ, n ≠ 0 → ξ.χ (n : ZMod ξ.N) = primVal D (rd ξ) n) ∧ (rd ξ = 0 ↔ ξ = PC.one) ∧
      (ξ ≠ PC.one → ell (rd ξ) = ξ.kappa) ∧ (T.psK = some ξ ∨ ξ = PC.one ↔ rd ξ = psC ∨ rd ξ = 0)
def ChainCoreH (T : DType) (eD eL K cHH eK M CE x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H) (U0 : Type) (_ : Fintype U0) (tr : U0 → H)
    (W : U0 → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (Top : Type) (_ : Fintype Top)
    (m f : ℕ) (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (S : Finset ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ Ko : ℝ)
    (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)),
    Dd.x = x ∧ Dd.ε = T.eps ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    HostFactsS D S ∧ (∀ s ∈ A0, ∃ u, tr u = s) ∧ IdentU Dd tr D N ell TT a w eT eP ∧
    SizeData₂ Dd C Xpp ∧ ErrWindows Dd C Xpp eK K ∧ BNBoundsU Dd T2 ∧
    SizesA A0 TT T2 a w N x Dd.b Dd.b' η X' θ ∧ ThinScales D ell X' θ ∧
    CostWindows x (fPl H) Dd.b η θ ∧
    RestSize T.eps x (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a ∧
    (∀ s ∈ T2, s ∈ A0) ∧ CharsA ell A0 Kp TT T.aStar M Ko CE T.eps x ∧ ReadsKept T D ell Kp ∧
    ∀ ψ ∈ PsiA A0, ψ ∉ Kp → ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + T.eps)
end Deduction.CH
end



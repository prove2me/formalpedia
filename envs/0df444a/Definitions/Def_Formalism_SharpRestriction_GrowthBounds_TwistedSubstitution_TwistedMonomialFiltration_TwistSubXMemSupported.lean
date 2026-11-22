-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
-- name    : Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:49.291132+00:00
-- url     : https://prove2.me/theorems/df469b56-27e7-47f3-ad20-52d86cb71396
-- title:
--   Twist Sub XMem Supported
-- statement:
--   Definitions and structural lemmas for Twist Sub XMem Supported, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
def wDeg (w : Set ι) (μ : ι × Fin n →₀ ℕ) : ℕ := ∑ v ∈ μ.support, if v.1 ∈ w then μ v else 0
def wCoeff (w : Set ι) (M : ι × Fin n →₀ ℕ) (F : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ μ ∈ F.support with μ.filter (fun v => v.1 ∈ w) = M, monomial (μ.filter (fun v => v.1 ∉ w)) (F.coeff μ)
def WFree {B : Type*} [CommRing B] (w : Set ι) (P : MvPolynomial (ι × Fin n) B) : Prop :=
  ∀ ν ∈ P.support, ν.filter (fun v => v.1 ∈ w) = 0
def trivFil (B : Type*) [CommRing B] : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Fil B where
  F t := if t ≤ 0 then ⊤ else ⊥
  mul_mem := by
    intro t u a b ha hb
    by_cases ht : t ≤ 0
    · by_cases hu : u ≤ 0
      · rw [if_pos (by omega)]; exact AddSubgroup.mem_top _
      · rw [if_neg hu, AddSubgroup.mem_bot] at hb; rw [hb, mul_zero]; exact AddSubgroup.zero_mem _
    · rw [if_neg ht, AddSubgroup.mem_bot] at ha; rw [ha, zero_mul]; exact AddSubgroup.zero_mem _
  one_mem := by simp
  anti := by
    intro t u htu
    by_cases hu : u ≤ 0
    · rw [if_pos hu, if_pos (by omega)]
    · rw [if_neg hu]; exact bot_le
def wDegHom (w : Set ι) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Finsupp.liftAddHom fun v => if v.1 ∈ w then Nat.castAddMonoidHom ℤ else 0
def untw (w : Set ι) (j : Fin n) :
    MvPolynomial (ι × Fin n) (GLLaurent R n) →+* MvPolynomial (ι × Fin n) (GLLaurent R n) :=
  eval₂Hom C fun v =>
    if v.1 ∈ w then ∑ b : Fin n, C (twistMat R n j (-1) b v.2) * X (v.1, b) else X v
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3



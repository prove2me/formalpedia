-- Prove2me | Definitions.Def_LowRankUnivariateSOS_PeelingStep
-- name    : LowRankUnivariateSOS_PeelingStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:58:37.828972+00:00
-- url     : https://prove2.me/theorems/0f35c333-090f-5cfb-9d9f-2e41ebfe3dd4
-- title:
--   Peeling Step
-- statement:
--   Definitions and structural lemmas for Peeling Step, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd


set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
@[simp] theorem add_fst (u v : UPair) : (u + v).fst = u.fst + v.fst :=
  rfl
@[simp] theorem add_snd (u v : UPair) : (u + v).snd = u.snd + v.snd :=
  rfl
@[simp] theorem A_add_right (u v w : UPair) :
    A u (v + w) = A u v + A u w := by
  simp [A]
  ring
@[simp] theorem A_smul_left (a : ℝ) (u v : UPair) :
    A (a • u) v = a • A u v := by
  simp [A, Polynomial.smul_eq_C_mul]
  ring_nf
@[simp] theorem A_perpPair_right (t : Poly) (u v : UPair) :
    A (perpPair t u) (perpPair 1 v) = t * A u v := by
  simp [A, perpPair]
  ring
@[simp] theorem A_perpPair_self (t : Poly) (u : UPair) :
    A u (perpPair t u) = 0 := by
  simp [A, perpPair]
  ring
@[simp] theorem sigma2_add (u v : UPair) :
    sigma2 (u + v) = sigma2 u + 2 * A u v + sigma2 v := by
  simp [sigma2, A, pow_two]
  ring
structure PeelingStepWitness (u uImgPrev : UPair) (q : Poly) where
  qQuad : Poly
  sigmaConst : Poly
  aConst : Poly
  quad_in_prev_image : InImageA uImgPrev qQuad
  family : ℝ → UPair
  A_const : ∀ η : ℝ, A u (family η) = aConst
  sigma_eq : ∀ η : ℝ,
    sigma2 (family η) = (η ^ 2 : ℝ) • qQuad + (2 * η : ℝ) • q + sigmaConst
structure RotatedPeelingData (u uImgPrev : UPair) (q : Poly) where
  quad : UPair
  const : UPair
  quad_orth : InKerA u quad
  quad_in_prev_image : InImageA uImgPrev (sigma2 quad)
  cross_eq : A quad const = q
def HasPeelingWitness (u uImgPrev uImgNext : UPair) : Prop :=
  ∀ q : Poly, InImageA uImgNext q → Nonempty (PeelingStepWitness u uImgPrev q)
structure QuadraticFactorStep (u0 : UPair) (gStart gNext : Poly) where
  r : Poly
  r_dvd_sigma : r ∣ sigma2 u0
  r_dvd_scale : r ∣ gStart
  peel_eq : gNext * r = (Polynomial.X ^ 2) * gStart
section DotForm
variable {B : DotForm}
end DotForm
def RotatedPeelingData.family {u uImgPrev : UPair} {q : Poly}
    (hdata : RotatedPeelingData u uImgPrev q) (η : ℝ) : UPair :=
  η • hdata.quad + hdata.const
def RotatedPeelingData.toWitness {u uImgPrev : UPair} {q : Poly}
    (hdata : RotatedPeelingData u uImgPrev q) :
    PeelingStepWitness u uImgPrev q := by
  refine
    { qQuad := sigma2 hdata.quad
      sigmaConst := sigma2 hdata.const
      aConst := A u hdata.const
      quad_in_prev_image := hdata.quad_in_prev_image
      family := hdata.family
      A_const := ?_
      sigma_eq := ?_ }
  · intro η
    have horth : A u hdata.quad = 0 := by
      simpa [InKerA] using hdata.quad_orth
    calc
      A u (hdata.family η) = (η : ℝ) • A u hdata.quad + A u hdata.const := by
        simp [RotatedPeelingData.family, A_add_right, A_smul_right]
      _ = A u hdata.const := by simp [horth]
  · intro η
    calc
      sigma2 (hdata.family η) =
          sigma2 (η • hdata.quad) + 2 * A (η • hdata.quad) hdata.const + sigma2 hdata.const := by
            simp [RotatedPeelingData.family, sigma2_add]
      _ = (η ^ 2 : ℝ) • sigma2 hdata.quad +
            2 * ((η : ℝ) • A hdata.quad hdata.const) +
            sigma2 hdata.const := by
              simp [A_smul_left]
      _ = (η ^ 2 : ℝ) • sigma2 hdata.quad +
            ((2 * η : ℝ) • A hdata.quad hdata.const) +
            sigma2 hdata.const := by
              have hsmul :
                  2 * ((η : ℝ) • A hdata.quad hdata.const) =
                    ((2 * η : ℝ) • A hdata.quad hdata.const) := by
                simp [Polynomial.smul_eq_C_mul, two_mul]
                ring
              rw [hsmul]
      _ = (η ^ 2 : ℝ) • sigma2 hdata.quad + ((2 * η : ℝ) • q) + sigma2 hdata.const := by
              simp [hdata.cross_eq]
section DotForm
variable {B : DotForm}
end DotForm
inductive PeelingPath (u : UPair) : UPair → UPair → Prop
  | refl (uStart : UPair) : PeelingPath u uStart uStart
  | step {uStart uMid uEnd : UPair} :
      PeelingPath u uStart uMid →
      HasPeelingWitness u uMid uEnd →
      PeelingPath u uStart uEnd
inductive PeelingSchedule (u u0 : UPair) : Poly → Poly → Prop
  | done (g : Poly) : PeelingSchedule u u0 g g
  | peel {gStart gMid gEnd : Poly} :
      HasPeelingWitness u (scalePair gStart u0) (scalePair gMid u0) →
      PeelingSchedule u u0 gMid gEnd →
      PeelingSchedule u u0 gStart gEnd
def peelTerminalScale (gBase : Poly) : List Poly → Poly
  | [] => gBase
  | _ :: rs => peelTerminalScale ((Polynomial.X ^ 2) * gBase) rs
section DotForm
variable {B : DotForm}
end DotForm
end LowRankUnivariateSOS



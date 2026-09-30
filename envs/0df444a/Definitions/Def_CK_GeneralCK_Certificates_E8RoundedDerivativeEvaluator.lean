-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8RoundedDerivativeEvaluator
-- name    : CK_GeneralCK_Certificates_E8RoundedDerivativeEvaluator
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:51:11.224869+00:00
-- url     : https://prove2.me/theorems/27b15c7d-cd2a-4bdb-9153-8a8187e9afdf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8RoundedDerivativeEvaluator` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8RoundedDerivativeEvaluator` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8RoundedDerivativeEvaluator` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8RoundedDerivativeEvaluator (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8RoundedDerivativeEvaluator.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8RoundedRatBall
import Definitions.Def_CK_GeneralCK_Certificates_E8DerivativeBallEvaluator

-- ===== source module GeneralCK.Certificates.E8RoundedDerivativeEvaluator =====
section

/-! Fixed-precision derivative evaluator. Every arithmetic intermediate is
compressed, allowing generated leaves to use shallow literal equalities. -/

namespace GeneralCK.Certificates.E8RoundedDerivativeEvaluator

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8ThetaParamDerivativeExplicit
open E8ThetaTauDerivativeFormula
open Reflection.ComplexEntropy Reflection.ComplexGlobalAnalytic
open E8ThetaTauAnalytic

def rneg (D : ℕ) (a : RatBall) := compress D a.neg
def rsub (D : ℕ) (a b : RatBall) := sub D a b
def rdiv (D : ℕ) (a b : RatBall) := mul D a (invAuto D b)
def rsquare (D : ℕ) (a : RatBall) := mul D a a
def rlog (D : ℕ) (c : RatBall) : LogBoxes :=
  let raw := checkLogs c
  ⟨compress D raw.plus, compress D raw.minus, compress D raw.square⟩

structure RoundedThetaEval where
  plus : RatBall
  minus : RatBall
  square : RatBall
  B : RatBall
  E : RatBall
  Ep : RatBall
  oneMinus : RatBall
  den : RatBall
  denPrime : RatBall
  num : RatBall
  denSq : RatBall
  frac : RatBall
  prefactor : RatBall
  out : RatBall
  ok : Bool
  deriving Repr

def evalTheta (D : ℕ) (c L : RatBall) : RoundedThetaEval :=
  let logs := rlog D c
  let B := rsub D L (scale D (1/2) logs.square)
  let plusTerm := mul D (add D oneBall c) logs.plus
  let minusTerm := mul D (rsub D oneBall c) logs.minus
  let E := rsub D L (scale D (1/2) (add D plusTerm minusTerm))
  let Ep := scale D (1/2) (rsub D logs.minus logs.plus)
  let oneMinus := rsub D oneBall (rsquare D c)
  let den := mul D oneMinus B
  let denPrime := add D (mul D (scale D (-2) c) B)
    (mul D oneMinus (rdiv D c oneMinus))
  let num := rsub D (mul D (add D E (mul D c Ep)) den)
    (mul D (mul D c E) denPrime)
  let denSq := rsquare D den
  let frac := rdiv D num denSq
  let prefactor := rdiv D E8DerivativeBallEvaluator.twoBall L
  let out := mul D prefactor (add D (invAuto D oneMinus) frac)
  ⟨logs.plus, logs.minus, logs.square, B, E, Ep, oneMinus, den, denPrime,
    num, denSq, frac, prefactor, out,
    L.invOK && oneMinus.invOK && denSq.invOK⟩

structure RoundedTauEval where
  theta : RoundedThetaEval
  jac : RatBall
  cPrime : RatBall
  product : RatBall
  out : RatBall
  ok : Bool
  deriving Repr

def evalTau (D : ℕ) (tau c L : RatBall) : RoundedTauEval :=
  let theta := evalTheta D c L
  let jac := rsub D oneBall (mul D tau theta.Ep)
  let cPrime := rdiv D theta.E jac
  let product := mul D theta.out cPrime
  let out := rsub D product E8DerivativeBallEvaluator.fourBall
  ⟨theta, jac, cPrime, product, out,
    theta.ok && jac.invOK && out.acceptsUnit⟩

private theorem rsub_sound {D : ℕ} (hD : 0 < D) {a b : RatBall} {x y : ℂ}
    (hx : a.Holds x) (hy : b.Holds y) : (rsub D a b).Holds (x-y) :=
  compress_sound hD (holds_sub hx hy)

private theorem rscale_sound {D : ℕ} (hD : 0 < D) (q : ℚ)
    {a : RatBall} {x : ℂ} (hx : a.Holds x) :
    (scale D q a).Holds ((q : ℂ) * x) := compress_sound hD (holds_scale q hx)

private theorem rdiv_sound {D : ℕ} (hD : 0 < D) {a b : RatBall} {x y : ℂ}
    (hx : a.Holds x) (hy : b.Holds y) (hok : b.invOK = true) :
    (rdiv D a b).Holds (x/y) := by
  simpa [rdiv, div_eq_mul_inv] using mul_sound hD hx (invAuto_sound hD hy hok)

private theorem rsquare_sound {D : ℕ} (hD : 0 < D) {a : RatBall} {x : ℂ}
    (hx : a.Holds x) : (rsquare D a).Holds (x^2) := by
  simpa [rsquare, pow_two] using mul_sound hD hx hx

theorem evalTheta_sound {D : ℕ} (hD : 0 < D) {c L : RatBall} {z : ℂ}
    (hc : c.Holds z) (hz : ‖z‖ ≤ (1103/2500 : ℝ))
    (hL : L.Holds (Real.log 2 : ℂ)) (hok : (evalTheta D c L).ok = true) :
    (evalTheta D c L).out.Holds (thetaParamDerivExplicit z) := by
  have hz' : ‖z‖ ≤ (contactRadiusQ : ℝ) := by simpa [contactRadiusQ] using hz
  have hlogs := checkLogs_sound hc hz'
  have hp := compress_sound hD hlogs.1
  have hm := compress_sound hD hlogs.2.1
  have hs := compress_sound hD hlogs.2.2
  have hone := holds_point (1:ℚ) 0
  have htwo := holds_point (2:ℚ) 0
  have hB := rsub_sound hD hL (rscale_sound hD (1/2) hs)
  have hpt := mul_sound hD (add_sound hD hone hc) hp
  have hmt := mul_sound hD (rsub_sound hD hone hc) hm
  have hE := rsub_sound hD hL (rscale_sound hD (1/2) (add_sound hD hpt hmt))
  have hEp := rscale_sound hD (1/2) (rsub_sound hD hm hp)
  have hOne := rsub_sound hD hone (rsquare_sound hD hc)
  have hDen := mul_sound hD hOne hB
  have hOkL : L.invOK = true := by
    simpa [evalTheta] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1
  have hOkOne : (evalTheta D c L).oneMinus.invOK = true := by
    simpa [evalTheta, oneBall] using
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).2
  have hOkDen : (evalTheta D c L).denSq.invOK = true := by
    simpa [evalTheta, rlog, oneBall] using (Bool.and_eq_true_iff.mp hok).2
  have hcOver := rdiv_sound hD hc hOne
    (by simpa [evalTheta, oneBall] using hOkOne)
  have hDenPrime := add_sound hD (mul_sound hD (rscale_sound hD (-2) hc) hB)
    (mul_sound hD hOne hcOver)
  have hNum := rsub_sound hD (mul_sound hD (add_sound hD hE (mul_sound hD hc hEp)) hDen)
    (mul_sound hD (mul_sound hD hc hE) hDenPrime)
  have hDenSq := rsquare_sound hD hDen
  have hFrac := rdiv_sound hD hNum hDenSq
    (by simpa [evalTheta, rlog, oneBall] using hOkDen)
  have hPref := rdiv_sound hD htwo hL hOkL
  have hOut := mul_sound hD hPref (add_sound hD (invAuto_sound hD hOne
    (by simpa [evalTheta, oneBall] using hOkOne)) hFrac)
  have hOut' : (evalTheta D c L).out.Holds
      (thetaParamDerivFromLogs z (Complex.log (1+z)) (Complex.log (1-z))
        (Complex.log (1-z^2)) (Real.log 2 : ℂ)) := by
    convert hOut using 1 <;>
      simp [evalTheta, rlog, rsub, rdiv, rsquare, thetaParamDerivFromLogs,
        oneBall, E8DerivativeBallEvaluator.twoBall, GaussianRat.val,
        div_eq_mul_inv] <;> try ring <;> aesop
  rw [← explicit_eq_from_logs] at hOut'
  exact hOut'

theorem evalTau_sound {D : ℕ} (hD : 0 < D) {tauBall c L : RatBall} {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ)) (ht : tauBall.Holds tau)
    (hc : c.Holds (fixedPointOnDisc tau)) (hL : L.Holds (Real.log 2 : ℂ))
    (hok : (evalTau D tauBall c L).ok = true) :
    ‖thetaTauDerivExpr tau - 4‖ ≤ (1:ℝ) := by
  let z := fixedPointOnDisc tau
  have hz := norm_fixedPointOnDisc_le htau
  have hThetaOK : (evalTheta D c L).ok = true := by
    simpa [evalTau] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1
  have hJacOK : (evalTau D tauBall c L).jac.invOK = true := by
    simpa [evalTau] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).2
  have hAccept : (evalTau D tauBall c L).out.acceptsUnit = true :=
    (Bool.and_eq_true_iff.mp hok).2
  have hTheta := evalTheta_sound hD hc hz hL hThetaOK
  have hz' : ‖z‖ ≤ (contactRadiusQ : ℝ) := by simpa [contactRadiusQ] using hz
  have hlogs := checkLogs_sound hc hz'
  have hp := compress_sound hD hlogs.1
  have hm := compress_sound hD hlogs.2.1
  have hone := holds_point (1:ℚ) 0
  have hpt := mul_sound hD (add_sound hD hone hc) hp
  have hmt := mul_sound hD (rsub_sound hD hone hc) hm
  have hE := rsub_sound hD hL (rscale_sound hD (1/2) (add_sound hD hpt hmt))
  have hEp := rscale_sound hD (1/2) (rsub_sound hD hm hp)
  have hJac := rsub_sound hD hone (mul_sound hD ht hEp)
  have hcPrime := rdiv_sound hD hE hJac
    (by simpa [evalTau, evalTheta, rlog, oneBall] using hJacOK)
  have hcPrime' : (evalTau D tauBall c L).cPrime.Holds
      (entropyExt (fixedPointOnDisc tau) /
        (1 - tau * entropyDeriv (fixedPointOnDisc tau))) := by
    convert hcPrime using 1 <;>
      simp [evalTau, evalTheta, rlog, rsub, rdiv, rsquare, oneBall,
        GaussianRat.val, entropyExt, entropyDeriv] <;> try ring
  have hProduct := mul_sound hD hTheta hcPrime'
  have hOut := rsub_sound hD hProduct (holds_point (4:ℚ) 0)
  have hOut' : (evalTau D tauBall c L).out.Holds
      (thetaParamDerivExplicit (fixedPointOnDisc tau) *
        (entropyExt (fixedPointOnDisc tau) /
          (1 - tau * entropyDeriv (fixedPointOnDisc tau))) - 4) := by
    convert hOut using 1 <;>
      simp [evalTau, evalTheta, rlog, rsub, rdiv, rsquare, oneBall,
        E8DerivativeBallEvaluator.fourBall, GaussianRat.val] <;> try ring
  have hunit := acceptsUnit_sound hAccept hOut'
  have hderiv := deriv_thetaParam_eq_explicit hz
  rw [thetaTauDerivExpr, hderiv]
  exact hunit

/-- Soundness of the output ball before choosing a norm acceptance test. -/
theorem evalTau_out_sound {D : ℕ} (hD : 0 < D) {tauBall c L : RatBall} {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ)) (ht : tauBall.Holds tau)
    (hc : c.Holds (fixedPointOnDisc tau)) (hL : L.Holds (Real.log 2 : ℂ))
    (hThetaOK : (evalTheta D c L).ok = true)
    (hJacOK : (evalTau D tauBall c L).jac.invOK = true) :
    (evalTau D tauBall c L).out.Holds (thetaTauDerivExpr tau - 4) := by
  let z := fixedPointOnDisc tau
  have hz := norm_fixedPointOnDisc_le htau
  have hTheta := evalTheta_sound hD hc hz hL hThetaOK
  have hz' : ‖z‖ ≤ (contactRadiusQ : ℝ) := by simpa [contactRadiusQ] using hz
  have hlogs := checkLogs_sound hc hz'
  have hp := compress_sound hD hlogs.1
  have hm := compress_sound hD hlogs.2.1
  have hone := holds_point (1:ℚ) 0
  have hpt := mul_sound hD (add_sound hD hone hc) hp
  have hmt := mul_sound hD (rsub_sound hD hone hc) hm
  have hE := rsub_sound hD hL (rscale_sound hD (1/2) (add_sound hD hpt hmt))
  have hEp := rscale_sound hD (1/2) (rsub_sound hD hm hp)
  have hJac := rsub_sound hD hone (mul_sound hD ht hEp)
  have hcPrime := rdiv_sound hD hE hJac
    (by simpa [evalTau, evalTheta, rlog, oneBall] using hJacOK)
  have hcPrime' : (evalTau D tauBall c L).cPrime.Holds
      (entropyExt (fixedPointOnDisc tau) /
        (1 - tau * entropyDeriv (fixedPointOnDisc tau))) := by
    convert hcPrime using 1 <;>
      simp [evalTau, evalTheta, rlog, rsub, rdiv, rsquare, oneBall,
        GaussianRat.val, entropyExt, entropyDeriv] <;> try ring
  have hProduct := mul_sound hD hTheta hcPrime'
  have hOut := rsub_sound hD hProduct (holds_point (4:ℚ) 0)
  have hOut' : (evalTau D tauBall c L).out.Holds
      (thetaParamDerivExplicit (fixedPointOnDisc tau) *
        (entropyExt (fixedPointOnDisc tau) /
          (1 - tau * entropyDeriv (fixedPointOnDisc tau))) - 4) := by
    convert hOut using 1 <;>
      simp [evalTau, evalTheta, rlog, rsub, rdiv, rsquare, oneBall,
        E8DerivativeBallEvaluator.fourBall, GaussianRat.val] <;> try ring
  have hderiv := deriv_thetaParam_eq_explicit hz
  rw [thetaTauDerivExpr, hderiv]
  exact hOut'

end GeneralCK.Certificates.E8RoundedDerivativeEvaluator

end



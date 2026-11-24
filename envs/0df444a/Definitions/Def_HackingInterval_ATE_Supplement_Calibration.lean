-- Prove2me | Definitions.Def_HackingInterval_ATE_Supplement_Calibration
-- name    : HackingInterval_ATE_Supplement_Calibration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:54:27.700808+00:00
-- url     : https://prove2.me/theorems/2389e381-a231-4979-93e7-4f873f4bd6c9
-- title:
--   Student-t calibration and the displayed ATE and scalar prediction intervals
-- statement:
--   For $n$ observations and $p$ covariates, put $\nu=n-p-1>0$. For a residual sum of squares $s$ and a quantile $q$, define the calibrated loss threshold by
--
--   $$\theta(s,\nu,q)=s\left(1+\frac{q^2}{\nu}\right).$$
--
--   For treatment data, write $\widetilde\beta_{0,\mathrm{LS}}$ for the treatment coefficient of the full design $\widetilde X=[X,1[\mathrm{treated}]]$, and $V_{tt}$ for the treatment diagonal of $(\widetilde X^\top\widetilde X)^{-1}$. The classical ATE boundary pair is
--
--   $$\left(\widetilde\beta_{0,\mathrm{LS}}-q\sqrt{s/\nu}\sqrt{V_{tt}},\ \widetilde\beta_{0,\mathrm{LS}}+q\sqrt{s/\nu}\sqrt{V_{tt}}\right).$$
--
--   For a generic full design $X$, least-squares coefficient $\beta_{\mathrm{LS}}$, and prediction covariate $x$, the scalar comparison pair is
--
--   $$\left(x^\top\beta_{\mathrm{LS}}-q\sqrt{s/\nu}\sqrt{x^\top(X^\top X)^{-1}x},\ x^\top\beta_{\mathrm{LS}}+q\sqrt{s/\nu}\sqrt{x^\top(X^\top X)^{-1}x}\right).$$
--
--   These pairs are the displayed comparison intervals of Theorems 2 and 5. The treatment residual $s$ is the published base definition's full-design SSE; the prediction residual is that of the generic design. The square in the threshold follows published Appendix D ec17, and the scalar prediction center follows ec19.
--
--   **Formalization Note** The natural subtraction defining $\nu$ is used only under $p+1<n$, so its real cast equals the real difference $n-p-1$. Theorem 5 retains the source's displayed degrees of freedom; this definition asserts no additional coverage theorem.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), DOI 10.1287/mnsc.2020.3818, pp. 11–12 (PDF 12–13), Theorem 2 and eq. (18); p. 14 (PDF 15), Theorem 5; published Online Appendix D ec17, ec19

import Mathlib
import Definitions.Def_HackingInterval_ATE_Model
import Definitions.Def_HackingInterval_ATE_Supplement_StudentT
open Matrix
noncomputable section

namespace HackingInterval.ATE.Supplement

/-- Used with p + 1 < n; the cast then equals (n : ℝ) - (p : ℝ) - 1. -/
def residualDof (n p : ℕ) : ℕ := n - (p + 1)

/-- Appendix D ec17 / ec19: the squared-quantile calibration. -/
def calibratedTheta (s : ℝ) (ν : ℕ) (q : ℝ) : ℝ :=
  s * (1 + q ^ 2 / (ν : ℝ))

/-- Both boundary points of the displayed classical ATE interval (18). -/
def ateClassical {n p : ℕ} (D : TreatData n p) (ν : ℕ) (q : ℝ) : ℝ × ℝ :=
  (D.beta0TildeLS - q * Real.sqrt (D.SSE / (ν : ℝ)) * Real.sqrt D.Vtt,
   D.beta0TildeLS + q * Real.sqrt (D.SSE / (ν : ℝ)) * Real.sqrt D.Vtt)

/-- Scalar prediction boundaries from Theorem 5, with its center corrected as in ec19. -/
def predictionClassical {n p : ℕ} (D : Design (Fin n) (Fin p))
    (xnew : Fin p → ℝ) (ν : ℕ) (q : ℝ) : ℝ × ℝ :=
  (xnew ⬝ᵥ D.betaLS - q * Real.sqrt (D.SSE / (ν : ℝ)) *
      Real.sqrt (xnew ⬝ᵥ ((D.Xᵀ * D.X)⁻¹ *ᵥ xnew)),
   xnew ⬝ᵥ D.betaLS + q * Real.sqrt (D.SSE / (ν : ℝ)) *
      Real.sqrt (xnew ⬝ᵥ ((D.Xᵀ * D.X)⁻¹ *ᵥ xnew)))

end HackingInterval.ATE.Supplement



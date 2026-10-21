-- Prove2me | Definitions.Def_SysRiskPortfolio_CoER_Portfolio
-- name    : SysRiskPortfolio_CoER_Portfolio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:21.523825+00:00
-- url     : https://prove2.me/theorems/c064009b-544a-4d56-9a5d-f474f37106bc
-- title:
--   §2.1 and (A.6) — Gaussian portfolio model and standing assumptions
-- statement:
--   A portfolio has $n=m+1\ge2$ risky assets, weights $w$ with $\sum_i w_i=1$, mean vector $\mu$, covariance matrix $\Sigma$, asset-system covariance vector $\sigma$, and system mean and standard deviation $\mu_m,\sigma_m$. Its mean, standard deviation and correlation with the system are
--   $$\mu_p=w^\top\mu,\qquad \sigma_p=\sqrt{w^\top\Sigma w},\qquad \rho_p=\frac{w^\top\sigma}{\sigma_m\sigma_p}.$$
--   The portfolio criterion is CoER= under the bivariate Gaussian law with those parameters. The transformed optimization data are $\widehat\mu=\mu+\Phi^{-1}(q_m)\sigma/\sigma_m$, $\lambda=\phi(\Phi^{-1}(q_p))/q_p$, and $\widehat\Sigma=\Sigma-\sigma\sigma^\top/\sigma_m^2$.
--
--   **Formalization Note** The standing predicate includes $q_m,q_p\in(0,1/2)$, $\sigma_m>0$, $n\ge2$, and positive definiteness of the joint covariance $[\Sigma\ \sigma;\sigma^\top\ \sigma_m^2]$. The latter makes the Gaussian densities and printed inverses nondegenerate.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), pp. 4–7, 28–29, Assumptions 1–2, (A.6)

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_BivariateNormal
import Definitions.Def_SysRiskPortfolio_CoER_Optimizer

namespace SysRiskPortfolio.CoER

open Matrix

/-- Asset and system return parameters in §2.1. -/
structure PortfolioData (m : ℕ) where
  mu : Fin (m + 1) → ℝ
  Sig : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  sig : Fin (m + 1) → ℝ
  muM : ℝ
  sigM : ℝ
  qm : ℝ
  qp : ℝ

/-- Joint covariance of asset returns and system return, p. 28. -/
def jointCov {m : ℕ} (d : PortfolioData m) :
    Matrix (Fin (m + 1) ⊕ Unit) (Fin (m + 1) ⊕ Unit) ℝ :=
  Matrix.fromBlocks d.Sig (Matrix.replicateCol Unit d.sig)
    (Matrix.replicateRow Unit d.sig) (fun _ _ => d.sigM ^ 2)

/-- Standing §2 assumptions and the disclosed nondegeneracy of the joint Gaussian. -/
def Standing {m : ℕ} (d : PortfolioData m) : Prop :=
  1 ≤ m ∧ 0 < d.qm ∧ d.qm < (1 / 2 : ℝ) ∧
    0 < d.qp ∧ d.qp < (1 / 2 : ℝ) ∧
    0 < d.sigM ∧ (jointCov d).PosDef

/-- Portfolio mean. -/
def muP {m : ℕ} (d : PortfolioData m) (w : Fin (m + 1) → ℝ) : ℝ :=
  w ⬝ᵥ d.mu

/-- Portfolio standard deviation. -/
noncomputable def sigP {m : ℕ} (d : PortfolioData m) (w : Fin (m + 1) → ℝ) : ℝ :=
  Real.sqrt (w ⬝ᵥ (d.Sig *ᵥ w))

/-- Correlation of portfolio and system returns. -/
noncomputable def rhoP {m : ℕ} (d : PortfolioData m) (w : Fin (m + 1) → ℝ) : ℝ :=
  (w ⬝ᵥ d.sig) / (d.sigM * sigP d w)

/-- CoER= for a portfolio under the joint Gaussian model of Assumption 2. -/
noncomputable def coerPort {m : ℕ} (d : PortfolioData m)
    (w : Fin (m + 1) → ℝ) : ℝ :=
  CoER (muP d w) d.muM (sigP d w) d.sigM (rhoP d w) d.qm d.qp

/-- μ̂, λ, and Σ̂ of (A.6), supplied to the deterministic optimization problem. -/
noncomputable def optimData {m : ℕ} (d : PortfolioData m) : OptimData m where
  muHat := fun i => d.mu i + (PhiInv d.qm / d.sigM) * d.sig i
  lam := phi (PhiInv d.qp) / d.qp
  SigHat := d.Sig - (1 / d.sigM ^ 2) • Matrix.vecMulVec d.sig d.sig

end SysRiskPortfolio.CoER



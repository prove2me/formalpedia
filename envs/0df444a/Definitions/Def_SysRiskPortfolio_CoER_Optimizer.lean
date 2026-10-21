-- Prove2me | Definitions.Def_SysRiskPortfolio_CoER_Optimizer
-- name    : SysRiskPortfolio_CoER_Optimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:10.172171+00:00
-- url     : https://prove2.me/theorems/11c6240d-c381-466e-8aa3-55072fb5e872
-- title:
--   (A.5)–(A.8) — transformed objective and printed optimizer
-- statement:
--   For a vector $\widehat\mu$, a square matrix $\widehat\Sigma$, and a scalar $\lambda$, define
--   $$F(w)=w^\top\widehat\mu-\lambda\sqrt{w^\top\widehat\Sigma w}.$$
--   Separate the last asset from the first $n-1$. With $\Delta=\widehat\mu_n\mathbf1-\widetilde{\widehat\mu}$ and $Q=\widetilde\Sigma-\mathbf1\widetilde\sigma^\top-\widetilde\sigma\mathbf1^\top+\sigma_{nn}\mathbf1\mathbf1^\top$, define $w^*$ by the inverse-matrix expression printed in Proposition 2. This definition records the candidate; optimality is a separate theorem.
--
--   **Formalization Note** The last asset is the final index of $\operatorname{Fin}(m+1)$, and $Q$ is indexed by the first $m$ assets.
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), pp. 9, 29, Proposition 2, (A.5)–(A.8)

import Mathlib

namespace SysRiskPortfolio.CoER

open Matrix

/-- Data in the deterministic objective of (A.5), partitioned as in (A.7). -/
structure OptimData (m : ℕ) where
  muHat : Fin (m + 1) → ℝ
  SigHat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  lam : ℝ

/-- The all-ones vector. -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- Delta in (A.7), with the final asset eliminated. -/
def Del {m : ℕ} (d : OptimData m) : Fin m → ℝ :=
  fun i => d.muHat (Fin.last m) - d.muHat i.castSucc

/-- Q in (A.7), with sigma_nn taken from the final diagonal entry of Sigma-hat. -/
def Qm {m : ℕ} (d : OptimData m) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => d.SigHat i.castSucc j.castSucc
    - d.SigHat i.castSucc (Fin.last m)
    - d.SigHat (Fin.last m) j.castSucc
    + d.SigHat (Fin.last m) (Fin.last m)

/-- The printed closed-form portfolio in Proposition 2 and (A.7). -/
noncomputable def wStar {m : ℕ} (d : OptimData m) : Fin (m + 1) → ℝ :=
  let invS := d.SigHat⁻¹
  let invQ := (Qm d)⁻¹
  let h := ones (m + 1) ⬝ᵥ (invS *ᵥ ones (m + 1))
  let g := Del d ⬝ᵥ (invQ *ᵥ Del d)
  (1 / h) • (invS *ᵥ ones (m + 1)) -
    (1 / Real.sqrt ((d.lam ^ 2 - g) * h)) •
      Fin.snoc (invQ.transpose *ᵥ Del d) (-(ones m ⬝ᵥ (invQ *ᵥ Del d)))

/-- The deterministic objective wᵀμ̂ − λ√(wᵀΣ̂w) of (A.5). -/
noncomputable def objective {m : ℕ} (d : OptimData m) (w : Fin (m + 1) → ℝ) : ℝ :=
  w ⬝ᵥ (d.muHat) - d.lam * Real.sqrt (w ⬝ᵥ (d.SigHat *ᵥ w))

end SysRiskPortfolio.CoER



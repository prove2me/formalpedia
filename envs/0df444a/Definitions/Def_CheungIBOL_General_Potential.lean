-- Prove2me | Definitions.Def_CheungIBOL_General_Potential
-- name    : CheungIBOL_General_Potential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:10:32.761977+00:00
-- url     : https://prove2.me/theorems/1111a323-7b28-4e63-902d-58669ce47565
-- title:
--   Perturbed exponential potential and exact finite-capacity coefficient
-- statement:
--   For exploitation parameter $\epsilon$, the perturbed exponential potential is
--   $$\Psi_\epsilon(u)=\frac{e^{(1+\epsilon)u}-1}{e^{1+\epsilon}-1}.$$
--   For positive integer $b$, put
--   $$f_b(\epsilon)=\frac{1-e^{-(1+\epsilon)}}{(b+1+\epsilon)(1-e^{-(1+\epsilon)/b})}.$$
--   The coefficient $f_\Psi(\{b_i\},\epsilon)$ is the minimum of $f_{b_i}(\epsilon)$ over resources. Lean uses the infimum of this finite nonempty range; the model ensures $n>0$. All applications use $\epsilon\ge0$ and $u\in[0,1]$, where the denominators are positive. The functions are total outside those domains, but the theorems make no claims there.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 14 and 17, equations (7) and (14), https://arxiv.org/abs/1810.05640v2

import Mathlib

noncomputable section

namespace CheungIBOL.General

/-- Equation (7), used only at epsilon nonnegative and arguments in [0,1]. -/
def potential (ε u : ℝ) : ℝ :=
  (Real.exp ((1 + ε) * u) - 1) / (Real.exp (1 + ε) - 1)

/-- The resource-specific factor inside the minimum in equation (14). -/
def resourceFactor (b : ℕ+) (ε : ℝ) : ℝ :=
  (1 - Real.exp (-(1 + ε))) /
    (((b : ℕ) + 1 + ε) * (1 - Real.exp (-(1 + ε) / (b : ℕ))))

/-- On a nonempty resource set this finite infimum is precisely the minimum. -/
def coefficient {n : ℕ} (b : Fin n → ℕ+) (ε : ℝ) : ℝ :=
  sInf (Set.range fun i => resourceFactor (b i) ε)

end CheungIBOL.General



-- Prove2me | Definitions.Def_ThreeSum1960614_FixedModelAlgebra
-- name    : ThreeSum1960614_FixedModelAlgebra
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-14T13:32:32.590627+00:00
-- url     : https://prove2.me/theorems/d307edc4-2bbd-47f6-b033-0e818b9e8adb
-- title:
--   Exact witness constants for the expansion-232 model
-- statement:
--   Exact rational witnesses for the expansion-232 analytic model. The constants include lower bounds $E_0$ and $\kappa_0$, a ratio floor $\rho_0$, a split point $s$, upper and lower point bounds $G$ and $H$, and a saving cap $U$. The auxiliary coefficients are $$a=1-2\rho_0,\quad A=\tfrac12-\kappa_0-\rho_0,\quad C=aE_0-A.$$ The target is $1.96061349120$. These are numerical definitions; the model bound is proved separately.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/FixedModelAlgebra.lean#L10-L20

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
namespace ThreeSum1960614.FixedModel

def e0 : ℝ := 4648781151243719/1000000000000000
def k0 : ℝ := 778993608289/500000000000000
def ratio0 : ℝ := 34881106835777/125000000000000
def split : ℝ := 252561863698173/6250000000000000
def gammaCap : ℝ := 318487605190926/1000000000000000
def entropyFloor : ℝ := 244168410993740/1000000000000000
def savingCap : ℝ := 193175572822/1000000000000
def a : ℝ := 1-2*ratio0
def A : ℝ := 1/2-k0-ratio0
def C : ℝ := a*e0-A
def lowerTarget : ℝ := 196061349120/100000000000



end ThreeSum1960614.FixedModel



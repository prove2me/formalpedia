-- Prove2me | Definitions.Def_StableMSR_Recovery_Parameters
-- name    : StableMSR_Recovery_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:57:42.244212+00:00
-- url     : https://prove2.me/theorems/6367ee5a-544e-462e-a37f-c3d00b2031f1
-- title:
--   Explicit enumeration and treewidth parameters
-- statement:
--   For $0<\varepsilon<1$, set $\sigma=512$, $\chi=96$, and
--   $$
--   \Lambda_\varepsilon=\left\lceil\log_2(1+12\sigma/\varepsilon^2)\right\rceil,\quad
--   c_\varepsilon=1+80/\varepsilon+80/\varepsilon^2,
--   $$
--   $$
--   N_\varepsilon=\left\lceil16\sigma/\varepsilon^2\right\rceil,\quad
--   F_\varepsilon=\left\lceil12\chi\Lambda_\varepsilon/\varepsilon\right\rceil,\quad
--   h_\varepsilon=\lfloor12/\varepsilon\rfloor,\quad
--   \omega_\varepsilon=\left\lceil49c_\varepsilon^2+30c_\varepsilon\right\rceil.
--   $$
--   The parameter envelope is $N_\varepsilon+F_\varepsilon+h_\varepsilon(\omega_\varepsilon+1)+1$.
--
--   This is the source's explicit parameter layer for the running-time exponent. **Formalization Note** Natural ceilings and floors agree with the printed integers on $0<\varepsilon<1$. No runtime claim is made outside that domain. There is no invented numerical instruction constant.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), pp. 15–16, Appendix A.2/Table 2; p. 21, Appendix A.5; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Mathlib

set_option autoImplicit false

namespace StableMSR.Recovery

def sigma : ℝ := 512
def chi : ℝ := 96
noncomputable def lambda (ε : ℝ) : ℕ := ⌈Real.logb 2 (1 + 12 * sigma / ε ^ 2)⌉₊
noncomputable def growthConstant (ε : ℝ) : ℝ := 1 + 80 / ε + 80 / ε ^ 2
noncomputable def fewBound (ε : ℝ) : ℕ := ⌈16 * sigma / ε ^ 2⌉₊
noncomputable def splitBound (ε : ℝ) : ℕ := ⌈12 * chi * (lambda ε : ℝ) / ε⌉₊
noncomputable def ownerBound (ε : ℝ) : ℕ := ⌊12 / ε⌋₊
noncomputable def widthBound (ε : ℝ) : ℕ :=
  ⌈49 * growthConstant ε ^ 2 + 30 * growthConstant ε⌉₊
noncomputable def parameterEnvelope (ε : ℝ) : ℕ :=
  fewBound ε + splitBound ε + ownerBound ε * (widthBound ε + 1) + 1

end StableMSR.Recovery



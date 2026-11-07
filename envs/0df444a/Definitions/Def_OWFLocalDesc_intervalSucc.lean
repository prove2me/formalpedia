-- Prove2me | Definitions.Def_OWFLocalDesc_intervalSucc
-- name    : OWFLocalDesc_intervalSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:48:24.358193+00:00
-- url     : https://prove2.me/theorems/3ba77d20-474b-45f3-956e-aed5e66b9deb
-- title:
--   Success of a heuristic on one dataset
-- statement:
--   For a PPT heuristic $B$, a clock $t$, thresholds $\theta_1,\theta_2$ and a tolerance $d$, the success of $B$ on a dataset $(x,y)$ is
--   $$\Pr_B\Big[\mathrm{pSC}^t_{\theta_1}(x,y)-d\ \le\ B(1^n,x,y)\ \le\ \mathrm{pSC}^t_{\theta_2}(x,y)+d\Big],$$
--   over the coins of $B$, where the output of $B$ must be well formed.
--
--   **Formalization Note** The heuristic receives the code of $(1^n, x_1,\dots,x_m, y)$ (helper `datasetCode`).
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.5, p.19; Theorem 5.1, p.24

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_PPT
import Definitions.Def_OWFLocalDesc_pSC
import Definitions.Def_OWFLocalDesc_decodeOut
import Definitions.Def_OWFLocalDesc_InInterval
set_option autoImplicit false

namespace OWFLocalDesc

/-- The input of a heuristic: the code of `1ⁿ`, the points `x₁,…,x_m` and the label vector
`y` (§2.1, p.12: "A heuristic is a PPT algorithm that receives 1^n and a dataset"). -/
def datasetCode {m n : ℕ} (x : Fin m → Fin n → Bool) (y : Fin m → Bool) : List Bool :=
  QuantumPRC.tupleCode
    (QuantumPRC.unary n :: (List.ofFn fun i => List.ofFn (x i)) ++ [List.ofFn y])

/-- **Success of a heuristic on one dataset.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Theorem 4.5, p.19
and Theorem 5.1, p.24: the probability, over the coins of `B`, that `B(1ⁿ, x, y)` is well formed
and lies in `[pSC^t_{θ₁}(x,y) − d, pSC^t_{θ₂}(x,y) + d]`. A malformed output is a failure. -/
noncomputable def intervalSucc (U : Decoder) (t : ℕ) (θ₁ θ₂ : ℝ) (d : ℕ) (B : PPT) {m n : ℕ}
    (x : Fin m → Fin n → Bool) (y : Fin m → Bool) : ℝ :=
  B.prob (datasetCode x y) fun out =>
    ∃ o, decodeOut out = some o ∧ InInterval (pSC U t θ₁ x y) (pSC U t θ₂ x y) d o

end OWFLocalDesc



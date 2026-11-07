-- Prove2me | Definitions.Def_OnlineShadow_LogRate_logistic
-- name    : OnlineShadow_LogRate_logistic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:28.178548+00:00
-- url     : https://prove2.me/theorems/3c0b4578-6529-455c-83ec-fd138865fd6c
-- title:
--   Logistic function $f_{b,\lambda}(x)=1/(1+e^{\lambda(b-x)})$
-- statement:
--   For reals $b$ and $\lambda$, the logistic function centred at $b$ with sharpness $\lambda$ is
--   $$f_{b,\lambda}(x)=\frac1{1+e^{\lambda(b-x)}} .$$
--   It takes values in $(0,1)$. The soft threshold of Definition 4.2, $f_{\theta,\lambda}(x)=1/(1+e^{\lambda(\theta-\varepsilon/8-x)})$, is $f_{\theta-\varepsilon/8,\lambda}$: centred halfway between the low and high thresholds $\theta-\varepsilon/4$ and $\theta$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.2, p. 11; Corollary 4.6, p. 13

import Mathlib

namespace OnlineShadow.LogRate

/-- The logistic function `f_{b,λ}(x) = 1/(1 + e^{λ(b − x)})` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Corollary 4.6, p.13 and its proof,
p.17). The soft threshold of Definition 4.2 (p.11), `f_{θ,λ}(x) = 1/(1 + e^{λ(θ − ε/8 − x)})`, is
`logistic (θ − ε/8) λ`. -/
noncomputable def logistic (b lam x : ℝ) : ℝ :=
  1 / (1 + Real.exp (lam * (b - x)))

end OnlineShadow.LogRate



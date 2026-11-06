-- Prove2me | Definitions.Def_OmniMix_vLossR
-- name    : OmniMix_vLossR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:19.729601+00:00
-- url     : https://prove2.me/theorems/10a7d79e-f9e2-4ccc-a62f-1f294cb90772
-- title:
--   V-shaped loss $\lambda_v$ (real values)
-- statement:
--   For a threshold $v$, the **V-shaped loss** $\lambda_v$ is
--   $$
--   \lambda_v(q,1)=(1-v)\,\mathbb I\{q<v\},\qquad \lambda_v(q,0)=v\,\mathbb I\{q\ge v\},\qquad q\in[0,1].
--   $$
--   Its Bayes risk $\mathbb E_{Y\sim\mathrm{Ber}(p)}\lambda_v(p,Y)$ is the V-shaped function $\min\{(1-v)p,\,v(1-p)\}$. Every Lipschitz or mixable proper loss is, up to a constant, a conic combination of these losses (Lemma 2.1).
--
--   **Formalization Note** The threshold is a real number $v$ (the paper uses $v\in[0,1]$); this function returns the real value.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.9, Eq. (12)

import Mathlib

namespace OmniMix

/-- **The V-shaped loss `λ_v` (real values).** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.9, Eq. (12): "for any `v ∈ [0, 1]`,
the V-shaped loss `λ_v` parameterized by threshold `v` is defined through
`λ_v(q, 1) = (1 − v)I{q < v}` and `λ_v(q, 0) = vI{q ≥ v}`".

**Formalization Note.** The threshold `v` is a real number (it is an integration variable in
(13)); the paper uses `v ∈ [0, 1]`. The outcome `true` is `1`. -/
noncomputable def vLossR (v : ℝ) (q : unitInterval) (y : Bool) : ℝ :=
  if y then (if (q : ℝ) < v then 1 - v else 0) else (if v ≤ (q : ℝ) then v else 0)

end OmniMix



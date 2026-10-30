-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_B
-- name    : CrossLayerControl_ECCA_B
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:50:38.839983+00:00
-- url     : https://prove2.me/theorems/16504451-6f56-43b5-ba5d-991f786edc14
-- title:
--   The drift constant $B$
-- statement:
--   The drift constant is
--   $$B=\frac{L(\mu_{max}^2+\hat R^2)+P_{av}^2+P_{max}^2}{2}.$$
--
--   It bounds the second-order terms of the one-slot drift of the Lyapunov function $\tfrac12\big(\sum_i U_i^2+D^2\big)$, obtained from Lemma 4.3 for the $L$ data queues and the virtual power queue.
--
--   **Formalization Note** The paper leaves $B$ unspecified ("a constant that can be computed from the Lyapunov drift"); this is the explicit constant, which depends only on the model data and not on $V$.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115; (6.11), p. 109; Lemma 4.3, p. 52

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink

namespace CrossLayerControl.ECCA

/-- **The drift constant B.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115: "B is a constant that can be computed from the
Lyapunov drift of the system [116]"; (6.11), p. 109: "where B is a finite and positive constant".

`B M = (L (µmax² + R̂²) + Pav² + Pmax²) / 2`.

**Formalization Note.** The paper leaves B unspecified. This is the constant obtained from
Lemma 4.3 (p. 52) applied to the `L` data queues (service at most µmax, arrivals at most R̂) and to
the virtual power queue (6.13) (service Pav, arrivals at most Pmax), with the Lyapunov function
`(Σᵢ Uᵢ² + D²)/2`. It depends only on the model data, not on the control parameter `V`. -/
noncomputable def B {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) : ℝ :=
  ((L : ℝ) * (M.muMax ^ 2 + M.Rhat ^ 2) + M.Pav ^ 2 + M.Pmax ^ 2) / 2

end CrossLayerControl.ECCA



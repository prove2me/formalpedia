-- Prove2me | Definitions.Def_AggCG_Supplement_reluCost
-- name    : AggCG_Supplement_reluCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:26:34.79949+00:00
-- url     : https://prove2.me/theorems/385a7110-97ec-46b8-ae87-d33ee918b149
-- title:
--   One-weight four-example ReLU stopping cost
-- statement:
--   For four examples $(u_j,v_j,y_j)$, the one-trainable-weight ReLU model has loss
--   $$
--   f_S(w)=\tfrac12\sum_{j=1}^4(\max\{0,u_jw+v_j\}-y_j)^2.
--   $$
--   Constant-step gradient descent uses its derivative away from the ReLU kinks, and the normalized response is its capped gradient-norm stopping time.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), §L.3, p.66, PDF p.67

import Mathlib
import Definitions.Def_AggCG_Supplement_stopCost

namespace AggCG.Supplement

/-- A training example `(u, v, y)` for the one-weight ReLU model `h_w(u, v) = max{0, uw + v}`
(Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and
Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §L.3, p.66, PDF p.67). -/
structure ReLUEx where
  /-- Feature multiplying the trainable weight. -/
  u : ℚ
  /-- Feature with fixed coefficient one. -/
  v : ℚ
  /-- Label. -/
  y : ℚ

/-- The training loss `f_S(w) = ½ Σ_{j=1}^4 (max{0, u_j w + v_j} − y_j)²` (§L.3, p.66). -/
noncomputable def reluLoss (S : Fin 4 → ReLUEx) (w : ℝ) : ℝ :=
  (1 / 2) * ∑ j, (max 0 ((S j).u * w + (S j).v) - (S j).y) ^ 2

/-- The derivative of `f_S` at a point off every ReLU kink: `Σ_j 1{u_j w + v_j > 0} u_j (u_j w + v_j − y_j)`.

**Formalization Note** At a kink (`u_j w + v_j = 0`) `f_S` need not be differentiable; the theorems only
evaluate this at regular runs, which avoid the kinks, where it is the derivative of `reluLoss`. -/
noncomputable def reluGrad (S : Fin 4 → ReLUEx) (w : ℝ) : ℝ :=
  ∑ j, if 0 < (S j).u * w + (S j).v then ((S j).u : ℝ) * ((S j).u * w + (S j).v - (S j).y) else 0

/-- Gradient descent on the scalar weight with constant step size `η`: `w_{t+1} = w_t − η f_S'(w_t)`. -/
noncomputable def reluIter (S : Fin 4 → ReLUEx) (w0 η : ℝ) : ℕ → ℝ
  | 0 => w0
  | t + 1 => reluIter S w0 η t - η * reluGrad S (reluIter S w0 η t)

/-- A regular run: the iterates `w_0, …, w_H` avoid every kink `u_j w + v_j = 0` (§L, p.64). -/
def ReLURegular (S : Fin 4 → ReLUEx) (w0 η : ℝ) (H : ℕ) : Prop :=
  ∀ t ≤ H, ∀ j, ((S j).u : ℝ) * reluIter S w0 η t + (S j).v ≠ 0

/-- The capped stopping cost `min{t ≤ H : |f_S'(w_t)| < ϑ}` (else `H`) of the run. -/
noncomputable def reluCost (S : Fin 4 → ReLUEx) (w0 η ϑ : ℝ) (H : ℕ) : ℕ :=
  stopCost (fun t => |reluGrad S (reluIter S w0 η t)|) ϑ H

end AggCG.Supplement



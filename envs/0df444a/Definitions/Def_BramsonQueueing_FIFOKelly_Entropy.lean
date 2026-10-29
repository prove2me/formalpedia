-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Entropy
-- name    : BramsonQueueing_FIFOKelly_Entropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:06:40.723987+00:00
-- url     : https://prove2.me/theorems/1a848cac-83ee-49a8-9495-fb03d9d89061
-- title:
--   FIFO entropy, regular points and dissipation expressions
-- statement:
--   For nonnegative arguments put $h(x)=x\log x$ and $h_k(x)=x\log(x/\lambda_k)$. The entropy is
--   $$H(t)=\sum_k\int_t^{t+W_{s(k)}(t)}h_k(D_k'(r))\,dr.$$
--   Derivatives are within the nonnegative time half-line, so the endpoint uses a right derivative. Regular points are times when all six component derivatives exist. The module also names the arrival-minus-departure entropy flux, the station term $\sum_j h(1+W_j')/m_j^s$, the total queue derivative, and $\sum_j(W_j')^2$.
--
--   **Formalization Note** At zero total arrival rate the declared reading uses Lean's total real division and logarithm, giving $h_k(x)=0$. This does not repair the source's missing domain convention: the recorded counterexample remains a target of Proposition 5.13. For basic fluid solutions derivatives are bounded almost everywhere on bounded intervals, so entropy integrals do not acquire a spurious zero from nonintegrability.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 105, 148–151; PDF 113, 156–159

import Definitions.Def_BramsonQueueing_FIFOKelly_Fluid

namespace BramsonQueueing.FIFOKelly

open scoped BigOperators
open MeasureTheory Set

noncomputable def h (x : ℝ) : ℝ := x * Real.log x

/-- Full-domain reading of (5.22): real division and log are total, so
this is zero when the reference rate is zero. See the source finding. -/
noncomputable def classEntropy {K J : ℕ} (p : Parameters K J)
    (k : Fin K) (x : ℝ) : ℝ := x * Real.log (x / arrivalRate p k)

noncomputable def rate (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  derivWithin f (Ici 0) t

noncomputable def entropy {K J : ℕ} (p : Parameters K J)
    (X : SixPaths K J) (t : ℝ) : ℝ :=
  ∑ k, ∫ r in t..(t + X.W t (p.data.p k)),
    classEntropy p k (rate (fun s => X.D s k) r)

def Regular {K J : ℕ} (X : SixPaths K J) (t : ℝ) : Prop :=
  0 ≤ t ∧
  (∀ k, DifferentiableWithinAt ℝ (fun r => X.A r k) (Ici 0) t ∧
    DifferentiableWithinAt ℝ (fun r => X.D r k) (Ici 0) t ∧
    DifferentiableWithinAt ℝ (fun r => X.T r k) (Ici 0) t ∧
    DifferentiableWithinAt ℝ (fun r => X.Z r k) (Ici 0) t) ∧
  (∀ j, DifferentiableWithinAt ℝ (fun r => X.W r j) (Ici 0) t ∧
    DifferentiableWithinAt ℝ (fun r => X.Y r j) (Ici 0) t)

noncomputable def entropyFlux {K J : ℕ} (p : Parameters K J)
    (X : SixPaths K J) (t : ℝ) : ℝ :=
  ∑ k, (classEntropy p k (rate (fun r => X.A r k) t) -
    classEntropy p k (rate (fun r => X.D r k) t))

noncomputable def stationEntropyFlux {K J : ℕ} (p : Parameters K J)
    (X : SixPaths K J) (t : ℝ) : ℝ :=
  ∑ j, (stationMean p j)⁻¹ * h (1 + rate (fun r => X.W r j) t)

noncomputable def queueDerivative {K J : ℕ} (X : SixPaths K J) (t : ℝ) : ℝ :=
  ∑ k, rate (fun r => X.Z r k) t

noncomputable def workloadDissipation {K J : ℕ} (X : SixPaths K J) (t : ℝ) : ℝ :=
  ∑ j, (rate (fun r => X.W r j) t) ^ 2

end BramsonQueueing.FIFOKelly



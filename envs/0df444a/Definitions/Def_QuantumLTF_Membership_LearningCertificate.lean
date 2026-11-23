-- Prove2me | Definitions.Def_QuantumLTF_Membership_LearningCertificate
-- name    : QuantumLTF_Membership_LearningCertificate
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:51:45.524945+00:00
-- url     : https://prove2.me/theorems/6bc5cd49-b043-4391-ac46-a8d9eb51322b
-- title:
--   Analytic success certificate for the proof of Theorem 3.4
-- statement:
--   For $0<\epsilon\le 1/2$, record one of the two success modes in the proof of Theorem 3.4. In the **constant mode**, the test satisfies $T_\epsilon=\sqrt{2\log(1/\epsilon)}\le|\theta|$ and the output $(a,b)$ represents the constant LTF with value $f_{w,\theta}(0)$. In the **nonconstant mode**, there are an orientation $s\in\{-1,1\}$, an exact direction-gradient vector $g$ and its estimate $\widetilde g$, and an exact offset $h$ and its estimate $\widetilde h$ such that
--   \[
--   1/3\le\|g\|\le10,\qquad w=-sg/\|g\|,\qquad\theta=sh/\|g\|,
--   \]
--   \[
--   L_\epsilon\ge1,\qquad |h|\le L_\epsilon,\qquad |\widetilde h-h|\le\epsilon/100,
--   \]
--   and
--   \[
--   \|\widetilde g-g\|\le\frac{\epsilon}{100(L_\epsilon+1)}.
--   \]
--   The output parameters are $a=-s\widetilde g$ and $b=s\widetilde h$.
--
--   This predicate merely exposes the data used by the proof: actual output wires need only the unnormalized pair $(a,b)$, since $f_{a,b}$ already equals the normalized hypothesis $f_{\widehat w,\widehat\theta}$ with $\widehat w=-s\widetilde g/\|\widetilde g\|$ and $\widehat\theta=s\widetilde h/\|\widetilde g\|$. It separates the coherent algorithm from the deterministic normalization and Gaussian-error analysis.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, proof of Theorem 3.4, pp. 31–34 (PDF pp. 32–34), Eqs. (64)–(71) and the final displayed output formula on p. 33 (PDF p. 34).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_Leps

namespace QuantumLTF.Membership

/-- The analytic success certificate produced by the endpoint test or by offset and gradient estimation
in the proof of Theorem 3.4. The constant branch stores the constant label as an LTF with zero normal
vector. The nonconstant branch stores the unnormalized output `a = -s*gtilde` and `b = s*htilde`. -/
noncomputable def LearningCertificate {n : ℕ} (ε : ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (b : ℝ) : Prop :=
  ((∀ x, ltf a b x = ltf w θ 0) ∧ Teps ε ≤ |θ|) ∨
  ∃ (s : ℤ) (h ht : ℝ) (g gt : EuclideanSpace ℝ (Fin n)),
    (s = 1 ∨ s = -1) ∧
    1 ≤ Leps ε ∧
    1 / 3 ≤ ‖g‖ ∧ ‖g‖ ≤ 10 ∧
    w = -(s : ℝ) • (‖g‖⁻¹ • g) ∧
    θ = (s : ℝ) * h / ‖g‖ ∧
    |ht - h| ≤ ε / 100 ∧ |h| ≤ Leps ε ∧
    ‖gt - g‖ ≤ ε / (100 * (Leps ε + 1)) ∧
    a = -(s : ℝ) • gt ∧ b = (s : ℝ) * ht

end QuantumLTF.Membership



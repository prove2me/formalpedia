-- Prove2me | Definitions.Def_AnchoredEP_lyapunovV
-- name    : AnchoredEP_lyapunovV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:03.987816+00:00
-- url     : https://prove2.me/theorems/072ff50e-a28b-49d7-aab8-380a00864889
-- title:
--   Potential $V_k$ of the AEP analysis
-- statement:
--   Along a run of the AEP framework with anchor $z_0$, set $V_0=0$ and, for $k\ge1$,
--   $$
--   V_k=A_k\langle F(z_k)+v_k,\,z_k-z_0\rangle+\frac{A_k^2}{2}\|F(z_k)+v_k\|^2 .
--   $$
--   This potential decreases along the run (Lemma C.2) and yields the tangent-residual bound of Theorem 3.2.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma C.2, Eq. (35), p.22

import Mathlib

open InnerProductSpace

namespace AnchoredEP

/-- **The potential `V_k` of the AEP analysis.** Jiang–Yoon, arXiv:2609.30212, Lemma C.2, Eq. (35),
p.22: "Set `V₀ := 0` and, for every `k ≥ 1`, define
`V_k := A_k⟨F(z_k) + v_k, z_k − z₀⟩ + A_k²/2 ‖F(z_k) + v_k‖²`."

The anchor `z₀` is `z 0`. -/
noncomputable def lyapunovV {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z v : ℕ → EuclideanSpace ℝ (Fin d)) (A : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else A k * ⟪F (z k) + v k, z k - z 0⟫_ℝ + A k ^ 2 / 2 * ‖F (z k) + v k‖ ^ 2

end AnchoredEP



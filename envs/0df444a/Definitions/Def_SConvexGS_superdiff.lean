-- Prove2me | Definitions.Def_SConvexGS_superdiff
-- name    : SConvexGS_superdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:24.311989+00:00
-- url     : https://prove2.me/theorems/cb626fe6-bcb0-49c4-b925-d0f2d868c5c6
-- title:
--   Superdifferential $\partial h(p)$
-- statement:
--   For an extended-real-valued $h$ and a point $p$ with $h(p)$ finite, the **superdifferential** is
--
--   $$\partial h(p)=\{v\in\mathbb R^n\mid h(r)\le h(p)+v^{T}(r-p)\ \text{ for all } r\in\mathbb R^n\}.$$
--
--   It is empty when $h(p)$ is not finite. The paper uses it for $h=f_*$ in the proof of Theorem 7 and in Appendix EC.5.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Proof of Theorem 7, p.22, and Appendix EC.5, p.ec6

import Mathlib

open Matrix

namespace SConvexGS

/-- The set of supergradients `∂h(p)` of a function `h : ℝⁿ → [−∞, ∞]` at `p` (Chen, Li, *S-Convexity
and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), Proof of Theorem 7, p.22, and
Appendix EC.5, p.ec6).

Formalization Note: `h p` is required finite, so `∂h(p) = ∅` off `dom h`, as in Rockafellar (1970),
§23, read on the concave side. The right side is then `h(p) + vᵀ(r − p)`, with finite `h p`. -/
def superdiff {n : ℕ} (h : (Fin n → ℝ) → EReal) (p : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {v | h p ≠ ⊤ ∧ h p ≠ ⊥ ∧ ∀ r, h r ≤ h p + ((v ⬝ᵥ (r - p) : ℝ) : EReal)}

end SConvexGS



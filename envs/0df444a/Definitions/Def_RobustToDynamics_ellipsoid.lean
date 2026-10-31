-- Prove2me | Definitions.Def_RobustToDynamics_ellipsoid
-- name    : RobustToDynamics_ellipsoid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:17.99496+00:00
-- url     : https://prove2.me/theorems/ca7b14ec-5f6f-4195-bd27-73bcad2e1e1b
-- title:
--   The sublevel set $E(\alpha)=\{x : x^TMx\le\alpha\}$
-- statement:
--   For a real $n\times n$ matrix $M$ and a real number $\alpha$,
--   $$
--   E(\alpha)=\{x\in\mathbb R^n : x^TMx\le\alpha\}.
--   $$
--   When $M\succ0$ and $\alpha>0$ this is a solid ellipsoid. The proof of Theorem 2.7 sandwiches $P$ between two such sets that are invariant under $x\mapsto Gx$.
--
--   **Formalization Note** $x^TMx$ is `x ⬝ᵥ (M *ᵥ x)`; the definition is stated for every real $M$ and $\alpha$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 1, p.14

import Mathlib

open Matrix

namespace RobustToDynamics

/-- **The sublevel set `E(α) = {x ∈ ℝⁿ | xᵀMx ≤ α}`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 1, p.14: "E(α) := {x ∈ Rn| xT Mx ≤ α}".

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ` and `xᵀMx` is `x ⬝ᵥ (M *ᵥ x)`. The definition makes
sense for every real matrix `M` and every real `α`; it is an ellipsoid when `M` is positive
definite and `α > 0`. -/
def ellipsoid {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : Set (Fin n → ℝ) :=
  {x | x ⬝ᵥ (M *ᵥ x) ≤ α}

end RobustToDynamics



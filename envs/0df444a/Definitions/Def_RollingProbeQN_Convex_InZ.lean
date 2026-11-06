-- Prove2me | Definitions.Def_RollingProbeQN_Convex_InZ
-- name    : RollingProbeQN_Convex_InZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:57.629682+00:00
-- url     : https://prove2.me/theorems/cb968b9d-3c71-437b-8063-939b8ec120e7
-- title:
--   The model set $\mathcal Z=\{B\in\mathbb S^d:0\preceq B\preceq L_1I\}$
-- statement:
--   The set of admissible curvature models is
--
--   $$\mathcal Z=\{B\in\mathbb S^d:\ 0\preceq B\preceq L_1 I\},$$
--
--   the symmetric matrices satisfying the spectral bounds of Assumption 2.1. Algorithm 1 projects its model onto $\mathcal Z$.
--
--   **Formalization Note** $\preceq$ is the Loewner order, written with positive semidefiniteness (which includes symmetry).
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, §2, p. 7

import Mathlib

namespace RollingProbeQN.Convex

/-- **The model set `Z = {B ∈ S^d : 0 ⪯ B ⪯ L₁ I}`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §2, p. 7: "We write `f★ = f(x★)` and `Z = {B ∈ S^d : 0 ⪯ B ⪯ L1 I}`, the set of symmetric
matrices satisfying Assumption 2.1".

**Formalization Note.** `⪯` is the Loewner order, written with `Matrix.PosSemidef` (which includes
symmetry). -/
def InZ {d : ℕ} (L₁ : ℝ) (B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  B.PosSemidef ∧ (L₁ • (1 : Matrix (Fin d) (Fin d) ℝ) - B).PosSemidef

end RollingProbeQN.Convex



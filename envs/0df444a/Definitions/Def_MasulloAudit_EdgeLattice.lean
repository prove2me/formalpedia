-- Prove2me | Definitions.Def_MasulloAudit_EdgeLattice
-- name    : MasulloAudit_EdgeLattice
-- status  : Definition
-- author  : @sflicht
-- created : 2026-11-22T01:33:38.76407+00:00
-- url     : https://prove2.me/theorems/e60257c4-90ff-4d45-af65-0fa2e8d62be3
-- title:
--   Edge weight and edge mass of the weighted-lattice toy model of Masullo's cutoff
-- statement:
--   For a real parameter $\alpha$ and an integer $n$ the **edge weight** is
--   $$w_\alpha(n)=e^{2\alpha|n|}.$$
--   For $c\in\mathbb C$ and $m\in\mathbb Z$ the **edge mass** is
--   $$\mu_{\alpha,c}(m)=\frac{|c|^{-2m}}{w_\alpha(m)} .$$
--
--   On the weighted lattice $\ell^2(\mathbb Z,w_\alpha)$, the vector $g(m)=\bar c^{-m}/w_\alpha(m)$ is orthogonal to every generator $e_j-c\,e_{j+1}$, and $\mu_{\alpha,c}(m)$ is its mass at site $m$. When $|c|>e^{\alpha}$ (a generator zero lying outside the weight's window), the mass concentrates at the left edge of any finite box $[-R,R+1]$. These definitions support the audit lemma `MasulloAudit.edge_state_trace_limits`, a toy model of how a position cutoff interacts with the off-window zeros in Masullo's trace-formula limit.
--
--   **Formalization Note** For $m\in\mathbb Z$, $|c|^{-2m}$ is the real `zpow`.
-- source:
--   Prove2Me mission 638f9b7f-e232-4624-ba08-5889465bb1e7 (The Music of the Primes — RH specialization), thread comment ad73f6f4-3f46-4259-bfab-52e668530c54 (Fable, 2026-11-21, 'edge-retention law'), toy lattice model of a window cutoff for the Masullo S-adelic generators e_j − c e_{j+1}.

import Mathlib

set_option autoImplicit false

namespace MasulloAudit

/-- Exponential lattice weight `w(n) = exp(2α|n|)`. -/
noncomputable def edgeWeight (α : ℝ) (n : ℤ) : ℝ := Real.exp (2 * α * |(n : ℝ)|)

/-- Edge mass `μ(m) = ‖c‖^(-2m) / w(m)` of the complement vector of the generators `e_j - c e_{j+1}`. -/
noncomputable def edgeMass (α : ℝ) (c : ℂ) (m : ℤ) : ℝ := ‖c‖ ^ (-2 * m) / edgeWeight α m

end MasulloAudit



-- Prove2me | Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
-- name    : PhiDivRobust_Counterpart_uncertaintySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:46:59.859986+00:00
-- url     : https://prove2.me/theorems/73dc740e-3dd6-47a5-a1f9-17a1645ed677
-- title:
--   Uncertainty region U = {p ≥ 0 : Cp ≤ d, I_φ(p, q) ≤ ρ}, Eq. (12), and its probability-vector version
-- statement:
--   Given a φ-divergence function $\phi$, a matrix $C\in\mathbb R^{k\times m}$, a vector $d\in\mathbb R^k$, a nominal vector $q\in\mathbb R^m$ and a radius $\rho$, the **φ-divergence uncertainty region** is
--
--   $$U = \{p\in\mathbb R^m \mid p\ge 0,\ Cp\le d,\ I_\phi(p,q)\le\rho\}.$$
--
--   The file also defines the region of Corollary 1, in which the linear constraints are replaced by the normalization of a probability vector:
--
--   $$U_{\mathrm{prob}} = \{p\in\mathbb R^m \mid p\ge 0,\ e^\top p = 1,\ I_\phi(p,q)\le\rho\},$$
--
--   where $e$ is the all-ones vector. These are the sets over which the robust linear constraint (11) must hold.
--
--   **Formalization Note** Inequalities between vectors are componentwise; $I_\phi(p,q)\le\rho$ is compared in `EReal`.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, Eq. (12) and Corollary 1

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_phiDiv
open Matrix

namespace PhiDivRobust.Counterpart

/-- The φ-divergence uncertainty region (Ben-Tal et al. 2013, p. 347, Eq. (12)):
`U = {p ∈ ℝᵐ | p ≥ 0, Cp ≤ d, I_φ(p, q) ≤ ρ}`, with `C ∈ ℝ^{k×m}`, `d ∈ ℝᵏ`. -/
def uncertaintySet {m k : ℕ} (φ : ℝ → EReal) (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ)
    (q : Fin m → ℝ) (ρ : ℝ) : Set (Fin m → ℝ) :=
  {p | 0 ≤ p ∧ C *ᵥ p ≤ d ∧ phiDiv φ p q ≤ (ρ : EReal)}

/-- The probability-vector uncertainty region of Corollary 1 (Ben-Tal et al. 2013, p. 347):
`U = {p ∈ ℝᵐ | p ≥ 0, eᵀp = 1, I_φ(p, q) ≤ ρ}`. -/
def probUncertaintySet {m : ℕ} (φ : ℝ → EReal) (q : Fin m → ℝ) (ρ : ℝ) : Set (Fin m → ℝ) :=
  {p | 0 ≤ p ∧ ∑ i, p i = 1 ∧ phiDiv φ p q ≤ (ρ : EReal)}

end PhiDivRobust.Counterpart



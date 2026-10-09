-- Prove2me | Definitions.Def_StatComplexityDM_LinearLB_GapFamily
-- name    : StatComplexityDM_LinearLB_GapFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:16.470801+00:00
-- url     : https://prove2.me/theorems/eeb5297f-a3e2-4713-b384-86e0918944d9
-- title:
--   Proof of Proposition 6.8, p. 103 — ±1 rewards and the gap-Δ family θ₁ = Δe₁, θᵢ = Δe₁ + 2Δeᵢ on Π = {e₁, …, e_d}
-- statement:
--   This file fixes the hard family used for Proposition 6.8 (linear bandits with gaps).
--
--   1. Outcomes are $\pm 1$ and the **reward** of an outcome is the outcome itself, $r(+1) = 1$, $r(-1) = -1$, so the mean reward of $\mathrm{Rad}(\mu)$ is $\mu$.
--   2. Fix $\Delta$ and a distinguished coordinate $1 \in \{1, \dots, d\}$. The **parameters** of the family are
--   $$
--   \theta_1 = \Delta \cdot e_1, \qquad \theta_i = \Delta \cdot e_1 + 2\Delta \cdot e_i \quad (i \ne 1),
--   $$
--   written as coordinate vectors in $\mathbb{R}^d$.
--   3. The decision space is the set of standard basis vectors $\Pi = \{e_1, \dots, e_d\}$, and the **model** $M_i$ plays $M_i(e_j) = \mathrm{Rad}(\langle \theta_i, e_j \rangle)$, so $f^{M_i}(e_j) = \langle \theta_i, e_j\rangle$ is the $j$-th coordinate of $\theta_i$.
--
--   In this family $M_1$ serves as the reference model; each $M_i$ with $i \ne 1$ moves the best decision from $e_1$ to $e_i$ while keeping every gap at least $\Delta$.
--
--   **Formalization Note** The decision $e_j$ is encoded by its index $j \in \mathrm{Fin}\,d$ (0-based), and the distinguished first coordinate is a parameter $i_1$, so statements hold for whichever coordinate is called $e_1$. The Rademacher laws are those of the `Setting` file.
-- source:
--   arXiv:2112.13487v3, Proposition 6.8 (p. 44), proof of Proposition 6.8 (p. 103)

import Mathlib
import Definitions.Def_StatComplexityDM_LinearLB_Setting

namespace StatComplexityDM.LinearLB

/-- The reward of a `±1` outcome, encoded on `Bool` (`true` ↔ `+1`, `false` ↔ `−1`), so that the
mean reward of `Rad(μ)` is `μ` (`R = [−1, +1]`, Proposition 6.8, p. 44). -/
def pmRew : Bool → ℝ := fun y => if y then 1 else -1

/-- The parameters of the hard family of Proposition 6.8 (proof, p. 103), as coordinate vectors in
`ℝ^d` with a distinguished first coordinate `i₁`: `θ_{i₁} = Δ·e_{i₁}` and
`θ_i = Δ·e_{i₁} + 2Δ·e_i` for `i ≠ i₁`. -/
noncomputable def gapTheta {d : ℕ} (Δ : ℝ) (i₁ i : Fin d) : Fin d → ℝ :=
  fun j => (if j = i₁ then Δ else 0) + (if i ≠ i₁ ∧ j = i then 2 * Δ else 0)

/-- The linear bandit models of the hard family of Proposition 6.8 on the decision set
`Π = {e_1, …, e_d}` (indexed by `Fin d`, decision `j` ↔ `e_j`): `M_i(e_j) = Rad(⟨θ_i, e_j⟩)`, so
`f^{M_i}(e_j) = ⟨θ_i, e_j⟩` (proof, p. 103). -/
noncomputable def gapModel {d : ℕ} (Δ : ℝ) (i₁ i : Fin d) : Fin d → Bool → ℝ :=
  fun j => rad (gapTheta Δ i₁ i j)

end StatComplexityDM.LinearLB



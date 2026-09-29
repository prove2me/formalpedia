-- Prove2me | Definitions.Def_virial_theorem_defs
-- name    : virial_theorem_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-28T16:09:51.0433+00:00
-- url     : https://prove2.me/theorems/a9daa1f4-8f8e-4171-b08c-a6ec82c15378
-- title:
--   Virial theorem: kinetic energy, moment of inertia, virial $G$, time averages, pair forces
-- statement:
--   Basic objects for $N$ point particles in three-dimensional Euclidean space $\mathbb R^3$. Particle $k\in\{1,\dots,N\}$ has a constant mass $m_k$, a position trajectory $r_k:\mathbb R\to\mathbb R^3$ and a velocity trajectory $v_k:\mathbb R\to\mathbb R^3$.
--
--   1. **Kinetic energy.** $T(t)=\frac12\sum_{k} m_k\,\|v_k(t)\|^2$.
--   2. **Moment of inertia** about the origin. $I(t)=\sum_k m_k\,\|r_k(t)\|^2$.
--   3. **Virial scalar.** $G(t)=\sum_k p_k(t)\cdot r_k(t)$ with $p_k=m_kv_k$.
--   4. **Time average** over a duration $\tau$. $\langle f\rangle_\tau=\frac1\tau\int_0^\tau f(t)\,dt$.
--   5. **Pair force from a distance potential.** Given pair potentials $V_{jk}:\mathbb R\to\mathbb R$ and a configuration $x=(x_1,\dots,x_N)$, the force of particle $j$ on particle $k$ is
--   $$F_{jk}=-\nabla_{x_k}\,V_{jk}\big(\|x_k-x_j\|\big)\quad (j\ne k),\qquad F_{kk}=0 .$$
--   6. **Net force.** $F_k=\sum_j F_{jk}$.
--   7. **Total potential energy.** $V_{\mathrm{TOT}}=\sum_k\sum_{j<k}V_{jk}(\|x_k-x_j\|)$.
--   8. **Power-law potentials.** $V_{jk}(s)=\alpha_{jk}\,s^{n}$ with a real exponent $n$.
--
--   These are the objects in terms of which every statement of the mission is phrased.
--
--   **Formalization Note** Space is `EuclideanSpace ℝ (Fin 3)`. The time average is $\tau^{-1}\int_0^\tau$, which Lean evaluates to $0$ at $\tau=0$. The gradient is Mathlib's `gradient`, which returns $0$ where the function is not differentiable. $s^n$ is the real power `Real.rpow`. The coefficients $\alpha_{jk}$ are allowed to depend on the pair, which covers the article's single constant $\alpha$ as well as gravity, where $\alpha_{jk}=-Gm_jm_k$.
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, sections 'Statement and derivation', 'Connection with the potential energy between particles', 'Special case of power-law forces', 'Time averaging'

import Mathlib

namespace VirialTheorem

/-- Physical space: three-dimensional Euclidean space `ℝ³`. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

variable {N : ℕ}

/-- Total kinetic energy `T(t) = ½ ∑ₖ mₖ ‖vₖ(t)‖²` of `N` particles with masses `m`
and velocity trajectories `v`. -/
noncomputable def kineticEnergy (m : Fin N → ℝ) (v : Fin N → ℝ → Space) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, m k * ‖v k t‖ ^ 2

/-- Scalar moment of inertia about the origin, `I(t) = ∑ₖ mₖ ‖rₖ(t)‖²`. -/
noncomputable def momentOfInertia (m : Fin N → ℝ) (r : Fin N → ℝ → Space) (t : ℝ) : ℝ :=
  ∑ k, m k * ‖r k t‖ ^ 2

/-- The virial scalar `G(t) = ∑ₖ pₖ(t) · rₖ(t)`, where `pₖ = mₖ vₖ` is the momentum. -/
noncomputable def virialG (m : Fin N → ℝ) (r v : Fin N → ℝ → Space) (t : ℝ) : ℝ :=
  ∑ k, inner ℝ (m k • v k t) (r k t)

/-- The time average `⟨f⟩_τ = (1/τ) ∫₀^τ f(t) dt` of `f` over the duration `τ`. -/
noncomputable def timeAverage (f : ℝ → ℝ) (τ : ℝ) : ℝ :=
  τ⁻¹ * ∫ t in (0 : ℝ)..τ, f t

/-- The force `F_{jk}` exerted by particle `j` on particle `k` in the configuration
`x : Fin N → Space`, derived from pair potentials `V j k : ℝ → ℝ` depending only on the
interparticle distance: `F_{jk} = -∇_{r_k} V_{jk}(‖r_k - r_j‖)`, and `F_{kk} = 0`
(no particle acts on itself). -/
noncomputable def pairForce (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space) (j k : Fin N) :
    Space :=
  if j = k then 0 else -gradient (fun y : Space => V j k (dist y (x j))) (x k)

/-- Net force on particle `k`: `F_k = ∑ⱼ F_{jk}`. -/
noncomputable def netPairForce (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space) (k : Fin N) :
    Space :=
  ∑ j, pairForce V x j k

/-- Total potential energy `V_TOT = ∑ₖ ∑_{j<k} V_{jk}(‖r_k - r_j‖)`. -/
noncomputable def totalPotential (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space) : ℝ :=
  ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k), V j k (dist (x k) (x j))

/-- Power-law pair potentials `V_{jk}(s) = α_{jk} s^n` (real exponent `n`). -/
noncomputable def powerLawPotential (α : Fin N → Fin N → ℝ) (n : ℝ) :
    Fin N → Fin N → ℝ → ℝ :=
  fun j k s => α j k * s ^ n

end VirialTheorem



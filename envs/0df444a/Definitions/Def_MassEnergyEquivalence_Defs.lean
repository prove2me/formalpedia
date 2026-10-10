-- Prove2me | Definitions.Def_MassEnergyEquivalence_Defs
-- name    : MassEnergyEquivalence_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:10:38.750913+00:00
-- url     : https://prove2.me/theorems/b04be705-fd7f-4aa8-b91a-8fba4150c1cc
-- title:
--   Special-relativistic kinematics for mass–energy equivalence: Lorentz factor, relativistic energy, momentum and mass, rest and kinetic energy, invariant mass, boosts
-- statement:
--   Basic objects of special-relativistic kinematics with an explicit speed of light $c$, as used in the article *Mass–energy equivalence*.
--
--   Velocities and momenta are vectors in $\mathbb R^3$ with the Euclidean norm $|\cdot|$; the coordinates are indexed $1,2,3$ here ($0,1,2$ in Lean). For a speed of light $c$, a rest mass $m$ and a velocity $\mathbf v\in\mathbb R^3$:
--
--   1. **Lorentz factor** $\gamma(\mathbf v) = \dfrac{1}{\sqrt{1-|\mathbf v|^2/c^2}}$.
--   2. **Relativistic energy** $E_{\mathrm{rel}} = \gamma m c^2$.
--   3. **Relativistic momentum** $\mathbf p = \gamma m\,\mathbf v$.
--   4. **Rest energy** $E_0 = mc^2$.
--   5. **Kinetic energy** $E_k = E_{\mathrm{rel}} - mc^2 = mc^2(\gamma-1)$.
--   6. **Relativistic mass** $m_{\mathrm{rel}} = E_{\mathrm{rel}}/c^2$.
--   7. **Invariant mass** of a finite system of free particles $i\in s$ with rest masses $m_i$ and velocities $\mathbf v_i$:
--   $$M = \frac{1}{c^2}\sqrt{\Big(\sum_{i\in s} E_i\Big)^2 - c^2\Big|\sum_{i\in s}\mathbf p_i\Big|^2},$$
--   where $E_i$, $\mathbf p_i$ are the relativistic energy and momentum of particle $i$; i.e. $M$ is the total energy divided by $c^2$ in the centre-of-momentum frame.
--   8. **Lorentz boost** with speed $u$ along the first axis, $\gamma_u = 1/\sqrt{1-u^2/c^2}$, acting on an energy–momentum pair $(E,\mathbf p)$:
--   $$E' = \gamma_u\,(E - u\,p_1),\qquad \mathbf p' = \Big(\gamma_u\big(p_1 - \tfrac{uE}{c^2}\big),\ p_2,\ p_3\Big).$$
--
--   These are the objects in terms of which the article states $E=mc^2$, its extension $E_{\mathrm{rel}}^2-(pc)^2=(m_0c^2)^2$ to moving systems, the low-speed expansion, and the invariance of rest/invariant mass.
--
--   **Formalization Note** $\mathbb R^3$ is `EuclideanSpace ℝ (Fin 3)`. All quantities are total functions: when $1-|\mathbf v|^2/c^2\le 0$ (or $1-u^2/c^2\le0$) the square root returns the junk value $0$, hence $\gamma=0$; every theorem of the mission therefore assumes $c>0$ and $|\mathbf v|<c$ (resp. $|u|<c$). For $c=0$ the divisions by $c^2$ return $0$. Inside the invariant-mass square root a negative argument would give $0$; for physical data ($m_i\ge0$, $|\mathbf v_i|<c$) the argument is non-negative.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.): lead section and §The formula ($E=mc^2$, rest frame); §Mass in special relativity and §Relativistic mass (p. 2) ($m_{\mathrm{rel}}=E/c^2$, rest/invariant mass); §Composite systems (p. 3) (invariant mass, centre-of-momentum frame); §Extension for systems in motion (pp. 5–6) ($E_{\mathrm{rel}}$, $\mathbf p$); §Low-speed approximation (p. 6) (Lorentz factor $\gamma$, $E=\gamma mc^2$); §History → Mass–velocity relationship (pp. 10–11) ($E_k = m_0c^2(\gamma-1)$).

import Mathlib

namespace MassEnergyEquivalence

/-- Three-dimensional Euclidean space `ℝ³`, the space of velocities and momenta. -/
abbrev Vec3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The Lorentz factor `γ = 1 / √(1 - ‖v‖² / c²)` of a velocity `v ∈ ℝ³`, where `c` is the
speed of light.  For `‖v‖ ≥ c` the square root is the junk value `0` and so is `γ`. -/
noncomputable def lorentzFactor (c : ℝ) (v : Vec3) : ℝ :=
  1 / Real.sqrt (1 - ‖v‖ ^ 2 / c ^ 2)

/-- The relativistic energy `E_rel = γ m c²` of a body of rest mass `m` moving with
velocity `v`. -/
noncomputable def relEnergy (c m : ℝ) (v : Vec3) : ℝ :=
  lorentzFactor c v * m * c ^ 2

/-- The relativistic momentum `p = γ m v` of a body of rest mass `m` moving with velocity `v`. -/
noncomputable def relMomentum (c m : ℝ) (v : Vec3) : Vec3 :=
  (lorentzFactor c v * m) • v

/-- The rest energy `E₀ = m c²` of a body of rest mass `m`. -/
noncomputable def restEnergy (c m : ℝ) : ℝ :=
  m * c ^ 2

/-- The relativistic kinetic energy `E_k = E_rel - m c² = m c² (γ - 1)`. -/
noncomputable def kineticEnergy (c m : ℝ) (v : Vec3) : ℝ :=
  relEnergy c m v - restEnergy c m

/-- The relativistic mass `m_rel = E_rel / c²`. -/
noncomputable def relMass (c m : ℝ) (v : Vec3) : ℝ :=
  relEnergy c m v / c ^ 2

/-- The invariant mass `M` of a finite system of free particles indexed by `s`, particle `i`
having rest mass `m i` and velocity `v i`:
`M = √((Σ E_i)² - c² ‖Σ p_i‖²) / c²`. -/
noncomputable def invariantMass {ι : Type*} (s : Finset ι) (c : ℝ) (m : ι → ℝ)
    (v : ι → Vec3) : ℝ :=
  Real.sqrt ((∑ i ∈ s, relEnergy c (m i) (v i)) ^ 2
      - c ^ 2 * ‖∑ i ∈ s, relMomentum c (m i) (v i)‖ ^ 2) / c ^ 2

/-- The Lorentz factor `γ_u = 1 / √(1 - u² / c²)` of a boost with speed `u` along the
first coordinate axis. -/
noncomputable def boostFactor (c u : ℝ) : ℝ :=
  1 / Real.sqrt (1 - u ^ 2 / c ^ 2)

/-- Energy measured in a frame moving with speed `u` along the first coordinate axis:
`E' = γ_u (E - u p₁)`. -/
noncomputable def boostEnergy (c u E : ℝ) (p : Vec3) : ℝ :=
  boostFactor c u * (E - u * p 0)

/-- Momentum measured in a frame moving with speed `u` along the first coordinate axis:
`p' = (γ_u (p₁ - u E / c²), p₂, p₃)`. -/
noncomputable def boostMomentum (c u E : ℝ) (p : Vec3) : Vec3 :=
  !₂[boostFactor c u * (p 0 - u * E / c ^ 2), p 1, p 2]

end MassEnergyEquivalence



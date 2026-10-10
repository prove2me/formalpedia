-- Prove2me | Definitions.Def_EnergyMomentum_basic
-- name    : EnergyMomentum_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:10:41.359134+00:00
-- url     : https://prove2.me/theorems/32f236df-4d4b-4ff1-a8bc-d188b9b4e575
-- title:
--   Special-relativistic kinematics: Lorentz factor, energy, momentum, four-momentum, Minkowski form, invariant mass, boosts
-- statement:
--   Basic objects of special-relativistic kinematics in flat spacetime, with an explicit speed of light $c$.
--
--   Spatial vectors live in $\mathbb R^3$ with Euclidean norm $|\cdot|$ and dot product; four-vectors are pairs $P = (P^0, \mathbf P) \in \mathbb R \times \mathbb R^3$ of contravariant components. For a body of mass $m$ moving with velocity $\mathbf v$:
--
--   1. **Lorentz factor** $\gamma(\mathbf v) = \dfrac{1}{\sqrt{1 - (|\mathbf v|/c)^2}}$;
--   2. **total energy** $E = \gamma m c^2$;
--   3. **relativistic momentum** $\mathbf p = \gamma m\,\mathbf v$;
--   4. **rest energy** $E_0 = mc^2$ and **kinetic energy** $E_K = E - E_0$;
--   5. **four-momentum** $\mathbf P = (E/c, \mathbf p)$.
--
--   On four-vectors:
--
--   6. the **Minkowski inner product** of signature $(+,-,-,-)$, $\langle P, Q\rangle = P^0 Q^0 - \mathbf P \cdot \mathbf Q$;
--   7. the **invariant mass** of a four-momentum $P$, $M = \sqrt{\langle P, P\rangle}/c$, so that $\langle P,P\rangle = (Mc)^2$ when $\langle P,P\rangle\ge 0$, $c>0$;
--   8. the **Lorentz boost along the $x$-axis** with velocity $u$: $(P^0, P^x, P^y, P^z) \mapsto (\gamma_u(P^0 - \beta P^x),\ \gamma_u(P^x - \beta P^0),\ P^y,\ P^z)$, where $\beta = u/c$, $\gamma_u = 1/\sqrt{1-\beta^2}$.
--
--   These definitions are the shared model for every statement of the mission.
--
--   **Formalization Note** Spatial vectors are `EuclideanSpace ℝ (Fin 3)` with coordinates `0, 1, 2` for $x, y, z$. Division and square root are total in Lean: for $|\mathbf v| \ge c$ (or $|u|\ge c$) the Lorentz factor evaluates to $0$, and for $c = 0$ divisions by $c$ evaluate to $0$; theorems therefore assume $c>0$ and $|\mathbf v|<c$ explicitly.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer): lead section (eq. (1), $E_0 = mc^2$, $E_K$); §Heuristic approach for massive particles ($E=\gamma mc^2$, $p=\gamma mv$, $\gamma$); §Norm of the four-momentum / Special relativity (four-momentum, Minkowski metric with signature $(+,-,-,-)$, Lorentz invariance); §Many-particle systems (total mass $M$).

import Mathlib

/-!
# Energy–momentum relation: basic special-relativistic quantities

Spatial vectors (velocities, three-momenta) live in `EuclideanSpace ℝ (Fin 3)`;
coordinates `0, 1, 2` are the `x, y, z` components.
Four-vectors are pairs `(P⁰, 𝐏) : ℝ × EuclideanSpace ℝ (Fin 3)` of contravariant components.
-/

namespace EnergyMomentum

/-- Three-dimensional Euclidean space of spatial vectors. -/
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

/-- Four-vectors `(P⁰, 𝐏)` (contravariant components). -/
abbrev FourVec := ℝ × Vec3

/-- The Lorentz factor `γ = 1 / √(1 - (|v|/c)²)` of a body moving with velocity `v`
when the speed of light is `c`. (Only meaningful for `|v| < c`.) -/
noncomputable def lorentzFactor (c : ℝ) (v : Vec3) : ℝ :=
  1 / Real.sqrt (1 - (‖v‖ / c) ^ 2)

/-- Total (relativistic) energy `E = γ m c²` of a body of mass `m` moving with velocity `v`. -/
noncomputable def energy (m c : ℝ) (v : Vec3) : ℝ :=
  lorentzFactor c v * m * c ^ 2

/-- Relativistic three-momentum `𝐩 = γ m 𝐯` of a body of mass `m` moving with velocity `v`. -/
noncomputable def momentum (m c : ℝ) (v : Vec3) : Vec3 :=
  (lorentzFactor c v * m) • v

/-- Rest energy `E₀ = m c²`. -/
def restEnergy (m c : ℝ) : ℝ :=
  m * c ^ 2

/-- Relativistic kinetic energy `E_K = E - E₀`. -/
noncomputable def kineticEnergy (m c : ℝ) (v : Vec3) : ℝ :=
  energy m c v - restEnergy m c

/-- Minkowski inner product with metric signature `(+ − − −)`:
`⟨P, Q⟩ = P⁰ Q⁰ − 𝐏 · 𝐐`. -/
noncomputable def minkowskiInner (P Q : FourVec) : ℝ :=
  P.1 * Q.1 - inner ℝ P.2 Q.2

/-- Four-momentum `𝐏 = (E / c, 𝐩)` of a body of mass `m` moving with velocity `v`. -/
noncomputable def fourMomentum (m c : ℝ) (v : Vec3) : FourVec :=
  (energy m c v / c, momentum m c v)

/-- Invariant mass `M` associated with a (total) four-momentum `P`, defined through
`⟨P, P⟩ = (M c)²`, i.e. `M = √⟨P, P⟩ / c`. -/
noncomputable def invariantMass (c : ℝ) (P : FourVec) : ℝ :=
  Real.sqrt (minkowskiInner P P) / c

/-- Lorentz boost along the `x`-axis with velocity `u` (speed of light `c`), acting on
contravariant four-vector components:
`P'⁰ = γ (P⁰ − β Pˣ)`, `P'ˣ = γ (Pˣ − β P⁰)`, `P'ʸ = Pʸ`, `P'ᶻ = Pᶻ`,
where `β = u / c` and `γ = 1 / √(1 − β²)`. -/
noncomputable def boostX (c u : ℝ) (P : FourVec) : FourVec :=
  (1 / Real.sqrt (1 - (u / c) ^ 2) * (P.1 - u / c * P.2 0),
    !₂[1 / Real.sqrt (1 - (u / c) ^ 2) * (P.2 0 - u / c * P.1), P.2 1, P.2 2])

end EnergyMomentum



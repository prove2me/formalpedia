-- Prove2me | Definitions.Def_ReynoldsNumber_core
-- name    : ReynoldsNumber_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T19:00:33.444714+00:00
-- url     : https://prove2.me/theorems/457a5630-0556-4c36-94a4-045c9da06392
-- title:
--   Reynolds number $Re=\rho u L/\mu$, kinematic viscosity, hydraulic diameter, and dimension exponents
-- statement:
--   The base model for the mission. For real numbers $\rho$ (density), $u$ (flow velocity), $L$ (characteristic length) and $\mu$ (dynamic viscosity) we set the **Reynolds number** $\mathrm{Re}(\rho,u,L,\mu)=\rho u L/\mu$, the **kinematic viscosity** $\nu(\mu,\rho)=\mu/\rho$, and the **hydraulic diameter** $D_H(A,P)=4A/P$ of a duct of cross-sectional area $A$ and wetted perimeter $P$.
--
--   For dimensional analysis we record the physical dimension of the monomial $\rho^{a}u^{b}L^{c}\mu^{d}$ through its three exponents in the mass–length–time system, using $[\rho]=ML^{-3}$, $[u]=LT^{-1}$, $[L]=L$ and $[\mu]=ML^{-1}T^{-1}$:
--   $$\mathrm{dimExponents}(a,b,c,d)=\bigl(a+d,\; -3a+b+c-d,\; -b-d\bigr),$$
--   the three entries being the exponents of mass, length and time respectively. The monomial is **dimensionless** when this triple is $(0,0,0)$.
--
--   All four quantities are modelled as plain real numbers; division in Lean is total, so statements that need $\mu\neq 0$ or $P\neq0$ carry the corresponding positivity hypotheses explicitly.
-- source:
--   Wikipedia, “Reynolds number” (uploaded PDF, Reynolds_number.pdf), sections “Definition”, “Derivation”, “Alternative derivation”, “Flow in a pipe”: https://en.wikipedia.org/wiki/Reynolds_number

import Mathlib.Data.Real.Basic

namespace ReynoldsNumber

/-- The Reynolds number `Re = ρ u L / μ` of a flow of a fluid of density `rho`
and dynamic viscosity `mu`, with flow velocity `u` and characteristic length
`L`. -/
noncomputable def Re (rho u L mu : ℝ) : ℝ := rho * u * L / mu

/-- The kinematic viscosity `ν = μ / ρ`. -/
noncomputable def kinematicViscosity (mu rho : ℝ) : ℝ := mu / rho

/-- The hydraulic diameter `D_H = 4 A / P` of a duct of cross-sectional area
`A` and wetted perimeter `P`. -/
noncomputable def hydraulicDiameter (A P : ℝ) : ℝ := 4 * A / P

/-- The exponents of mass, length and time in the physical dimension of the
monomial `ρ^a u^b L^c μ^d`, read off from `[ρ] = M L⁻³`, `[u] = L T⁻¹`,
`[L] = L` and `[μ] = M L⁻¹ T⁻¹`. -/
def dimExponents (a b c d : ℝ) : ℝ × ℝ × ℝ :=
  (a + d, -3 * a + b + c - d, -b - d)

/-- The monomial `ρ^a u^b L^c μ^d` is dimensionless exactly when all three of
its dimension exponents vanish. -/
def Dimensionless (a b c d : ℝ) : Prop := dimExponents a b c d = (0, 0, 0)

end ReynoldsNumber



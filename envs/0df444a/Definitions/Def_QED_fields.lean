-- Prove2me | Definitions.Def_QED_fields
-- name    : QED_fields
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T04:06:39.189243+00:00
-- url     : https://prove2.me/theorems/a78e2b52-2134-4dea-9f1b-3350a09f9eb0
-- title:
--   QED fields: $F_{\mu\nu}$, $D_\mu$, the current $J^\mu$, the Lagrangian, and the field equations
-- statement:
--   The field content of quantum electrodynamics and the equations it satisfies, in the notation of the QED action.
--
--   A **gauge field** is a map $x\mapsto A_\mu(x)$ with values in $\mathbb{R}^4$ (the electromagnetic four-potential, with lower index), and a **spinor field** is a map $x\mapsto\psi(x)\in\mathbb{C}^4$. From the potential one forms the **field tensor** $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$, the curvature of the gauge connection, and its raised form $F^{\mu\nu}=\eta^{\mu\alpha}\eta^{\nu\beta}F_{\alpha\beta}$. For a coupling constant $e$ the **gauge covariant derivative** is $D_\mu\psi=\partial_\mu\psi+ieA_\mu\psi$, and the **Dirac current** is $J^\mu=\bar\psi\gamma^\mu\psi$, recorded as a real number through its real part.
--
--   The **QED Lagrangian density** is
--   $$\mathcal{L}=\bar\psi\,(i\gamma^\mu D_\mu-m)\,\psi-\tfrac14F_{\mu\nu}F^{\mu\nu},$$
--   and its Euler–Lagrange equations are recorded here as two conditions on a pair $(\psi,A)$: the **Dirac equation** $\sum_\mu i\gamma^\mu D_\mu\psi=m\psi$ and the **Maxwell equation** $\partial_\mu F^{\mu\nu}=eJ^\nu$. The **Lorenz gauge** condition is $\eta^{\mu\nu}\partial_\mu A_\nu=0$. Finally, a $U(1)$ **gauge transformation** with real parameter $\chi$ is recorded as the pair of operations $A_\mu\mapsto A_\mu+\partial_\mu\chi$ and $\psi\mapsto e^{-ie\chi}\psi$.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_dirac_algebra

namespace QED

/-- A gauge field (electromagnetic four-potential): `A x μ` is the covariant
component `A_μ(x)`. -/
abbrev GaugeField : Type := Spacetime → Fin 4 → ℝ

/-- A Dirac spinor field: `ψ x` is a four-component complex spinor at `x`. -/
abbrev SpinorField : Type := Spacetime → Fin 4 → ℂ

/-- The covariant components `A^ν = η^{νβ} A_β` of the four-potential. -/
noncomputable def gaugeUp (A : GaugeField) (ν : Fin 4) (x : Spacetime) : ℝ :=
  ∑ β : Fin 4, minkowski ν β * A x β

/-- The electromagnetic field tensor `F_{μν} = ∂_μ A_ν - ∂_ν A_μ`. -/
noncomputable def fieldStrength (A : GaugeField) (μ ν : Fin 4) (x : Spacetime) : ℝ :=
  partialD μ (fun y => A y ν) x - partialD ν (fun y => A y μ) x

/-- The field tensor with both indices raised, `F^{μν} = η^{μα} η^{νβ} F_{αβ}`. -/
noncomputable def fieldStrengthUp (A : GaugeField) (μ ν : Fin 4) (x : Spacetime) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, minkowski μ α * minkowski ν β * fieldStrength A α β x

/-- The gauge covariant derivative `D_μ ψ = ∂_μ ψ + i e A_μ ψ`, where `e` is the
coupling constant (the electric charge of the spinor field). -/
noncomputable def covariantD (e : ℝ) (A : GaugeField) (ψ : SpinorField) (μ : Fin 4)
    (x : Spacetime) : Fin 4 → ℂ :=
  partialD μ ψ x + ((Complex.I * (e : ℂ) * (A x μ : ℂ)) • ψ x)

/-- The Dirac current `J^μ = ψ̄ γ^μ ψ`, taken as a real number via its real part.
(Its imaginary part vanishes for any Dirac representation; see
`QED.current_isReal`.) -/
noncomputable def current (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (ψ : SpinorField)
    (μ : Fin 4) (x : Spacetime) : ℝ :=
  (diracPairing γ (γ μ) (ψ x) (ψ x)).re

/-- The QED Lagrangian density
`L = ψ̄ (i γ^μ D_μ - m) ψ - (1/4) F_{μν} F^{μν}`. -/
noncomputable def lagrangian (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) (x : Spacetime) : ℂ :=
  (∑ μ : Fin 4, Complex.I * diracPairing γ (γ μ) (ψ x) (covariantD e A ψ μ x))
    - (m : ℂ) * diracPairing γ 1 (ψ x) (ψ x)
    - (1 / 4 : ℂ) *
        ((∑ μ : Fin 4, ∑ ν : Fin 4, fieldStrength A μ ν x * fieldStrengthUp A μ ν x : ℝ) : ℂ)

/-- The Dirac equation `(i γ^μ D_μ - m) ψ = 0` in the external gauge field `A`. -/
def IsDiracSolution (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) : Prop :=
  ∀ x : Spacetime,
    ∑ μ : Fin 4, Complex.I • (γ μ).mulVec (covariantD e A ψ μ x) = (m : ℂ) • ψ x

/-- The Maxwell equation of motion `∂_μ F^{μν} = e J^ν` sourced by the Dirac
current. -/
noncomputable def IsMaxwellSolution (e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) : Prop :=
  ∀ (ν : Fin 4) (x : Spacetime),
    (∑ μ : Fin 4, partialD μ (fun y => fieldStrengthUp A μ ν y) x) = e * current γ ψ ν x

/-- The Lorenz gauge condition `∂^μ A_μ = η^{μν} ∂_μ A_ν = 0`. -/
noncomputable def LorenzGauge (A : GaugeField) : Prop :=
  ∀ x : Spacetime,
    (∑ μ : Fin 4, ∑ ν : Fin 4, minkowski μ ν * partialD μ (fun y => A y ν) x) = 0

/-- The gauge transform `A_μ ↦ A_μ + ∂_μ χ` of the four-potential by a real
scalar function `χ`. -/
noncomputable def gaugeShift (χ : Spacetime → ℝ) (A : GaugeField) : GaugeField :=
  fun x μ => A x μ + partialD μ χ x

/-- The accompanying phase rotation `ψ ↦ exp (-i e χ) ψ` of the spinor field. -/
noncomputable def gaugePhase (e : ℝ) (χ : Spacetime → ℝ) (ψ : SpinorField) : SpinorField :=
  fun x => Complex.exp (-(Complex.I * (e : ℂ) * (χ x : ℂ))) • ψ x

end QED



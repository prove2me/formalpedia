-- Prove2me | Definitions.Def_ClausiusDuhem_thermo_process
-- name    : ClausiusDuhem_thermo_process
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:28:07.105156+00:00
-- url     : https://prove2.me/theorems/93b33cf9-3ab6-4d4f-910c-71189c3f3d21
-- title:
--   Thermomechanical processes, balance laws and the Clausius–Duhem inequalities
-- statement:
--   A **thermomechanical process** on $\mathbb R^3$ is a collection of fields of time $t$ and position $x$: mass density $\rho$, specific entropy $\eta$, velocity $\mathbf v$, heat flux $\mathbf q$, energy source per unit mass $s$, absolute temperature $T$, specific internal energy $e$ and Cauchy stress $\boldsymbol\sigma$. With the operators of the field-calculus definition:
--
--   1. **Regularity**: $\rho,\eta,\mathbf v,\mathbf q,T,e$ are $C^1$ jointly in $(t,x)$ and $s$ is jointly continuous.
--   2. **Integral Clausius–Duhem inequality** on every fixed control volume, here every box $\Omega=[a,b]$ with $a_i<b_i$:
--   $$\frac{d}{dt}\int_\Omega\rho\eta\,dV\ge-\int_{\partial\Omega}\rho\eta\,\mathbf v\cdot\mathbf n\,dA-\int_{\partial\Omega}\frac{\mathbf q\cdot\mathbf n}{T}\,dA+\int_\Omega\frac{\rho s}{T}\,dV.$$
--   3. **Conservation of mass**: $\dot\rho+\rho\,\nabla\cdot\mathbf v=0$.
--   4. **Balance of energy**: $\rho\dot e-\boldsymbol\sigma:\nabla\mathbf v+\nabla\cdot\mathbf q-\rho s=0$.
--   5. **Differential (entropy) form**: $\rho\dot\eta\ge-\nabla\cdot(\mathbf q/T)+\rho s/T$.
--   6. **Internal-energy form**: $\rho(\dot e-T\dot\eta)-\boldsymbol\sigma:\nabla\mathbf v\le-\mathbf q\cdot\nabla T/T$.
--   7. **Dissipation**: $\mathcal D=\rho(T\dot\eta-\dot e)+\boldsymbol\sigma:\nabla\mathbf v-\mathbf q\cdot\nabla T/T$.
--
--   Conditions 3–6 are required at every time and every point.
--
--   **Formalization Note** The control volumes are the non-degenerate boxes; the source's general moving-boundary form (normal velocity $u_n$) is specialised to fixed control volumes, $u_n=0$, which is the case the source's derivation uses. Division by $T$ is Lean division (with $x/0=0$); every theorem of the mission that divides by $T$ in an essential way assumes $T>0$.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, sections "Clausius–Duhem inequality in terms of the specific entropy" (integral form with u_n = 0, differential form, conservation of mass), "Clausius–Duhem inequality in terms of specific internal energy" (balance of energy, internal-energy form) and "Dissipation".

import Definitions.Def_ClausiusDuhem_field_calculus

/-!
Thermomechanical processes of a continuum and the balance laws / inequalities appearing in
the Wikipedia article "Clausius–Duhem inequality" (oldid=1182390552).
-/

namespace ClausiusDuhem

/-- A thermomechanical process of a continuum body occupying `ℝ³`: every field is a function
of time `t` and of the spatial point `x`. -/
structure ThermoProcess where
  /-- mass density `ρ` -/
  rho : ℝ → Space → ℝ
  /-- specific entropy (entropy per unit mass) `η` -/
  eta : ℝ → Space → ℝ
  /-- velocity of the particles `v` -/
  vel : ℝ → Space → Fin 3 → ℝ
  /-- heat flux vector `q` -/
  heatFlux : ℝ → Space → Fin 3 → ℝ
  /-- energy source per unit mass `s` -/
  source : ℝ → Space → ℝ
  /-- absolute temperature `T` -/
  temp : ℝ → Space → ℝ
  /-- specific internal energy (internal energy per unit mass) `e` -/
  energy : ℝ → Space → ℝ
  /-- Cauchy stress tensor `σ` -/
  stress : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ

/-- A time-dependent field is `C¹` jointly in time and space. -/
def IsC1Field {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (φ : ℝ → Space → β) : Prop :=
  ContDiff ℝ 1 (fun p : ℝ × Space => φ p.1 p.2)

/-- Standing regularity of a process: `ρ, η, v, q, T, e` are continuously differentiable
jointly in `(t, x)`, and the source `s` is jointly continuous. -/
def ThermoProcess.Smooth (P : ThermoProcess) : Prop :=
  IsC1Field P.rho ∧ IsC1Field P.eta ∧ IsC1Field P.vel ∧ IsC1Field P.heatFlux ∧
    IsC1Field P.temp ∧ IsC1Field P.energy ∧
    Continuous (fun p : ℝ × Space => P.source p.1 p.2)

/-- The integral Clausius–Duhem inequality for every fixed control volume (so the normal
velocity of the boundary is `u_n = 0`), with control volumes the non-degenerate closed
rectangular boxes `Ω = [a, b]`:
`d/dt ∫_Ω ρη dV ≥ ∫_{∂Ω} ρη(0 - v·n) dA - ∫_{∂Ω} (q·n)/T dA + ∫_Ω ρs/T dV`. -/
def ThermoProcess.IntegralEntropyInequality (P : ThermoProcess) : Prop :=
  ∀ (a b : Space), (∀ i, a i < b i) → ∀ t : ℝ,
    deriv (fun τ => ∫ x in Set.Icc a b, P.rho τ x * P.eta τ x) t ≥
      -boxOutwardFlux (fun x => (P.rho t x * P.eta t x) • P.vel t x) a b
      - boxOutwardFlux (fun x => (P.temp t x)⁻¹ • P.heatFlux t x) a b
      + ∫ x in Set.Icc a b, P.rho t x * P.source t x / P.temp t x

/-- Conservation of mass: `ρ̇ + ρ ∇·v = 0` at every time and point. -/
def ThermoProcess.MassConservation (P : ThermoProcess) : Prop :=
  ∀ t x, materialDeriv P.rho P.vel t x + P.rho t x * div (P.vel t) x = 0

/-- Balance of energy: `ρ ė - σ : ∇v + ∇·q - ρ s = 0` at every time and point. -/
def ThermoProcess.EnergyBalance (P : ThermoProcess) : Prop :=
  ∀ t x, P.rho t x * materialDeriv P.energy P.vel t x
      - doubleDot (P.stress t x) (velocityGradient (P.vel t) x)
      + div (P.heatFlux t) x - P.rho t x * P.source t x = 0

/-- The Clausius–Duhem inequality in differential form (in terms of the specific entropy):
`ρ η̇ ≥ -∇·(q/T) + ρ s / T` at every time and point. -/
def ThermoProcess.EntropyInequality (P : ThermoProcess) : Prop :=
  ∀ t x, P.rho t x * materialDeriv P.eta P.vel t x ≥
    -div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) x + P.rho t x * P.source t x / P.temp t x

/-- The Clausius–Duhem inequality in terms of the specific internal energy:
`ρ (ė - T η̇) - σ : ∇v ≤ -(q · ∇T)/T` at every time and point. -/
def ThermoProcess.InternalEnergyInequality (P : ThermoProcess) : Prop :=
  ∀ t x, P.rho t x * (materialDeriv P.energy P.vel t x
        - P.temp t x * materialDeriv P.eta P.vel t x)
      - doubleDot (P.stress t x) (velocityGradient (P.vel t) x) ≤
    -(dot (P.heatFlux t x) (grad (P.temp t) x) / P.temp t x)

/-- The dissipation `𝒟 = ρ (T η̇ - ė) + σ : ∇v - (q · ∇T)/T`. -/
noncomputable def ThermoProcess.dissipation (P : ThermoProcess) (t : ℝ) (x : Space) : ℝ :=
  P.rho t x * (P.temp t x * materialDeriv P.eta P.vel t x - materialDeriv P.energy P.vel t x)
    + doubleDot (P.stress t x) (velocityGradient (P.vel t) x)
    - dot (P.heatFlux t x) (grad (P.temp t) x) / P.temp t x

end ClausiusDuhem



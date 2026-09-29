-- Prove2me | Definitions.Def_LawsonDTPlasma
-- name    : LawsonDTPlasma
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T10:53:31.181442+00:00
-- url     : https://prove2.me/theorems/d4443c91-b8be-4c5e-bdd2-1fb49c0ca94d
-- title:
--   Energy-balance model of a steady-state 50-50 D-T fusion plasma
-- statement:
--   The model layer for the Lawson criterion. A *D-T plasma* is a tuple of six strictly positive real numbers: the particle (electron) density $n$, the temperature $T$ measured in energy units (electronvolts, so that Boltzmann's constant does not appear), the Maxwellian-averaged reactivity $\langle\sigma v\rangle$, the energy $E_{\mathrm{ch}}$ of the charged fusion products, the energy confinement time $\tau_E$, and the power loss density $P_{\mathrm{loss}}$, subject to the single defining relation
--
--   $$\tau_E = \frac{W}{P_{\mathrm{loss}}}, \qquad W = 3nT,$$
--
--   where $W$ is the energy density of electrons and ions together given by the ideal gas law. The standing assumptions of the derivation are built into the model: all species share the temperature $T$, the only ions present are fuel ions, and deuterium and tritium are in the optimal 50-50 mixture, so that $n_{\mathrm{d}} = n_{\mathrm{t}} = n/2$ and the volumetric reaction rate is $f = n_{\mathrm{d}} n_{\mathrm{t}} \langle\sigma v\rangle$. The rate of heating by fusion is $f E_{\mathrm{ch}}$ — only the charged products heat the plasma — and the plasma is called *self-heating* when $f E_{\mathrm{ch}} \ge P_{\mathrm{loss}}$. A concrete inhabitant is provided so that the model is demonstrably non-vacuous.
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 — section "Extensions into nτE", the equations W = 3nT, f = n_d n_t ⟨σv⟩ = (1/4) n² ⟨σv⟩, τ_E = W / P_loss and f E_ch ≥ P_loss; after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6–10, doi:10.1088/0370-1301/70/1/303

import Mathlib

/-!
# The Lawson criterion — model layer

Formalization of the energy-balance model used in the derivation of the Lawson
criterion for a steady-state, 50-50 deuterium–tritium fusion plasma, following
the Wikipedia article *Lawson criterion*
(https://en.wikipedia.org/wiki/Lawson_criterion, revision 1367242125),
sections "Extensions into $n\tau_E$" and "Extension into the triple product".

Throughout, the temperature `T` is measured in energy units (electronvolts), so
that the article's `k_B T` is simply `T` here.
-/

namespace LawsonCriterion

/-- The energy density of the electrons and ions together of a plasma of
particle density `n` at temperature `T` (in energy units), according to the
ideal gas law: `W = 3 n T`. -/
def energyDensity (n T : ℝ) : ℝ := 3 * n * T

/-- The volume rate of fusion reactions (reactions per volume per time) of a
two-species fuel with number densities `nd`, `nt` and Maxwellian-averaged
reactivity `sigmav = ⟨σ v⟩`: `f = n_d n_t ⟨σ v⟩`. -/
def fusionRate (nd nt sigmav : ℝ) : ℝ := nd * nt * sigmav

/-- A steady-state deuterium–tritium fusion plasma, as in the derivation of the
Lawson criterion: all species share the temperature `T` (in energy units), the
only ions present are the fuel ions, and deuterium and tritium are present in
the optimal 50-50 mixture, so that the ion density equals the electron
density `n`.

The field `tauE_eq` is the definition of the energy confinement time,
`τ_E = W / P_loss`, with `W = 3 n T` the energy density and `P_loss` the power
loss density. -/
structure DTPlasma where
  /-- particle (electron) density -/
  n : ℝ
  /-- temperature, in energy units (eV) -/
  T : ℝ
  /-- the Maxwellian-averaged reactivity `⟨σ v⟩` at temperature `T` -/
  sigmav : ℝ
  /-- the energy of the charged fusion products (3.5 MeV for D-T) -/
  Ech : ℝ
  /-- the energy confinement time -/
  tauE : ℝ
  /-- the power loss density -/
  Ploss : ℝ
  n_pos : 0 < n
  T_pos : 0 < T
  sigmav_pos : 0 < sigmav
  Ech_pos : 0 < Ech
  tauE_pos : 0 < tauE
  Ploss_pos : 0 < Ploss
  tauE_eq : tauE = energyDensity n T / Ploss

/-- The volume rate of fusion reactions of a D-T plasma in the optimal 50-50
mixture, where the deuterium and tritium densities are both `n / 2`. -/
noncomputable def DTPlasma.rate (p : DTPlasma) : ℝ := fusionRate (p.n / 2) (p.n / 2) p.sigmav

/-- The volume rate of heating by fusion: the reaction rate times the energy
`E_ch` of the charged fusion products (the neutrons do not heat the plasma). -/
noncomputable def DTPlasma.fusionHeating (p : DTPlasma) : ℝ := p.rate * p.Ech

/-- Lawson's self-heating condition: the fusion heating rate exceeds the power
loss density, `f E_ch ≥ P_loss`. -/
def DTPlasma.SelfHeating (p : DTPlasma) : Prop := p.fusionHeating ≥ p.Ploss

/-- A witness that the model is inhabited (so that no statement about
`DTPlasma` is vacuous): unit density, unit temperature, unit reactivity, unit
charged-product energy and unit power loss density, whose confinement time is
then `W / P_loss = 3`. -/
noncomputable def unitDTPlasma : DTPlasma where
  n := 1
  T := 1
  sigmav := 1
  Ech := 1
  tauE := 3
  Ploss := 1
  n_pos := by norm_num
  T_pos := by norm_num
  sigmav_pos := by norm_num
  Ech_pos := by norm_num
  tauE_pos := by norm_num
  Ploss_pos := by norm_num
  tauE_eq := by unfold energyDensity; norm_num

end LawsonCriterion



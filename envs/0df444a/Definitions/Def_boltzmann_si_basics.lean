-- Prove2me | Definitions.Def_boltzmann_si_basics
-- name    : boltzmann_si_basics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T13:42:57.000762+00:00
-- url     : https://prove2.me/theorems/ba8a2146-7719-4edc-b31a-8a913285413c
-- title:
--   SI constants and statistical-mechanical quantities built on $k_B$
-- statement:
--   The shared model for the mission. Four SI constants are fixed at their exact post-2019 values as real numbers: the Boltzmann constant $k_B = 1.380649\times10^{-23}\ \mathrm{J\,K^{-1}}$, the Avogadro constant $N_A = 6.02214076\times10^{23}\ \mathrm{mol^{-1}}$, the elementary charge $q = 1.602176634\times10^{-19}\ \mathrm{C}$, and the molar gas constant defined as the product $R = k_B N_A$.
--
--   On top of these the file defines the quantities the mission reasons about. The **thermal voltage** is $V_T(T) = k_B T / q$. The **Boltzmann factor** of a state of energy $E$ at temperature $T$ is $e^{-E/(k_B T)}$; summing it over a finite index set $s$ of states with energies $E_i$ gives the **partition function** $Z = \sum_{i \in s} e^{-E_i/(k_B T)}$, and the **Boltzmann occupation probability** is $P_i = e^{-E_i/(k_B T)}/Z$.
--
--   Three entropies are defined. **Boltzmann's entropy** of a system with $W$ equiprobable microstates is $S = k_B \log W$. The **Gibbs entropy** of a distribution $p$ on a finite set is $S = -k_B \sum_i p_i \log p_i$. The **Shannon entropy**, in nats, is the same sum without the constant, $-\sum_i p_i \log p_i$.
--
--   All quantities are plain real numbers: units are carried by convention in the prose, not by the type system, and every formula is read in SI units (joules, kelvin, coulombs, volts). Logarithms are natural logarithms, so entropies are measured in nats.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, sections "Roles of the Boltzmann constant", "Role in Boltzmann factors", "Role in the statistical definition of entropy", "Thermal voltage"

import Mathlib

namespace BoltzmannConstant

/-- The Boltzmann constant `k_B`, in joules per kelvin.  Since the 2019 revision of
the SI its value is exact. -/
noncomputable def kB : ℝ := 1.380649e-23

/-- The Avogadro constant `N_A`, per mole (exact since the 2019 revision of the SI). -/
noncomputable def NA : ℝ := 6.02214076e23

/-- The molar gas constant `R = k_B N_A`, in J·K⁻¹·mol⁻¹. -/
noncomputable def R : ℝ := kB * NA

/-- The elementary charge `q`, in coulombs (exact since the 2019 revision of the SI). -/
noncomputable def elemCharge : ℝ := 1.602176634e-19

/-- The thermal voltage `V_T = k_B T / q` at absolute temperature `T`. -/
noncomputable def thermalVoltage (T : ℝ) : ℝ := kB * T / elemCharge

/-- The Boltzmann factor `exp(-E / (k_B T))` of a state of energy `E` at temperature `T`. -/
noncomputable def boltzmannWeight (T E : ℝ) : ℝ := Real.exp (-E / (kB * T))

/-- The partition function `Z = ∑ exp(-E i / (k_B T))` of a finite set of states `s`. -/
noncomputable def partitionFunction {ι : Type*} (s : Finset ι) (T : ℝ) (E : ι → ℝ) : ℝ :=
  ∑ i ∈ s, boltzmannWeight T (E i)

/-- The Boltzmann occupation probability `P i = exp(-E i / (k_B T)) / Z`. -/
noncomputable def boltzmannProb {ι : Type*} (s : Finset ι) (T : ℝ) (E : ι → ℝ) (i : ι) : ℝ :=
  boltzmannWeight T (E i) / partitionFunction s T E

/-- Boltzmann's entropy `S = k_B log W` of a system with `W` equiprobable microstates. -/
noncomputable def boltzmannEntropy (W : ℕ) : ℝ := kB * Real.log W

/-- The Gibbs entropy `S = -k_B ∑ p log p` of a distribution `p` on a finite set `s`. -/
noncomputable def gibbsEntropy {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -kB * ∑ i ∈ s, p i * Real.log (p i)

/-- The Shannon entropy `-∑ p log p` (in nats) of a distribution `p` on a finite set `s`. -/
noncomputable def shannonEntropy {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -∑ i ∈ s, p i * Real.log (p i)

end BoltzmannConstant



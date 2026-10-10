-- Prove2me | Definitions.Def_ThirdLawThermo_Defs
-- name    : ThirdLawThermo_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:25:09.23998+00:00
-- url     : https://prove2.me/theorems/dea8621c-391a-42d2-bff8-823ccb813fd4
-- title:
--   Boltzmann entropy, ground states, and the canonical (Gibbs) entropy of a finite system
-- statement:
--   Throughout, $k_B$ denotes the Boltzmann constant (a real parameter; the theorems assume $k_B>0$).
--
--   1. **Boltzmann entropy.** For a macrostate realised by $W\in\mathbb N$ microstates,
--   $$S_B(W)=k_B\ln W .$$
--
--   2. **A finite system and its ground states.** A system has a finite, nonempty set $\iota$ of microstates; microstate $i$ has energy $E_i\in\mathbb R$. The **ground-state energy** is $E_0=\min_{i\in\iota}E_i$, and the **ground states** are the microstates $G=\{i\in\iota : E_i=E_0\}$; the number $|G|\ge 1$ is the ground-state degeneracy.
--
--   3. **Canonical (Gibbs) equilibrium at temperature $T>0$.** The partition function, the Gibbs probabilities and the Gibbs entropy are
--   $$Z(T)=\sum_{i\in\iota}e^{-E_i/(k_BT)},\qquad p_i(T)=\frac{e^{-E_i/(k_BT)}}{Z(T)},\qquad S(T)=-k_B\sum_{i\in\iota}p_i(T)\ln p_i(T).$$
--
--   These are the objects in which the statistical-mechanics form of the third law is stated: the entropy of a system at zero temperature is determined by the degeneracy of its ground state.
--
--   **Formalization Note** Lean's conventions $\ln 0=0$ and $x/0=0$ make the formulas total. At $T=0$ the exponent $-E_i/(k_B\cdot 0)$ evaluates to $0$, so the value of $S(0)$ in Lean is the junk value $k_B\ln|\iota|$; every theorem of the mission therefore only uses $S(T)$ for $T>0$, through the one-sided limit $T\to0^+$. The ground-state set uses classical decidability of equality of reals.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; sections "History" (S = k_B ln Ω) and "Explanation" (ground states, absolute entropy at zero temperature).

import Mathlib

namespace ThirdLawThermo

/-- The Boltzmann entropy `S = k_B ln W` of a macrostate realised by `W` microstates, where `kB`
is the Boltzmann constant. -/
noncomputable def boltzmannEntropy (kB : ℝ) (W : ℕ) : ℝ := kB * Real.log W

variable {ι : Type*} [Fintype ι]

/-- The ground-state energy of a system with finitely many (and at least one) microstates
`i : ι` of energies `E i`: the minimum of the energies. -/
noncomputable def groundEnergy [Nonempty ι] (E : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty E

/-- The set of ground states: the microstates whose energy equals the ground-state energy. -/
noncomputable def groundStates [Nonempty ι] (E : ι → ℝ) : Finset ι :=
  open Classical in Finset.univ.filter fun i => E i = groundEnergy E

/-- The canonical partition function `Z(T) = ∑ᵢ exp (-Eᵢ / (k_B T))` at temperature `T`. -/
noncomputable def partitionFunction (kB : ℝ) (E : ι → ℝ) (T : ℝ) : ℝ :=
  ∑ i, Real.exp (-E i / (kB * T))

/-- The Gibbs (canonical) probability `pᵢ(T) = exp (-Eᵢ / (k_B T)) / Z(T)` of microstate `i`
at temperature `T`. -/
noncomputable def gibbsProb (kB : ℝ) (E : ι → ℝ) (T : ℝ) (i : ι) : ℝ :=
  Real.exp (-E i / (kB * T)) / partitionFunction kB E T

/-- The Gibbs entropy `S(T) = -k_B ∑ᵢ pᵢ(T) ln pᵢ(T)` of the canonical equilibrium state at
temperature `T`. -/
noncomputable def gibbsEntropy (kB : ℝ) (E : ι → ℝ) (T : ℝ) : ℝ :=
  -kB * ∑ i, gibbsProb kB E T i * Real.log (gibbsProb kB E T i)

end ThirdLawThermo



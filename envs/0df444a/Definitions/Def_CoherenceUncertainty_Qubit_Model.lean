-- Prove2me | Definitions.Def_CoherenceUncertainty_Qubit_Model
-- name    : CoherenceUncertainty_Qubit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:41.942264+00:00
-- url     : https://prove2.me/theorems/f01aea97-ceb0-412d-8549-a9b27443fb58
-- title:
--   §II–§III, pp. 2–10 — qubit states, measurement bases, dephasing, relative entropy of coherence, purity, maximal overlap c, and f(x)
-- statement:
--   This file fixes the objects of Yuan, Bai, Peng and Ma's quantum uncertainty relation for the relative entropy of coherence on a single qubit.
--
--   1. **Qubit state.** A $2\times 2$ complex matrix $\rho$ is a qubit state (density matrix) when it is positive semidefinite and $\operatorname{Tr}\rho = 1$.
--   2. **Measurement basis.** A measurement basis $\mathbb X = \{|x_0\rangle, |x_1\rangle\}$ of $\mathbb C^2$ is represented by the $2\times 2$ unitary matrix $U$ whose $i$-th column is $|x_i\rangle$; every orthonormal basis of $\mathbb C^2$ arises this way.
--   3. **Outcome probabilities.** Measuring $\rho$ in the basis $U$ gives outcome $i$ with probability $p_i = \langle x_i|\rho|x_i\rangle = (U^\dagger \rho U)_{ii}$ (taken as a real number).
--   4. **Dephasing.** The dephased state is
--   $$\rho_{\mathrm{diag}} = \sum_i \langle x_i|\rho|x_i\rangle\, |x_i\rangle\langle x_i| = U\,\operatorname{diag}(p_0, p_1)\,U^\dagger .$$
--   5. **Relative entropy of coherence** (Eq. (6)): $C^{\mathbb X}_{\mathrm{RE}}(\rho) = H(\rho_{\mathrm{diag}}) - H(\rho)$, where $H$ is the von Neumann entropy in bits.
--   6. **Shannon entropy** of a two-outcome distribution, $H(p) = -\sum_i p_i \log_2 p_i$ with $0\log 0 = 0$; applied to the outcome probabilities it is the outcome entropy $H(X)$.
--   7. **Purity** $P(\rho) = \operatorname{Tr}[\rho^2]$.
--   8. **Overlaps and $c$.** For bases $U$ (vectors $|x_i\rangle$) and $V$ (vectors $|z_j\rangle$), the squared overlap is $|\langle x_i|z_j\rangle|^2 = |(U^\dagger V)_{ij}|^2$, and
--   $$c = c_{\max}(\mathbb X, \mathbb Z) = \max_{i,j} |\langle x_i|z_j\rangle|^2, \qquad c_{\min}(\mathbb X, \mathbb Z) = \min_{i,j} |\langle x_i|z_j\rangle|^2,$$
--   each over all four pairs $(i,j)$.
--   9. **The function $f$** of the proof of Theorem 2: for a parameter $p$, $f(x) = H(xp + (1-x)(1-p))$, with $H(t) = -t\log_2 t - (1-t)\log_2(1-t)$ the binary entropy in bits.
--
--   These are the paper's objects from §I (p. 2, $c_{\max}$), §II (p. 5, Eq. (6)), §III (pp. 6–8, $c_{\min}$, purity) and the proof of Theorem 2 (p. 10, $f$); every theorem of the mission is stated in terms of them.
--
--   **Formalization Note.** States are `Matrix (Fin 2) (Fin 2) ℂ`; bases are elements of `Matrix.unitaryGroup (Fin 2) ℂ`. The von Neumann entropy is the published `ShadowTomography.QuantumLB.vnEntropy` (bits; it returns $0$ on a non-Hermitian matrix, a branch never reached because $\rho$ and $\rho_{\mathrm{diag}}$ are Hermitian for a state), and the binary entropy is the published `WildeQIT.binaryEntropy` (bits, `Real.logb 2`). Off $[0,1]$ the binary entropy formula returns meaningless values, so statements that vary its argument restrict it to $[0,1]$. The relative entropy of coherence is defined from the dephased matrix, as in Eq. (6), not from the closed form $H(X) - H(\rho)$, which is a milestone.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 2 (c_max), p. 5 Eq. (6), pp. 6–8 (c_min, purity P = Tr[ρ²]), p. 10 (f in the proof of Theorem 2)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy

namespace CoherenceUncertainty.Qubit

open scoped ComplexOrder

/-- A 2 × 2 complex matrix: an operator on the qubit space `ℂ²`. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- `ρ` is a qubit state (density matrix): positive semidefinite with unit trace. -/
def IsDensity (ρ : Mat2) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- A measurement basis `{|x₀⟩, |x₁⟩}` of `ℂ²`, represented by the unitary matrix whose
column `i` is the basis vector `|xᵢ⟩`. Every orthonormal basis of `ℂ²` arises this way. -/
abbrev MBasis := Matrix.unitaryGroup (Fin 2) ℂ

/-- Outcome probability `⟨xᵢ|ρ|xᵢ⟩` of measuring `ρ` in the basis `U`. -/
noncomputable def prob (U : MBasis) (ρ : Mat2) (i : Fin 2) : ℝ :=
  ((star (U : Mat2) * ρ * (U : Mat2)) i i).re

/-- `ρ_diag = Σᵢ ⟨xᵢ|ρ|xᵢ⟩ |xᵢ⟩⟨xᵢ|`: the state `ρ` after dephasing in the basis `U`
(Eq. (6)). -/
noncomputable def dephase (U : MBasis) (ρ : Mat2) : Mat2 :=
  (U : Mat2) * Matrix.diagonal (fun i => ((prob U ρ i : ℝ) : ℂ)) * star (U : Mat2)

/-- Relative entropy of coherence in the basis `U`, `C^U_RE(ρ) = H(ρ_diag) − H(ρ)`
(Eq. (6)), with `H` the von Neumann entropy in bits. -/
noncomputable def relEntCoh (U : MBasis) (ρ : Mat2) : ℝ :=
  ShadowTomography.QuantumLB.vnEntropy (dephase U ρ) - ShadowTomography.QuantumLB.vnEntropy ρ

/-- Shannon entropy in bits of a distribution `p` on two outcomes, `−Σᵢ pᵢ log₂ pᵢ`
(with `0 log 0 = 0`); `shannon (prob U ρ)` is the outcome entropy `H(X)`. -/
noncomputable def shannon (p : Fin 2 → ℝ) : ℝ := -∑ i, p i * Real.logb 2 (p i)

/-- Purity `P(ρ) = Tr[ρ²]`. -/
noncomputable def purity (ρ : Mat2) : ℝ := (ρ * ρ).trace.re

/-- Squared overlap `|⟨xᵢ|z_j⟩|²` between basis vector `i` of `U` and basis vector `j` of `V`. -/
noncomputable def overlap (U V : MBasis) (i j : Fin 2) : ℝ :=
  ‖(star (U : Mat2) * (V : Mat2)) i j‖ ^ 2

/-- `c_max(X, Z) = max_{|x⟩ ∈ X, |z⟩ ∈ Z} |⟨x|z⟩|²`, the maximum over all four pairs. -/
noncomputable def cmax (U V : MBasis) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun ij : Fin 2 × Fin 2 => overlap U V ij.1 ij.2)

/-- `c_min(X, Z) = min_{|x⟩ ∈ X, |z⟩ ∈ Z} |⟨x|z⟩|²`, the minimum over all four pairs. -/
noncomputable def cmin (U V : MBasis) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ij : Fin 2 × Fin 2 => overlap U V ij.1 ij.2)

/-- `f(x) = H(xp + (1 − x)(1 − p))` of the proof of Theorem 2 (p. 10), with `H` the binary
entropy in bits. -/
noncomputable def fp (p x : ℝ) : ℝ := WildeQIT.binaryEntropy (x * p + (1 - x) * (1 - p))

end CoherenceUncertainty.Qubit



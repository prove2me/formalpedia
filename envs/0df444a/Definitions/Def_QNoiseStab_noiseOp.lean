-- Prove2me | Definitions.Def_QNoiseStab_noiseOp
-- name    : QNoiseStab_noiseOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:05.968601+00:00
-- url     : https://prove2.me/theorems/53d44418-acd3-48f6-a8b0-56807b26c84d
-- title:
--   Restricted noise operator $T_p^A=\sum_z(1-p)^{|\mathrm{Supp}'(z)\cap A|}|\hat z\rangle\langle\hat z|$
-- statement:
--   Let $A\subseteq[n]$ and $p\in\mathbb R$. The restricted noise operator on $\mathbb C^{\mathbb Z_m^n}$ is
--
--   $$
--   T_p^A=I^{\otimes([n]\setminus A)}\otimes\bigotimes_{i\in A}\Bigl(|\hat0\rangle\langle\hat0|+(1-p)\sum_{z_i\neq0}|\hat z_i\rangle\langle\hat z_i|\Bigr)=\sum_{z\in\mathbb Z_m^n}(1-p)^{|\mathrm{Supp}'(z)\cap A|}\,|\hat z\rangle\langle\hat z| .
--   $$
--
--   With $A=[n]$ it is $T_p^{\otimes n}$. In the standard basis its entries are the transition probabilities of the noise $N_p^A$ (Proposition 3.2), which is what turns the quantum bound into a classical stability question.
--
--   **Formalization Note** Defined by the right-hand (Fourier-diagonal) form of the display, with the primitive root $e^{2\pi i/m}$; $|\mathrm{Supp}'(z)\cap A|$ is the number of $i\in A$ with $z_i\neq0$. Defined for every real $p$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, p.12 (display for T_p^A); p.11 (T_p^{⊗n})

import Mathlib
import Definitions.Def_QNoiseStab_fourierVec
import Definitions.Def_QNoiseStab_ketBra

namespace QNoiseStab

/-- The restricted noise operator `T_p^A` on the input register `ℂ^{Z_mⁿ}` (Beame–Holman–Kornerup,
*A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*,
arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, p.12, display for `T_p^A`):
`T_p^A = Σ_{z ∈ Z_mⁿ} (1 − p)^{|Supp′(z) ∩ A|} |ẑ⟩⟨ẑ|`, the right-hand form of the display (the
left-hand form is `I^{⊗([n]∖A)} ⊗ ⊗_{i∈A} (|0̂⟩⟨0̂| + (1 − p) Σ_{z_i ≠ 0} |ẑ_i⟩⟨ẑ_i|)`). With
`A = [n]` it is `T_p^{⊗n}` (p.11).

**Formalization Note** `|Supp′(z) ∩ A|` is the number of `i ∈ A` with `z_i ≠ 0`. The Fourier basis
uses the primitive root `exp(2πi/m)`. Defined for every real `p`. -/
noncomputable def noiseOp {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n)) :
    Matrix (Fin n → ZMod m) (Fin n → ZMod m) ℂ :=
  ∑ z : Fin n → ZMod m,
    (((1 - p) ^ (A.filter fun i => z i ≠ 0).card : ℝ) : ℂ) • ketBra (fourierVec z)

end QNoiseStab



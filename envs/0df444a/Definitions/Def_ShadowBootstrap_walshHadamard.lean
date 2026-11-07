-- Prove2me | Definitions.Def_ShadowBootstrap_walshHadamard
-- name    : ShadowBootstrap_walshHadamard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:55.833522+00:00
-- url     : https://prove2.me/theorems/e5488c6c-008b-4169-8a63-cec09eb5e50b
-- title:
--   Walsh–Hadamard transforms, $Z$-strings and visibilities $m_P$
-- statement:
--   For $x \in \mathbb C^d$ indexed by $\{0,1\}^n$, the **Walsh–Hadamard transform** and its inverse are (§3.5, p.10)
--   $$\mathrm{WH}(x)_j := \frac{1}{2^n}\sum_i (-1)^{i\cdot j}x_i,\qquad \mathrm{WH}^{-1}(x)_j = \sum_i (-1)^{i\cdot j}x_i,$$
--   with $i\cdot j$ taken modulo two. $Z_a := \bigotimes_j Z^{a_j}$ is the $Z$-string of $a \in \{0,1\}^n$, and the **visibility** of an operator $A$ under an ensemble $E$ is
--   $$m_A := \Pr_{V\sim E}\big[VAV^\dagger \in \pm\{I, Z\}^{\otimes n}\big],$$
--   which for a Pauli operator $P$ is the paper's $m_P$ (Eq. (4), p.9).
--
--   These are the ingredients of the fast shadow action of Lemma 6.3.
--
--   **Formalization Note** The visibility is defined for any operator, so that $m_{U^\dagger Z_aU}$ can be written without naming the Pauli label of $U^\dagger Z_a U$; signs do not matter ($m_{-P} = m_P$).
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §3.5, p.10; Eq. (4), p.9; proof of Lemma 6.3, p.24

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_prob
import Definitions.Def_ShallowShadows_ShadowNorm_InPmZ

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- The parity `i · j mod 2` of two bit strings, as the sign `(−1)^{i·j}`. -/
def paritySign {n : ℕ} (i j : Bits n) : ℂ :=
  (-1 : ℂ) ^ (∑ k, (i k).val * (j k).val)

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §3.5,
p.10: the Walsh–Hadamard transform `WH(x)_j := (1/2ⁿ) Σ_i (−1)^{i·j} x_i`. -/
noncomputable def walshHadamard {n : ℕ} (x : Bits n → ℂ) : Bits n → ℂ :=
  fun j => ((1 / (2 : ℝ) ^ n : ℝ) : ℂ) * ∑ i, paritySign i j * x i

/-- §3.5, p.10: the inverse transform `WH⁻¹(x)_j := Σ_i (−1)^{i·j} x_i`. -/
def walshHadamardInv {n : ℕ} (x : Bits n → ℂ) : Bits n → ℂ :=
  fun j => ∑ i, paritySign i j * x i

/-- `Z_a := ⊗_j Z^{a_j}` (Lemma 6.3's proof, p.24), the Pauli string `P^{(0, a)}`. -/
noncomputable def zString {n : ℕ} (a : Bits n) : Op n := pauli (0, a)

/-- Eq. (4), p.9: the visibility `m_A := Pr_{V ∼ E}[V A V† ∈ ±{I, Z}^{⊗n}]` of an operator `A`
under the ensemble `E`. For a Pauli operator `A = ±P` it is the paper's `m_P` (signs do not
matter, `m_{−P} = m_P`); Lemma 6.3 evaluates it at `A = U†Z_aU`. -/
noncomputable def vis {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) (A : Op n) : ℝ :=
  prob E fun V => InPmZ ((V : Op n) * A * star (V : Op n))

end ShadowBootstrap



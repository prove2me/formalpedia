-- Prove2me | Definitions.Def_PRUPermLayer_clifford24
-- name    : PRUPermLayer_clifford24
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:58.942707+00:00
-- url     : https://prove2.me/theorems/5f53ee94-4e0c-423d-81b5-87c6229992e4
-- title:
--   The 24 single-qubit Clifford gates modulo global phase
-- statement:
--   **Single-qubit Clifford gates** are the 24 gates, up to global phase, that map the Pauli matrices $X, Y, Z$ to Pauli matrices up to sign under conjugation. With the Hadamard gate $H$ and the phase gate $S = \mathrm{diag}(1, i)$, one representative of each class is
--   $$
--   G_a S^j, \qquad (G_0, \dots, G_5) = (I,\ X,\ H,\ HX,\ SH,\ S^3H), \quad j \in \{0,1,2,3\},
--   $$
--   listed as gate number $k = 4a + j$, $k = 0, \dots, 23$.
--
--   Conjugation $c\,Z\,c^\dagger$ by $G_aS^j$ sends $Z$ to $Z, -Z, X, -X, Y, -Y$ for $a = 0,\dots,5$, and $S^j$ sends $X$ to $X, Y, -X, -Y$. Hence the 24 gates send the pair $(Z, X)$ to the 24 ordered pairs of anticommuting signed Pauli axes: they are pairwise different modulo phase and exhaust the single-qubit Clifford group modulo phase.
--
--   **Formalization Note** A global phase on a gate multiplies the oracle by a phase and changes no acceptance probability (checked in the sanity file), so a fixed choice of representatives is harmless.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

namespace PRUPermLayer

/-- The 24 single-qubit Clifford gates modulo global phase, one representative each
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.2 (PDF p.4): "Single-qubit Clifford gates are the 24 gates, up to global phase, that
map the Pauli matrices X, Y, Z to Pauli matrices up to sign, such as the Hadamard gate H and the
phase gate S = diag(1, i)"). Gate `k = 4a + j` (`a < 6`, `j < 4`) is `G_a S^j` with
`(G_0, …, G_5) = (I, X, H, HX, SH, S³H)`.

**Formalization Note** Conjugation `c Z c†` by `G_a S^j` sends `Z` to `Z, −Z, X, −X, Y, −Y` for
`a = 0, …, 5`, and `S^j` sends `X` to `X, Y, −X, −Y`; so the 24 gates map `(Z, X)` to the 24 pairs
of anticommuting signed Pauli axes, are pairwise different modulo phase, and are all of the
single-qubit Clifford group modulo phase. A global phase on a gate multiplies the oracle by a phase
and changes no acceptance probability (checked in the sanity file). The gates `H`, `X`, `S` are
the published `QAlgorithms.hadamard`, `pauliX`, `phaseS`. -/
noncomputable def clifford24 (k : Fin 24) : Matrix.unitaryGroup Bool ℂ :=
  ⟨![1, QAlgorithms.pauliX, QAlgorithms.hadamard, QAlgorithms.hadamard * QAlgorithms.pauliX,
      QAlgorithms.phaseS * QAlgorithms.hadamard,
      QAlgorithms.phaseS ^ 3 * QAlgorithms.hadamard] ⟨k / 4, by omega⟩ *
    QAlgorithms.phaseS ^ (k % 4 : ℕ), by
    have hX : QAlgorithms.pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]; ext a b
      cases a <;> cases b <;> simp [Matrix.mul_apply, QAlgorithms.pauliX]
    have hS : QAlgorithms.phaseS ∈ Matrix.unitaryGroup Bool ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]; ext a b
      cases a <;> cases b <;> simp [Matrix.mul_apply, QAlgorithms.phaseS]
    have hH : QAlgorithms.hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      have : star QAlgorithms.hadamard = QAlgorithms.hadamard := by
        ext a b; cases a <;> cases b <;> simp [QAlgorithms.hadamard]
      rw [this]; exact QAlgorithms.hadamard_mul_self
    refine Submonoid.mul_mem _ ?_ (Submonoid.pow_mem _ hS _)
    have hk : (k : ℕ) / 4 < 6 := by omega
    generalize (⟨(k : ℕ) / 4, hk⟩ : Fin 6) = a
    fin_cases a
    · exact Submonoid.one_mem _
    · exact hX
    · exact hH
    · exact Submonoid.mul_mem _ hH hX
    · exact Submonoid.mul_mem _ hS hH
    · exact Submonoid.mul_mem _ (Submonoid.pow_mem _ hS _) hH⟩

end PRUPermLayer



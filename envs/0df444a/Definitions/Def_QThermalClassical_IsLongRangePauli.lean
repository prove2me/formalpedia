-- Prove2me | Definitions.Def_QThermalClassical_IsLongRangePauli
-- name    : QThermalClassical_IsLongRangePauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:32.04151+00:00
-- url     : https://prove2.me/theorems/bda6a3de-ea9c-4509-9844-71efd27fcb0c
-- title:
--   $(s,k)$-long-range Pauli Hamiltonian
-- statement:
--   For reals $s,k$, a Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ is **$(s,k)$-long-range** (Definition 2.3, eq. (12)) if
--   $$
--   |\mathrm{supp}(P_a)|\le k\quad\text{for all }a\in A,\qquad \max_{x}\sum_{a:\,x\in\mathrm{supp}(P_a)}|c_a|\le s .
--   $$
--   Each term acts on at most $k$ qubits and every qubit has total incident coupling (on-site strength) at most $s$; all-to-all couplings are allowed.
--
--   **Formalization Note** $H$ is its coefficient function $c$ with $c(I)=0$ (no identity term, eq. (5)), and $A=\{P:c_P\neq0\}$. Definition 2.3 takes $s,k>0$; positivity is a hypothesis of each theorem that uses the class.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11; Definition 2.3, eq. (12), p.12

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

/-- `H = Σ_P c_P P` is an `(s, k)`-long-range Pauli Hamiltonian (Definition 2.3, eq. (12)):
it is a Pauli Hamiltonian in the sense of eq. (5) (no identity term), every term with nonzero
coefficient acts on at most `k` qubits, and every qubit `x` has on-site strength
`Σ_{P : x ∈ supp P} |c_P| ≤ s`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11, and Definition 2.3,
eq. (12), p.12.

**Formalization Note.** The label set `A` is `{P : c P ≠ 0}`; a word with coefficient `0`
contributes nothing to the sum in (12). `s` and `k` are real, as in Definition 2.3; the
positivity `s, k > 0` of Definition 2.3 is stated separately in each theorem. The maximum over
`x ∈ [n]` is a `∀ x`. -/
def IsLongRangePauli {Q : Type} [Fintype Q] [DecidableEq Q] (s k : ℝ)
    (c : PauliWord Q → ℝ) : Prop :=
  c (fun _ => 0) = 0 ∧
  (∀ P : PauliWord Q, c P ≠ 0 → ((pauliSupport P).card : ℝ) ≤ k) ∧
  ∀ x : Q, ∑ P ∈ Finset.univ.filter (fun P : PauliWord Q => x ∈ pauliSupport P), |c P| ≤ s

end QThermalClassical



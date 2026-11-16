-- Prove2me | Definitions.Def_QThermalClassical_Supplement_IsLowIntersectionPauli
-- name    : QThermalClassical_Supplement_IsLowIntersectionPauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:33:53.922615+00:00
-- url     : https://prove2.me/theorems/481d42d2-11d5-4b45-88f5-441aa8e84f00
-- title:
--   $(\mathfrak d,k)$-low-intersection Pauli Hamiltonians and the dual interaction graph
-- statement:
--   For a Pauli Hamiltonian $H=\sum_P c_P P$, the **dual interaction graph** has the terms $\{P : c_P\neq0\}$ as vertices and an edge between two distinct terms whose supports intersect. The **dual degree** of a term $P$ is the number of other terms $P'\neq P$ with $\mathrm{supp}\,P\cap\mathrm{supp}\,P'\neq\emptyset$, and the dual degree of $H$ is the maximum over its terms ($0$ if $H$ has none).
--
--   For real $\mathfrak d,k>0$, $H$ is a **$(\mathfrak d,k)$-low-intersection Pauli Hamiltonian** (Definition 2.4) if it has no identity term and
--   $$
--   |c_P|\le 1,\qquad |\mathrm{supp}\,P|\le k\ \text{ for every term},\qquad \text{dual degree}\le \mathfrak d .
--   $$
--
--   This is the bounded-degree family of [BLMT24], compared with the long-range family in Theorem 1(b).
--
--   **Formalization Note** A vertex is not its own neighbour (graph degree); this is the convention under which Theorem 35's low-intersection Hamiltonian has $\mathfrak d=3L^D-2$. $\mathfrak d$ and $k$ are real; their positivity is stated in each theorem.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11; Definition 2.4, eq. (13), p.12

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical.Supplement

open Classical in
/-- The degree of the term `P` in the dual interaction graph of `H = Σ_P c_P P`: the number of
other terms `P' ≠ P` (words with `c P' ≠ 0`) whose support meets `supp P`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.4, p.12.

**Formalization Note.** The vertex itself is not counted (a graph degree), which is the
convention under which Theorem 35's low-intersection Hamiltonian has `d = 3L^D − 2`. -/
noncomputable def dualNeighborCount {Q : Type} [Fintype Q] [DecidableEq Q]
    (c : PauliWord Q → ℝ) (P : PauliWord Q) : ℕ :=
  (Finset.univ.filter fun P' : PauliWord Q =>
    P' ≠ P ∧ c P' ≠ 0 ∧ (pauliSupport P ∩ pauliSupport P').Nonempty).card

open Classical in
/-- The maximum degree of the dual interaction graph of `H = Σ_P c_P P` (vertices: the words
with `c P ≠ 0`; an edge between two distinct terms whose supports intersect); `0` when `H` has
no terms.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.4, p.12. -/
noncomputable def dualDegree {Q : Type} [Fintype Q] [DecidableEq Q]
    (c : PauliWord Q → ℝ) : ℕ :=
  (Finset.univ.filter fun P : PauliWord Q => c P ≠ 0).sup (dualNeighborCount c)

/-- `H = Σ_P c_P P` is a `(d, k)`-low-intersection Pauli Hamiltonian (Definition 2.4, eq. (13)):
it is a Pauli Hamiltonian in the sense of eq. (5) (no identity term), `|c_P| ≤ 1` for every
term, every term acts on at most `k` qubits, and the dual interaction graph has maximum degree
at most `d`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11, and Definition 2.4, eq. (13), p.12.

**Formalization Note.** The label set `A` is `{P : c P ≠ 0}`; `|c P| ≤ 1` is stated for every
word (words outside `A` have `c P = 0`). `d` and `k` are real, as in Definition 2.4; the
positivity `d, k > 0` is stated in each theorem. -/
def IsLowIntersectionPauli {Q : Type} [Fintype Q] [DecidableEq Q] (d k : ℝ)
    (c : PauliWord Q → ℝ) : Prop :=
  c (fun _ => 0) = 0 ∧
  (∀ P : PauliWord Q, |c P| ≤ 1) ∧
  (∀ P : PauliWord Q, c P ≠ 0 → ((pauliSupport P).card : ℝ) ≤ k) ∧
  ((dualDegree c : ℕ) : ℝ) ≤ d

end QThermalClassical.Supplement



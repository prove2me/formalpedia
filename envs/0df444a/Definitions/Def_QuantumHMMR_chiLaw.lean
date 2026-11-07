-- Prove2me | Definitions.Def_QuantumHMMR_chiLaw
-- name    : QuantumHMMR_chiLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:02.87221+00:00
-- url     : https://prove2.me/theorems/44b9e277-1747-407d-b4b0-4eb7eae5fd09
-- title:
--   Local Clifford distribution $\chi_n$
-- statement:
--   Arrange $n$ qubits on a ring, with edges $(i, i+1)$ for $i = 0, \dots, n-1$ taken modulo $n$. The **local Clifford distribution** $\chi_n$ chooses an edge uniformly among the $n$ edges and applies to those two qubits a gate drawn uniformly from the generating set $G$. As a law on $2^n \times 2^n$ matrices,
--   $$
--   \chi_n = \frac1n \sum_{i=0}^{n-1} \frac1{|G|} \sum_{g \in G} \delta_{\,g_{i,i+1}},
--   $$
--   where $g_{i,i+1}$ is $g$ acting on qubits $i, i+1$ and the identity elsewhere.
--
--   **Formalization Note** The edge $(i, i+1)$ is the published `edgeLift` on wires $(i, \mathrm{nextWire}\, i)$, wire $n-1$ followed by wire $0$; gate wire $0$ sits on wire $i$. Each class $g \in G$ acts through its published representative; a phase of the representative changes neither moment operators nor acceptance probabilities. Matrices carry the Borel $\sigma$-algebra of the published module. For $n = 0$ the expression is the zero measure; only large $n$ is used.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 4, p.11

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped ENNReal

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- The local Clifford distribution `χ_n` (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §4, p.11): choose an edge `(i, i + 1)` of the
ring uniformly among the `n` edges and apply a uniformly random gate from `G` to those two
qubits. As a measure on `n`-qubit matrices it is
`χ_n = n⁻¹ Σ_i |G|⁻¹ Σ_{g ∈ G} δ_{edgeLift i (rep g)}`.

**Formalization Note** Edge `i` is the ordered pair of wires `(i, nextWire i)` of the published
`edgeLift` (wire `n - 1` is followed by wire `0`); gate wire 0 sits on wire `i`. A gate `g ∈ G`
is applied through its published representative `Clifford.representative g`; a global phase of
the representative changes neither moment operators nor acceptance probabilities. The measurable
structure on matrices is the Borel one of the published module (re-activated locally). For
`n = 0` the expression is the zero measure; only large `n` is used. -/
noncomputable def chiLaw (G : Finset (Clifford.ProjectiveGroup 2)) (n : ℕ) : Measure (QMat n) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, ((G.card : ℝ≥0∞)⁻¹ •
    ∑ g ∈ G, Measure.dirac (edgeLift i (Clifford.representative g).val.val))

end QuantumHMMR



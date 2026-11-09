-- Prove2me | Definitions.Def_AgnosticTNS_CopyLearner
-- name    : AgnosticTNS_CopyLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:36.556208+00:00
-- url     : https://prove2.me/theorems/115d0d95-1722-4da8-b816-52338be970ee
-- title:
--   Quantum learner acting on copies
-- statement:
--   A **learner family** indexed by instances $i$ (each with $n_i$ qudits of dimension $d_i$) specifies at each $i$ a number of copies $m_i$, a number of ancillas $a_i$, a layered quantum circuit over the Clifford+T gate set $\{H,S,T,X,\mathrm{CNOT}\}$ on the $m_i$ copies of the input (each encoded on $n_i\lceil\log_2 d_i\rceil$ qubits) followed by $a_i$ ancillas in $|0\rangle$, and a list of output wires. All wires are measured in the computational basis at the end and the output wires give the output string. The learner may measure many copies jointly (p.3).
--
--   **Formalization Note** Clifford+T is a fixed finite universal gate set; adaptive measurements and classical post-processing are part of the circuit (they can be deferred and made reversible).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 1.1, p.3; Theorem 3.6, p.23; Lemma 3.9 and Proposition 3.10, p.26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

namespace AgnosticTNS

/-- **A family of quantum learners acting on copies**, the learner model of Theorem 1.1, Theorem 3.6,
Proposition 3.10, Lemma 3.9 and Corollaries 3.7, 5.1, 5.2 (pp.3, 23, 26, 24, 39–40) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
"The learner has access to independent copies and may measure several copies jointly" (p.3);
quantum running time counts gates and classical running time the post-processing (p.26).

At index `i` the instance has `nOf i` qudits of dimension `dOf i`. The learner is one layered
circuit over the published Clifford+T instruction set on `copies i` copies of the encoded state
(`nOf i · ⌈log₂ dOf i⌉` qubits each, Eq. (3.68)) followed by `anc i` ancillas in `|0⟩`; all wires are
measured in the computational basis at the end and the bits on `out i` (in order) are the output.

**Formalization Note** Clifford+T is a fixed finite universal gate set ("The learning stage can also be
implemented over a fixed finite universal gate set", p.26); adaptivity and classical processing are
part of the circuit (they can be deferred to the end and made reversible). -/
structure CopyLearner (ι : Type) (nOf dOf : ι → ℕ) where
  /-- the number of copies of the input used at index `i` -/
  copies : ι → ℕ
  /-- the number of ancilla qubits at index `i` -/
  anc : ι → ℕ
  /-- the circuit at index `i` -/
  circ : (i : ι) → QAlgorithms.Complexity.Layered (copies i * (nOf i * Nat.clog 2 (dOf i)) + anc i)
  /-- the output wires at index `i`, in order -/
  out : (i : ι) → List (Fin (copies i * (nOf i * Nat.clog 2 (dOf i)) + anc i))

end AgnosticTNS



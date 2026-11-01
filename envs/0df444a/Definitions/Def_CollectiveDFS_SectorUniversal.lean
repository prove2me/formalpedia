-- Prove2me | Definitions.Def_CollectiveDFS_SectorUniversal
-- name    : CollectiveDFS_SectorUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:08:07.408798+00:00
-- url     : https://prove2.me/theorems/686d37c9-95d0-4156-92d6-3ab2dece3d07
-- title:
--   Induction hypothesis: $\mathfrak{su}$ on every $\mathrm{DFS}_n(J)$
-- statement:
--   Exchange acts as $\mathfrak{su}$ independently on every $\mathrm{DFS}_n(J)$ of $n$ qubits: for every legal $J$ and every legal $m$, every traceless Hermitian operator on $\mathrm{DFS}_n(J)$ at $m$ agrees there with some element of $H^n_J$. Applied at $n-1$, this is the induction hypothesis of the proof of Theorem 5 (p.26).
--
--   **Formalization Note** Only the direction "every $\mathfrak{su}$ element is reached" is included; the converse holds automatically (clause (b) of Theorem 5).
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §VII.D, p.26

import Mathlib
import Definitions.Def_CollectiveDFS_ReachesSu
import Definitions.Def_CollectiveDFS_LegalJ
import Definitions.Def_CollectiveDFS_LegalM

namespace CollectiveDFS

/-- The induction hypothesis of the proof of Theorem 5 at `n` qubits: exchange acts as `su(n_J)`
independently on every `DFS_n(J)`, for every legal `J` and every legal `m` (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.D,
p.26, PDF p.26: "We assume that it is possible to perform su(n_J) on each of the different
DFS_{n−1}(J) independently using only exchange operators").

**Formalization Note** Doubled labels. Only the direction "every su element is reached" is
included; the converse is automatic (clause (b) of `CollectiveDFS.theorem_5`). -/
def SectorUniversal (n : ℕ) : Prop :=
  ∀ j2 : ℕ, LegalJ n j2 → ∀ m2 : ℤ, LegalM j2 m2 → ReachesSu n j2 m2

end CollectiveDFS



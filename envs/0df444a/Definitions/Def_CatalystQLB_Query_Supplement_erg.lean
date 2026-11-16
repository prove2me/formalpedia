-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_erg
-- name    : CatalystQLB_Query_Supplement_erg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:58:48.255884+00:00
-- url     : https://prove2.me/theorems/55d8a135-8c58-4b83-91ff-3b878f76dcb4
-- title:
--   Ergotropy $\mathrm{erg}_{\rho,H}=\max_{U}\mathrm{tr}[H(\rho-U\rho U^\dagger)]$
-- statement:
--   For an $n$-qubit state $\rho\in\mathrm{Den}(n)$ and a Hamiltonian $H\in\mathrm{Herm}(n)$, the **ergotropy** is the largest energy that a unitary can extract:
--   $$\mathrm{erg}_{\rho,H} := \max_{U\in\mathcal U(n)}\mathrm{tr}\big[H(\rho-U\rho U^\dagger)\big].$$
--
--   **Formalization Note** The maximum is the real supremum over the unitary group; the set of values is nonempty and bounded (the group is compact), so the supremum is attained and equals the paper's maximum. The trace is taken as the real part of the complex trace, which is the trace itself for Hermitian $H$ and $\rho$. The definition is stated for a general finite basis index type; the paper's case is $\{0,1\}^n$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 13, p.19 (PDF 22)

import Mathlib

open scoped Matrix

namespace CatalystQLB.Query.Supplement

/-- The **ergotropy** `erg_{ρ,H} := max_{U ∈ U(n)} tr[H (ρ − U ρ U†)]` of a state `ρ ∈ Den(n)`
with respect to a Hamiltonian `H ∈ Herm(n)` (Arora, Chakraborty, Cojocaru, Saminathan, Singh,
*Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), Definition 13, p.19 (PDF 22)).

**Formalization Note** The maximum is the real supremum `⨆` over the unitary group of the index
type `m` (for the paper `m = QAlgorithms.Qubits n`). The set of values is nonempty and bounded
(the unitary group is compact and the map is continuous), so the supremum is attained and is the
paper's maximum; no junk value occurs. `tr[H(ρ − UρU†)]` is real for Hermitian `H` and `ρ`; Lean
takes the real part of the complex trace, which changes nothing for those inputs. -/
noncomputable def erg {m : Type} [Fintype m] [DecidableEq m] (ρ H : Matrix m m ℂ) : ℝ :=
  ⨆ U : Matrix.unitaryGroup m ℂ,
    (Matrix.trace (H * (ρ - (U : Matrix m m ℂ) * ρ * (U : Matrix m m ℂ)ᴴ))).re

end CatalystQLB.Query.Supplement



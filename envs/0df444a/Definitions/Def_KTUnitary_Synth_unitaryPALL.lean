-- Prove2me | Definitions.Def_KTUnitary_Synth_unitaryPALL
-- name    : KTUnitary_Synth_unitaryPALL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:34:48.495211+00:00
-- url     : https://prove2.me/theorems/52e7612f-fcaf-4e3e-9a0f-15a83b83eb1d
-- title:
--   The class $\mathsf{unitaryP}^{\mathsf{ALL}}$
-- statement:
--   $$\mathsf{unitaryP}^{\mathsf{ALL}}=\bigcup_{K\subseteq\{0,1\}^*}\mathsf{unitaryP}^{K},$$
--   the unitary languages that can be implemented in polynomial time relative to some classical oracle $K$ (accessed through its unitary embedding). The **unitary synthesis problem** asks whether $\mathsf{unitaryP}^{\mathsf{ALL}}=\mathsf{unitaryALL}$, the set of all unitary languages.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), p. 4; Problem 7.1, p. 34

import Mathlib
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_emb

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `unitaryP^ALL`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), p. 4 and Problem 7.1, p. 34: "the unitary synthesis
problem asks whether every unitary language can be implemented efficiently relative to some
classical oracle"; "ALL is the set of all languages"): the union of `unitaryP^K` over all languages
`K`, each accessed through its unitary embedding. The unitary synthesis problem asks whether
`unitaryP^ALL = unitaryALL` (`= Set.univ`). -/
def unitaryPALL : Set ULang := ⋃ K : Oracle, unitaryP (emb K)

end KTUnitary.Synth



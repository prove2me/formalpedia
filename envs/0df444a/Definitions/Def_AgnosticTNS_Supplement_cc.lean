-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_cc
-- name    : AgnosticTNS_Supplement_cc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:28:16.463207+00:00
-- url     : https://prove2.me/theorems/03173a22-24a3-443c-abe3-eb94ab9bff04
-- title:
--   Contraction complexity $\mathrm{cc}(G)$
-- statement:
--   The **contraction complexity** $\mathrm{cc}(G)$ is the minimum complexity over all contraction sequences of $G$; if no contraction is required (every component is a single vertex) then $\mathrm{cc}(G)=0$. It enters the bound $\mathrm{lc}_{d,\chi}(G)\le\min\{n,3\max\{1,\lceil \mathrm{cc}(G)\log_d\chi\rceil\}\}$ of Corollary 5.6 and Theorem 1.3.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 5.4, p.41

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_IsContractionSeq
import Definitions.Def_AgnosticTNS_Supplement_contrComplexity

namespace AgnosticTNS.Supplement

/-- **The contraction complexity** `cc(G)`, Definition 5.4, p.41 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
the minimum complexity over all contraction sequences of `G` (`0` if no contraction is required). -/
noncomputable def cc {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c | ∃ steps, IsContractionSeq G steps ∧ contrComplexity G steps = c}

end AgnosticTNS.Supplement



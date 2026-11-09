-- Prove2me | Definitions.Def_AgnosticTNS_OPT
-- name    : AgnosticTNS_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:42.935329+00:00
-- url     : https://prove2.me/theorems/85276a83-3f0f-4628-ab2f-82b949ad5509
-- title:
--   Optimal overlap $\mathrm{OPT}_{G,\chi}(\rho)$
-- statement:
--   For a graph $G=([n],E)$, a bond dimension bound $\chi$ and an operator $\rho$ on $(\mathbb C^d)^{\otimes n}$,
--   $$
--   \mathrm{OPT}_{G,\chi}(\rho):=\sup_{|\phi\rangle\in S_d(G,\chi)}\langle\phi|\rho|\phi\rangle .
--   $$
--   An agnostic learner must output $|\hat\psi\rangle$ with $\langle\hat\psi|\rho|\hat\psi\rangle\ge \mathrm{OPT}_{G,\chi}(\rho)-\epsilon$.
--
--   **Formalization Note** `sSup` of the set of overlaps; for a density operator, $d\ge1$ and $\chi\ge1$ the set is nonempty and bounded (proved sanity checks), so this is the supremum.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Eq. (3.1), p.15 and Eq. (1.1), p.2

import Mathlib
import Definitions.Def_AgnosticTNS_TNSchi
import Definitions.Def_AgnosticTNS_expVal

namespace AgnosticTNS

/-- **The optimal overlap `OPT_{G,χ}(ρ)`**, Eq. (3.1), p.15 (also (1.1), p.2) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`OPT_{G,χ}(ρ) := sup_{|ϕ⟩ ∈ S_d(G,χ)} ⟨ϕ|ρ|ϕ⟩`.

**Formalization Note** `sSup` of the set of overlaps. For a density operator and `χ ≥ 1, d ≥ 1`
the set is nonempty (it contains the product state `|0…0⟩`) and bounded above, so `sSup` is the
supremum (`Solutions/verification/AgnosticTNS_sanity.lean`). -/
noncomputable def OPT {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (χ : ℕ)
    (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : ℝ :=
  sSup (expVal ρ '' TNSchi d G χ)

end AgnosticTNS



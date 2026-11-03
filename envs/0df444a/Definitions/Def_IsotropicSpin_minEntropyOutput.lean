-- Prove2me | Definitions.Def_IsotropicSpin_minEntropyOutput
-- name    : IsotropicSpin_minEntropyOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:19.868475+00:00
-- url     : https://prove2.me/theorems/6aaffef1-8d65-441e-b42c-539dcb9a79aa
-- title:
--   Minimal entropy output $S[\Lambda]=\inf_\rho S(\Lambda(\rho))$
-- statement:
--   The **minimal entropy output** of a channel $\Lambda$, first form of eq. (1), is
--
--   $$
--   S[\Lambda]=\inf_{\rho} S(\Lambda(\rho)),
--   $$
--
--   the infimum over all density matrices $\rho$ of the von Neumann entropy of the output. The paper notes that it equals $\inf_{|\phi\rangle}S(\Lambda(|\phi\rangle\langle\phi|))$ over pure states by concavity of $S$; that second form is the published `WHAdditivity.Renyi.minOutputEntropy 1`.
--
--   **Formalization Note** The infimum is the real `sInf`, which is $0$ on a set that is empty or unbounded below; every theorem that uses it also concludes that the set of values is bounded below.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (1), p.1

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_densityOutputEntropies

namespace IsotropicSpin

/-- **Minimal entropy output**, first form, Alicki, arXiv:quant-ph/0402080v1, eq. (1), p. 1:
`S[Λ] = inf_ρ S(Λ(ρ))`, the infimum over all density matrices `ρ`.

The second form of (1), `inf_{|φ⟩} S(Λ(|φ⟩⟨φ|))` over unit vectors, is the published
`WHAdditivity.Renyi.minOutputEntropy 1 Λ`.

**Formalization Note** This is the real `sInf`, which is `0` on a set that is empty or unbounded
below; theorems using it also conclude `BddBelow (densityOutputEntropies Λ)`. -/
noncomputable def minEntropyOutput {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) : ℝ :=
  sInf (densityOutputEntropies Φ)

end IsotropicSpin



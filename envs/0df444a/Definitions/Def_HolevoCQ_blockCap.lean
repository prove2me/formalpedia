-- Prove2me | Definitions.Def_HolevoCQ_blockCap
-- name    : HolevoCQ_blockCap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:41.873969+00:00
-- url     : https://prove2.me/theorems/a08e72b6-123e-4271-81b9-e6574e7dde4e
-- title:
--   $C_n=\sup_{\pi,X}I_n(\pi,X)$
-- statement:
--   For the $n$-fold product channel $u\mapsto S_u$ on $\mathcal H^{\otimes n}$,
--
--   $$
--   C_n=\sup_{\pi,X}I_n(\pi,X),
--   $$
--
--   where $\pi$ ranges over all probability distributions on the words $A^n$ and $X$ over all resolutions of identity in $\mathcal H^{\otimes n}$ with an arbitrary finite output alphabet. In particular $\pi$ need not be a product law and $X$ may be an entangled measurement.
--
--   **Formalization Note** The output alphabet is `Fin m` for every `m`. The supremum is the real `sSup`; the set is nonempty (one outcome, $X=I$) and bounded above by $n\log_2|A|$, so it is the true supremum.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, p.1 (definition of $C_n$)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_HolevoCQ_shannonInfo

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, p.1: `C_n = sup_{π, X} I_n(π, X)`, the supremum over all probability
distributions `π` on the words `Aⁿ` and all resolutions of identity `X` in `H^{⊗n}` with some
finite output alphabet.

**Formalization Note.** `π` ranges over the whole simplex on `Fin n → A` (not only product
laws), and `X` over every POVM `Fin m → Matrix (Fin n → D) (Fin n → D) ℂ` for every `m : ℕ`
(including entangled measurements). The real `sSup` is the paper's supremum: the set is
nonempty (`m = 1`, `X = 1`) and bounded above by `n log₂ |A|`. -/
noncomputable def blockCap {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (n : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ π ∈ stdSimplex ℝ (Fin n → A), ∃ m : ℕ,
    ∃ X : Fin m → Matrix (Fin n → D) (Fin n → D) ℂ, IsPOVM X ∧ v = shannonInfo (wordState S n) π X}

end HolevoCQ



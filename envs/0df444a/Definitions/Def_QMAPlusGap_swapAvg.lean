-- Prove2me | Definitions.Def_QMAPlusGap_swapAvg
-- name    : QMAPlusGap_swapAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:52.401625+00:00
-- url     : https://prove2.me/theorems/48c4d7af-0fb1-4c31-b253-55c2e34745dd
-- title:
--   Averaged swap operators $T_P$, $T_Q$
-- statement:
--   For an operator $P$ on $\mathcal H$ (an orthogonal projector in Lemma A.2), on two copies of $\mathcal H^{\otimes m}$,
--   $$
--   T_P=\frac1{m^2}\sum_{i,j=1}^{m}P^{(1)}_iP^{(2)}_jF_{ij},
--   $$
--   and $T_Q$ is the same expression with $Q=I-P$ in place of $P$. Lemma A.2 bounds these operators on $\mathrm{Sym}^m(\mathcal H)\otimes\mathrm{Sym}^m(\mathcal H)$.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma A.2, p.32

import Mathlib
import Definitions.Def_QMAPlusGap_onFirst
import Definitions.Def_QMAPlusGap_swapF

set_option autoImplicit false

namespace QMAPlusGap

/-- The operators **`T_P`, `T_Q`** of Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma A.2, p.32: on two copies of `H^{⊗m}`,
`T_P = (1/m²) Σ_{i,j=1}^{m} P^{(1)}_i P^{(2)}_j F_{ij}` (and `T_Q` with `Q` in place of `P`).

**Formalization Note** `swapAvg m P` is `T_P`; `T_Q` is `swapAvg m (1 − P)`. Registers are `0`-based. -/
noncomputable def swapAvg {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (P : Matrix ι ι ℂ) :
    Matrix ((Fin m → ι) × (Fin m → ι)) ((Fin m → ι) × (Fin m → ι)) ℂ :=
  (((m : ℂ) ^ 2)⁻¹) • ∑ i : Fin m, ∑ j : Fin m, onFirst i P * onSecond j P * swapF i j

end QMAPlusGap



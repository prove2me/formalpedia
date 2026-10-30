-- Prove2me | Definitions.Def_BBPSSW_Distill_recurrenceKept
-- name    : BBPSSW_Distill_recurrenceKept
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:45:53.559+00:00
-- url     : https://prove2.me/theorems/cb17d1e8-9871-42e5-b33f-116f55f8669c
-- title:
--   Kept source pair of one recurrence step (A1–A3)
-- statement:
--   Given a state $\rho$ of two pairs (source pair first), one recurrence step does:
--
--   1. (A1) a $\sigma_y$ rotation of Alice's particle of each pair;
--   2. (A2) BXOR, then a measurement of both target spins along $z$; the source pair is kept if the two outcomes are parallel ($\uparrow\uparrow$ or $\downarrow\downarrow$), and the target pair is discarded;
--   3. (A3, first part) a $\sigma_y$ rotation of Alice's particle of the kept pair.
--
--   The result is the **unnormalized** state of the kept source pair,
--
--   $$K=(\sigma_y\otimes1)\,\mathrm{Tr}_{T}\big[(1\otimes\Pi_\parallel)\,\mathrm{BXOR}\,\Sigma\rho\Sigma^\dagger\,\mathrm{BXOR}^\dagger(1\otimes\Pi_\parallel)\big]\,(\sigma_y\otimes1)^\dagger,$$
--
--   with $\Sigma=(\sigma_y\otimes1)\otimes(\sigma_y\otimes1)$ and $\Pi_\parallel$ the projector onto $\{\uparrow\uparrow,\downarrow\downarrow\}$. Its trace is the probability that the source pair is kept; $K/\mathrm{tr}K$ is the kept state.
--
--   **Formalization Note** The final random bilateral rotation of A3 is not applied (it does not change the singlet fidelity). The paper's "unilateral" rotations are applied on Alice's side.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, pp. 2–3, steps A1–A3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BBPSSW_Distill_bxor

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)
open scoped Matrix

namespace BBPSSW.Distill

/-- **The kept source pair of one recurrence step (steps A1–A2, and the σy of A3).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, pp. 2–3:
"A1. A unilateral σy rotation is performed on each of the two pairs, converting them from
mostly-Ψ− Werner states to the analogous mostly-Φ+ states …
A2. A BXOR is performed on the two impure Φ+ states, after which the target pair is locally
measured along the z axis. If the target pair's z spins come out parallel, as they would if
both inputs were true Φ+ states, the unmeasured source pair is kept; otherwise it is discarded.
A3. If the source pair has been kept, it is converted back to a mostly-Ψ− state by a unilateral
σy rotation, then made rotationally symmetric by a random bilateral rotation".

Given a two-pair state `ρ` (index `((s₁, s₂), (s₃, s₄))`, source pair first, Alice's spins
1 and 3):
1. `σ := (σy ⊗ 1) ⊗ (σy ⊗ 1)` (σy on Alice's spin of each pair), `ρ₁ := σ ρ σ†` (A1);
2. `τ := BXOR ρ₁ BXOR†` (A2);
3. measure both target spins along z and keep the outcome "parallel" (↑↑ or ↓↓), then discard
   the target: `κ p p' := ∑_{q ∈ {↑↑, ↓↓}} τ (p, q) (p', q)`;
4. apply σy to Alice's spin of the kept pair (first part of A3): `(σy ⊗ 1) κ (σy ⊗ 1)†`.

The result is the **unnormalized** post-selected state of the source pair: its trace is the
probability that the source pair is kept, and dividing by that trace gives the kept state.

**Formalization Note.** The final random bilateral rotation of A3 is not applied; it does not
change the singlet fidelity (the singlet is invariant under bilateral rotations). The
unilateral rotations act on Alice's spin; acting on Bob's gives the same state (the paper says
"unilateral" without naming the side). -/
noncomputable def recurrenceKept (ρ : Matrix (QQ × QQ) (QQ × QQ) ℂ) : Matrix QQ QQ ℂ :=
  let sy : Matrix QQ QQ ℂ := Matrix.kronecker (pauli .y) (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let σ : Matrix (QQ × QQ) (QQ × QQ) ℂ := Matrix.kronecker sy sy
  let τ : Matrix (QQ × QQ) (QQ × QQ) ℂ := bxor * (σ * ρ * σᴴ) * bxorᴴ
  let κ : Matrix QQ QQ ℂ := Matrix.of fun p p' =>
    ∑ q : QQ, if q.1 = q.2 then τ (p, q) (p', q) else 0
  sy * κ * syᴴ

end BBPSSW.Distill



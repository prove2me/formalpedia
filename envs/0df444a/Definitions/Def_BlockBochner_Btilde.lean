-- Prove2me | Definitions.Def_BlockBochner_Btilde
-- name    : BlockBochner_Btilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:43.010709+00:00
-- url     : https://prove2.me/theorems/bb873956-c839-43af-84d2-242520f6ab47
-- title:
--   Reduced Bochner operator $\tilde B=((B^{-1})_{TT})^{-1}$
-- statement:
--   For $T\subseteq[n]$, $\tilde B=((B^{-1})_{TT})^{-1}$ on $H^T_1=\bigoplus_{i\in T}W_i$, the Schur complement of $B$ onto $H^T_1$.
--
--   **Formalization Note** Inverses are `Ring.inverse` (genuine under the hypotheses of Theorem 21). The operator is extended by zero to $H_1$: it is $\iota\circ\tilde B\circ P_{H^T_1}$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, p.23

import Mathlib
import Definitions.Def_BlockBochner_blk
import Definitions.Def_BlockBochner_bochnerOp
import Definitions.Def_BlockBochner_coordSub

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The reduced Bochner operator `B̃ = ((B⁻¹)_{TT})⁻¹` on `H^T_1 = ⊕_{i∈T} W_i`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3,
p.23: "define `B̃ : H^T_1 → H^T_1` via `B̃ = ((B^{−1})_{TT})^{−1}`".

**Formalization Note** `B⁻¹` and the outer inverse are `Ring.inverse` (genuine inverses under the
hypotheses of Theorem 21, by the coercivity of `B` and Lemma 9); `(·)_{TT}` is the compression `blk`
to `coordSub W T`. The operator is extended by zero to all of `⊕_i W_i`: it is
`ι ∘ B̃ ∘ P_{H^T_1}`, which agrees with `B̃` on `H^T_1`. -/
noncomputable def Btilde {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (J : Set (Fin n)) :
    PiLp 2 (fun i => (W i : Submodule ℝ H)) →L[ℝ] PiLp 2 (fun i => (W i : Submodule ℝ H)) :=
  (coordSub W J).subtypeL ∘L
    Ring.inverse (blk (Ring.inverse (bochnerOp W)) (coordSub W J) (coordSub W J)) ∘L
      (coordSub W J).orthogonalProjectionOnto

end BlockBochner



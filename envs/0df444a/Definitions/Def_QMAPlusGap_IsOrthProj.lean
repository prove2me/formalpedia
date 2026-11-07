-- Prove2me | Definitions.Def_QMAPlusGap_IsOrthProj
-- name    : QMAPlusGap_IsOrthProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:23.322933+00:00
-- url     : https://prove2.me/theorems/75ea1fd1-4afd-44d4-9aa8-abf95168c262
-- title:
--   Orthogonal projector
-- statement:
--   An operator $P$ on $\mathbb C^\kappa$ is an **orthogonal projector** if $P^2=P$ and $P^\dagger=P$. Lemmas A.2, A.3, 13 and 14 split one register by such a $P$ and $Q=I-P$.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma A.2, p.32; Lemma 14, p.27

import Mathlib

set_option autoImplicit false

open Matrix

namespace QMAPlusGap

/-- An **orthogonal projector** on `ℂ^κ`: `P² = P` and `P† = P` (Lemmas A.2, A.3, 13, 14 of Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), pp.27, 32,
34, 36). -/
def IsOrthProj {κ : Type} [Fintype κ] (P : Matrix κ κ ℂ) : Prop :=
  P * P = P ∧ Pᴴ = P

end QMAPlusGap



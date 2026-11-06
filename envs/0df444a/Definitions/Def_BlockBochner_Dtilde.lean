-- Prove2me | Definitions.Def_BlockBochner_Dtilde
-- name    : BlockBochner_Dtilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:08.342824+00:00
-- url     : https://prove2.me/theorems/8b32fd40-8860-4808-8d71-f07f86c94eba
-- title:
--   $\tilde D=\mathrm{blockdiag}(\tilde B_{T_1T_1},\dots,\tilde B_{T_mT_m})$
-- statement:
--   $\tilde D$ is the block-diagonal part of $\tilde B$ for the blocks $T_1,\dots,T_m$: $\tilde D=\sum_a\Pi_a\tilde B\,\Pi_a$, with $\Pi_a$ the orthogonal projection onto $\bigoplus_{i\in T_a}W_i$.
--
--   **Formalization Note** Extended by zero to $H_1$, like $\tilde B$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, p.25

import Mathlib
import Definitions.Def_BlockBochner_Btilde
import Definitions.Def_BlockBochner_blockUnion

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **`D̃ = blockdiag(B̃_{T₁T₁}, …, B̃_{T_mT_m})`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3, p.25: "we define
`D̃ = blockdiag(B̃_{T₁T₁}, …, B̃_{T_mT_m})`".

**Formalization Note** `Σ_a Π_a B̃ Π_a` with `Π_a` the orthogonal projection of `⊕_i W_i` onto
`⊕_{i∈T_a} W_i` and `B̃` extended by zero (`Btilde`). For pairwise disjoint blocks this is the
block-diagonal part of `B̃` on `H^T_1`, extended by zero. -/
noncomputable def Dtilde {n m : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (T : Fin m → Finset (Fin n)) :
    PiLp 2 (fun i => (W i : Submodule ℝ H)) →L[ℝ] PiLp 2 (fun i => (W i : Submodule ℝ H)) :=
  ∑ a, (coordSub W (T a : Set (Fin n))).starProjection ∘L
    Btilde W (blockUnion T : Set (Fin n)) ∘L (coordSub W (T a : Set (Fin n))).starProjection

end BlockBochner



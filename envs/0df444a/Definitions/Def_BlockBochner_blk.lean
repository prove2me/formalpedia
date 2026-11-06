-- Prove2me | Definitions.Def_BlockBochner_blk
-- name    : BlockBochner_blk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:44.389817+00:00
-- url     : https://prove2.me/theorems/8f0cb569-b7f4-4fed-bdd9-9656ad33080a
-- title:
--   Blocks $A_{UV}=P_UA|_V$ and compression $A_{UU}$
-- statement:
--   For a bounded operator $A$ on $H$ and subspaces $U$ (closed) and $V$, $A_{UV}=P_UA|_V:V\to U$. The compression of $A$ to $U$ is $A_{UU}=P_UA|_U$, an operator on $U$. For a coordinate subspace this is the principal submatrix.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.1, p.13; Lemma 9, p.13

import Mathlib

namespace BlockBochner

/-- **Block `A_{UV} = P_U A|_V` of an operator; compression `A_{UU}`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.1, p.13: "the
compression of `A` to `U` as `A_{UU} = P_U A|_U`", and the blocks `A_{UV}` of Lemma 9, p.13.

**Formalization Note** A bounded operator from `V` to `U`; the compression `A_{UU}` is `blk A U U`,
an operator on `U`. -/
noncomputable def blk {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (U V : Submodule ℝ E) [U.HasOrthogonalProjection] : V →L[ℝ] U :=
  U.orthogonalProjectionOnto ∘L A ∘L V.subtypeL

end BlockBochner



-- Prove2me | Definitions.Def_RandPurIso_Completion_IsCompletion
-- name    : RandPurIso_Completion_IsCompletion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:27.450576+00:00
-- url     : https://prove2.me/theorems/c72cdd5a-8749-43ed-af7d-f04ae4634477
-- title:
--   Completion $D^V$ of an isometry (Definition 5.2)
-- statement:
--   Let $1\le N<M$ and $V:\mathcal H([N])\to\mathcal H([M])$ an isometry. With $\mathcal H([N])=\mathcal H(M_0)\subseteq\mathcal H([M])$, a unitary $D^V$ on $\mathcal H([M])$ is a **completion** of $V$ if $D^V|x\rangle=V|x\rangle$ for all $x\in[N]$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 5.2, p. 29

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **Completion of an isometry** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 5.2, p. 29): with `H([N]) = H(M0) ⊆ H([M])`,
a unitary `D^V` on `H([M])` is a completion of `V : H([N]) → H([M])` if `D^V|x⟩ = V|x⟩` for all
`x ∈ [N]`, i.e. the first `N` columns of `D^V` are the columns of `V`. -/
def IsCompletion {N M : ℕ} (V : Matrix (Fin M) (Fin N) ℂ) (D : Matrix.unitaryGroup (Fin M) ℂ) : Prop :=
  ∀ (x y : Fin M) (hx : x.val < N), (D : Matrix (Fin M) (Fin M) ℂ) y x = V y ⟨x.val, hx⟩

end RandPurIso.Completion



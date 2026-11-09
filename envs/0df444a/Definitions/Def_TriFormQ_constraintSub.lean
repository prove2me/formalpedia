-- Prove2me | Definitions.Def_TriFormQ_constraintSub
-- name    : TriFormQ_constraintSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:40.492564+00:00
-- url     : https://prove2.me/theorems/de8615af-1acb-45ce-8b9f-346aa441976b
-- title:
--   Subspace cut out by a list of covectors
-- statement:
--   For a list $c_1,\dots,c_r$ of vectors of $\mathbb F^n$, viewed as covectors,
--
--   $$S(c_1,\dots,c_r)=\{y\in\mathbb F^n:\ c_i\cdot y=0\ \text{for all } i\}.$$
--
--   The iterative pivot reduction of Theorem 7 returns subspaces $S_V,S_W$ through spanning lists of their annihilators $S_V^\perp,S_W^\perp$; this definition recovers the subspaces. The codimension of $S$ is $n-\dim S$, the rank of the list.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 7 and Fig. 7, p.34 (PDF p.37)

import Definitions.Def_TriFormQ_TriForm

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 7, p.34 (PDF p.37) and
Fig. 7: the algorithm returns subspaces `S_V ≤ V`, `S_W ≤ W` through their annihilators
`S_V^⊥`, `S_W^⊥` (step (11): "return (S_V^⊥, S_W^⊥)"). Given a list `cs` of covectors, the
subspace `{y | c ⬝ᵥ y = 0 for every c ∈ cs}` they cut out.

**Formalization Note.** The kernel of the matrix whose rows are the entries of `cs`; its
codimension in `𝔽ⁿ` is `n − Module.finrank`, which is exact (the finrank is at most `n`). -/
def constraintSub {F : Type} [Field F] {n : ℕ} (cs : List (Vec F n)) : Submodule F (Vec F n) :=
  LinearMap.ker (Matrix.mulVecLin (Matrix.of fun i : Fin cs.length => cs.get i))

end TriFormQ



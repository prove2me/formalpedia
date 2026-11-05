-- Prove2me | Definitions.Def_DotySW_Deranged_ActsBy
-- name    : DotySW_Deranged_ActsBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:57.539691+00:00
-- url     : https://prove2.me/theorems/929fb4b1-a5fd-4a30-80bf-59e915e96f79
-- title:
--   $T$ is the restriction of $\sigma(x)$ to $\mathfrak{sl}_n^{\otimes r}$
-- statement:
--   An endomorphism $T$ of $\mathfrak{sl}_n^{\otimes r}$ and an element $x\in\mathcal B^{(n)}_{r,r}$ are related when $T(w)=\sigma(x)w$ for every $w\in\mathfrak{sl}_n^{\otimes r}$. The action of the deranged algebra on $\mathfrak{sl}_n^{\otimes r}$ in (19) and (20) is this restriction.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.3, Eqs. (19)–(20), p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_sigma
import Definitions.Def_DotySW_Deranged_slTensor

namespace DotySW.Deranged

/-- **`T` is the restriction of `σ(x)` to `sl_n^{⊗r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.3, Eqs. (19)–(20), p. 11.

`ActsBy n r x T` says that the endomorphism `T` of `sl_n^{⊗r}` agrees with `σ(x)` on every vector
of `sl_n^{⊗r}`.

**Formalization Note** The paper's action of `e B^{(n)}_{r,r} e` on `sl_n^{⊗r}` is this restriction. -/
def ActsBy (n r : ℕ) (x : WB n r r) (T : Module.End ℂ (slTensor n r)) : Prop :=
  ∀ w : slTensor n r, ((T w : slTensor n r) : Idx n (r + r) → ℂ) = (sigma n r r x).mulVec w

end DotySW.Deranged



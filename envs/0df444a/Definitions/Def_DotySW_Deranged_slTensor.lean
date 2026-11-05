-- Prove2me | Definitions.Def_DotySW_Deranged_slTensor
-- name    : DotySW_Deranged_slTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:07.261585+00:00
-- url     : https://prove2.me/theorems/f8a8ca2b-e9a9-41be-b41d-02e7e008bf6c
-- title:
--   The tensor power $\mathfrak{sl}_n^{\otimes r}$ inside $V^{r,r}$
-- statement:
--   The subspace of $V^{r,r}=\mathfrak{gl}_n^{\otimes r}$ spanned by the pure tensors $X_0\otimes\cdots\otimes X_{r-1}$ with every $X_a$ traceless. It is the $r$-th tensor power of the adjoint module, the module whose centralizer §4 determines.
--
--   **Formalization Note** It is defined from traceless matrices and not through $\sigma$ or $e$, so the statement that $e$ projects onto it has content. For $r=0$ it is the line $\mathbb C$.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.1, p. 10, and §4.2, p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_pureGl

namespace DotySW.Deranged

/-- **The tensor power `sl_n^{⊗r}` inside `V^{r,r} = gl_n^{⊗r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.1–§4.2, p. 10–11.

The linear span of the pure tensors `X₀ ⊗ ⋯ ⊗ X_{r-1}` of traceless matrices.

**Formalization Note** It is defined from traceless matrices, not through `σ` or `e`, so that "`e`
projects onto `sl_n^{⊗r}`" (`eIdem_projection`) has content. For `r = 0` it is the line `ℂ`. -/
def slTensor (n r : ℕ) : Submodule ℂ (Idx n (r + r) → ℂ) :=
  Submodule.span ℂ {w | ∃ X : Fin r → Matrix (Fin n) (Fin n) ℂ,
    (∀ a, (X a).trace = 0) ∧ w = pureGl n r X}

end DotySW.Deranged



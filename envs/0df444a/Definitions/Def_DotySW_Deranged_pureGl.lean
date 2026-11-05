-- Prove2me | Definitions.Def_DotySW_Deranged_pureGl
-- name    : DotySW_Deranged_pureGl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:28.890237+00:00
-- url     : https://prove2.me/theorems/88c1047d-6142-45e8-8ddf-c985e8a20d71
-- title:
--   Pure tensors of $\mathfrak{gl}_n^{\otimes r}$ in $V^{r,r}$
-- statement:
--   The natural isomorphism $V\otimes V^*\simeq\mathrm{End}(V)\simeq\mathfrak{gl}_n$ identifies $V^{r,r}$ with $\mathfrak{gl}_n^{\otimes r}$ by pairing position $i$ with position $-i$. Under it the pure tensor $X_0\otimes\cdots\otimes X_{r-1}$ has coordinate
--
--   $$
--   \prod_{a<r}(X_a)_{u(a),\,u(r+a)}
--   $$
--
--   at the basis label $u$.
--
--   **Formalization Note** $e_i\otimes e_j^*$ is the matrix unit $E_{ij}$, and position $-i$ is position $r+i$ in 0-based numbering.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, unnumbered, p. 11, with the labels of §3.1, p. 7

import Mathlib
import Definitions.Def_DotySW_Deranged_Idx

namespace DotySW.Deranged

/-- **The pure tensor `X₀ ⊗ ⋯ ⊗ X_{r-1}` of `gl_n^{⊗r}`, as a vector of `V^{r,r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, unnumbered, p. 11 ("the natural isomorphism `V ⊗ V* ≃ End(V) ≃ gl_n`"), with the
labels `i`, `-i` of §3.1, p. 7.

The coordinate at the basis label `u` is `∏ a, X a (u a) (u (r + a))`.

**Formalization Note** Slot `a` of `gl_n^{⊗r}` pairs position `a` with position `r + a` (`i` with
`-i`), and `e_i ⊗ e*_j` is the matrix unit `E_{ij}`. -/
def pureGl (n r : ℕ) (X : Fin r → Matrix (Fin n) (Fin n) ℂ) : Idx n (r + r) → ℂ :=
  fun u => ∏ a : Fin r, X a (u (Fin.castAdd r a)) (u (Fin.natAdd r a))

end DotySW.Deranged



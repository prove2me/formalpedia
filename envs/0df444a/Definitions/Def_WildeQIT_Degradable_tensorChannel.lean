-- Prove2me | Definitions.Def_WildeQIT_Degradable_tensorChannel
-- name    : WildeQIT_Degradable_tensorChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:26.963321+00:00
-- url     : https://prove2.me/theorems/f07ead6c-c352-4c4a-a0c3-b6c245ae2b67
-- title:
--   Tensor-product channel $\mathcal N\otimes\mathcal M$
-- statement:
--   For quantum channels $\mathcal N_{A_1'\to B_1}$ with Kraus operators $\{K_i\}$ and $\mathcal M_{A_2'\to B_2}$ with Kraus operators $\{L_j\}$, the **tensor-product channel** $\mathcal N\otimes\mathcal M$ acts on the joint input $A_1'A_2'$ with the Kraus operators
--
--   $$
--   K_i\otimes L_j ,\qquad (i,j)\ \text{ranging over pairs}.
--   $$
--
--   It is the channel of the additivity questions of this chapter (Theorems 13.4.1, 13.5.1, 13.6.3), whose inputs may be entangled across the two uses.
--
--   **Formalization Note** Joint systems are product index types in the Kronecker convention; the completeness relation of the product family is proved from those of the factors. The environment of the canonical isometric extension of $\mathcal N\otimes\mathcal M$ is the pair of environments $E_1E_2$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.4.1, Theorem 13.4.1, p. 407; also pp. 402, 413, 419

import Definitions.Def_WildeQIT_QChannel
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.3.1 and §13.4.1, pp. 401–408
(the tensor-product channel `N ⊗ M`, Figures 13.4–13.6).
-/

open Matrix
open scoped Kronecker

namespace WildeQIT.Degradable

/-- **Tensor-product channel `N ⊗ M`** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.4.1, p. 407,
Theorem 13.4.1; also pp. 402, 413, 419): the channel `N_{A₁′→B₁} ⊗ M_{A₂′→B₂}` acting on the
joint input `A₁′A₂′`. If `N(X) = ∑ᵢ Kᵢ X Kᵢ†` and `M(Y) = ∑ⱼ Lⱼ Y Lⱼ†`, then `N ⊗ M` has the
Kraus operators `Kᵢ ⊗ Lⱼ`, indexed by pairs `(i, j)`.

**Formalization Note.** Joint systems are product index types in the Kronecker convention of
`⊗ₖ` (`(a × c)` for `A₁′A₂′`, `(b × d)` for `B₁B₂`). The completeness relation of the product
family follows from those of the factors. The canonical environment of `N ⊗ M` is `N.ι × M.ι`,
the joint environment `E₁E₂` of the product of the canonical isometric extensions. -/
def tensorChannel {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq c] (N : QChannel a b) (M : QChannel c d) :
    QChannel (a × c) (b × d) where
  ι := N.ι × M.ι
  K ij := N.K ij.1 ⊗ₖ M.K ij.2
  complete := by
    simp_rw [conjTranspose_kronecker, ← mul_kronecker_mul]
    rw [← one_kronecker_one, ← N.complete, ← M.complete]
    ext ⟨x, w⟩ ⟨x', w'⟩
    simp only [Matrix.sum_apply, kronecker_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

end WildeQIT.Degradable



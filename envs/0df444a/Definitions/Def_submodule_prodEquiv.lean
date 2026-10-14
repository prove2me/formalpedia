-- Prove2me | Definitions.Def_submodule_prodEquiv
-- name    : submodule_prodEquiv
-- status  : Definition
-- author  : @t4v1
-- created : 2026-09-09T22:36:49.323093+00:00
-- url     : https://prove2.me/theorems/39735a4d-b701-4fec-bc27-d30255d2222e
-- title:
--   $p \times q \cong p \times q$: the product submodule as a product module
-- statement:
--   Let $R$ be a ring and let $M$, $N$ be $R$-modules. For submodules $p \subseteq M$ and $q \subseteq N$, Mathlib's `Submodule.prod` forms the submodule $p \times q \subseteq M \times N$. This file records the $R$-linear isomorphism
--
--   $$p \times q \;\cong\; p \times q,$$
--
--   between the submodule $p \times q$ of $M \times N$, regarded as a module in its own right, and the product module of $p$ and $q$. The map sends $((m,n), h)$ to $((m, h_1), (n, h_2))$, where $h = (h_1, h_2)$ witnesses $m \in p$ and $n \in q$; its inverse reassembles the pair. Every structure field, including linearity and the two inverse laws, holds by `rfl`. Two `simp` lemmas describe the map and its inverse pointwise.
--
--   Together with `Submodule.quotientProdEquiv` (the analogous statement for quotients) it lets a rank computation on a direct sum $f \oplus g$ of linear maps be split into one on $f$ and one on $g$: for instance $\ker(f \oplus g) = \ker f \times \ker g$ as modules.
-- source:
--   Drafted as a Mathlib contribution for `Mathlib/LinearAlgebra/Prod.lean`, beside `Submodule.prod`; source repository: github.com/tavi-halmaghi (MorseFloer project, `contrib/Mathlib/LinearAlgebra/Prod.lean`).

import Mathlib.LinearAlgebra.Prod

/-!
The submodule `p × q` of `M × N`, viewed as a module in its own right, is the
product module `p × q`. Every structure field is definitional.
-/

namespace Submodule

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The submodule `p × q` of `M × N`, viewed as a module, is the product of `p`
and `q`. -/
def prodEquiv (p : Submodule R M) (q : Submodule R N) : p.prod q ≃ₗ[R] p × q where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun w := ⟨(w.1.1, w.2.1), ⟨w.1.2, w.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem prodEquiv_apply (p : Submodule R M) (q : Submodule R N) (z : p.prod q) :
    prodEquiv p q z = (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩) := rfl

@[simp]
theorem prodEquiv_symm_apply (p : Submodule R M) (q : Submodule R N) (w : p × q) :
    (prodEquiv p q).symm w = ⟨(w.1.1, w.2.1), ⟨w.1.2, w.2.2⟩⟩ := rfl

end Submodule



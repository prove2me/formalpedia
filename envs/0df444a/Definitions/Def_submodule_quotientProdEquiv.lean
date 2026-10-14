-- Prove2me | Definitions.Def_submodule_quotientProdEquiv
-- name    : submodule_quotientProdEquiv
-- status  : Definition
-- author  : @t4v1
-- created : 2026-09-09T22:36:55.039267+00:00
-- url     : https://prove2.me/theorems/e6af360a-ad59-49db-b4af-922872dfd5dc
-- title:
--   $(M \times N)/(p \times q) \cong M/p \times N/q$
-- statement:
--   Let $R$ be a ring and let $M$, $N$ be $R$-modules with submodules $p \subseteq M$ and $q \subseteq N$. This file records the $R$-linear isomorphism
--
--   $$(M \times N)\,/\,(p \times q) \;\cong\; (M/p) \times (N/q).$$
--
--   In words: the cokernel of a direct sum of linear maps is the direct sum of the cokernels.
--
--   The construction is the first isomorphism theorem applied to the product $\pi_p \times \pi_q : M \times N \to M/p \times N/q$ of the two quotient maps. This map is surjective, since each factor is, and its kernel is $\ker \pi_p \times \ker \pi_q = p \times q$ by Mathlib's `LinearMap.ker_prodMap`. Rewriting the quotient along this identification of the kernel (`Submodule.quotEquivOfEq`) and composing with `LinearMap.quotKerEquivOfSurjective` gives the isomorphism. It is `noncomputable` because the first isomorphism theorem is.
-- source:
--   Drafted as a Mathlib contribution for `Mathlib/LinearAlgebra/Prod.lean`, beside `Submodule.prod`; source repository: github.com/tavi-halmaghi (MorseFloer project, `contrib/Mathlib/LinearAlgebra/Prod.lean`).

import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Isomorphisms

/-!
The quotient of `M × N` by the submodule `p × q` is the product of the two
quotients `M ⧸ p` and `N ⧸ q`: the cokernel of a direct sum of linear maps is
the direct sum of the cokernels.
-/

namespace Submodule

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The quotient of `M × N` by `p × q` is the product of the two quotients. -/
noncomputable def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) := by
  have hsurj : Function.Surjective (p.mkQ.prodMap q.mkQ) := by
    rintro ⟨a, b⟩
    obtain ⟨a', rfl⟩ := p.mkQ_surjective a
    obtain ⟨b', rfl⟩ := q.mkQ_surjective b
    exact ⟨(a', b'), rfl⟩
  refine (quotEquivOfEq _ (LinearMap.ker (p.mkQ.prodMap q.mkQ)) ?_).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)
  rw [LinearMap.ker_prodMap, ker_mkQ, ker_mkQ]

end Submodule



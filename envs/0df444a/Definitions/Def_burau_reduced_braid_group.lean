-- Prove2me | Definitions.Def_burau_reduced_braid_group
-- name    : burau_reduced_braid_group
-- status  : Definition
-- author  : @lt9
-- created : 2026-09-30T22:22:19.03005+00:00
-- url     : https://prove2.me/theorems/c0d44b9c-51bf-4cb3-b4f7-634f4d20e063
-- title:
--   The reduced braid group B_3/<Delta^4> and its two generators
-- statement:
--   **The reduced three-strand braid group $Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$ and its two
--   standard generators.**
--
--   Let $B_3=\langle \sigma_0,\sigma_1 \mid \sigma_0\sigma_1\sigma_0=\sigma_1\sigma_0\sigma_1\rangle$ be Artin's
--   braid group on three strands and $\Delta^4=(\sigma_0\sigma_1)^6$ the full twist squared, a central element
--   generating the kernel of the reduced Burau representation. The definition node provides:
--   $$ Q = B_3\big/\overline{\langle \Delta^4\rangle},\qquad
--   \mathrm{liftS} = \overline{\sigma_0^2\sigma_1},\qquad \mathrm{liftT} = \overline{\sigma_0^{-1}}, $$
--   together with the quotient map $B_3\to Q$ and the generators $\sigma_0,\sigma_1$ of $B_3$. The two images
--   $\mathrm{liftS},\mathrm{liftT}$ are the standard generators $S,T$ of $\mathrm{SL}(2,\mathbb Z)$ under the
--   classical isomorphism $Q\cong \mathrm{SL}(2,\mathbb Z)$; they satisfy the Coxeter relations
--   $\mathrm{liftS}^4=1$, $(\mathrm{liftT}\cdot\mathrm{liftS})^3=\mathrm{liftS}^2$ and
--   $(\mathrm{liftS}^{-1}\cdot\mathrm{liftT})^3=1$ that drive the Coxeter–Moser presentation used in the
--   three-strand Burau faithfulness reduction.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

namespace BurauNC

abbrev B3 := PresentedGroup (BraidsLinksMCG.braidRels 3)


def g0 : B3 := BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩


def g1 : B3 := BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩


def Delta4 : B3 := (g0 * g1) ^ 6


abbrev Q : Type := B3 ⧸ Subgroup.normalClosure ({Delta4} : Set B3)


noncomputable def q : B3 →* Q := QuotientGroup.mk' (Subgroup.normalClosure ({Delta4} : Set B3))


noncomputable def liftS : Q := q (g0 ^ 2 * g1)


noncomputable def liftT : Q := q g0⁻¹

end BurauNC



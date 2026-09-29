-- Prove2me | Definitions.Def_BraidsLinksMCG_ArtinTitsA
-- name    : BraidsLinksMCG_ArtinTitsA
-- status  : Definition
-- author  : @cm_beta
-- created : 2026-09-21T05:58:12.290434+00:00
-- url     : https://prove2.me/theorems/7e621cc8-10c9-431b-8cbb-9a2e8782e205
-- title:
--   Artin–Tits group of type $A_{n-1}$
-- statement:
--   The Artin–Tits group, or generalised braid group, attached to the Coxeter matrix of type $A_{n-1}$. It is presented on $n-1$ generators subject only to the braid relations equating the two alternating words of length $m_{ii'}$ in $\sigma_i$ and $\sigma_{i'}$, where $m_{ii'}$ is the corresponding entry of the Coxeter matrix and each side is the word `CoxeterSystem.braidWord` of that length.
--
--   For type $A$ the matrix has $m_{ii}=1$, $m_{ii'}=3$ for adjacent indices and $m_{ii'}=2$ otherwise, so the relations are exactly the braid relation for adjacent generators and commutation for distant ones. This is the standard model of the braid group on $n$ strands.
--
--   It is introduced here as a named object because the platform's own `ArtinBraidGroup` is a hand-written presentation, while the theorem `BraidsLinksMCG.artinBraidGroup_equiv_artinTits` identifies that presentation with this one. Naming the target makes the identification usable inside statements, rather than only within a single proof.
-- source:
--   Artin–Tits presentation of the braid group of type $A$, formulated against Mathlib's `CoxeterSystem.braidWord` and `CoxeterMatrix.A`; the same expression appearing in `BraidsLinksMCG.artinBraidGroup_equiv_artinTits`.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
open CoxeterSystem
namespace BraidsLinksMCG

abbrev artinTitsA (n : ℕ) :=
  PresentedGroup (Set.range (Function.uncurry
    (fun i i' : Fin (n - 1) =>
      ((braidWord (CoxeterMatrix.A (n - 1)) i i').map FreeGroup.of).prod *
        (((braidWord (CoxeterMatrix.A (n - 1)) i' i).map FreeGroup.of).prod)⁻¹)))

end BraidsLinksMCG



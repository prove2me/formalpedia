-- Prove2me | Definitions.Def_mme_dwz_step2_broken_copy
-- name    : mme_dwz_step2_broken_copy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T06:12:35.483399+00:00
-- url     : https://prove2.me/theorems/3d988a24-e3ca-4bdc-a31f-1dfce4fbf4d2
-- title:
--   The broken-copy nonhole set produced by DWZ Additional Zeroing-Out Step 2
-- statement:
--   For a finite family of retained large copies and a finite universe of small $Z$-blocks, this definition package implements the two deletion rules of DWZ Additional Zeroing-Out Step 2. A block $z$ is a nonhole of copy $j$ precisely when it is useful for $j$, compatible with $j$, and no other copy is compatible with $z$. The resulting finite set is stored in the public `BrokenBlockCopy` structure used by the Hole Lemma:
--
--   $$
--   \operatorname{nonholes}(j)=\{z:\operatorname{useful}(z,j)\;\wedge\;\operatorname{compatible}(z,j)\;\wedge\;\forall j'\,(\operatorname{compatible}(z,j')\Rightarrow j'=j)\}.
--   $$
--
--   Thus the paper's Step-2 deletion rule and its later Definition-5.5 hole count share one exact finite object.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 5.5 and Additional Zeroing-Out Step 2 in Section 6.1 (printed p. 52 / PDF p. 53). https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_hole_cover_data

open Finset

namespace MME.DWZStep2

set_option autoImplicit false

/-- A small Z-block survives Step 2 for copy `j` exactly when it is useful for `j` and `j` is its unique compatible copy. -/
def Keeps
    {Block Copy : Type*}
    (compatible useful : Block → Copy → Prop)
    (z : Block) (j : Copy) : Prop :=
  useful z j ∧ compatible z j ∧
    ∀ j', compatible z j' → j' = j

/-- Definition 5.5's broken-copy data produced by the two deletion rules of Additional Zeroing-Out Step 2. -/
noncomputable def brokenCopy
    {Block Copy : Type*}
    [Fintype Block] [DecidableEq Block]
    [Fintype Copy] [DecidableEq Copy]
    (compatible useful : Block → Copy → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (j : Copy) : MME.DWZSquare.BrokenBlockCopy Block := by
  classical
  exact ⟨Finset.univ.filter (fun z => Keeps compatible useful z j)⟩

end MME.DWZStep2



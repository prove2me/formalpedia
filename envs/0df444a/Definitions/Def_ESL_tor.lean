-- Prove2me | Definitions.Def_ESL_tor
-- name    : ESL_tor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:08:32.148005+00:00
-- url     : https://prove2.me/theorems/36817749-a878-494f-a413-a4311d2a4f50
-- title:
--   The world layer: pure braid groups of the disk and the surface with their link-homotopy quotients
-- statement:
--   The idealized world of the exact sequence for generalized string links. The definition carries: the pure braid group of the disk and the pure braid group of the surface, with their link-homotopically trivial subgroups, normal by the companion paper of the author; the two link-homotopy quotient groups with their projection maps, characterized as the quotients by the trivial subgroups and surjective; the homomorphism f_n from the disk pure braid group to the surface pure braid group, induced by the inclusion of the disk into the surface, carrying the Goldsmith disk-triviality property: a pure braid of the disk whose image is trivial on the surface is trivial on the disk; and the homomorphism theta_n from the surface pure braid group onto the abstract target group, reading off the loops traced by the strands, with the properties consumed by the exact sequence: surjectivity, killing of the trivial subgroup, and Goldberg's kernel characterization - the kernel of theta_n is the normal closure of the image of f_n.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Sections 2-3 (Lemma 2.14, Lemma 3.2, Lemma 3.3, Lemma 3.4, and Theorem 3.1).

import Mathlib
import Definitions.Def_ESL_alg

/-!
# The world layer: the idealized pure string-link groups and the maps

The world layer of the ESL mission: the idealized pure braid groups of the
disk and of the surface M with their link-homotopy quotients, and the three
structural maps of the source paper of Juliana R. T. Theodoro de Lima. The
world carries: the link-homotopically trivial subgroups H_D and H_M of the
pure braid groups of the disk and the surface, normal by Proposition 3.6
of the companion paper; the quotient groups with their projections; the
homomorphism f_n induced by the inclusion of the disk into the surface,
with the Goldsmith disk-triviality property - a pure braid of the disk whose
image is trivial on the surface is trivial on the disk; the homomorphism
theta_n to the n-fold product of the fundamental group of the surface,
surjective, killing the trivial subgroup, and with kernel the normal
closure of the image of f_n by Goldberg's theorem.
-/

namespace ESL

/-- The idealized world of the exact sequence of generalized string links:
the pure braid groups PB_D and PB_M of the disk and of the surface, their
link-homotopy quotients HhatD and HhatM, and the target group Pi of the
homomorphism theta_n, together with the quotient projections, the
Goldsmith disk-triviality property, and Goldberg's kernel characterization
as world data. -/
structure StringLinkExactWorld (n : ℕ) (PB_D PB_M HhatD HhatM Pi : Type*)
    [Group PB_D] [Group PB_M] [Group HhatD] [Group HhatM] [Group Pi] where
  HD : Subgroup PB_D
  HDnormal : HD.Normal
  HM : Subgroup PB_M
  HMnormal : HM.Normal
  qD : PB_D →* HhatD
  qDker : MonoidHom.ker qD = HD
  qDsurj : ∀ y : HhatD, ∃ x : PB_D, qD x = y
  qM : PB_M →* HhatM
  qMker : MonoidHom.ker qM = HM
  qMsurj : ∀ y : HhatM, ∃ x : PB_M, qM x = y
  f : PB_D →* PB_M
  diskTrivial : ∀ x : PB_D, f x ∈ HM → x ∈ HD
  theta : PB_M →* Pi
  thetaSurj : ∀ y : Pi, ∃ x : PB_M, theta x = y
  thetaKill : ∀ x ∈ HM, theta x = 1
  goldberg : MonoidHom.ker theta = Subgroup.normalClosure (Set.range f)

end ESL



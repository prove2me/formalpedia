-- Prove2me | Definitions.Def_PRUPermLayer_dnpSub
-- name    : PRUPermLayer_dnpSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:09.014516+00:00
-- url     : https://prove2.me/theorems/3cc04a6e-7a48-4d2a-bea9-3414a1318365
-- title:
--   Distinct non-plussed subspace $\mathrm{DNP}_{N,t}$
-- statement:
--   The **distinct non-plussed subspace** is the intersection
--   $$
--   \mathrm{DNP}_{N,t} = \mathrm{Dist}_{N,t} \cap \mathrm{NoPlus}_{N,t} .
--   $$
--   A randomizer applied before a random permutation must move every $t$-register state into it.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PRUPermLayer_distSub
import Definitions.Def_PRUPermLayer_noPlusSub

namespace PRUPermLayer

/-- The distinct non-plussed subspace `DNP_{N,t} = Dist_{N,t} ∩ NoPlus_{N,t}`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.1, p.10 (PDF p.12)). -/
noncomputable def dnpSub (N t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin t → Fin N)) :=
  distSub N t ⊓ noPlusSub N t

end PRUPermLayer



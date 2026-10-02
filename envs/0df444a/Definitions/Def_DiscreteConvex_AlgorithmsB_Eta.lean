-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_Eta
-- name    : DiscreteConvex_AlgorithmsB_Eta
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:02:57.931049+00:00
-- url     : https://prove2.me/theorems/aafda465-f45f-4253-8ccd-f585dc22b364
-- title:
--   Eta
-- statement:
--   $\eta=\max_{u\in U}[\tilde\rho(R(u))-\tilde\rho(R(u)\setminus\{u\})]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, Eq. (10.26).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, Eq. (10.26)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_RhoTilde
import Definitions.Def_DiscreteConvex_AlgorithmsB_ReachSet

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `η = max_{u∈U} [ρ̃(R(u)) - ρ̃(R(u)∖{u})]`, Eq. (10.26). -/
noncomputable def Eta {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U] (rho : Finset V → ℤ)
    (Gamma : U → Finset V) (Z : Finset V) (F : U → U → Prop) : ℤ :=
  (Finset.univ : Finset U).sup' Finset.univ_nonempty
    (fun u => RhoTilde rho Gamma Z (ReachSet F u) - RhoTilde rho Gamma Z ((ReachSet F u).erase u))

-- ===== Theorems =====

end DiscreteConvex.AlgorithmsB



-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_Eta
-- name    : DiscreteConvex_AlgorithmsC_Eta
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:35:19.25234+00:00
-- url     : https://prove2.me/theorems/faa92339-14ef-4f98-8781-0b15a4c7bf9c
-- title:
--   Eta
-- statement:
--   $\eta=\max_{u\in U}[\tilde\rho(R(u))-\tilde\rho(R(u)\setminus\{u\})]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, Eq. (10.26), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, Eq. (10.26), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_RhoTilde
import Definitions.Def_DiscreteConvex_AlgorithmsC_ReachSet

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `η = max_{u∈U} [ρ̃(R(u)) - ρ̃(R(u)∖{u})]`, Eq. (10.26). -/
noncomputable def Eta {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U] (rho : Finset V → ℤ)
    (Gamma : U → Finset V) (Z : Finset V) (F : U → U → Prop) : ℤ :=
  (Finset.univ : Finset U).sup' Finset.univ_nonempty
    (fun u => RhoTilde rho Gamma Z (ReachSet F u) - RhoTilde rho Gamma Z ((ReachSet F u).erase u))

-- ===== L-convex functions and the steepest descent algorithm (§10.3.1) =====

end DiscreteConvex.AlgorithmsC



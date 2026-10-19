-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
-- name    : OAI_Analysis_CoulombTransport_GoodTypePermutation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:21:27.963842+00:00
-- url     : https://prove2.me/theorems/b56405d0-7072-471c-8bea-c83f39f73195
-- title:
--   Local certificates on ordered component products
-- statement:
--   Work in $\mathbb{R}^3$. The three-body Coulomb cost of a triple $(x,y,z)$ is $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. Let $U_0,\dots,U_4$ be sets with potentials $v_i:U_i\to\mathbb{R}$, and $\mathrm{Contact}$ a predicate on triples. The local type certificate for the ordered type $(i,j,k)$ says that for all $x\in U_i$, $y\in U_j$, $z\in U_k$,
--   $$
--   v_i(x)+v_j(y)+v_k(z)\le c(x,y,z),
--   $$
--   and equality forces $\mathrm{Contact}(x,y,z)$.
--
--   Equality is localized to the contact set in one direction only. That is exactly what is needed to exclude deterministic optimizers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/GoodTypePermutation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/GoodTypePermutation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate

namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.GoodTypePermutation

/-- A supporting certificate on an ordered component product, with the
one-way contact localization needed for excluding deterministic optimizers. -/
def LocalTypeCertificate (U : Fin 5 → Set E3) (v : Fin 5 → E3 → ℝ)
    (Contact : Triple → Prop) (i j k : Fin 5) : Prop :=
  ∀ x ∈ U i, ∀ y ∈ U j, ∀ z ∈ U k,
    ENNReal.ofReal (v i x + v j y + v k z) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (v i x + v j y + v k z) = coulombCost (x, (y, z)) →
      Contact (x, (y, z)))

variable {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ}
  {Contact : Triple → Prop}

end Problem356.GoodTypePermutation

end

end OAI



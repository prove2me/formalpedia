-- Prove2me | Definitions.Def_HuangN13_ComparisonOrdersCore
-- name    : HuangN13_ComparisonOrdersCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:09:46.697906+00:00
-- url     : https://prove2.me/theorems/b520acc2-bd2f-4ba4-aaf1-38ec5b19cc5d
-- title:
--   Finite and infinity divisor orders and the special divisor code
-- statement:
--   The original finite branch selector, finite and infinity tensor-order counts, and the weighted point/divisor code, shared by the two sheet-balance statements and their degree-four comparison consumer.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SixLocalOrdersCore

set_option autoImplicit false

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
def tensorOrder (negative : Bool) (D E : EffectiveDivisorTwo) : ℕ :=
  divisorOrder negative D + divisorOrder negative E
end
end MazurProof.N13SpecialDivisorBranchOrders
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- The two sheets over a base point receive opposite codes. -/
def pointCode (P : N13AbelFiberTwoModel.CurvePoint) : Code :=
  let (B, z) := N13AbelFiberTwoModel.curvePointEquiv P
  if z = 0 then baseAmplitude B else -(baseAmplitude B)
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
/-- Code an unordered degree-two divisor by adding its two point codes. -/
def divisorCode : EffectiveDivisorTwo → Code :=
  Sym2.lift
    ⟨fun P Q => pointCode P + pointCode Q,
     fun P Q => by simp [add_comm]⟩
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchFaithfulness
noncomputable section
open Polynomial N13SpecialFiniteBranchJets N13SpecialInfinityBranchJets
def finiteBranch (a : K) (negative : Bool) : R →+* P :=
  if negative then branchOne a else branchZero a
end
end MazurProof.N13SpecialFiniteBranchFaithfulness
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFinitePointOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialFiniteBranchFaithfulness
open N13SpecialFiniteBranchJets
open scoped Sym2
def finiteTensorOrder (a : K) (negative : Bool) (D E : EffectiveDivisorTwo) : ℕ :=
  finiteDivisorOrder a negative D + finiteDivisorOrder a negative E
end
end MazurProof.N13SpecialFinitePointOrders
end
end



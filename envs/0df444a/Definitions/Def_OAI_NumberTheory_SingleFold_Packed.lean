-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_Packed
-- name    : OAI_NumberTheory_SingleFold_Packed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:31:33.033074+00:00
-- url     : https://prove2.me/theorems/6a8d850d-fcd8-4e9d-858d-30b6352523c3
-- title:
--   Base-$B$ digits and packed sequences
-- statement:
--   For $B,x,t,k\in\mathbb{N}$ and $f:\mathbb{N}\to\mathbb{N}$:
--
--   1. The digit of $x$ at position $t$ is $\lfloor x/B^t\rfloor\bmod B$.
--   2. The packing of the first $k$ values of $f$ is
--   $$
--   \mathrm{pack}_B(k,f)=\sum_{t<k}f(t)B^t ,
--   $$
--      and $\mathrm{ones}_B(k)=\mathrm{pack}_B(k,1)$.
--   3. Binary domination $x\preceq y$ means every binary digit of $x$ is at most that of $y$.
--
--   A whole computation history is stored as one number whose base-$B$ digits are the values at successive times.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Packed.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Packed.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

def digit (B x t : ℕ) : ℕ := x/B^t%B

def pack (B k : ℕ) (f : ℕ → ℕ) : ℕ := ∑ t∈Finset.range k, f t*B^t

def Bits (x y : ℕ) : Prop := ∀ i, x/2^i%2 ≤ y/2^i%2
def ones (B k : ℕ) : ℕ := pack B k (fun _=>1)
end SingleFold.Packed

end OAI



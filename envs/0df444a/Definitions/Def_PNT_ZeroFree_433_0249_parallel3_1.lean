-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0249_parallel3_1
-- name    : PNT_ZeroFree_433_0249_parallel3_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:53:14.97033+00:00
-- url     : https://prove2.me/theorems/dc021f51-3176-494f-97bd-c539fa2aca7b
-- title:
--   Zero-free region foundations: Eisenstein.InverseCorrespondence [0249_parallel3_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.InverseCorrespondence
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCorrespondence.lean#L115-L356

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0134
import Definitions.Def_PNT_ZeroFree_433_0136
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel2
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel3
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0244_parallel3
import Definitions.Def_PNT_ZeroFree_433_0245
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0246_parallel2
import Definitions.Def_PNT_ZeroFree_433_0247_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0267_parallel1
import Definitions.Def_PNT_ZeroFree_433_0285_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCorrespondence.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


lemma integralCoverMap_fiberPoint {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralCoverFiberPoint H K q w)=integralOrbitProjection K w := by
  rw [integralCoverFiberPoint_rep,integralCoverMap_projection,integralSubgroup_smul,
    integralOrbitProjection_eq]

lemma integralCoverTraceFunction_pairing {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (F : IntegralOrbitQuotient K→ℂ)
    (f : IntegralOrbitQuotient H→ℂ) (q : IntegralOrbitQuotient K) :
    integralCoverTraceFunction H K (fun r=>inner ℂ (F (integralCoverMap hHK r)) (f r)) q=
      inner ℂ (F q) (integralCoverTraceFunction H K f q) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,inner ℂ
      (F (integralCoverMap hHK (integralCoverFiberPoint H K r w)))
      (f (integralCoverFiberPoint H K r w)))=
      inner ℂ (F (integralOrbitProjection K w)) (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))
    simp only [integralCoverMap_fiberPoint,inner_sum]


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein


section

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


lemma diagonal_once_block_expansion (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s=
    ∑l:Fin 3,affineCuspBlock (onceCuspScale t*omega^l.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s := by
  have hsum:=(diagonalOnceCuspIndex u t).summable_iff.mpr
    (summable_summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s hs)
  have ht:Summable (fun p:OnceRamifiedData=>affineLowerTerm (onceCuspScale t*omega^p.1.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val):=
    hsum.congr (fun p=>diagonal_once_summand u t z v hv s p)
  rw [mul_assoc,diagonal_once_eisenstein_rows,ht.tsum_prod,tsum_fintype]
  rfl

lemma diagonal_once_weighted_periodic (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  rw [diagonal_once_block_expansion u t _ v hv s hs,diagonal_once_block_expansion u t _ v hv s hs,
    Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  exact affineCuspBlock_weighted_periodic h (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) (onceCuspRayIndex u t l).val 1
      (mul_ne_zero (onceCusp_scale_ne_zero t) (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero))
      (by simpa only [pow_one] using onceCuspRayIndex_spec u t l)
      (onceCusp_period_congruence t l h _ hfreq) v s m z


end


end CubicEisenstein


end

end OAI

end



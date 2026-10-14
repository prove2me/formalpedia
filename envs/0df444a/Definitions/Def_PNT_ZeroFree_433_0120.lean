-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0120
-- name    : PNT_ZeroFree_433_0120
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:03:52.893986+00:00
-- url     : https://prove2.me/theorems/80deaf5c-a8b7-4a6a-9755-475717d2966c
-- title:
--   Zero-free region foundations: CubicSieve.PrincipalNormalization [0120]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalNormalization.lean#L81-L624

import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0119
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1

/- Supporting principal normalization for the zero-free-region proof.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalNormalization.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Classical
namespace OAI.SecondPassArithmetic
open OAI.ActualEisensteinCubic
open OAI.FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalSecondRawRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (x : GlobalSecondData ι) (y : O) :
    fixedChildRow p hp hcop hg ((F\(x.cube.support∪x.common))\x.firstCommon) Ψ
      (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit *
        primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
      H (globalSecondLabel p x) y =
    fixedChildRow p hp hcop hg F Ψ (fixedTripleMask m (globalSecondFixedTriple p x))
      H (globalSecondLabel p x) y := by
  exact (fixedChildRow_fixed_pool p hp hcop hg hinj
    (F\(x.cube.support∪x.common)) x.firstCommon Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit *
      primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
    H (globalSecondLabel p x) y).trans
    ((fixedChildRow_restore_killed_pool p hp hcop hg F (x.cube.support∪x.common) Ψ
      (globalSecondMask p m x) (globalSecondLabel p x) y H
      (globalSecondMask_kills_cube_common p m x)).trans
      (fixedChildRow_congr_mask_span p hp hcop hg F Ψ
        (globalSecondMask_span p m x) H (globalSecondLabel p x) y))

end OAI.SecondPassArithmetic
end



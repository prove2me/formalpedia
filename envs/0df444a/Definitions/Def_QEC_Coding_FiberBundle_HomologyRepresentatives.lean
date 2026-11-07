-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
-- name    : QEC_Coding_FiberBundle_HomologyRepresentatives
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:40:22.651017+00:00
-- url     : https://prove2.me/theorems/d52d52dc-51fe-4bdf-b697-8a26357dc980
-- title:
--   Homology Representatives
-- statement:
--   Definitions and structural lemmas for Homology Representatives, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
namespace QEC.Coding.FiberBundle
universe u
def homologyBaseProjection
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype fiberZero]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) baseOne :=
  fun b => ∑ i : fiberZero, horizontalFiber z b i
def cycleFiberChainBoundary
    (n : Nat) [NeZero n]
    (c : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun i => ∑ j : ZMod n, cycleBoundary n i j * c j
def cycleFiberChainPrimitive
    (n : Nat) [NeZero n]
    (g : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  cycleFiberPrimitive n (fun i => g (i + 1))
def horizontalFiberPrimitiveTwoChain
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))) := by
  letI : NeZero (ell * ell) :=
    ⟨Nat.mul_ne_zero (NeZero.ne ell) (NeZero.ne ell)⟩
  exact fun bj =>
    cycleFiberChainPrimitive (ell * ell)
      (horizontalFiber z bj.1) bj.2
def verticalFundamentalCoefficient
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Zero fiberOne]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (a : baseZero) : ZMod 2 :=
  verticalFiber z a 0
def verticalFundamentalWord
    {baseZero baseOne fiberZero fiberOne : Type u}
    (y : Word (ZMod 2) baseZero) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)
  | Sum.inl _ => 0
  | Sum.inr (a, _j) => y a
def constantFiberTwoChain
    {baseOne fiberOne : Type u}
    (x : Word (ZMod 2) baseOne) :
    Word (ZMod 2) (C2Index baseOne fiberOne) :=
  fun bj => x bj.1
def fiberResidue (ell : Nat) [NeZero ell] :
    ZMod (ell * ell) →+ ZMod ell :=
  (ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom
def IsHorizontallyResidueNormalized
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Prop :=
  ∀ b i, z (Sum.inl (b, i)) ≠ 0 → fiberResidue ell i = 0
def HorizontalBoundaryOverlap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  ∃ a : Fin (3 * r),
    RandomBase.boundary baseSample a x.1 ≠ 0 ∧
    RandomBase.boundary baseSample a y.1 ≠ 0 ∧
    (((RandomTwist.fiberBundleData baseSample twistSample
      ).connection x.1 a).onZero) x.2 =
    (((RandomTwist.fiberBundleData baseSample twistSample
      ).connection y.1 a).onZero) y.2
theorem horizontalBoundaryOverlap_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Symmetric (HorizontalBoundaryOverlap baseSample twistSample) := by
  intro x y
  rintro ⟨a, hax, hay, hxy⟩
  exact ⟨a, hay, hax, hxy.symm⟩
def InSameHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  Relation.ReflTransGen
    (HorizontalBoundaryOverlap baseSample twistSample) x y
def SupportedHorizontalBoundaryOverlap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  z (Sum.inl x) ≠ 0 ∧
  z (Sum.inl y) ≠ 0 ∧
  HorizontalBoundaryOverlap baseSample twistSample x y
def InSameSupportedHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  Relation.ReflTransGen
    (SupportedHorizontalBoundaryOverlap
      baseSample twistSample z) x y
theorem supportedHorizontalBoundaryOverlap_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Symmetric
      (SupportedHorizontalBoundaryOverlap
        baseSample twistSample z) := by
  intro x y
  rintro ⟨hx, hy, hxy⟩
  exact ⟨hy, hx,
    horizontalBoundaryOverlap_symmetric
      baseSample twistSample hxy⟩
theorem inSameSupportedHorizontalCluster_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Symmetric
      (InSameSupportedHorizontalCluster
        baseSample twistSample z) := by
  letI : Std.Symm (SupportedHorizontalBoundaryOverlap baseSample twistSample z) :=
    ⟨fun _ _ h => supportedHorizontalBoundaryOverlap_symmetric baseSample twistSample z h⟩
  exact fun _ _ h => Relation.ReflTransGen.stdSymm.symm _ _ h
def SupportedHorizontalCell
    {r ell : Nat}
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :=
  {x : Fin (4 * r) × ZMod (ell * ell) // z (Sum.inl x) ≠ 0}
def supportedHorizontalClusterSetoid
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Setoid (SupportedHorizontalCell z) where
  r x y :=
    InSameSupportedHorizontalCluster
      baseSample twistSample z x.1 y.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Relation.ReflTransGen.refl
    · intro x y hxy
      exact inSameSupportedHorizontalCluster_symmetric
        baseSample twistSample z hxy
    · intro x y w hxy hyw
      exact Relation.ReflTransGen.trans hxy hyw
noncomputable def horizontalClusterCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Nat := by
  exact Nat.card
    (Quotient
      (supportedHorizontalClusterSetoid
        baseSample twistSample z))
noncomputable def horizontalClusterSubchain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    Word (ZMod 2) (Fin (4 * r) × ZMod (ell * ell)) := by
  classical
  exact fun x =>
    if InSameSupportedHorizontalCluster
        baseSample twistSample z root x
    then z (Sum.inl x)
    else 0
def IsBinarySubword
    {ι : Type u}
    (h z : Word (ZMod 2) ι) : Prop :=
  ∀ i, h i = 0 ∨ h i = z i
def WeightedHammingCost
    {ι : Type u} [Fintype ι]
    (weight : ι → Nat)
    (z : Word (ZMod 2) ι) : Nat :=
  ∑ i, if z i ≠ 0 then weight i else 0
def shiftHorizontalSubchain
    {baseOne : Type u}
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    Word (ZMod 2) (baseOne × ZMod n) :=
  fun bi => h (bi.1, bi.2 - 1)
def horizontalResiduePotential
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Nat :=
  WeightedHammingCost
    (fun bi => (-fiberResidue ell bi.2).val)
    (horizontalComponent z)
def horizontalChainWord
    {baseZero baseOne fiberZero fiberOne : Type u}
    (h : Word (ZMod 2) (baseOne × fiberZero)) :
    Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)
  | Sum.inl bi => h bi
  | Sum.inr _ => 0
def oneStepSlideTwoChain
    {baseOne fiber : Type u}
    (h : Word (ZMod 2) (baseOne × fiber)) :
    Word (ZMod 2) (C2Index baseOne fiber) :=
  fun bj => h bj
noncomputable def oneStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))) :=
  z +
    boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (oneStepSlideTwoChain h)
def backwardShiftHorizontalSubchain
    {baseOne : Type u}
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    Word (ZMod 2) (baseOne × ZMod n) :=
  fun bi => h (bi.1, bi.2 + 1)
def negativeStepSlideTwoChain
    {baseOne : Type u}
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    Word (ZMod 2) (C2Index baseOne (ZMod n)) :=
  fun bj => h (bj.1, bj.2 + 1)
noncomputable def negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))) :=
  z +
    boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (negativeStepSlideTwoChain (ell * ell) h)
def twistGraphWordOfHorizontalComponent
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Word (ZMod 2) (ZMod ell × Fin (4 * r)) :=
  fun ub =>
    horizontalFiber z ub.2
      (TwistGraph.layerEmbedding ell ub.1)
noncomputable def horizontalChainBoundary
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    Word (ZMod 2) (ZMod (ell * ell)) :=
  fun j =>
    ∑ b : Fin (4 * r),
      RandomBase.boundary baseSample a b *
        h (b,
          (((RandomTwist.fiberBundleData baseSample twistSample
            ).connection b a).onOne.symm) j)
noncomputable def horizontalBoundaryShadow
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    Finset (Fin (3 * r)) := by
  classical
  exact Finset.univ.filter (fun a =>
    ∃ j, horizontalChainBoundary baseSample twistSample h a j ≠ 0)
def coarseFiberWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell))) :
    Word (ZMod 2) (ZMod ell) :=
  fun u => v (TwistGraph.layerEmbedding ell u)
def coarseBoundaryWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell))) :
    Word (ZMod 2) (ZMod ell) :=
  fun u =>
    cycleFiberChainBoundary (ell * ell) v
      (TwistGraph.layerEmbedding ell u)
def backwardVertexToggle
    (n : Nat) [NeZero n]
    (g : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun j => g (j + 1)
def IsHomologyClassWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Prop :=
  ∀ c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))),
    HammingWeight z ≤
      HammingWeight
        (z +
          boundary2
            (RandomTwist.fiberBundleData baseSample twistSample) c)
def bundleFiberTranslationEquiv
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n) :
    QubitIndex baseZero baseOne (ZMod n) (ZMod n) ≃
      QubitIndex baseZero baseOne (ZMod n) (ZMod n) :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl baseOne) (Equiv.addRight t))
    (Equiv.prodCongr (Equiv.refl baseZero) (Equiv.addRight t))
def translateBundleWord
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n))) :
    Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)) :=
  reindexWord (bundleFiberTranslationEquiv n t) z
noncomputable def globalSlideIterate
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Nat → Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))
  | 0 => z
  | k + 1 =>
      oneStepSlide baseSample twistSample
        (globalSlideIterate baseSample twistSample z k)
        (horizontalComponent
          (globalSlideIterate baseSample twistSample z k))
end QEC.Coding.FiberBundle



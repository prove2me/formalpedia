-- Prove2me | Definitions.Def_AlpoGeB003
-- name    : AlpoGeB003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:19:54.054689+00:00
-- url     : https://prove2.me/theorems/a5d5ad66-cd38-4d91-952f-d71fb4670b88
-- title:
--   Definitions bundle AlpoGeB003 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 15 declarations of the release's Lean: 7 definitions, 3 inductive types or structures, 5 instances and 0 theorems. The definitions and types are `ReciprocityTheory.ChartRestriction.G.Geo.Tor.UnramExt`, `ReciprocityTheory.Def.IsCNL`, `ReciprocityTheory.PGsh.LAlg`, `ReciprocityTheory.PGsh.extModR`, `UpperTheory.GalStar.IsQpBig`, `UpperTheory.Reformulated.B.CovariantDegrees.G`, `UpperTheory.Reformulated.B.JumpSetsAlt.G0`, `UpperTheory.Reformulated.B.JumpSetsAlt.GG`, `UpperTheory.Reformulated.B.JumpSetsAlt.GalL`, `UpperTheory.Reformulated.B.JumpSetsAlt.HGrp`.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib

section
-- module Solutions.AlpoGe.ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace ReciprocityTheory.Gal

noncomputable section

open Representation

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

variable (rho : Representation R G M)

section Inertia

variable {D : Type*} [Group D] [TopologicalSpace D] (rhoD : Representation R D M)
  (J : Subgroup D)

variable (Mplus : Submodule R M) (hMplus : ∀ g, Mplus ≤ Mplus.comap (rhoD g))

instance continuousConstSMul_quotient (N : Submodule R M) : ContinuousConstSMul R (M ⧸ N) :=
  ⟨fun c => by
    rw [(Submodule.isQuotientMap_mkQ N).continuous_iff]
    exact (Submodule.isQuotientMap_mkQ N).continuous.comp (continuous_const_smul c)⟩

end Inertia

end

end ReciprocityTheory.Gal
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.Hypotheses.GalCohDefs
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Representation

namespace ReciprocityTheory.Gal

instance (priority := 100) continuousConstSMul_of_discrete {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

end ReciprocityTheory.Gal
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.JumpSets
attribute [-instance] _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.G0 :
    Type :=
    ℤˣ × ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HGrp :
    ℕ → Type :=
    fun (e : ℕ) ↦ (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ)

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.GG :
    ℕ → Type :=
    fun (e : ℕ) ↦ UpperTheory.Reformulated.B.JumpSetsAlt.G0 × UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e

@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.GalL :
    ℕ → Type :=
    fun (n : ℕ) ↦ (ZMod ((2 : ℕ) ^ n))ˣ × ℤˣ × ℤˣ
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.DualLattices.SqZeroOfSpan
attribute [-instance] _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open IsLocalRing TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure LAlg (R₀ : Type u) [CommRing R₀] where
  carrier : Type u
  [cr : CommRing carrier]
  [alg : Algebra R₀ carrier]
  [loc : IsLocalRing carrier]

attribute [instance] LAlg.cr LAlg.alg LAlg.loc

variable {R₀ : Type u} [CommRing R₀]

instance instCoeSortLAlgType : CoeSort (LAlg R₀) (Type u) := ⟨LAlg.carrier⟩

end ReciprocityTheory.PGsh
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.BasicDefinitions.ExistsUnique
attribute [-instance] _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace ReciprocityTheory.Def

open IsLocalRing Matrix

universe u v w w'

class IsCNL (O : Type u) (A : Type w) [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (maximalIdeal A) A
  localHom : IsLocalHom (algebraMap O A)
  resSurj : Function.Surjective fun x : O => residue A (algebraMap O A x)

attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom

end ReciprocityTheory.Def
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
attribute [-instance] _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.Inh

instance geomConn_id (S : Scheme.{0}) : GeometricallyConnected (𝟙 S) := by
  rw [geometricallyConnected_iff]
  intro K _ y Z fst snd h
  have h' : IsPullback y (𝟙 _) (𝟙 S) y := IsPullback.of_vert_isIso ⟨by simp⟩
  let e : Z ≅ Spec (CommRingCat.of K) := h.isoIsPullback _ _ h'
  exact (Scheme.homeoOfIso e.symm).surjective.connectedSpace (Scheme.homeoOfIso e.symm).continuous

end ReciprocityTheory.ChartRestriction.G.Out.Inh
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
attribute [-instance] _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

structure UnramExt (V : Type) [CommRing V] where
  W : Type
  [ring : CommRing W]
  [dom : IsDomain W]
  [dvr : IsDiscreteValuationRing W]
  [alg : Algebra V W]
  fin : Module.Finite V W
  inj : Function.Injective (algebraMap V W)
  unram : Algebra.FormallyUnramified V W
  complete : IsAdicComplete (maximalIdeal W) W

attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.DualLattices.SmallLevelClassSet
attribute [-instance] _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Polynomial Matrix
open scoped TensorProduct

namespace ReciprocityTheory.PGsh

abbrev extModR (R K V : Type*) [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] : Module R (ExteriorAlgebra K V) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] extModR

end ReciprocityTheory.PGsh
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis
attribute [-instance] _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis

open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

instance isEmpty_real : IsEmpty {w : InfinitePlace E // IsReal w} :=
  ⟨fun w => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩

end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
attribute [-instance] _root_.ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.isEmpty_real _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

@[reducible] noncomputable def UpperTheory.Reformulated.B.CovariantDegrees.G.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [@Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] →
              Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [inst : Field F] [inst_1 : Field Ω]
        [inst_2 :
          @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] ↦
      @AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2 inst_2
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Polynomial
open scoped commutatorElement

namespace UpperTheory.GalStar

def IsQpBig {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Prop :=
  ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i ∧ (n = 1 ∨ 16 * n ^ 2 < g)

end UpperTheory.GalStar
end
end



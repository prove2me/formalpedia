-- Prove2me | Definitions.Def_AlpoGeB001
-- name    : AlpoGeB001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:21:32.007358+00:00
-- url     : https://prove2.me/theorems/a589e310-45ea-4605-b254-384c0c6a6983
-- title:
--   Definitions bundle AlpoGeB001 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 339 declarations of the release's Lean: 125 definitions, 22 inductive types or structures, 21 instances and 171 theorems. The definitions and types are `Formalism.BasicNotions.placesOver`, `Formalism.BasicNotions.tensTopL`, `Formalism.ConjugateSelfDual.G`, `Formalism.ConjugateSelfDual.Inertia`, `Formalism.ConjugateSelfDual.IsFrob`, `Formalism.ConjugateSelfDual.IsPlaceOver`, `Formalism.ConjugateSelfDual.Qbar`, `Formalism.ConjugateSelfDual.normV`, `Formalism.IndefR.Bridge.CoefDatG`, `Formalism.IndefR.Cx.CxData`, `Formalism.IndefR.Links.HMod`, `Formalism.L2.Col.Cpl`, `Formalism.L2.Col.Fields`, `Formalism.L2.Col.GFam`, `Formalism.L2.Col.GFam.mem`, `Formalism.L2.Col.GSD`, `Formalism.L2.Col.GSD.restr`, `Formalism.L2.Col.GSD.toFam`, `Formalism.L2.Col.Primes`, `Formalism.L2.DIV.AfE`, `Formalism.L2.DIV.CSD`, `Formalism.L2.DIV.RInt`, `Formalism.L2.GlobalTheoryTheory.DivPassage.LevelAmb`, `Formalism.L2.Host.HChar`, `Formalism.L2.Host.HChar.inf`, `Formalism.L2.Host.HChar.loc`, `Formalism.L2.Host.HChar.locInf`, `Formalism.L2.Host.HChar.locK`, `Formalism.L2.Host.HChar.val`, `Formalism.L2.Host.IsUnifAt`, `Formalism.L2.Host.IsUnitAt`, `Formalism.L2.Host.atFin`, `Formalism.L2.Host.atInf`, `Formalism.L2.Host.hcharSub`, `Formalism.L2.Host.infDiag`, `Formalism.L2.Host.unif`, `Formalism.L2.Indef.DefAmb`, `Formalism.L2.Indef.DefBase`, `Formalism.L2.Indef.IndefNum`, `Formalism.L2.NC.HC`, `Formalism.L2.Pj.CDVR`, `Formalism.MainNotions.ArithmeticCylinders.entN`, `Formalism.MainNotions.BlochKatoReduction.IsWild`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens`, `Formalism.MainNotions.ModuliIntegralCharts.CF`, `Formalism.MainNotions.N.GRep`, `Formalism.MainNotions.N.IsInv`, `Formalism.MainNotions.N.IsSSRep`, `Formalism.MainNotions.N.mapRep`, `Formalism.MainNotions.PrimeDegreeVariant.GoodSet`, `Formalism.MainNotions.StandardLattice.IsInfEmb`, `Formalism.Per.Gq`, `Formalism.REAL.Tm`, `Formalism.REAL.qdet`, `Formalism.REAL.qminor`, `Formalism.ResultantValuation.ParabolicCounting.act`, `Formalism.UG.P.levelafQ`, and 87 more.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

class IsCMExtension (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop where
  totallyReal : IsTotallyReal F
  totallyComplex : IsTotallyComplex E
  quadratic : Algebra.IsQuadraticExtension F E

section Extension

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

instance liesOver_under (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩

def finiteCompletionMap (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).adicCompletion K →+* w.adicCompletion L :=
  ((adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((w.under (𝓞 K)).valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K)) w).continuous)).comp
    (adicCompletion.equiv K (w.under (𝓞 K))).toRingHom

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w) :=
  (adicCompletion.uniformEquiv L w).symm.uniformContinuous.continuous.comp
    (UniformSpace.Completion.continuous_map.comp
      (adicCompletion.uniformEquiv K (w.under (𝓞 K))).uniformContinuous.continuous)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w (algebraMap K _ x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  erw [show (adicCompletion.equiv K (w.under (𝓞 K))) (algebraMap K _ x) =
    ((WithVal.equiv ((w.under (𝓞 K)).valuation K)).symm x :
      ((w.under (𝓞 K)).valuation K).Completion) from rfl]
  erw [UniformSpace.Completion.mapRingHom_apply, UniformSpace.Completion.map_coe
    (uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K)) w)]
  rfl

end Extension

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ImportsTer
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LocalNormBound

theorem local_bound (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (W : Set (v.adicCompletion F)) (hW : W ∈ 𝓝 (0 : v.adicCompletion F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ v.adicCompletionIntegers F, N • x ∈ W := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hW
  have hp : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  set p := Ideal.absNorm v.asIdeal with hpdef
  have hlt : Valued.v ((p : ℕ) : v.adicCompletion F) < 1 := by
    have h1 : ((p : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by
      simp
    rw [h1]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (p : 𝓞 F))
    have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 (Ideal.absNorm_mem _)
    exact h2 ▸ h3
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hlt
  have hS := Valued.mem_nhds_zero.2 ⟨γ, subset_rfl (a := _)⟩
  obtain ⟨n, hn⟩ := (ht.eventually hS).exists
  refine ⟨p ^ n, pow_pos hp n, fun x hx => hγ ?_⟩
  refine lt_of_le_of_lt ?_ hn
  rw [Valuation.restrict_le_iff, nsmul_eq_mul, map_mul, Nat.cast_pow]
  exact mul_le_of_le_one_right' hx

theorem main : ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F], ∀ U ∈ nhds (0 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), ∃ (N : ℕ), (0 : ℕ) < N ∧ ∀ (a : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (a : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion F a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) → N • a ∈ U := by
  intro F _ _ U hU
  classical
  let φ : (Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
      FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hφ : Continuous φ := RestrictedProduct.isEmbedding_structureMap.continuous
  let z : Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨0, zero_mem _⟩
  have hz : φ z = 0 := FiniteAdeleRing.ext F fun v => rfl
  have h1 : φ ⁻¹' U ∈ 𝓝 z := hφ.continuousAt.preimage_mem_nhds (hz ▸ hU)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  have h2 : ∀ v : HeightOneSpectrum (𝓞 F), ∃ N : ℕ, 0 < N ∧
      ∀ x (hx : x ∈ v.adicCompletionIntegers F), ⟨N • x, nsmul_mem hx N⟩ ∈ t v := by
    intro v
    obtain ⟨W, hW, hWt⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨N, hN, h⟩ := local_bound F v W hW
    exact ⟨N, hN, fun x hx => hWt (h x hx)⟩
  choose n hn hnt using h2
  refine ⟨∏ v ∈ hI.toFinset, n v, Finset.prod_pos fun v _ => hn v, fun a ha => ?_⟩
  set N := ∏ v ∈ hI.toFinset, n v with hN
  have h3 : φ (fun v => ⟨N • a v, nsmul_mem (ha v) N⟩) = N • a :=
    FiniteAdeleRing.ext F fun v => rfl
  rw [← h3]
  refine hsub fun v hv => ?_
  obtain ⟨k, hk⟩ : n v ∣ N := Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv)
  have h4 := hnt v (k • a v) (nsmul_mem (ha v) k)
  convert h4 using 2
  rw [hk, mul_smul]

end GlobalTheory.LocalNormBound
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NsmulIntegralMemNhdsZero
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace GlobalTheory.IntegralNeighbourhoodZero

open IsDedekindDomain NumberField

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _

theorem nsmul_integral_mem_nhds_zero (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (RingOfIntegers F) F |
      ∃ a : FiniteAdeleRing (RingOfIntegers F) F,
        (∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F) ∧
          c = M • a} ∈ nhds (0 : FiniteAdeleRing (RingOfIntegers F) F) := by
  obtain ⟨m, hm⟩ : ∃ m : FiniteAdeleRing (RingOfIntegers F) F, m = algebraMap F _ ((M : F)⁻¹) := ⟨_, rfl⟩
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hmM : (M : FiniteAdeleRing (RingOfIntegers F) F) * m = 1 := by
    rw [hm, ← map_natCast (algebraMap F (FiniteAdeleRing (RingOfIntegers F) F)), ← map_mul,
      mul_inv_cancel₀ hMF, map_one]
  have hopen : IsOpen ((fun c => m * c) ⁻¹' {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F}) :=
    (isOpen_integral F).preimage (continuous_const.mul continuous_id)
  have h0 : (0 : FiniteAdeleRing (RingOfIntegers F) F) ∈ (fun c => m * c) ⁻¹'
      {a : FiniteAdeleRing (RingOfIntegers F) F |
        ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} := by
    intro v
    change (m * 0) v ∈ _
    rw [mul_zero]
    exact zero_mem _
  refine Filter.mem_of_superset (hopen.mem_nhds h0) ?_
  intro c hc
  refine ⟨m * c, hc, ?_⟩
  rw [nsmul_eq_mul, ← mul_assoc, hmM, one_mul]

end GlobalTheory.IntegralNeighbourhoodZero
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdLat.OpenLat

variable (F : Type) [Field F] [NumberField F]

theorem exists_nsmul_adele (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → N • a ∈ U := by
  first
  | exact @_root_.GlobalTheory.LocalNormBound.main
  | exact _root_.GlobalTheory.LocalNormBound.main
  | (apply _root_.GlobalTheory.LocalNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalNormBound.main ..)

theorem nsmul_integral_mem_nhds (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (𝓞 F) F | ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
  first
  | exact @_root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | exact _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | (apply _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero ..)

end GlobalTheory.AdLat.OpenLat
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.NeutralLocalFields.Reciprocity
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Topology

namespace Neutral.B1

section Global

variable (K : Type*) [Field K] [NumberField K]

abbrev Ideles : Type _ := (AdeleRing (𝓞 K) K)ˣ

def diagUnits : Kˣ →* Ideles K :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom

open Classical in

def finiteSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y

def localIdele (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* Ideles K :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing K), finiteSingle K v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle K v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle K v) x y) }

end Global

end Neutral.B1
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

set_option linter.style.haveILetI false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1

namespace ReciprocityTheory.Neutral.Bridge.HCFR

variable (K : Type) [Field K] [NumberField K]

open Classical in

def infIdele (w : InfinitePlace K) : (w.Completion)ˣ →* Ideles K :=
  Units.map
    { toFun := fun x => ((Pi.mulSingle w x : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K))
      map_one' := Prod.ext (Pi.mulSingle_one w) rfl
      map_mul' := fun x y => Prod.ext (Pi.mulSingle_mul w x y) (mul_one 1).symm }

end ReciprocityTheory.Neutral.Bridge.HCFR
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR nonZeroDivisors

namespace Formalism.L2.Host

variable (L : Type) [Field L] [NumberField L]

def hcharSub : Subgroup (Ideles L →* ℂˣ) where
  carrier := {χ | Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1}
  one_mem' := ⟨continuous_const, fun _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun k => by
    rw [MonoidHom.mul_apply, ha.2 k, hb.2 k, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨ha.1.inv, fun k => by rw [MonoidHom.inv_apply, ha.2 k, inv_one]⟩

abbrev HChar : Type := ↥(hcharSub L)

variable {L}

def atFin (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* (v.adicCompletion L)ˣ :=
  Units.map (algebraMap L (v.adicCompletion L)).toMonoidHom

def atInf (w : InfinitePlace L) : Lˣ →* (w.Completion)ˣ :=
  Units.map (algebraMap L w.Completion).toMonoidHom

def IsUnitAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = 1

def IsUnifAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = WithZero.exp (-1 : ℤ)

def infDiag : Lˣ →* Ideles L := ∏ w : InfinitePlace L, (infIdele L w).comp (atInf w)

theorem exists_unif (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ, IsUnifAt v (atFin v k) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π h0, ?_⟩
  show Valued.v ((algebraMap L (v.adicCompletion L)) π) = _
  rw [← hπ]
  exact v.valuedAdicCompletion_eq_valuation' π

def unif (v : HeightOneSpectrum (𝓞 L)) : Lˣ := Classical.choose (exists_unif v)

namespace HChar

variable (χ : HChar L)

def loc (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* ℂˣ := χ.1.comp (localIdele L v)

def locInf (w : InfinitePlace L) : (w.Completion)ˣ →* ℂˣ := χ.1.comp (infIdele L w)

def locK (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* ℂˣ := (χ.loc v).comp (atFin v)

def inf : Lˣ →* ℂˣ := χ.1.comp infDiag

def val (v : HeightOneSpectrum (𝓞 L)) : ℂˣ := χ.locK v (unif v)

@[simp] theorem loc_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) (x) : (χ * χ').loc v x = χ.loc v x * χ'.loc v x := rfl
@[simp] theorem loc_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (x) : (χ⁻¹).loc v x = (χ.loc v x)⁻¹ := rfl
@[simp] theorem loc_one (v : HeightOneSpectrum (𝓞 L)) (x) : (1 : HChar L).loc v x = 1 := rfl
@[simp] theorem locInf_mul (χ χ' : HChar L) (w : InfinitePlace L) (x) : (χ * χ').locInf w x = χ.locInf w x * χ'.locInf w x := rfl
@[simp] theorem locInf_inv (χ : HChar L) (w : InfinitePlace L) (x) : (χ⁻¹).locInf w x = (χ.locInf w x)⁻¹ := rfl
@[simp] theorem val_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ * χ').val v = χ.val v * χ'.val v := rfl
@[simp] theorem val_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ⁻¹).val v = (χ.val v)⁻¹ := rfl
@[simp] theorem inf_mul (χ χ' : HChar L) (k : Lˣ) : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
@[simp] theorem inf_inv (χ : HChar L) (k : Lˣ) : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl

end HChar

end Formalism.L2.Host
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped ContDiff

namespace GlobalTheory.CuspRep

variable {ι : Type} [Fintype ι]

def expU (z : ι → ℂ) : (ι → ℂ)ˣ :=
  ⟨fun i => Complex.exp (z i), fun i => Complex.exp (-z i),
    by funext i; simp [← Complex.exp_add], by funext i; simp [← Complex.exp_add]⟩

omit [Fintype ι] in

theorem expU_add (z z' : ι → ℂ) : expU (z + z') = expU z * expU z' :=
  Units.ext (funext fun i => Complex.exp_add (z i) (z' i))

omit [Fintype ι] in

theorem expU_zero : expU (0 : ι → ℂ) = 1 := Units.ext (funext fun _ => Complex.exp_zero)

omit [Fintype ι] in

theorem unit_ne_zero (u : (ι → ℂ)ˣ) (i : ι) : (u : ι → ℂ) i ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrFun u.mul_inv i)

omit [Fintype ι] in

theorem expU_log (u : (ι → ℂ)ˣ) : expU (fun i => Complex.log ((u : ι → ℂ) i)) = u :=
  Units.ext (funext fun i => Complex.exp_log (unit_ne_zero u i))

omit [Fintype ι] in

theorem continuous_expU : Continuous (expU : (ι → ℂ) → (ι → ℂ)ˣ) :=
  Units.continuous_iff.2 ⟨continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i),
    continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i).neg⟩

theorem exists_lin (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ L : (ι → ℂ) →L[ℝ] ℂ, ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z) := by
  let f : C(ι → ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun z => ⟨(ψ (expU z) : ℂˣ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp continuous_expU)).subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f, expU_zero]))
  have hF' : ∀ z, Complex.exp (F z) = (ψ (expU z) : ℂˣ) := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', expU_add, map_mul, Units.val_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

open Classical in

def extZero (ψ : (ι → ℂ)ˣ →* ℂˣ) (x : ι → ℂ) : ℂ := if h : IsUnit x then (ψ h.unit : ℂˣ) else 0

omit [Fintype ι] in

theorem extZero_unit (ψ : (ι → ℂ)ˣ →* ℂˣ) (u : (ι → ℂ)ˣ) : extZero ψ u = (ψ u : ℂˣ) := by
  simp [extZero]

theorem extZero_eventually {ψ : (ι → ℂ)ˣ →* ℂˣ} {L : (ι → ℂ) →L[ℝ] ℂ}
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) (u : (ι → ℂ)ˣ) :
    extZero ψ =ᶠ[𝓝 (u : ι → ℂ)] fun x => (ψ u : ℂˣ) * Complex.exp (L fun i => Complex.log (x i / (u : ι → ℂ) i)) := by
  have h : ∀ᶠ x in 𝓝 (u : ι → ℂ), ∀ i, x i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually_ne (unit_ne_zero u i)
  filter_upwards [h] with x hx
  have e : x = ((u * expU fun i => Complex.log (x i / (u : ι → ℂ) i) : (ι → ℂ)ˣ) : ι → ℂ) := by
    funext i
    change x i = (u : ι → ℂ) i * Complex.exp (Complex.log (x i / (u : ι → ℂ) i))
    rw [Complex.exp_log (div_ne_zero (hx i) (unit_ne_zero u i)), mul_div_cancel₀ _ (unit_ne_zero u i)]
  conv_lhs => rw [e, extZero_unit, map_mul, Units.val_mul, hL]

theorem contDiffAt_extZero (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) (u : (ι → ℂ)ˣ) :
    ContDiffAt ℝ ∞ (extZero ψ) u := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  refine ContDiffAt.congr_of_eventuallyEq ?_ (extZero_eventually hL u)
  refine contDiffAt_const.mul (ContDiffAt.cexp (L.contDiff.contDiffAt.comp _ (contDiffAt_pi.2 fun i => ?_)))
  have h1 : ContDiffAt ℝ ∞ Complex.log ((u : ι → ℂ) i / (u : ι → ℂ) i) := by
    rw [div_self (unit_ne_zero u i)]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  exact h1.comp (f := fun x : ι → ℂ => x i / (u : ι → ℂ) i) _ ((contDiffAt_apply ℝ ℂ i _).div_const _)

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.PRep

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

variable {W : Type} [AddCommGroup W] [Module k W]

def rightReg (k G W : Type) [Field k] [Group G] [AddCommGroup W] [Module k W] :
    Representation k G (G → W) where
  toFun g := LinearMap.funLeft k W (fun x => x * g)
  map_one' := by ext f x; simp [LinearMap.funLeft]
  map_mul' a b := by ext f x; simp [LinearMap.funLeft, mul_assoc]

def sub (ρ : Representation k G V) (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) :
    Representation k G U where
  toFun g := (ρ g).restrict (hU g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

end GlobalTheory.PRep
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} [CommRing A]

theorem factorPow_evalₐ (I : Ideal A) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h x =>
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I hle x

theorem evalₐ_pow_eq_zero (I : Ideal A) {x : AdicCompletion I A}
    (hx : AdicCompletion.evalOneₐ I x = 0) (n : ℕ) : AdicCompletion.evalₐ I n x ^ n = 0 := by
  rcases n with _ | n
  · exact Subsingleton.elim (h := Ideal.Quotient.subsingleton_iff.2 (by simp)) _ _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have h1 := factorPow_evalₐ I (show 1 ≤ n + 1 by omega) x
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← h1, ← ha] at hx
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [← ha, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hx _

def truncLog {B : Type*} [CommRing B] [Algebra ℚ B] (N : ℕ) (x : B) : B :=
  ∑ k ∈ Finset.range N, ((-1 : ℚ) ^ k / (k + 1)) • x ^ (k + 1)

theorem map_truncLog {B B' : Type*} [CommRing B] [Algebra ℚ B] [CommRing B'] [Algebra ℚ B']
    (f : B →+* B') (N : ℕ) (x : B) : f (truncLog N x) = truncLog N (f x) := by
  simp [truncLog, map_rat_smul]

theorem truncLog_eq_of_pow_eq_zero {B : Type*} [CommRing B] [Algebra ℚ B] {x : B} {m n : ℕ}
    (h : x ^ m = 0) (hle : m ≤ n) : truncLog n x = truncLog m x := by
  induction n, hle using Nat.le_induction with
  | base => rfl
  | succ n hle ih =>
    rw [← ih, truncLog, Finset.sum_range_succ, pow_eq_zero_of_le (by omega) h, smul_zero, add_zero]
    rfl

end Adic

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

@[reducible] def actionOf {G B : Type*} [Monoid G] [CommRing B] (f : G → B →+* B)
    (h1 : ∀ x, f 1 x = x) (hmul : ∀ g h x, f (g * h) x = f g (f h x)) : MulSemiringAction G B where
  smul g x := f g x
  one_smul := h1
  mul_smul := hmul
  smul_zero g := map_zero (f g)
  smul_add g := map_add (f g)
  smul_one g := map_one (f g)
  smul_mul g := map_mul (f g)

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal Filter Topology

namespace Reformulated.AutPerF

universe u v

namespace IsUnitBall

variable {C : Type u}
  [NormedField C]
  (O : ValuationSubring C)

variable (p : ℕ)

variable [hp : Fact (‖(p : C)‖ < 1)]

omit hp in
instance instIsAlgClosedFractionRingSubtypeMemValuationSubring [IsAlgClosed C] : IsAlgClosed (FractionRing O) :=
  IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv

end IsUnitBall

section Completion

variable (G : Type v) [Monoid G] (E : Type u) [NormedField E] [MulSemiringAction G E]
  [IsIsometricSMul G E]

instance (priority := 100) uniformContinuousConstSMul_of_isIsometricSMul :
    UniformContinuousConstSMul G E :=
  ⟨fun g => (isometry_smul E g).uniformContinuous⟩

open UniformSpace in

instance completionMulSemiringAction : MulSemiringAction G (Completion E) where
  __ := (inferInstance : DistribMulAction G (Completion E))
  smul_one g := by rw [← Completion.coe_one, ← Completion.coe_smul, smul_one]
  smul_mul g x y := by
    refine Completion.induction_on₂ x y
      (isClosed_eq ((continuous_fst.fun_mul continuous_snd).fun_const_smul g)
        ((continuous_fst.fun_const_smul g).fun_mul (continuous_snd.fun_const_smul g)))
      fun a b => ?_
    rw [← Completion.coe_mul, ← Completion.coe_smul, ← Completion.coe_smul,
      ← Completion.coe_smul, smul_mul', Completion.coe_mul]

open UniformSpace in
instance completionIsIsometricSMul : IsIsometricSMul G (Completion E) :=
  ⟨fun g => (isometry_smul E g).completion_map⟩

end Completion

section PadicComplex

variable (p : ℕ) [Fact p.Prime]

instance instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)] :
    IsIsometricSMul (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (PadicAlgCl p) :=
  ⟨fun g => Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub]
    exact (spectralNorm_eq_of_equiv (g.restrictScalars ℚ_[p]) (x - y)).symm⟩

end PadicComplex

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.CrystallineRing.Acris0
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace UpperTheory.Ring.Comp

open Reformulated.AutPerF

abbrev Gq (l : ℕ) [Fact (Nat.Prime l)] : Type := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

end UpperTheory.Ring.Comp
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

theorem mem_span_of_approx {A : Type*} [CommRing A] (q ξ : A) [IsAdicComplete (span {q}) A]
    (K : Set A) (h : ∀ x ∈ K, ∃ a, ∃ y ∈ K, x = ξ * a + q * y) {x : A} (hx : x ∈ K) :
    x ∈ span {ξ} := by
  choose! a s hs hxs using h
  have hK : ∀ n, s^[n] x ∈ K := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hs _ ih
  let b : ℕ → A := fun n => ∑ i ∈ Finset.range n, q ^ i * a (s^[i] x)
  have hb : ∀ n, x = ξ * b n + q ^ n * s^[n] x := by
    intro n
    induction n with
    | zero => simp [b]
    | succ n ih =>
      have h1 := hxs _ (hK n)
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      linear_combination ih + q ^ n * h1
  have hmem : ∀ (n : ℕ) (z : A), z ∈ (span {q} ^ n • ⊤ : Ideal A) ↔ q ^ n ∣ z := by
    intro n z
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {q}) (M := A) inferInstance (f := b) (by
    intro m n hle
    rw [SModEq.sub_mem, hmem]
    induction n, hle using Nat.le_induction with
    | base => simp
    | succ n hle ih =>
      simp only [b] at ih ⊢
      rw [Finset.sum_range_succ, ← sub_sub]
      exact dvd_sub ih ((pow_dvd_pow q hle).mul_right _))
  have : x - ξ * L = 0 := by
    refine IsHausdorff.haus (I := span {q}) (M := A) inferInstance _ fun n => ?_
    have h1 := hL n
    rw [SModEq.sub_mem, hmem] at h1 ⊢
    have : x - ξ * L - 0 = ξ * (b n - L) + q ^ n * s^[n] x := by linear_combination hb n
    rw [this]
    exact dvd_add (h1.mul_left _) (dvd_mul_right _ _)
  rw [sub_eq_zero.1 this]
  exact Ideal.mul_mem_right _ _ (mem_span_singleton_self _)

theorem eq_zero_of_forall_pow_dvd {A : Type*} [CommRing A] (q : A) [IsHausdorff (span {q}) A]
    {x : A} (h : ∀ n : ℕ, q ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := span {q}) (M := A) inferInstance _ fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  exact h n

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem exists_pow_eq_of_isAlgClosed {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsAlgClosed (FractionRing R)] (a : R) {n : ℕ} (hn : 0 < n) : ∃ b : R, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) a) hn
  have hi : IsIntegral R z := IsIntegral.of_pow hn (hz ▸ isIntegral_algebraMap)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨b, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩

namespace AinfInv

variable [IsDomain R]

variable [ValuationRing R]

variable [CharZero R]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] [ValuationRing R] in
theorem algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (p : R))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

end AinfInv

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

section Adic

variable {A : Type u} [CommRing A]

theorem evalₐ_eq_zero_iff_dvd_of_eq_span {I : Ideal A} {a : A} (hI : I = span {a}) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n x = 0 ↔ algebraMap A (AdicCompletion I A) a ^ n ∣ x := by
  have hfg : I.FG := hI ▸ Submodule.fg_span_singleton a
  have h1 : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0 := by
    constructor
    · intro h
      rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), h, map_zero]
    · intro h
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), h, map_zero]
  rw [h1, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hfg]
  have h2 : I ^ n = span {a ^ n} := by rw [hI, Ideal.span_singleton_pow]
  rw [h2, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem eq_zero_of_algebraMap_mul_eq_zero [IsDomain A] {I : Ideal A} {a : A} (hI : I = span {a})
    (ha : a ≠ 0) {x : AdicCompletion I A} (h : algebraMap A (AdicCompletion I A) a * x = 0) :
    x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ I (n + 1)) h
  rw [map_mul, AlgHom.commutes, ← hy, map_zero, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : ∀ m, I ^ m = span {a ^ m} := fun m => by rw [hI, Ideal.span_singleton_pow]
  rw [h2, mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h1
  rw [← factorPow_evalₐ I n.le_succ, ← hy, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [h2, mem_span_singleton]
  exact h1

end Adic

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]

omit [Fact ¬IsUnit (p : R)] [CharZero R] [Fact p.Prime] in
theorem exists_dvd_p_pow {x : R} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (p : R) ^ n := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_forall_pow_dvd (p : R) fun n =>
    (ValuationRing.dvd_total x _).resolve_left (h n))

instance isFractionRing_away : IsFractionRing R (Localization.Away (p : R)) :=
  IsLocalization.isLocalization_of_is_exists_mul_mem _ (Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    (fun ⟨x, hx⟩ => by
      obtain ⟨n, c, hc⟩ := exists_dvd_p_pow (p := p) (nonZeroDivisors.ne_zero hx)
      exact ⟨c, n, by simp [hc, mul_comm]⟩)

variable (p R) in
omit [Fact ¬IsUnit (p : R)] in
theorem isField_away : IsField (Localization.Away (p : R)) :=
  (IsFractionRing.toField R (K := Localization.Away (p : R))).toIsField

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.Per

open Reformulated.AutPerF

section Cp
abbrev Gq (p : ℕ) [Fact p.Prime] : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p
end Cp

end Formalism.Per
end
end

section
-- module Solutions.AlpoGe.Formalism.SatakeDualWeyl.Statement
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG

section More

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def intAd (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun {a b} ha hb v => by
    show a v * b v ∈ _
    exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by show (1 : v.adicCompletion F) ∈ _; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    show a v + b v ∈ _
    exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by show (0 : v.adicCompletion F) ∈ _; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    show -(a v) ∈ _
    exact neg_mem (ha v)

def intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end More

open NumberField IsDedekindDomain

end Formalism.UG
end
end

section
-- module Solutions.AlpoGe.Formalism.ConjugateSelfDual.Statement
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups
namespace Formalism.ConjugateSelfDual
abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

abbrev Qbar (l : ℕ) [Fact l.Prime] := PadicAlgCl l

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def IsPlaceOver (A : ValuationSubring (Ω)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F (Ω) (x : F)) < 1 ↔ x ∈ v.asIdeal

def normV (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

def Inertia (A : ValuationSubring (Ω)) : Set (G F Ω) :=
  {σ | σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}

def IsFrob (A : ValuationSubring (Ω)) (q : ℕ) (σ : G F Ω) : Prop :=
  σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1

end places
end Formalism.ConjugateSelfDual
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.GaloisValuations.Global
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def Dec (A : ValuationSubring (Ω)) : Subgroup (G F Ω) := A.decompositionSubgroup F

theorem mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ σ • A = A := Iff.rfl

theorem apply_mem_iff_of_mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (x : Ω) : σ x ∈ A ↔ x ∈ A := by
  have h := mem_Dec.mp hσ
  have key : σ • x ∈ σ • A ↔ x ∈ A := ValuationSubring.smul_mem_pointwise_smul_iff
  rw [h] at key
  exact key

theorem valuation_lt_one_iff' (A : ValuationSubring (Ω)) (y : Ω) :
    A.valuation y < 1 ↔ y ∈ A ∧ (y = 0 ∨ y⁻¹ ∉ A) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, not_le,
      Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
    simp only [hy, false_or]
    exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

theorem valuation_apply_lt_one_iff {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (y : Ω) :
    A.valuation (σ y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', (map_inv₀ σ y).symm, apply_mem_iff_of_mem_Dec hσ,
    apply_mem_iff_of_mem_Dec hσ, EmbeddingLike.map_eq_zero_iff]

theorem mul_inv_apply {σ : G F Ω} (x : Ω) : σ ((σ⁻¹ : G F Ω) x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

def Ine (A : ValuationSubring (Ω)) : Subgroup (G F Ω) where
  carrier := Inertia (F := F) A
  one_mem' := ⟨(Dec (F := F) A).one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, hσ'⟩ ⟨hτ, hτ'⟩
    refine ⟨(Dec (F := F) A).mul_mem hσ hτ, fun x hx => ?_⟩
    have e : (σ * τ) x - x = σ (τ x - x) + (σ x - x) := by
      simp [AlgEquiv.mul_apply, map_sub]
    rw [e]
    exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσ _).mpr (hτ' x hx)) (hσ' x hx)
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨(Dec (F := F) A).inv_mem hσ, fun x hx => ?_⟩
    have hy : A.valuation ((σ⁻¹ : G F Ω) x) ≤ 1 := by
      rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hσ, mul_inv_apply]
      exact (A.valuation_le_one_iff x).mp hx
    have e : (σ⁻¹ : G F Ω) x - x = -(σ ((σ⁻¹ : G F Ω) x) - (σ⁻¹ : G F Ω) x) := by
      rw [mul_inv_apply]; ring
    rw [e, Valuation.map_neg]
    exact hσ' _ hy

end ReciprocityTheory.Gal
end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.LevelLetterCocycles.DataN
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def placesOver (E : Type) [Field E] [NumberField E] (p : ℕ) : Set (HeightOneSpectrum (𝓞 E)) :=
  {v | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}

end Formalism.BasicNotions

namespace Formalism.MainNotions.N

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section SharedN4

open Polynomial

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

def IsInv (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) : Prop :=
  ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

def IsSSRep (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsInv ρ W → ∃ W', IsInv ρ W' ∧ IsCompl W W'

end Rep

def mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : Γ →* GL (Fin a) B :=
  (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) A →+* Matrix (Fin a) (Fin a) B).toMonoidHom).comp ρ

end SharedN4

end Formalism.MainNotions.N

end
end

section
-- module Solutions.AlpoGe.Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace Eta

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

instance isGaloisGroup : IsGaloisGroup (K ≃ₐ[K⁺] K) (𝓞 K⁺) (𝓞 K) :=
  IsGaloisGroup.of_isFractionRing _ _ _ K⁺ K

end CM

end Eta

open Eta

end Formalism.FrobeniusOrbits
end
end

section
-- module Solutions.AlpoGe.Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField Matrix

noncomputable section

namespace Formalism.HN

namespace HeightGram

section NT

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

theorem isEmpty_real : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩

attribute [local instance] isEmpty_real

end NT

end HeightGram

end Formalism.HN
end
end

section
-- module Solutions.AlpoGe.Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section
namespace Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem levelaf_valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a := by
  rw [algebraMap_adicCompletion]; exact adicCompletion.valued_coe (K := F) (v := v) _

theorem levelaf_int_mem_v (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by
  rw [mem_adicCompletionIntegers, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
    levelaf_valued_algebraMap, valuation_of_algebraMap]
  exact intValuation_le_one v r

theorem levelaf_int_mem (r : 𝓞 F) : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r ∈ intAd F :=
  fun v => levelaf_int_mem_v v r

end Adele

section Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem levelaf_tmul_mem (e : 𝓞 E) {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] y ∈ 𝒮 := by
  have : algebraMap (𝓞 E) E e ⊗ₜ[F] y =
      (algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩))

def levelafQ {m : ℕ} (b : Fin m → 𝓞 E) (s : 𝒜) : Prop :=
  ∃ r : Fin m → FiniteAdeleRing (𝓞 F) F, (∀ j, r j ∈ intAd F) ∧
    s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j

theorem levelafQ_zero {m : ℕ} (b : Fin m → 𝓞 E) : levelafQ (F := F) b 0 :=
  ⟨0, fun _ => zero_mem _, by simp⟩

theorem levelafQ_add {m : ℕ} (b : Fin m → 𝓞 E) {x y : 𝒜} (hx : levelafQ b x) (hy : levelafQ b y) :
    levelafQ b (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  refine ⟨r + r', fun j => add_mem (hr j) (hr' j), ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_add _ _ _).symm

theorem levelafQ_neg {m : ℕ} (b : Fin m → 𝓞 E) {x : 𝒜} (hx : levelafQ b x) :
    levelafQ b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  refine ⟨-r, fun j => neg_mem (hr j), ?_⟩
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_neg _ _).symm

theorem levelafQ_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → 𝒜)
    (h : ∀ i ∈ s, levelafQ b (f i)) : levelafQ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (levelafQ b) (fun _ _ hx hy => levelafQ_add b hx hy) (levelafQ_zero b) h

theorem levelafQ_tmul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (e : 𝓞 E) {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    levelafQ b (algebraMap (𝓞 E) E e ⊗ₜ[F] y) := by
  have he : e ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 he
  refine ⟨fun j => c j • y, fun j => zsmul_mem hy _, ?_⟩
  rw [← hc, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, TensorProduct.smul_tmul]

theorem levelafQ_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : 𝒜} (hx : levelafQ b x) (hy : levelafQ b y) : levelafQ b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine levelafQ_sum b _ _ fun j _ => levelafQ_sum b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact levelafQ_tmul b hb _ (mul_mem (hr j) (hr' k))

theorem levelaf_decomp {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {s : 𝒜} (hs : s ∈ 𝒮) : levelafQ b s := by
  refine Subring.closure_induction (p := fun s _ => levelafQ b s) ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact levelafQ_tmul b hb e' (one_mem _)
    · have := levelafQ_tmul b hb 1 hy
      rwa [map_one] at this
  · exact levelafQ_zero b
  · have := levelafQ_tmul b hb 1 (one_mem (intAd F))
    rwa [map_one, ← Algebra.TensorProduct.one_def] at this
  · intro x y _ _ hx hy; exact levelafQ_add b hx hy
  · intro x _ hx; exact levelafQ_neg b hx
  · intro x y _ _ hx hy; exact levelafQ_mul b hb hx hy

end Tensor

end Formalism.UG.P
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.Mem.Chr

section General

variable (L : Type) [Field L] [NumberField L]

variable {L}

def ConjPl (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : L, v'.valuation L (c x) = v.valuation L x

end General

end GlobalTheory.Mem.Chr
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.intValuation_of_eq_comap {R : Type} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w w' : HeightOneSpectrum R) (h : w'.asIdeal = w.asIdeal.comap e) (x : R) :
    w'.intValuation x = w.intValuation (e x) := by
  have hmem : ∀ n : ℕ, x ∈ w'.asIdeal ^ n ↔ e x ∈ w.asIdeal ^ n := by
    intro n
    rw [h, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hle : ∀ n : ℕ, w'.intValuation x ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (e x) ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      HeightOneSpectrum.intValuation_le_pow_iff_mem, hmem]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hex : e x ≠ 0 := fun h0 => hx (e.injective (h0.trans (map_zero e).symm))
    rw [HeightOneSpectrum.intValuation_if_neg _ hx, HeightOneSpectrum.intValuation_if_neg _ hex]
      at hle ⊢
    set a := (Associates.mk w'.asIdeal).count (Associates.mk (Ideal.span {x})).factors
    set b := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {e x})).factors
    have h1 := (hle a).1 le_rfl
    have h2 := (hle b).2 le_rfl
    simp only [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
    rw [le_antisymm h1 h2]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.valuation_of_eq_comap {E : Type} [Field E] [NumberField E] (σ : E ≃+* E)
    (w w' : HeightOneSpectrum (𝓞 E))
    (h : w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ)) (y : E) :
    w'.valuation E y = w.valuation E (σ y) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hσ : ∀ r : 𝓞 E, σ (algebraMap (𝓞 E) E r) =
      algebraMap (𝓞 E) E (RingOfIntegers.mapRingEquiv σ r) := fun r => rfl
  rw [map_div₀ σ, hσ, hσ, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [_root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h a,
    _root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h b]

end GlobalTheory.QNorm
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem conjPl_iff_comap (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ v.asIdeal = v'.asIdeal.comap (RingOfIntegers.mapRingEquiv c) := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) =
        v.valuation L (algebraMap (𝓞 L) L x) := h (algebraMap (𝓞 L) L x)
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · intro h x
    exact (GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm

theorem existsUnique_conjPl (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : ∃! v', ConjPl c v v' := by
  set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he
  refine ⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩
  · show ConjPl c v _
    rw [conjPl_iff_comap]
    ext x
    change x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal
    rw [e.symm_apply_apply]
  · intro v' h
    rw [conjPl_iff_comap] at h
    ext x
    change x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal
    rw [h, Ideal.mem_comap, e.apply_symm_apply]

end General

end GlobalTheory.Mem.Chr
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx

variable {L : Type} [Field L] [NumberField L]

open scoped WithZeroTopology in

theorem exists_finCompl_map (c : L ≃+* L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') :
    ∃ φ : v.adicCompletion L →+* v'.adicCompletion L, Continuous φ ∧
      (∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k)) ∧ ∀ x, Valued.v (φ x) = Valued.v x := by
  have hc : Continuous (WithVal.map (v.valuation L) (v'.valuation L) (c : L →+* L)) :=
    continuous_of_valued_eq (fun γ => by
      obtain ⟨k, hk⟩ := v.valuation_surjective L γ
      exact ⟨WithVal.toVal _ k, hk⟩) _ fun x => h x.ofVal
  let φ : v.adicCompletion L →+* v'.adicCompletion L :=
    ((HeightOneSpectrum.adicCompletion.equiv L v').symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  have h1 : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L v').comp
      (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  have h2 : ∀ k : L, φ (algebraMap L _ k) = algebraMap L _ (c k) := fun k => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ k)
  refine ⟨φ, h1, h2, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap L v).induction_on (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq ((Valued.continuous_valuation_of_surjective (v'.valuedAdicCompletion_surjective L)).comp h1)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective L))) fun k => ?_
  rw [h2]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v' _).trans
    ((h k).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm)

theorem conjPl_symm_iff (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) : ConjPl c.symm v' v ↔ ConjPl c v v' :=
  ⟨fun h x => by simpa using (h (c x)).symm, fun h x => by simpa using (h (c.symm x)).symm⟩

end General

end GlobalTheory.Mem.Chr
end

section
-- module Solutions.AlpoGe.Formalism.RealPlaceAnalysis.StatementE
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Finset

noncomputable section

namespace Formalism.REAL

def Tm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) : A :=
  (if a = b then algebraMap ℂ A u else 0) + E a b

def qminor {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod

def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E id id u

end Formalism.REAL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ContDiff

namespace GlobalTheory.CuspRep

section Corner

variable {R S T : Type}

def corner [Ring R] [Ring S] (s : R →ₙ+* S) : R →* S where
  toFun x := 1 - s 1 + s x
  map_one' := by simp
  map_mul' x y := by
    have h1 : s 1 * s y = s y := by rw [← map_mul, one_mul]
    have h2 : s x * s 1 = s x := by rw [← map_mul, mul_one]
    have h3 : s 1 * s 1 = s 1 := by rw [← map_mul, mul_one]
    rw [map_mul]
    simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one, h1, h2, h3]
    abel

variable [CommRing R] [CommRing S] [CommRing T] {a : ℕ}

def matN (a : ℕ) (s : R →ₙ+* S) : Matrix (Fin a) (Fin a) R →ₙ+* Matrix (Fin a) (Fin a) S where
  toFun x := x.map s
  map_mul' x y := by ext i j; simp [Matrix.mul_apply, map_sum]
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp

def cornerGL (a : ℕ) (s : R →ₙ+* S) : GL (Fin a) R →* GL (Fin a) S := Units.map (corner (matN a s))

theorem map_cornerGL_of_zero (s : R →ₙ+* S) (p : S →+* T) (h : ∀ x, p (s x) = 0) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (cornerGL a s g) = 1 := by
  ext i j
  change p ((1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g i j)) = _
  simp [h, Matrix.one_apply, apply_ite p]

theorem map_cornerGL_of_hom (s : R →ₙ+* S) (p : S →+* T) (q : R →+* T) (h : ∀ x, p (s x) = q x) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (cornerGL a s g) = GeneralLinearGroup.map q g := by
  ext i j
  change p ((1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g i j)) = q (g i j)
  simp [h, Matrix.one_apply, apply_ite p, apply_ite q]

theorem det_map (p : S →+* T) (g : GL (Fin a) S) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map p g) : Tˣ) : T) = p (GeneralLinearGroup.det g : Sˣ) :=
  (RingHom.map_det p (g : Matrix (Fin a) (Fin a) S)).symm

end Corner

variable (E : Type) [Field E] [NumberField E]

abbrev Ad : Type := AdeleRing (𝓞 E) E

abbrev Af : Type := FiniteAdeleRing (𝓞 E) E

abbrev Cinf : Type := InfinitePlace E → ℂ

abbrev GA (a : ℕ) : Type := GL (Fin a) (Ad E)

abbrev Lie (a : ℕ) : Type := Fin a → Fin a → Cinf E

def pFin : Ad E →+* Af E := RingHom.snd (InfiniteAdeleRing E) (Af E)

def sFin : Af E →ₙ+* Ad E where
  toFun x := ((0, x) : InfiniteAdeleRing E × Af E)
  map_mul' _ _ := Prod.ext (mul_zero _).symm rfl
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero _).symm rfl

def ratGL (a : ℕ) : GL (Fin a) E →* GA E a := GeneralLinearGroup.map (algebraMap E (Ad E))

def finGL (a : ℕ) : GL (Fin a) (Af E) →* GA E a := cornerGL a (sFin E)

def finId : (Af E)ˣ →* Ideles E := Units.map (corner (sFin E))

variable [IsTotallyComplex E]

def infEq : Cinf E ≃+* InfiniteAdeleRing E :=
  RingEquiv.piCongrRight fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm

theorem continuous_infEq : Continuous (infEq E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      (continuous_apply w)

def pInf : Ad E →+* Cinf E := (infEq E).symm.toRingHom.comp (RingHom.fst (InfiniteAdeleRing E) (Af E))

def sInf : Cinf E →ₙ+* Ad E where
  toFun x := ((infEq E x, 0) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext (map_mul (infEq E) x y) (mul_zero _).symm
  map_zero' := Prod.ext (map_zero (infEq E)) rfl
  map_add' x y := Prod.ext (map_add (infEq E) x y) (add_zero _).symm

def infGL (a : ℕ) : GL (Fin a) (Cinf E) →* GA E a := cornerGL a (sInf E)

def infId : (Cinf E)ˣ →* Ideles E := Units.map (corner (sInf E))

theorem continuous_infId : Continuous (infId E) :=
  Continuous.units_map _ (continuous_const.add ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E)))

variable {E} {a : ℕ}

theorem ad_ext {x y : Ad E} (h1 : pInf E x = pInf E y) (h2 : pFin E x = pFin E y) : x = y :=
  Prod.ext ((infEq E).symm.injective h1) h2

theorem ga_ext {g h : GA E a} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : GeneralLinearGroup.map (pFin E) g = GeneralLinearGroup.map (pFin E) h) : g = h := by
  ext i j
  exact ad_ext (congrArg (fun x : GL (Fin a) (Cinf E) => x i j) h1) (congrArg (fun x : GL (Fin a) (Af E) => x i j) h2)

@[simp] theorem pInf_infGL (y : GL (Fin a) (Cinf E)) : GeneralLinearGroup.map (pInf E) (infGL E a y) = y := by
  rw [infGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x => (infEq E).symm_apply_apply x]; rfl

@[simp] theorem pFin_infGL (y : GL (Fin a) (Cinf E)) : GeneralLinearGroup.map (pFin E) (infGL E a y) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) y

@[simp] theorem pInf_finGL (k : GL (Fin a) (Af E)) : GeneralLinearGroup.map (pInf E) (finGL E a k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => map_zero (infEq E).symm) k

omit [IsTotallyComplex E] in
@[simp] theorem pFin_finGL (k : GL (Fin a) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E a k) = k := by
  rw [finGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x => rfl]; rfl

theorem infGL_mul_finGL (g : GA E a) :
    infGL E a (GeneralLinearGroup.map (pInf E) g) * finGL E a (GeneralLinearGroup.map (pFin E) g) = g :=
  ga_ext (by simp) (by simp)

theorem infGL_comm (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) :
    infGL E a y * finGL E a k = finGL E a k * infGL E a y :=
  ga_ext (by simp) (by simp)

theorem det_infGL (y : GL (Fin a) (Cinf E)) :
    GeneralLinearGroup.det (infGL E a y) = infId E (GeneralLinearGroup.det y) := by
  refine Units.ext (ad_ext ?_ ?_)
  · rw [← det_map, pInf_infGL]
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    simp [h]
  · rw [← det_map, pFin_infGL]
    change _ = (1 : Af E) - 0 + 0
    simp

omit [NumberField E] [IsTotallyComplex E] in

abbrev toL (x : Matrix (Fin a) (Fin a) (Cinf E)) : Lie E a := Matrix.of.symm x

omit [NumberField E] [IsTotallyComplex E] in

def invSet (E : Type) [Field E] (a : ℕ) : Set (Lie E a) := {x | IsUnit (Matrix.of x)}

omit [IsTotallyComplex E] in

theorem contDiff_det : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))

omit [IsTotallyComplex E] in

theorem isOpen_invSet : IsOpen (invSet E a) := by
  have : invSet E a = (fun x : Lie E a => (Matrix.of x).det) ⁻¹' {u | IsUnit u} := by
    ext x; exact Matrix.isUnit_iff_isUnit_det _
  rw [this]
  exact Units.isOpen.preimage contDiff_det.continuous

open Classical in

def chart (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then φ (g * infGL E a h.unit) else 0

theorem chart_val (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart φ g (toL y.val) = φ (g * infGL E a y) := by
  have h : IsUnit (Matrix.of (toL y.val)) := y.isUnit
  have e : h.unit = y := Units.ext h.unit_spec
  rw [chart, dif_pos h, e]

omit [IsTotallyComplex E] in

def lmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (Matrix.of y) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] _)

omit [IsTotallyComplex E] in

def rmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ (Matrix.of y) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] _)

theorem chart_mul (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart φ (g * infGL E a y) = chart φ g ∘ lmul (toL y.val) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = (toL u.val) := hu.symm
    rw [hx, chart_val, mul_assoc, ← map_mul, ← chart_val φ g]
    rfl
  · have h' : ¬ IsUnit (Matrix.of (lmul (toL y.val) x)) := fun h' => h ((Units.isUnit_units_mul y _).1 h')
    rw [Function.comp_apply, chart, chart, dif_neg h, dif_neg h']

theorem chart_rt_inf (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart (fun x => φ (x * infGL E a y)) g = chart φ g ∘ rmul (toL y.val) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = (toL u.val) := hu.symm
    rw [hx, chart_val, mul_assoc, ← map_mul, ← chart_val φ g]
    rfl
  · have h' : ¬ IsUnit (Matrix.of (rmul (toL y.val) x)) := fun h' => h ((Units.isUnit_mul_units _ y).1 h')
    rw [Function.comp_apply, chart, chart, dif_neg h, dif_neg h']

theorem chart_rt_fin (φ : GA E a → ℂ) (g : GA E a) (k : GL (Fin a) (Af E)) :
    chart (fun x => φ (x * finGL E a k)) g = chart φ (g * finGL E a k) := by
  funext x
  simp only [chart, mul_assoc, infGL_comm]

variable (E a) in

def Sm : Submodule ℂ (GA E a → ℂ) where
  carrier := {φ | ∀ g, ContDiffOn ℝ ∞ (chart φ g) (invSet E a)}
  add_mem' := fun {φ ψ} h h' g => ((h g).add (h' g)).congr fun x hx => by
    have hx' : IsUnit (Matrix.of x) := hx
    simp [chart, hx']
  zero_mem' g := contDiffOn_const.congr (f := fun _ => 0) fun x _ => by simp [chart]
  smul_mem' c φ h g := ((h g).const_smul c).congr fun x _ => by simp [chart]

theorem rt_mem_Sm (h : GA E a) (φ : GA E a → ℂ) (hφ : φ ∈ Sm E a) : GlobalTheory.PRep.rightReg ℂ (GA E a) ℂ h φ ∈ Sm E a := by
  intro g
  rw [← infGL_mul_finGL h]
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have e : GlobalTheory.PRep.rightReg ℂ (GA E a) ℂ (infGL E a y * finGL E a k) φ =
      fun x => (fun x => φ (x * finGL E a k)) (x * infGL E a y) := by
    funext x
    exact congrArg φ (mul_assoc _ _ _).symm
  rw [e, chart_rt_inf (fun x => φ (x * finGL E a k)), chart_rt_fin]
  exact (hφ _).comp (rmul (toL y.val)).contDiff.contDiffOn fun x hx => IsUnit.mul hx y.isUnit

variable (E a) in

def rt : Representation ℂ (GA E a) (Sm E a) := GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GA E a) ℂ) (Sm E a) rt_mem_Sm

@[simp] theorem rt_apply (h g : GA E a) (φ : Sm E a) : (rt E a h φ).1 g = φ.1 (g * h) := rfl

omit [NumberField E] [IsTotallyComplex E] in

abbrev oneL (E : Type) [Field E] (a : ℕ) : Lie E a := toL 1

def lieD (X : Lie E a) (φ : GA E a → ℂ) (g : GA E a) : ℂ := fderiv ℝ (chart φ g) (oneL E a) X

theorem contDiffAt_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ContDiffAt ℝ ∞ (chart φ g) x := (hφ g).contDiffAt (isOpen_invSet.mem_nhds hx)

theorem differentiableAt_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    DifferentiableAt ℝ (chart φ g) (oneL E a) := (contDiffAt_chart hφ g isUnit_one).differentiableAt (by simp)

theorem chart_lieD {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (X : Lie E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (lieD X φ) g x = fderiv ℝ (chart φ g) x (rmul X x) := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = (toL u.val) := hu.symm
  subst e
  rw [chart_val, lieD, chart_mul]
  have e1 : lmul (toL u.val) (oneL E a) = toL u.val := mul_one u.val
  rw [fderiv_comp _ (by rw [e1]; exact (contDiffAt_chart hφ g hx).differentiableAt (by simp)) (lmul (toL u.val)).differentiableAt,
    e1, ContinuousLinearMap.fderiv]
  rfl

theorem lieD_mem_Sm (X : Lie E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : lieD X φ ∈ Sm E a := fun g =>
  (((hφ g).fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul X).contDiff.contDiffOn).congr
    fun _ hx => chart_lieD hφ X g hx

variable (E a) in

def lie : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a) where
  toFun X :=
    { toFun := fun φ => ⟨lieD X φ.1, lieD_mem_Sm X φ.2⟩
      map_add' := fun φ ψ => Subtype.ext <| funext fun g => by
        have e : chart (φ.1 + ψ.1) g = chart φ.1 g + chart ψ.1 g := by
          funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
        change fderiv ℝ (chart (φ.1 + ψ.1) g) _ X = _
        rw [e, fderiv_add (differentiableAt_chart φ.2 g) (differentiableAt_chart ψ.2 g)]
        rfl
      map_smul' := fun c φ => Subtype.ext <| funext fun g => by
        have e : chart (c • φ.1) g = c • chart φ.1 g := by
          funext x; simp [chart]
        change fderiv ℝ (chart (c • φ.1) g) _ X = _
        rw [e, fderiv_const_smul (differentiableAt_chart φ.2 g)]
        rfl }
  map_add' X Y := LinearMap.ext fun φ => Subtype.ext <| funext fun g => map_add (fderiv ℝ (chart φ.1 g) _) X Y
  map_smul' c X := LinearMap.ext fun φ => Subtype.ext <| funext fun g => map_smul (fderiv ℝ (chart φ.1 g) _) c X

@[simp] theorem lie_apply (X : Lie E a) (φ : Sm E a) (g : GA E a) : (lie E a X φ).1 g = lieD X φ.1 g := rfl

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.TransposeInverse.TransposeInv
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace Reformulated.TransposeInverseTheory

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

def transposeInvFun (g : GL n R) : GL n R where
  val := ((g⁻¹ : GL n R) : Matrix n n R)ᵀ
  inv := (g : Matrix n n R)ᵀ
  val_inv := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  inv_val := by rw [← transpose_mul, Units.inv_mul, transpose_one]

theorem transposeInvFun_involutive :
    Function.Involutive (transposeInvFun : GL n R → GL n R) := by
  intro g
  apply Units.ext
  exact transpose_transpose _

def transposeInv : GL n R ≃* GL n R where
  toFun := transposeInvFun
  invFun := transposeInvFun
  left_inv := transposeInvFun_involutive
  right_inv := transposeInvFun_involutive
  map_mul' g h := by
    apply Units.ext
    change (((g * h)⁻¹ : GL n R) : Matrix n n R)ᵀ =
      ((g⁻¹ : GL n R) : Matrix n n R)ᵀ * ((h⁻¹ : GL n R) : Matrix n n R)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]

@[simp] theorem coe_transposeInv (g : GL n R) :
    ((transposeInv g : GL n R) : Matrix n n R) = ((g⁻¹ : GL n R) : Matrix n n R)ᵀ := rfl

@[simp] theorem transposeInv_transposeInv (g : GL n R) :
    transposeInv (transposeInv g) = g := transposeInvFun_involutive g

@[simp] theorem transposeInv_symm : (transposeInv : GL n R ≃* GL n R).symm = transposeInv := rfl

end Reformulated.TransposeInverseTheory
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Matrix

namespace GlobalTheory.CuspRep

abbrev BlockIx (a r : ℕ) := {p : Fin a × Fin a // p.1.val < r ∧ r ≤ p.2.val}

section
variable {a : ℕ} {R : Type} [CommRing R]

def nilM {r : ℕ} (x : BlockIx a r → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if h : i.val < r ∧ r ≤ j.val then x ⟨(i, j), h⟩ else 0

theorem nilM_mul_self {r : ℕ} (x : BlockIx a r → R) : nilM x * nilM x = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : l.val < r
  · simp [nilM, not_le.2 h]
  · simp [nilM, h]

def unip {r : ℕ} (x : BlockIx a r → R) : GL (Fin a) R where
  val := 1 + nilM x
  inv := 1 - nilM x
  val_inv := by simp [add_mul, mul_sub, nilM_mul_self]
  inv_val := by simp [sub_mul, mul_add, nilM_mul_self]

end

def invT (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R →* GL (Fin a) R :=
  (Reformulated.TransposeInverseTheory.transposeInv : GL (Fin a) R ≃* GL (Fin a) R).toMonoidHom

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open scoped ContDiff

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
open Classical in

def atEmb (τ : E →+* ℂ) (z : ℂ) : Cinf E :=
  Pi.single (InfinitePlace.mk τ) (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z)

variable (E a) in

def lieS (i j : Fin a) : Cinf E →ₗ[ℝ] Module.End ℂ (Sm E a) :=
  (lie E a).comp (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

theorem lieS_apply (i j : Fin a) (x : Cinf E) : lieS E a i j x = lie E a (toL (Matrix.single i j x)) := rfl

def Eop (τ : E →+* ℂ) (i j : Fin a) : Module.End ℂ (Sm E a) :=
  (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) - Complex.I • lieS E a i j (atEmb τ Complex.I))

def cap (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E a) := Formalism.REAL.qdet (Eop τ) (u + ((a : ℂ) - 1) / 2)

variable (E a) in

def Zalg : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Algebra.adjoin ℂ {z | ∃ τ u, z = cap τ u}

omit [IsTotallyComplex E] in

def chiDet (a : ℕ) (χ : HChar E) : GA E a →* ℂˣ := χ.1.comp GeneralLinearGroup.det

def chiInf (χ : HChar E) : (Cinf E)ˣ →* ℂˣ := χ.1.comp (infId E)

theorem continuous_chiInf (χ : HChar E) : Continuous (chiInf χ) := χ.2.1.comp (continuous_infId E)

def dchi (χ : HChar E) : Cinf E →L[ℝ] ℂ := fderiv ℝ (extZero (chiInf χ)) 1

def expo (χ : HChar E) (τ : E →+* ℂ) : ℂ := (1 / 2 : ℂ) * (dchi χ (atEmb τ 1) - Complex.I * dchi χ (atEmb τ Complex.I))

theorem chart_mul_chi (χ : HChar E) (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => φ x * (chiDet a χ x : ℂˣ)) g =
      fun x => chart φ g x * ((chiDet a χ g : ℂˣ) * extZero (chiInf χ) (Matrix.of x).det) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = toL u.val := hu.symm
    rw [hx, chart_val, chart_val, map_mul, Units.val_mul]
    congr 2
    rw [show chiDet a χ (infGL E a u) = chiInf χ (GeneralLinearGroup.det u) from congrArg χ.1 (det_infGL u)]
    exact (extZero_unit _ _).symm
  · simp [chart, h]

theorem contDiffAt_chi_det (χ : HChar E) {x : Lie E a} (hx : x ∈ invSet E a) :
    ContDiffAt ℝ ∞ (fun x : Lie E a => extZero (chiInf χ) (Matrix.of x).det) x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  exact ContDiffAt.comp (g := extZero (chiInf χ)) x (hu ▸ contDiffAt_extZero _ (continuous_chiInf χ) u)
    contDiff_det.contDiffAt

theorem mul_chi_mem_Sm (χ : HChar E) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) :
    (fun x => φ x * (chiDet a χ x : ℂˣ)) ∈ Sm E a := fun g => by
  rw [chart_mul_chi]
  exact (hφ g).mul (contDiffOn_const.mul fun x hx => (contDiffAt_chi_det χ hx).contDiffWithinAt)

variable (a) in

def mulChi (χ : HChar E) : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun x => φ.1 x * (chiDet a χ x : ℂˣ), mul_chi_mem_Sm χ φ.2⟩
  invFun φ := ⟨fun x => φ.1 x * (chiDet a χ⁻¹ x : ℂˣ), mul_chi_mem_Sm χ⁻¹ φ.2⟩
  map_add' φ ψ := Subtype.ext <| funext fun x => add_mul _ _ _
  map_smul' c φ := Subtype.ext <| funext fun x => mul_assoc _ _ _
  left_inv φ := Subtype.ext <| funext fun x => Units.mul_inv_cancel_right _ _
  right_inv φ := Subtype.ext <| funext fun x => Units.inv_mul_cancel_right _ _

@[simp] theorem mulChi_apply (χ : HChar E) (φ : Sm E a) (g : GA E a) :
    (mulChi a χ φ).1 g = φ.1 g * (chiDet a χ g : ℂˣ) := rfl

omit [IsTotallyComplex E] in

theorem fderiv_det_one (X : Lie E a) :
    fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a) X = (Matrix.of X).trace := by
  have hd : HasFDerivAt (fun x : Lie E a => (Matrix.of x).det)
      (fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (contDiff_det.differentiable (by simp) _).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a))
  rw [one_smul] at h1
  refine h1.unique ?_
  set P := (1 + (Polynomial.X : Polynomial (Cinf E)) • (Matrix.of X).map Polynomial.C).det.divX.divX
  have hr : HasDerivAt (fun t : ℝ => t • (1 : Cinf E)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (1 : Cinf E)
  have hP : DifferentiableAt ℝ (fun t : ℝ => P.eval (t • (1 : Cinf E))) 0 := by
    simp only [Polynomial.eval_eq_sum_range]
    fun_prop
  have h2 := ((hr.const_mul (Matrix.of X).trace).const_add 1).add (hP.hasDerivAt.mul (hr.mul hr))
  simp only [mul_one, zero_smul, Pi.mul_apply, mul_zero, zero_mul, add_zero] at h2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : Matrix.of (oneL E a + t • X) = 1 + (t • (1 : Cinf E)) • Matrix.of X := by
    rw [smul_assoc, one_smul]; rfl
  change (Matrix.of (oneL E a + t • X)).det = _
  rw [e, Matrix.det_one_add_smul, sq]
  rfl

section Conj

open GlobalTheory.Mem.Chr

omit [IsTotallyComplex E]

def conjSrc (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  (existsUnique_conjPl c.symm v).exists.choose

theorem conjPl_conjSrc (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : ConjPl c (conjSrc c v) v :=
  (conjPl_symm_iff c _ _).1 (existsUnique_conjPl c.symm v).exists.choose_spec

theorem conjSrc_injective (c : E ≃+* E) : Function.Injective (conjSrc c) := fun x y h =>
  (existsUnique_conjPl c (conjSrc c x)).unique (conjPl_conjSrc c x) (h ▸ conjPl_conjSrc c y)

def conjLoc (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : (conjSrc c v).adicCompletion E →+* v.adicCompletion E :=
  (exists_finCompl_map c (conjPl_conjSrc c v)).choose

theorem conjLoc_spec (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : Continuous (conjLoc c v) ∧
    (∀ k : E, conjLoc c v (algebraMap E _ k) = algebraMap E _ (c k)) ∧ ∀ x, Valued.v (conjLoc c v x) = Valued.v x :=
  (exists_finCompl_map c (conjPl_conjSrc c v)).choose_spec

def conjFin (c : E ≃+* E) : Af E →+* Af E :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) (conjSrc c) (conjSrc_injective c).tendsto_cofinite (conjLoc c)
    (Filter.Eventually.of_forall fun v x hx => ((conjLoc_spec c v).2.2 x).trans_le hx)

end Conj

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Divisibility.Tuples
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG

namespace Formalism.L2.DIV

section Ideles

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev AfE : Type := E ⊗[F] FiniteAdeleRing (𝓞 F) F

abbrev RInt : Subring (AfE F E) := tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

end Ideles

end Formalism.L2.DIV

end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open scoped ContDiff

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

abbrev Kinf (E : Type) [Field E] (a : ℕ) : Type := Matrix.unitaryGroup (Fin a) (Cinf E)

inductive Op (E : Type) [Field E] [NumberField E] (a : ℕ) : Type
  | fin (k : GL (Fin a) (Af E))
  | cpt (k : Kinf E a)
  | lie (X : Lie E a)

variable (E a) in

def finRep : Representation ℂ (GL (Fin a) (Af E)) (Sm E a) := (rt E a).comp (finGL E a)

variable (E a) in

def cptRep : Representation ℂ (Kinf E a) (Sm E a) := (rt E a).comp ((infGL E a).comp Unitary.toUnits)

def act : Op E a → Module.End ℂ (Sm E a)
  | .fin k => finRep E a k
  | .cpt k => cptRep E a k
  | .lie X => lie E a X

def IsStable (V : Submodule ℂ (Sm E a)) : Prop := ∀ o, ∀ φ ∈ V, act o φ ∈ V

def height (y : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖

structure IsAutForm (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  level : IsOpen {k | finRep E a k φ = φ}
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
  zfin : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
  growth : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N

def ratN (E : Type) [Field E] [NumberField E] (a r : ℕ) : AddSubgroup (BlockIx a r → Ad E) :=
  (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)).range

def IsCuspidal (φ : GA E a → ℂ) : Prop :=
  ∀ r : ℕ, 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g, ∫ x in 𝓕, φ (unip x * g) ∂μ = 0

def IsCuspForm (φ : Sm E a) : Prop := IsAutForm φ ∧ IsCuspidal φ.1

omit [IsTotallyComplex E] in

theorem one_le_height (y : GL (Fin a) (Cinf E)) : 1 ≤ height y := by
  unfold height; linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]

variable (E a) in

@[ext] structure CuspSub where

  V : Submodule ℂ (Sm E a)
  cusp : ∀ φ ∈ V, IsCuspForm φ
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

namespace CuspSub

variable (π π' : CuspSub E a)

def op (o : Op E a) : Module.End ℂ π.V := (act o).restrict (π.stable o)

@[simp] theorem op_val (o : Op E a) (φ : π.V) : (π.op o φ).1 = act o φ.1 := rfl

end CuspSub

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.DataLevel
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

@[reducible] def tensTopL (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)

end Defs

end Formalism.BasicNotions

end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : Prop :=
  NumberField.IsTotallyReal F ∧ NumberField.IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

variable (R : Type) [CommRing R] [Algebra F R]

def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

end Alg

end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

scoped instance topTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (R ⊗[F] E) := moduleTopology R (R ⊗[F] E)

end Top

section Adeles

variable (F : Type) [Field F] [NumberField F]

abbrev Ainf := InfiniteAdeleRing F

end Adeles

end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset
open scoped ENNReal

section Vol

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def IsInfEmb (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ) : Prop :=
  (∀ x : E, θ ((1 : Ainf F) ⊗ₜ[F] x) = τ x) ∧ Continuous fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))

end Vol

end Formalism.MainNotions.StandardLattice
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.AdelicUnitaryTop

section Restricted

theorem secondCountable_restrictedProduct {ι : Type} [Countable ι] (R : ι → Type)
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) : SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hS : ∀ T : Finset ι, cofinite ≤ 𝓟 ((T : Set ι)ᶜ) := fun T =>
    le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  have hsc : ∀ T : Finset ι, SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((T : Set ι)ᶜ)]) :=
    fun T => RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he := fun T : Finset ι => RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  haveI : ∀ T : Finset ι, SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) := fun T =>
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa using h)

end Restricted

section Adeles

variable (F : Type) [Field F] [NumberField F]

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
      fun a b h => HeightOneSpectrum.ext h

theorem t2Space_finiteAdeleRing_of_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

theorem t2Space_infiniteAdeleRing_of_numberField_field : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem t2Space_adeleRing_numberField : T2Space (AdeleRing (𝓞 F) F) :=
  haveI := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Adeles

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem nonempty_homeomorph :
    Nonempty (R ⊗[F] E ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

end Tensor

end GlobalTheory.AdelicUnitaryTop
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing

noncomputable section

namespace GlobalTheory.Idele

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

@[simp] theorem adele_mul_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

@[simp] theorem adele_add_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a + b) v = a v + b v := rfl

@[simp] theorem adele_sub_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a - b) v = a v - b v := rfl

@[simp] theorem adele_one_apply (v : HeightOneSpectrum R) : (1 : 𝔸ᶠ[R, K]) v = 1 := rfl

@[simp] theorem adele_zero_apply (v : HeightOneSpectrum R) : (0 : 𝔸ᶠ[R, K]) v = 0 := rfl

theorem setOf_valued_le_eq (v : HeightOneSpectrum R) (n : ℤ) :
    ∃ c : v.adicCompletion K, Valued.v.restrict c ≠ 0 ∧
      {y : v.adicCompletion K | Valued.v y ≤ exp n} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
  obtain ⟨c, hc⟩ := valuedAdicCompletion_surjective K v (exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact exp_ne_zero hc.symm
  refine ⟨c, by simp [hc0], ?_⟩
  ext y
  simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hc]

theorem isOpen_valued_le (v : HeightOneSpectrum R) (n : ℤ) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ exp n} := by
  obtain ⟨c, hc, h⟩ := setOf_valued_le_eq (K := K) v n
  rw [h]; exact Valued.isOpen_closedBall _ hc

theorem isClosed_valued_le (v : HeightOneSpectrum R) (n : ℤ) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ exp n} := by
  obtain ⟨c, hc, h⟩ := setOf_valued_le_eq (K := K) v n
  rw [h]; exact Valued.isClosed_closedBall _ _

theorem exists_exp_neg_lt {γ : ℤᵐ⁰} (hγ : γ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < γ := by
  refine ⟨(log γ).natAbs + 1, ?_⟩
  conv_rhs => rw [← exp_log hγ]
  rw [exp_lt_exp]
  omega

theorem exists_limit (v : HeightOneSpectrum R) (u : ℕ → v.adicCompletion K)
    (hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ))) :
    ∃ t : v.adicCompletion K, ∀ n : ℕ, Valued.v (t - u n) ≤ exp (-(n : ℤ)) := by
  have hc : CauchySeq u := by
    rw [(Valued.hasBasis_uniformity (v.adicCompletion K) ℤᵐ⁰).cauchySeq_iff']
    intro γ _
    obtain ⟨n, hn⟩ := exists_exp_neg_lt
      (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
    refine ⟨n, fun m hm => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    rw [Valuation.map_sub_swap]
    exact (hu m n hm).trans_lt hn
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨t, fun n => ?_⟩
  refine (isClosed_valued_le (K := K) v (-(n : ℤ))).mem_of_tendsto (ht.sub_const (u n)) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm using hu m n hm

end GlobalTheory.Idele
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem exists_valuation_sub_lt_of_injective (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → F) :
    ∃ w : F, (∀ v ∈ T, v.valuation F (w - c v) ≤ 1) ∧ ∀ v ∉ T, v.valuation F w ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 F)⁰ T c
  set d : 𝓞 F := (b : 𝓞 F) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdK : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * (if v ∈ T then c v else 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨r, hr⟩ := RingHom.mem_rangeS.1 (hb v hv)
      refine ⟨r, ?_⟩
      rw [if_pos hv, hr, Algebra.smul_def]
    · exact ⟨0, by simp [hv]⟩
  choose g hg using hex
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ hfin.toFinset with hS
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors)
    (fun v _ => v.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun i => g i)
  have key : ∀ v ∈ S, v.valuation F (algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d -
      (if v ∈ T then c v else 0)) ≤ 1 := by
    intro v hv
    have h1 : algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0)
        = algebraMap (𝓞 F) F (r - g v) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hg v, sub_div, mul_div_cancel_left₀ _ hdK]
    rw [h1, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff (v.valuation F)).2 hdK)),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_if_neg hd0]
    exact (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
  refine ⟨algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d, fun v hv => ?_, fun v hv => ?_⟩
  · have h := key v (Finset.mem_union_left _ hv)
    rwa [if_pos hv] at h
  · by_cases hvS : v ∈ S
    · have h := key v hvS
      rwa [if_neg hv, sub_zero] at h
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {d} := fun h =>
        hvS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
      have hd1 : v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d)
          (not_lt.1 (fun h => hnd ((v.intValuation_lt_one_iff_dvd d).1 h)))
      rw [map_div₀, hd1, div_one, HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one r

theorem exists_sub_mem_adicCompletionIntegers' (F : Type) [Field F] [NumberField F]
    (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ w : F, ∀ v, z v - algebraMap F (FiniteAdeleRing (𝓞 F) F) w v ∈
      v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ z v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 z.2
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : F,
      z v - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro v
    have hdense : DenseRange (fun c : F => (c : v.adicCompletion F)) :=
      HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)
    have hopen : IsOpen {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} :=
      (Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)
    have hne : z v ∈ {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} := by
      show z v - z v ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact zero_mem _
    exact hdense.exists_mem_open hopen ⟨z v, hne⟩
  choose c hc using hc
  obtain ⟨w, hw1, hw2⟩ := exists_valuation_sub_lt_of_injective F hfin.toFinset c
  refine ⟨w, fun v => ?_⟩
  rw [FiniteAdeleRing.algebraMap_apply]
  by_cases hv : v ∈ hfin.toFinset
  · have h1 : ((c v : F) : v.adicCompletion F) =
        ((c v - w : F) : v.adicCompletion F) + (w : v.adicCompletion F) := by
      rw [← HeightOneSpectrum.adicCompletion.coe_add, sub_add_cancel]
    have h2 : z v - (w : v.adicCompletion F) =
        (z v - (c v : v.adicCompletion F)) + ((c v - w : F) : v.adicCompletion F) := by
      rw [h1]; ring
    rw [h2]
    refine add_mem (hc v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap]
    exact hw1 v hv
  · have hz : z v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    refine sub_mem hz ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hw2 v hv

theorem exists_eq_algebraMap_add_nsmul (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N)
    (y : FiniteAdeleRing (𝓞 F) F) :
    ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      y = algebraMap F _ x + N • a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨w, hw⟩ := exists_sub_mem_adicCompletionIntegers' F
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y)
  refine ⟨N * w, algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y -
    algebraMap F (FiniteAdeleRing (𝓞 F) F) w, fun v => hw v, ?_⟩
  have hA : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hN', map_one]
  rw [nsmul_eq_mul, map_mul, map_natCast]
  linear_combination (-y) * hA

theorem strong_approximation_mod_nat : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → (∀ y : FiniteAdeleRing (𝓞 F) F, ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ x + N • a) ∧ ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) → ∃ (x : 𝓞 F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ (x : F) + N • a := by
  intro F _ _ N hN
  refine ⟨exists_eq_algebraMap_add_nsmul F N hN, fun y hy => ?_⟩
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F N hN y
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1 := by
    intro v
    have hNa : (N • a) v ∈ v.adicCompletionIntegers F := by
      rw [show (N • a) v = N • a v from rfl]
      exact nsmul_mem (ha v) N
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) x + N • a) v =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + (N • a) v := rfl
    have h := sub_mem (hy v) hNa
    rw [e, add_sub_cancel_right, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x hx
  subst hr
  exact ⟨r, a, ha, rfl⟩

end GlobalTheory.AdLat
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Filter Topology
open scoped ComplexOrder

variable {D}

variable (D)

def entN {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (a b : ℕ) : A :=
  if h : a < N ∧ b < N then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

end Formalism.MainNotions.ArithmeticCylinders
end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.MainNotions.PrimeDegreeVariant

open Formalism.BasicNotions MvPolynomial

section Abstract

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

structure GoodSet (K : Type) [Field K] (G : Type) [Group G] where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  W : S → Type
  [acgW : ∀ s, AddCommGroup (W s)]
  [modW : ∀ s, Module K (W s)]
  [fdW : ∀ s, FiniteDimensional K (W s)]
  [ntW : ∀ s, Nontrivial (W s)]
  tau : ∀ s, Representation K G (W s)

  irr : ∀ s, Function.Surjective (tau s).asAlgebraHom

  inj : Function.Injective fun s g => LinearMap.trace K (W s) (tau s g)

attribute [instance] GoodSet.finS GoodSet.decS GoodSet.acgW GoodSet.modW GoodSet.fdW GoodSet.ntW

end Abstract

end Formalism.MainNotions.PrimeDegreeVariant
end
end

section
-- module Solutions.AlpoGe.Formalism.DoubleCosetMeasures.Statement
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open MeasureTheory Matrix

namespace Formalism.DoubleCosetMeasures

section Integral

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

instance instMeasGL (n : ℕ) : MeasurableSpace (GL (Fin n) K) := borel _
instance instBorelGL (n : ℕ) : BorelSpace (GL (Fin n) K) := ⟨rfl⟩

end Integral

end Formalism.DoubleCosetMeasures
end
end

section
-- module Solutions.AlpoGe.Formalism.DoubleCosetMeasures.StatementZ
attribute [-instance] _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open MeasureTheory Matrix ComplexConjugate

namespace Formalism.DoubleCosetMeasures

instance instMeasMat {m n F : Type} [MeasurableSpace F] : MeasurableSpace (Matrix m n F) :=
  inferInstanceAs (MeasurableSpace (m → n → F))

end Formalism.DoubleCosetMeasures
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV Formalism.FrobeniusOrbits

structure Fields where

  F : Type

  E : Type

  K : Type
  [fieldF : Field F]
  [nfF : NumberField F]
  [fieldE : Field E]
  [nfE : NumberField E]
  [fieldK : Field K]
  [nfK : NumberField K]
  [algFE : Algebra F E]

  [starE : StarRing E]

  [starK : StarRing K]

  Tau : Type
  [ftTau : Fintype Tau]
  [deTau : DecidableEq Tau]

  emb : Tau → (E →+* K)

attribute [instance] Fields.fieldF Fields.nfF Fields.fieldE Fields.nfE Fields.fieldK Fields.nfK Fields.algFE
  Fields.starE Fields.starK Fields.ftTau Fields.deTau

structure Primes (X : Fields) where

  cond : ℕ

  g : Fin 2 → ℕ

  piG : Fin 2 → 𝓞 X.E

  Word : Type
  [ftWord : Fintype Word]
  [deWord : DecidableEq Word]

  T : Word → ℕ

  piT : Word → 𝓞 X.E

attribute [instance] Primes.ftWord Primes.deWord

end Formalism.L2.Col
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Columns.StdLatUnimodular
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

section RedLemmas

variable {E : Type} [Field E] [NumberField E]

instance instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions (P : HeightOneSpectrum (𝓞 E)) : IsDomain (𝓞 E ⧸ P.asIdeal) :=
  Ideal.Quotient.isDomain _

end RedLemmas

end Formalism.L2.Col
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Columns.DecoFin
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

section Orbits

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

instance finite_quot (P : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ P.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot

end Orbits

end Formalism.L2.Col
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Divisibility.ClassSum
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

structure CSD (K : Type) [Field K] [NumberField K] [StarRing K] where

  Cl : Type
  [finCl : Fintype Cl]

  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]

  ιV : Type
  [finιV : Fintype ιV]
  [decιV : DecidableEq ιV]
  bV : Basis ιV K V

  pair : V →ₗ⋆[K] V →ₗ[K] K

  Gam : Cl → Type
  [grpGam : ∀ c, Group (Gam c)]
  [finGam : ∀ c, Fintype (Gam c)]

  ρ : ∀ c, Gam c →* Module.End K V

  Nab : Cl → Submodule (𝓞 K) V

  Del : Cl → Submodule (𝓞 K) V

attribute [instance] CSD.finCl CSD.addV CSD.modV CSD.modOV CSD.towV CSD.finιV CSD.decιV CSD.grpGam
  CSD.finGam

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

instance instFiniteDimensionalV : FiniteDimensional K S.V := Module.Finite.of_basis S.bV

end CSD

end Formalism.L2.DIV
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

structure GSD (K : Type) [Field K] [NumberField K] [StarRing K] where

  G : Type
  [grpG : Group G]

  D : Type
  [actD : MulAction G D]

  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]

  ιV : Type
  [finιV : Fintype ιV]
  [decιV : DecidableEq ιV]
  bV : Basis ιV K V

  pair : V →ₗ⋆[K] V →ₗ[K] K

  ρ : G →* Module.End K V

  Nab : D → Submodule (𝓞 K) V

  Del : D → Submodule (𝓞 K) V

attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure GFam (K : Type) [Field K] [NumberField K] [StarRing K] where

  β : Type
  [finβ : Fintype β]
  [decβ : DecidableEq β]

  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]
  ιV : Type
  [finιV : Fintype ιV]
  [decιV : DecidableEq ιV]
  bV : Basis ιV K V

  pair : V →ₗ⋆[K] V →ₗ[K] K

  G : β → Type
  [grpG : ∀ b, Group (G b)]

  D : β → Type
  [actD : ∀ b, MulAction (G b) (D b)]

  ρ : ∀ b, G b →* Module.End K V
  Nab : ∀ b, D b → Submodule (𝓞 K) V
  Del : ∀ b, D b → Submodule (𝓞 K) V

attribute [instance] GFam.finβ GFam.decβ GFam.addV GFam.modV GFam.modOV GFam.towV GFam.finιV GFam.decιV GFam.grpG
  GFam.actD

namespace GFam

variable (F : GFam K)

@[reducible] def mem (b : F.β) : GSD K where
  G := F.G b
  D := F.D b
  V := F.V
  ιV := F.ιV
  bV := F.bV
  pair := F.pair
  ρ := F.ρ b
  Nab := F.Nab b
  Del := F.Del b

end GFam

@[reducible] def GSD.toFam (S : GSD K) : GFam K where
  β := Unit
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  G := fun _ => S.G
  D := fun _ => S.D
  ρ := fun _ => S.ρ
  Nab := fun _ => S.Nab
  Del := fun _ => S.Del

end Formalism.L2.Col
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.IndefiniteForms.IndefSide
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.L2.Indef

structure DefBase (K : Type) [Field K] [NumberField K] [StarRing K] where

  K0 : Subfield K

  v0 : InfinitePlace K

  Tup : Type

  μ0 : Tup

  Ix : Type

  fIx : Fintype Ix

  J : Type

  fJ : Fintype J

attribute [instance] DefBase.fIx DefBase.fJ

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure DefAmb (Bs : DefBase K) where

  FR : Bs.Tup → Type

  aR : ∀ t, AddCommGroup (FR t)

  mR : ∀ t, Module K (FR t)

  OpR : Bs.Tup → Type

  opR : ∀ t, OpR t → Module.End K (FR t)

  ZHR : ∀ t, Submodule K (FR t)

  FL : Bs.J → Bs.Tup → Type

  aL : ∀ j t, AddCommGroup (FL j t)

  mL : ∀ j t, Module K (FL j t)

  OpL : Bs.J → Bs.Tup → Type

  opL : ∀ j t, OpL j t → Module.End K (FL j t)

  ZHL : ∀ j t, Submodule K (FL j t)

attribute [instance] DefAmb.aR DefAmb.mR DefAmb.aL DefAmb.mL

@[ext] structure IndefNum (Bs : DefBase K) where

  F0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  J0 : Bs.Tup → HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  E1 : Bs.J → ℝ

  l3 : Bs.J → ℝ

  l6 : Bs.J → ℝ

  hh : ℝ

  la : ℝ

  de : ℝ

end Formalism.L2.Indef
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.IndefiniteReal.Bridge
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.DIV

section Pres

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure CoefDatG (Γ : Type) [Group Γ] where
  W : Type
  [nW : NormedAddCommGroup W]
  [iW : InnerProductSpace ℂ W]
  ρ : Γ →* Module.End ℂ W

attribute [instance] CoefDatG.nW CoefDatG.iW

end Pres

end Formalism.IndefR.Bridge
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.GlobalTheory.DivPassage
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage

open Formalism.L2.Indef

structure LevelAmb (K : Type) [Field K] [NumberField K] [StarRing K] (D0 D1 : ℕ) where

  Dg : ℕ

  Xg : InfinitePlace K → Matrix (Fin Dg) (Fin Dg) ℂ

  Rg : Submodule (𝓞 K) (Fin Dg → K)

  ep0 : Matrix (Fin Dg) (Fin Dg) K

  ep1 : Matrix (Fin Dg) (Fin Dg) K

  S : Type

  fS : Fintype S

  es : S → Matrix (Fin Dg) (Fin Dg) K

  nS : S → ℕ

  nbar : ℝ

  G : ℕ

  h0 : ℕ

  h1 : ℕ

  ι0 : Matrix (Fin Dg) (Fin D0) K

  ι1 : Matrix (Fin Dg) (Fin D1) K

attribute [instance] LevelAmb.fS

end Formalism.L2.GlobalTheoryTheory.DivPassage
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure CxData {Bs : DefBase K} (A : DefAmb Bs) where

  FC : Bs.Tup → Type
  [nFC : ∀ t, NormedAddCommGroup (FC t)]
  [iFC : ∀ t, InnerProductSpace ℂ (FC t)]
  [dFC : ∀ t, FiniteDimensional ℂ (FC t)]

  jR : ∀ t, A.FR t →ₛₗ[Bs.v0.embedding] FC t

  EE : Type
  [nEE : NormedAddCommGroup EE]
  [iEE : InnerProductSpace ℂ EE]
  [dEE : FiniteDimensional ℂ EE]

  Θ : ∀ t, FC t →ₗ[ℂ] EE

  EEp : Bs.Ix → Submodule ℂ EE

  EEl : Bool → Submodule ℂ EE

  FLC : Bs.J → Bs.Tup → Type
  [nFLC : ∀ j t, NormedAddCommGroup (FLC j t)]
  [iFLC : ∀ j t, InnerProductSpace ℂ (FLC j t)]
  [dFLC : ∀ j t, FiniteDimensional ℂ (FLC j t)]

  jL : ∀ j t, A.FL j t →ₛₗ[Bs.v0.embedding] FLC j t

  W : Bs.J → Type
  [nW : ∀ j, NormedAddCommGroup (W j)]
  [iW : ∀ j, InnerProductSpace ℂ (W j)]
  [fW : ∀ j, FiniteDimensional ℂ (W j)]

  θ' : ∀ j t, FLC j t →ₗ[ℂ] W j

  Wp : ∀ j, Bs.Ix → Submodule ℂ (W j)

  dW : Bool → Bs.J → ℕ

  WC : Bool → Bs.J → InfinitePlace K → Type
  [nWC : ∀ b j v, NormedAddCommGroup (WC b j v)]
  [iWC : ∀ b j v, InnerProductSpace ℂ (WC b j v)]

  bW : ∀ b j v, Fin (dW b j) → WC b j v

  eW : ∀ b j, WC b j Bs.v0 →ₗ[ℂ] W j

  M : ∀ b j, Submodule (𝓞 K) (Fin (dW b j) → K)

  nP : Bool → ℝ

  μ : HeightOneSpectrum (𝓞 K) → Bs.Tup

  Tw : Finset (HeightOneSpectrum (𝓞 K))

  κ : InfinitePlace K → ℝ

  lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ

  err0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

attribute [instance] CxData.nFC CxData.iFC CxData.dFC CxData.nEE CxData.iEE CxData.dEE CxData.nFLC CxData.iFLC CxData.dFLC
  CxData.nW CxData.iW CxData.fW CxData.nWC CxData.iWC

end Formalism.IndefR.Cx
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Columns.GSetLemmas
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace GSD

variable (S : GSD K)

@[reducible] def restr (T : SubMulAction S.G S.D) : GSD K where
  G := S.G
  D := T
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab := fun t => S.Nab (t : S.D)
  Del := fun t => S.Del (t : S.D)

end GSD

end Formalism.L2.Col
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Columns.LevGCount
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Matrix Finset IsDedekindDomain NumberField

namespace Formalism.L2.Col

instance finite_res (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ w.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot

end Formalism.L2.Col
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Module MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section Chains

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure Cpl (S : GSD K) where

  Yb : Type
  [actY : MulAction S.G Yb]

  ys : S.D → Set Yb
  fin : ∀ d, (ys d).Finite
  equiv : ∀ (g : S.G) (d : S.D) (y : Yb), g • y ∈ ys (g • d) ↔ y ∈ ys d

attribute [instance] Cpl.actY

end Chains

end Formalism.L2.Col
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.DIV Formalism.L2.Indef Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

structure HMod (X : Type) [AddCommGroup X] [Module ℂ X] where

  H : Type
  [nH : NormedAddCommGroup H]
  [iH : InnerProductSpace ℂ H]
  [fH : FiniteDimensional ℂ H]

  e : H →ₗ[ℂ] X

attribute [instance] HMod.nH HMod.iH HMod.fH

end Formalism.IndefR.Links

end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.finite_places_over (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).preimage
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.places_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by
  intro F E _ _ _ _ _
  refine ⟨fun S => ?_, fun v => ?_, fun w => ?_⟩
  · have hfin : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
      have hU : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S} =
          ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
        ext w; simp
      rw [hU]
      exact S.finite_toSet.biUnion fun v _ => _root_.GlobalTheory.QNorm.finite_places_over F E v
    exact ⟨hfin.toFinset, fun w => by simp⟩
  · obtain ⟨P, hmax, hover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 E)
    have hne : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
    exact ⟨⟨P, hmax.isPrime, hne⟩, HeightOneSpectrum.ext hover.over.symm⟩
  · haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    refine ⟨(w.under (𝓞 F)).asIdeal.ramificationIdx' w.asIdeal, Nat.pos_of_ne_zero ?_,
      fun x => ?_⟩
    · refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ w.isPrime Ideal.map_comap_le
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact (w.under (𝓞 F)).ne_bot
    · exact (HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 F)) w x).symm

end GlobalTheory.QNorm
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.AdLat

variable {F : Type} [Field F] [NumberField F]

theorem valued_natCast_eq (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) = v.intValuation (N : 𝓞 F) := by
  have h : (N : v.adicCompletion F)
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (N : 𝓞 F)) := by simp
  rw [h, ← v.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) ≤ 1 := by
  rw [valued_natCast_eq]; exact v.intValuation_le_one _

theorem valued_natCast_ne_zero (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    Valued.v (N : v.adicCompletion F) ≠ 0 := by
  rw [valued_natCast_eq]
  exact v.intValuation_ne_zero _ (by exact_mod_cast hN.ne')

theorem exists_nat_valued_pow_le (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, Valued.v ((p ^ n : ℕ) : v.adicCompletion F) ≤ exp (-(n : ℤ)) := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, fun n => ?_⟩
  · exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · rw [valued_natCast_eq, HeightOneSpectrum.intValuation_le_pow_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) n

theorem eq_zero_of_valued_le_natCast (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F)
    (h : ∀ N : ℕ, 0 < N → Valued.v y ≤ Valued.v (N : v.adicCompletion F)) : y = 0 := by
  by_contra hy
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (γ := Valued.v y) (by simpa using hy)
  exact absurd ((h _ (pow_pos hp n)).trans (hpn n)) (not_le.2 hn)

theorem exists_limit_of_compatible (v : HeightOneSpectrum (𝓞 F)) (x : ℕ → v.adicCompletion F)
    (h : ∀ N m : ℕ, 0 < N → 0 < m →
      Valued.v (x (N * m) - x N) ≤ Valued.v (N : v.adicCompletion F)) :
    ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
      Valued.v (t - x N) ≤ Valued.v (N : v.adicCompletion F) := by
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit (K := F) v (fun n => x (p ^ n)) (fun m n hnm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add]
    exact (h _ _ (pow_pos hp n) (pow_pos hp k)).trans (hpn n))
  refine ⟨t, fun N hN => ?_⟩
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (valued_natCast_ne_zero v hN)
  have h1 := (ht n).trans hn.le
  have h2 := ((h _ _ (pow_pos hp n) hN).trans (hpn n)).trans hn.le
  have h3 := h _ _ hN (pow_pos hp n)
  have e : t - x N = (t - x (p ^ n)) - (x (p ^ n * N) - x (p ^ n)) + (x (N * p ^ n) - x N) := by
    rw [mul_comm N]; ring
  rw [e]
  exact Valuation.map_add_le _ (Valuation.map_sub_le _ h1 h2) h3

theorem valued_nsmul_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : a v ∈ v.adicCompletionIntegers F) :
    Valued.v ((N • a) v) ≤ Valued.v (N : v.adicCompletion F) := by
  have : (N • a) v = N • a v := rfl
  rw [this, nsmul_eq_mul, map_mul]
  exact mul_le_of_le_one_right' ha

theorem integral_finiteAdele_complete_separated :
    ∀ (F : Type) [Field F] [NumberField F], (∀ y : FiniteAdeleRing (𝓞 F) F, (∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = N • a) → y = 0) ∧ ∀ x : ℕ → FiniteAdeleRing (𝓞 F) F, (∀ N v, x N v ∈ v.adicCompletionIntegers F) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x (N * m) = x N + N • a) → ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = x N + N • a := by
  intro F _ _
  refine ⟨fun y hy => ?_, fun x hx h => ?_⟩
  · refine DFunLike.ext _ _ fun v => ?_
    refine eq_zero_of_valued_le_natCast v (y v) fun N hN => ?_
    obtain ⟨a, ha, rfl⟩ := hy N hN
    exact valued_nsmul_le v N a (ha v)
  · have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
        Valued.v (t - x N v) ≤ Valued.v (N : v.adicCompletion F) := fun v => by
      refine exists_limit_of_compatible v (fun N => x N v) fun N m hN hm => ?_
      obtain ⟨a, ha, e⟩ := h N m hN hm
      have : x (N * m) v - x N v = (N • a) v := by
        rw [e]
        exact add_sub_cancel_left (x N v) ((N • a) v)
      rw [this]
      exact valued_nsmul_le v N a (ha v)
    choose t ht using key
    have ht1 : ∀ v, t v ∈ v.adicCompletionIntegers F := fun v => by
      have h1 : Valued.v (t v - x 1 v) ≤ 1 := (ht v 1 one_pos).trans (valued_natCast_le_one v 1)
      have h2 : t v - x 1 v ∈ v.adicCompletionIntegers F := h1
      simpa using add_mem h2 (hx 1 v)
    refine ⟨⟨t, Filter.Eventually.of_forall ht1⟩, fun N hN => ?_⟩
    have hq : ∀ v, (t v - x N v) / (N : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
      fun v => by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ (ht v N hN) zero_le'
    refine ⟨⟨fun v => (t v - x N v) / (N : v.adicCompletion F),
      Filter.Eventually.of_forall hq⟩, hq, ?_⟩
    refine DFunLike.ext _ _ fun v => ?_
    change t v = x N v + N • ((t v - x N v) / (N : v.adicCompletion F))
    have hN0 : (N : v.adicCompletion F) ≠ 0 := fun h0 =>
      valued_natCast_ne_zero v hN (by rw [h0, map_zero])
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hN0]
    ring

end GlobalTheory.AdLat
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV Formalism.UG Formalism.UG.P
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_locMap (F : Type) [Field F] [NumberField F] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) :
    ∃ φ : (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E,
      (∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ (n : ℕ) (a : (P.under (𝓞 F)).adicCompletion F), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
        Valued.v (φ a) ≤ WithZero.exp (-(n : ℤ)) := by
  have : P.asIdeal.LiesOver (P.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E (P.under (𝓞 F))
    P).continuous
  let φ : (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv F (P.under (𝓞 F))).toRingHom
  have hφ : ∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E P).comp
      ((UniformSpace.Completion.continuous_map (f := algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion F (P.under (𝓞 F))))
  refine ⟨φ, hφ, fun n a ha => ?_⟩
  have hd : Dense (Set.range (algebraMap F ((P.under (𝓞 F)).adicCompletion F))) :=
    HeightOneSpectrum.denseRange_algebraMap (K := F) (P.under (𝓞 F))
  have h1 := hd.open_subset_closure_inter
    (GlobalTheory.Idele.isOpen_valued_le (K := F) (P.under (𝓞 F)) (-(n : ℤ))) ha
  have hcl := (GlobalTheory.Idele.isClosed_valued_le (K := E) P (-(n : ℤ))).preimage hcont
  refine closure_minimal ?_ hcl h1
  rintro _ ⟨hx, x, rfl⟩
  change Valued.v (φ _) ≤ _
  replace hx : Valued.v (algebraMap F ((P.under (𝓞 F)).adicCompletion F) x) ≤ _ := hx
  rw [hφ, levelaf_valued_algebraMap]
  rw [levelaf_valued_algebraMap] at hx
  obtain ⟨e, he, h⟩ := (GlobalTheory.QNorm.places_over F E).2.2 P
  rw [h]
  refine le_trans ?_ hx
  refine pow_le_of_le_one zero_le' (hx.trans ?_) he.ne'
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

variable (F) in

def locMap (P : HeightOneSpectrum (𝓞 E)) :
    (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E := (exists_locMap F P).choose

theorem locMap_algebraMap (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    locMap F P (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) :=
  (exists_locMap F P).choose_spec.1 x

theorem locMap_valued (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (a : (P.under (𝓞 F)).adicCompletion F)
    (ha : Valued.v a ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (locMap F P a) ≤ WithZero.exp (-(n : ℤ)) :=
  (exists_locMap F P).choose_spec.2 n a ha

theorem locMap_int (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F)
    (ha : a ∈ (P.under (𝓞 F)).adicCompletionIntegers F) :
    locMap F P a ∈ P.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
  simpa using locMap_valued P 0 a (by simpa using ha)

variable (F E) in

def adMap : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E where
  toFun a := ⟨fun P => locMap F P (a (P.under (𝓞 F))), by
    have h : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
      Filter.eventually_cofinite.1 a.2
    refine Filter.eventually_cofinite.2 ((h.biUnion
      (fun v _ => GlobalTheory.QNorm.finite_places_over F E v)).subset fun P hP => ?_)
    simp only [Set.mem_iUnion]
    exact ⟨P.under (𝓞 F), fun hh => hP (locMap_int P _ hh), rfl⟩⟩
  map_one' := FiniteAdeleRing.ext _ fun P => map_one (locMap F P)
  map_mul' a b := FiniteAdeleRing.ext _ fun P => map_mul (locMap F P) _ _
  map_zero' := FiniteAdeleRing.ext _ fun P => map_zero (locMap F P)
  map_add' a b := FiniteAdeleRing.ext _ fun P => map_add (locMap F P) _ _

theorem adMap_algebraMap (x : F) :
    adMap F E (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) :=
  FiniteAdeleRing.ext _ fun P => locMap_algebraMap P x

theorem adMap_int {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ intAd F) : adMap F E a ∈ intAd E :=
  fun P => locMap_int P _ (ha _)

variable (F E) in
theorem exists_toAd : ∃ ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E,
    ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a := by
  letI : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
    ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] FiniteAdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : FiniteAdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 E) E :=
    ⟨adMap F E, fun x => adMap_algebraMap x⟩
  exact ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun x a => rfl⟩

theorem exists_nat_mul_integral {K : Type} [Field K] [NumberField K] (s : Finset K) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ s, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = D • x := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := K) s
  refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), fun x hx => ?_⟩
  have hi : IsIntegral ℤ ((y * y).natAbs • x) := by
    rw [← natCast_zsmul, Int.natAbs_of_nonneg (mul_self_nonneg y), mul_smul]
    exact (h x hx).smul y
  exact ⟨⟨_, hi⟩, rfl⟩

theorem exists_int_of_mem {K : Type} [Field K] [NumberField K] {x : K}
    (hx : algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ intAd K) :
    ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = x := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x fun v => ?_
  rw [← levelaf_valued_algebraMap]
  exact hx v

theorem algebraMap_int_mem {K : Type} [Field K] [NumberField K] (r : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K r) ∈ intAd K :=
  levelaf_int_mem r

theorem exists_approx (y : AfE F E) : ∃ x : E, ∃ r ∈ RInt F E, y = x ⊗ₜ[F] 1 + r := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add y y' hy hy' =>
    obtain ⟨x, r, hr, rfl⟩ := hy
    obtain ⟨x', r', hr', rfl⟩ := hy'
    exact ⟨x + x', r + r', add_mem hr hr', by rw [TensorProduct.add_tmul]; abel⟩
  | tmul e a =>
    obtain ⟨m, hm, h⟩ := exists_nat_mul_integral ({e} : Finset E)
    obtain ⟨o, ho⟩ := h e (Finset.mem_singleton_self e)
    obtain ⟨k, a', ha', rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F m hm).1 a
    refine ⟨k • e, _, levelaf_tmul_mem o ha', ?_⟩
    rw [TensorProduct.tmul_add, ho, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

def coord (i : Fin (Module.finrank F E)) : AfE F E →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ LinearMap.rTensor _ ((Module.finBasis F E).coord i)

theorem coord_tmul (i : Fin (Module.finrank F E)) (x : E) (a : FiniteAdeleRing (𝓞 F) F) :
    coord i (x ⊗ₜ[F] a) = (Module.finBasis F E).repr x i • a := by
  simp [coord]

theorem sum_coord (y : AfE F E) : ∑ i, Module.finBasis F E i ⊗ₜ[F] coord i y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hy']
  | tmul x a =>
    simp only [coord_tmul, ← TensorProduct.smul_tmul]
    rw [← TensorProduct.sum_tmul, Module.Basis.sum_repr]

variable (F E) in
theorem exists_coord_denom : ∃ D : ℕ, 0 < D ∧ ∀ y ∈ RInt F E, ∀ i, D • coord i y ∈ intAd F := by
  classical
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨D, hD, h⟩ := exists_nat_mul_integral (Finset.univ.image
    fun p : Fin m × Fin (Module.finrank F E) =>
      (Module.finBasis F E).repr (algebraMap (𝓞 E) E (g p.1)) p.2)
  refine ⟨D, hD, fun y hy i => ?_⟩
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp g hg hy
  rw [map_sum, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  obtain ⟨o, ho⟩ := h _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))
  rw [coord_tmul, ← smul_assoc, ← ho, Algebra.smul_def]
  exact mul_mem (algebraMap_int_mem o) (hr j)

theorem eq_zero_of_nsmul_eq_zero {K A : Type} [Field K] [CharZero K] [AddCommGroup A] [Module K A]
    {D : ℕ} (hD : 0 < D) {a : A} (h : D • a = 0) : a = 0 := by
  rw [← Nat.cast_smul_eq_nsmul K] at h
  exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hD.ne')

theorem eq_zero_of_divisible (y : AfE F E)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ RInt F E, y = N • w) : y = 0 := by
  obtain ⟨D, hD, hc⟩ := exists_coord_denom F E
  rw [← sum_coord y]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : D • coord i y = 0 := by
    refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).1 _ fun N hN => ?_
    obtain ⟨w, hw, rfl⟩ := h N hN
    exact ⟨_, hc w hw i, by rw [map_nsmul, smul_comm]⟩
  rw [eq_zero_of_nsmul_eq_zero (K := F) hD this, TensorProduct.tmul_zero]

theorem exists_limit (x : ℕ → AfE F E) (hx : ∀ N, x N ∈ RInt F E)
    (h : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ RInt F E, x (N * m) = x N + N • w) :
    ∃ D : ℕ, 0 < D ∧ ∃ y : AfE F E, ∀ N : ℕ, 0 < N → ∃ w ∈ RInt F E, y = D • x N + N • w := by
  classical
  obtain ⟨D, hD, hc⟩ := exists_coord_denom F E
  obtain ⟨M, hM, hb⟩ := exists_nat_mul_integral (Finset.univ.image (Module.finBasis F E))
  choose o ho using fun i => hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have key : ∀ i, ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = D • coord i (x N) + N • a := by
    intro i
    refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).2 (fun N => D • coord i (x N))
      (fun N => hc _ (hx N) i) fun N k hN hk => ?_
    obtain ⟨w, hw, e⟩ := h N k hN hk
    exact ⟨_, hc w hw i, by rw [e, map_add, map_nsmul, smul_add, smul_comm D N]⟩
  choose y hy using key
  refine ⟨M * D, Nat.mul_pos hM hD, ∑ i, algebraMap (𝓞 E) E (o i) ⊗ₜ[F] y i, fun N hN => ?_⟩
  choose a ha hya using fun i => hy i N hN
  refine ⟨∑ i, algebraMap (𝓞 E) E (o i) ⊗ₜ[F] a i,
    sum_mem fun i _ => levelaf_tmul_mem _ (ha i), ?_⟩
  conv_rhs => rw [← sum_coord (x N)]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hya i, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ho,
    ← TensorProduct.smul_tmul', smul_smul, mul_comm D M]

section
variable {ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E}
  (hι : ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a)
include hι

theorem map_tmul_one (x : E) : ι (x ⊗ₜ[F] 1) = algebraMap E _ x := by
  rw [hι, map_one, mul_one]

theorem map_mem_int {y : AfE F E} (hy : y ∈ RInt F E) : ι y ∈ intAd E := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp g hg hy
  rw [map_sum]
  refine sum_mem fun j _ => ?_
  rw [hι]
  exact mul_mem (algebraMap_int_mem _) (adMap_int (hr j))

theorem mem_int_of_map {y : AfE F E} (hy : ι y ∈ intAd E) : y ∈ RInt F E := by
  obtain ⟨x, r, hr, rfl⟩ := exists_approx y
  rw [map_add, map_tmul_one hι] at hy
  have h1 := sub_mem hy (map_mem_int hι hr)
  rw [add_sub_cancel_right] at h1
  obtain ⟨o, rfl⟩ := exists_int_of_mem h1
  exact add_mem (levelaf_tmul_mem o (one_mem _)) hr

theorem map_injective : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  refine eq_zero_of_divisible y fun N hN => ⟨(N : E)⁻¹ ⊗ₜ[F] 1 * y, mem_int_of_map hι ?_, ?_⟩
  · rw [map_mul, hy, mul_zero]; exact zero_mem _
  · rw [← smul_mul_assoc, TensorProduct.smul_tmul', nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), ← Algebra.TensorProduct.one_def, one_mul]

theorem exists_map_eq_of_int {s : FiniteAdeleRing (𝓞 E) E} (hs : s ∈ intAd E) : ∃ y, ι y = s := by
  have h0 : ∀ N : ℕ, ∃ (x : 𝓞 E) (a : FiniteAdeleRing (𝓞 E) E), a ∈ intAd E ∧
      (0 < N → s = algebraMap E _ (algebraMap (𝓞 E) E x) + N • a) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, 0, zero_mem _, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨x, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E N hN).2 s hs
      exact ⟨x, a, ha, fun _ => e⟩
  choose x a ha hxa using h0
  have hinv : ∀ N : ℕ, 0 < N → ∀ z : FiniteAdeleRing (𝓞 E) E,
      algebraMap E _ (N : E)⁻¹ * (N • z) = z := by
    intro N hN z
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)),
      ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one, one_mul]
  obtain ⟨D, hD, y, hy⟩ := exists_limit (F := F)
    (fun N => algebraMap (𝓞 E) E (x N) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
    (fun N => levelaf_tmul_mem _ (one_mem _)) (fun N m hN hm => by
      have e1 := hxa N hN
      have e2 := hxa (N * m) (Nat.mul_pos hN hm)
      have e3 : algebraMap E (FiniteAdeleRing (𝓞 E) E) ((N : E)⁻¹ *
          (algebraMap (𝓞 E) E (x (N * m)) - algebraMap (𝓞 E) E (x N))) = a N - m • a (N * m) := by
        rw [map_mul, ← hinv N hN (a N - m • a (N * m)), map_sub]
        congr 1
        rw [smul_sub, smul_smul]
        linear_combination e1 - e2
      obtain ⟨o, ho⟩ := exists_int_of_mem (e3 ▸ sub_mem (ha N) (nsmul_mem (ha (N * m)) m))
      refine ⟨_, levelaf_tmul_mem o (one_mem _), ?_⟩
      rw [TensorProduct.smul_tmul', ← TensorProduct.add_tmul, ho, nsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_mul, add_sub_cancel])
  have hz : ι y - D • s = 0 := by
    refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated E).1 _ fun N hN => ?_
    obtain ⟨w, hw, e⟩ := hy N hN
    refine ⟨ι w - D • a N, sub_mem (map_mem_int hι hw) (nsmul_mem (ha N) D), ?_⟩
    rw [e, map_add, map_nsmul, map_nsmul, map_tmul_one hι]
    conv_lhs => rw [hxa N hN]
    rw [smul_add, smul_sub, smul_comm D N]
    abel
  refine ⟨(D : E)⁻¹ ⊗ₜ[F] 1 * y, ?_⟩
  rw [map_mul, map_tmul_one hι, sub_eq_zero.1 hz, hinv D hD]

theorem map_surjective : Function.Surjective ι := by
  intro z
  obtain ⟨x, a, ha, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 z
  obtain ⟨y, rfl⟩ := exists_map_eq_of_int hι ha
  exact ⟨x ⊗ₜ[F] 1 + y, by rw [map_add, map_tmul_one hι, one_smul]⟩

end

end GlobalTheory.AdeleBaseChange
end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts

open Formalism.BasicNotions NumberField

structure CF (p : ℕ) where
  C : Type
  [fld : NontriviallyNormedField C]
  [ultra : IsUltrametricDist C]
  [ac : IsAlgClosed C]
  [cpl : CompleteSpace C]
  [ch0 : CharZero C]
  norm_p : ‖(p : C)‖ = (p : ℝ)⁻¹

attribute [instance] CF.fld CF.ultra CF.ac CF.cpl CF.ch0

end Formalism.MainNotions.ModuliIntegralCharts

end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero

namespace Formalism.L2.Pj

structure CDVR where

  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V]
  [ch0 : CharZero V]

attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0

end Formalism.L2.Pj
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdSplit

theorem exists_prod_equiv (F E A B : Type) [CommRing F] [CommRing E] [Algebra F E]
    [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [Algebra F B] [TopologicalSpace B] [IsTopologicalRing B] :
    letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
    letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
    letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
    ∃ e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E),
      (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z ∧
        (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) ∧
      Continuous e ∧ Continuous e.symm := by
  letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
  letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
  letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
  haveI : IsModuleTopology (A × B) ((A × B) ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology B (B ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd ((A × B) ⊗[F] E) := IsModuleTopology.toContinuousAdd (A × B) _
  haveI : ContinuousAdd (A ⊗[F] E) := IsModuleTopology.toContinuousAdd A _
  haveI : ContinuousAdd (B ⊗[F] E) := IsModuleTopology.toContinuousAdd B _
  let p := Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E)
  let q := Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E)
  let l := TensorProduct.prodLeft F F A B E
  have hl : ∀ z, l z = (p z, q z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [Prod.ext_iff]
    | tmul a x => obtain ⟨a, b⟩ := a; simp [l, p, q]
    | add x y hx hy => simp [hx, hy]
  let e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E) :=
    { l.toAddEquiv with
      map_mul' := fun x y => by
        change l (x * y) = l x * l y
        simp [hl] }
  have he : ∀ z, e z = (p z, q z) := hl
  let i : A ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inl F A B)
  let j : B ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inr F A B)
  have hp : Continuous p := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.fst A B] A ⊗[F] E :=
      { toFun := p
        map_add' := map_add p
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [p, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_fst φ
  have hq : Continuous q := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.snd A B] B ⊗[F] E :=
      { toFun := q
        map_add' := map_add q
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [q, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_snd φ
  have hi : Continuous i := by
    let φ : A ⊗[F] E →ₑ+[MonoidHom.inl A B] (A × B) ⊗[F] E :=
      { toFun := i
        map_zero' := map_zero i
        map_add' := map_add i
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [i, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_id.prodMk continuous_const) φ
  have hj : Continuous j := by
    let φ : B ⊗[F] E →ₑ+[MonoidHom.inr A B] (A × B) ⊗[F] E :=
      { toFun := j
        map_zero' := map_zero j
        map_add' := map_add j
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [j, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_const.prodMk continuous_id) φ
  have hpi : ∀ x, p (i x) = x ∧ q (i x) = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [i, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  have hpj : ∀ x, p (j x) = 0 ∧ q (j x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [j, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  refine ⟨e, fun z => by rw [he]; exact ⟨rfl, rfl⟩, ?_, ?_⟩
  · have : (e : _ → _) = fun z => (p z, q z) := funext he
    rw [this]
    exact hp.prodMk hq
  · have : (e.symm : _ → _) = fun w => i w.1 + j w.2 := by
      funext w
      rw [RingEquiv.symm_apply_eq, he]
      simp [(hpi _).1, (hpi _).2, (hpj _).1, (hpj _).2]
    rw [this]
    exact (hi.comp continuous_fst).add (hj.comp continuous_snd)

theorem exists_adele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] , letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ e : (AdeleRing (𝓞 F) F ⊗[F] E) ≃+* (InfiniteAdeleRing F ⊗[F] E) × (FiniteAdeleRing (𝓞 F) F ⊗[F] E), (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z ∧ (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z) ∧ Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _
  exact exists_prod_equiv F E (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

end GlobalTheory.AdSplit
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.Host
open scoped TensorProduct

namespace GlobalTheory.PlaceIdem

section General

variable {E : Type} [Field E] [NumberField E]

theorem eq_zero_of_val (P : HeightOneSpectrum (𝓞 E)) (y : P.adicCompletion E)
    (h : ∀ n : ℕ, Valued.v y ≤ WithZero.exp (-(n : ℤ))) : y = 0 := by
  by_contra hy
  have h0 : Valued.v y ≠ 0 := by rwa [Ne, map_eq_zero]
  have h1 := h ((WithZero.log (Valued.v y)).natAbs + 1)
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp] at h1
  omega

end General

end GlobalTheory.PlaceIdem
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.UnitOpen

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_val_le (v : HeightOneSpectrum (𝓞 L)) (m : ℤ) :
    IsOpen {x : v.adicCompletion L | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective L (WithZero.exp (-m))
  have h : IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := Valued.isOpen_valuationSubring _
  convert h.preimage (continuous_mul_const p) using 1
  ext x
  show _ ↔ Valued.v (x * p) ≤ 1
  rw [map_mul, hp, WithZero.exp_neg, mul_inv_le_iff₀ (WithZero.exp_pos), one_mul]
  rfl

end GlobalTheory.Mem.UnitOpen
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Formalism.IndefR.Links
  Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

namespace GlobalTheory.CharTransport

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locMap_eq (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F) :
    GlobalTheory.AdeleBaseChange.locMap F P a = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a := by
  refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val P _ fun n => ?_)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap F E P
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le (P.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)
  have h2 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-(n : ℤ))).preimage
    ((continuous_sub_left (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a)).comp hc)
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F)
    (P.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩
  have e : GlobalTheory.AdeleBaseChange.locMap F P a - GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a =
      GlobalTheory.AdeleBaseChange.locMap F P (a - algebraMap F _ k) -
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a -
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P (algebraMap F _ k)) := by
    rw [map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
    ring
  rw [e]
  exact Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk1) hk2

end General

end GlobalTheory.CharTransport
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ContraPair

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in

def barK (k : Kinf E a) : Kinf E a :=
  ⟨(star k.1)ᵀ, Matrix.mem_unitaryGroup_iff.2 (by
    have h : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
    have e : star ((star k.1)ᵀ) = k.1ᵀ := by
      ext i j : 1
      simp [Matrix.star_apply]
    have h' : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
    rw [e, ← Matrix.transpose_mul, h', Matrix.transpose_one])⟩

omit [IsTotallyComplex E] in

def invTOp : Op E a → Op E a
  | .fin k => .fin (invT a (Af E) k)
  | .cpt k => .cpt (barK k)
  | .lie X => .lie (toL (-(Matrix.of X)ᵀ))

def Paired (π π' : CuspSub E a) (s : Op E a → Op E a) : Prop :=
  ∃ B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ k φ ψ, B (π.op (.fin k) φ) (π'.op (s (.fin k)) ψ) = B φ ψ) ∧
    (∀ k φ ψ, B (π.op (.cpt k) φ) (π'.op (s (.cpt k)) ψ) = B φ ψ) ∧
    ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π'.op (s (.lie X)) ψ) = 0

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

def conjOp : Op L a → Op L a
  | .fin k => .fin (GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k)
  | .cpt k => .cpt (barK k)
  | .lie X => .lie fun i j => star (X i j)

end GlobalTheory.ContraPair

end
end

section
-- module Solutions.AlpoGe.Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

end BorderedIndexCases

open Matrix

open Matrix

end Formalism.GaloisIrreducibility
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace Formalism.L2.NG

instance isAlgClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

end Formalism.L2.NG
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONLeaves
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField IsDedekindDomain CategoryTheory

namespace Formalism.L2.Indef.Tree

open Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section ToyLevel

theorem one_hundred_forty_three_ne_zero : NeZero ((143 : ℕ) : ℚ) := ⟨by norm_num⟩

attribute [local instance] one_hundred_forty_three_ne_zero

end ToyLevel

end Formalism.L2.Indef.Tree
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

section hecke

variable {E : Type} [Field E] [NumberField E]

@[ext]
structure HC (E : Type) [Field E] [NumberField E] where
  χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ
  cont : Continuous χ
  triv : ∀ a : Eˣ, χ (Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom a) = 1

instance instMulHC : Mul (HC E) where
  mul χ ψ := ⟨χ.χ * ψ.χ, χ.cont.mul ψ.cont, fun a => by rw [MonoidHom.mul_apply, χ.triv a, ψ.triv a, one_mul]⟩

instance instInvHC : Inv (HC E) where
  inv χ := ⟨χ.χ⁻¹, χ.cont.inv, fun a => by rw [MonoidHom.inv_apply, χ.triv a, inv_one]⟩

instance instOneHC : One (HC E) where
  one := ⟨1, continuous_const, fun _ => rfl⟩

@[simp] theorem HC.mul_χ (χ ψ : HC E) : (χ * ψ).χ = χ.χ * ψ.χ := rfl
@[simp] theorem HC.inv_χ (χ : HC E) : (χ⁻¹).χ = χ.χ⁻¹ := rfl
@[simp] theorem HC.one_χ : (1 : HC E).χ = 1 := rfl

end hecke

end Formalism.L2.NC
end
end

section
-- module Solutions.AlpoGe.Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.Z.BN

section
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W S : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup S] [Module A S]

instance instFiniteDimensionalSubtypeMemSubmodule_solutions (N : Submodule A V) [FiniteDimensional k V] : FiniteDimensional k N :=
  Module.Finite.of_injective (N.subtype.restrictScalars k) N.subtype_injective

instance instFiniteDimensionalQuotientSubmodule_solutions (N : Submodule A V) [FiniteDimensional k V] : FiniteDimensional k (V ⧸ N) :=
  Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective

end

end Formalism.IrreducibleCountingLemmas.Z.BN
end
end

section
-- module Solutions.AlpoGe.Formalism.ResultantValuation.ResultantAdjugateProofs.Parabolic
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.ResultantValuation

open Module

namespace ParabolicCounting

variable (F : Type) [Field F] (r t : ℕ)

@[instance_reducible] def act : MulAction (GL (Fin (r + t)) F) (Submodule F (Fin (r + t) → F)) where
  smul g W := W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F))
  one_smul W := by
    show W.map _ = W
    rw [Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]
  mul_smul g h W := by
    show W.map _ = (W.map _).map _
    rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

attribute [local instance] act

end ParabolicCounting

end Formalism.ResultantValuation
end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.MainNotions.N

open Module

structure GRep (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] where
  V : Type
  [acg : AddCommGroup V]
  [modLL : Module LL V]
  [modQp : Module Qp V]
  [towQp : IsScalarTower Qp LL V]
  [modO : Module O V]
  [towO : IsScalarTower O LL V]
  [fd : FiniteDimensional LL V]
  [top : TopologicalSpace V]
  [mtop : IsModuleTopology LL V]
  [cadd : ContinuousAdd V]
  [csmul : ContinuousConstSMul LL V]
  ρ : Representation LL G V
  cont : ∀ x, Continuous fun g => ρ g x

attribute [instance] GRep.acg GRep.modLL GRep.modQp GRep.towQp GRep.modO GRep.towO GRep.fd GRep.top
  GRep.mtop GRep.cadd GRep.csmul

end Formalism.MainNotions.N
end
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
attribute [-instance] _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal TensorProduct

namespace Formalism.MainNotions.BlochKatoReduction

def IsWild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  σ ∈ Ine (F := E) A ∧ ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x

end Formalism.MainNotions.BlochKatoReduction

end
end



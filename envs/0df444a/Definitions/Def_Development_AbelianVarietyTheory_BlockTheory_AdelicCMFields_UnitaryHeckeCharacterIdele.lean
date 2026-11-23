-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
-- name    : Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:30.26244+00:00
-- url     : https://prove2.me/theorems/ce671d1f-472a-4b5b-998d-0eb256f256a6
-- title:
--   Unitary Hecke Character Idele
-- statement:
--   Definitions and structural lemmas for Unitary Hecke Character Idele, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AdelicCMFields/UnitaryHeckeCharacterIdele.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
class IsCMExtension (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop where
  totallyReal : IsTotallyReal F
  totallyComplex : IsTotallyComplex E
  quadratic : Algebra.IsQuadraticExtension F E
section CM
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension.isCMField [h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] : IsCMField E := by
  haveI := h.totallyReal
  haveI := h.totallyComplex
  haveI := h.quadratic
  exact IsCMField.ofCMExtension F E
instance isCMExtension_maximalRealSubfield (E : Type) [Field E] [NumberField E] [IsCMField E] :
    IsCMExtension (maximalRealSubfield E) E where
  totallyReal := inferInstance
  totallyComplex := inferInstance
  quadratic := inferInstance
def conj [h : IsCMExtension F E] : E ≃ₐ[F] E :=
  haveI := h.totallyReal
  haveI := h.totallyComplex
  haveI := h.quadratic
  haveI := IsCMExtension.isCMField F E
  { (IsCMField.complexConj E).toRingEquiv with
    commutes' := fun x => by
      have := IsCMField.complexConj_apply_eq_self E (CMExtension.equivMaximalRealSubfield F E x)
      rw [CMExtension.equivMaximalRealSubfield_apply] at this
      exact this }
end CM
abbrev Idele (K : Type) [Field K] [NumberField K] : Type := (AdeleRing (𝓞 K) K)ˣ
def principalIdele (K : Type) [Field K] [NumberField K] : Kˣ →* Idele K :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom
section Extension
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
instance liesOver_under (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) :=
  ⟨rfl⟩
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo (w : HeightOneSpectrum (𝓞 L)) :
    Set.MapsTo (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w)
      ((w.under (𝓞 K)).adicCompletionIntegers K : Set _) (w.adicCompletionIntegers L : Set _) := by
  intro x hx
  have hS : IsClosed ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w) ⁻¹'
      (w.adicCompletionIntegers L : Set (w.adicCompletion L))) :=
    (Valued.isClopen_integer (w.adicCompletion L)).isClosed.preimage
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap K L w)
  have hopen : IsOpen (((w.under (𝓞 K)).adicCompletionIntegers K :
      Set ((w.under (𝓞 K)).adicCompletion K))) :=
    (Valued.isClopen_integer ((w.under (𝓞 K)).adicCompletion K)).isOpen
  have hd := Dense.open_subset_closure_inter (denseRange_algebraMap K (w.under (𝓞 K))) hopen hx
  refine closure_minimal ?_ hS hd
  rintro _ ⟨hy, k, rfl⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers] at hy ⊢
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
  have h1 : Valued.v (algebraMap K ((w.under (𝓞 K)).adicCompletion K) k) =
      (w.under (𝓞 K)).valuation K k := valuedAdicCompletion_eq_valuation' _ k
  have h2 : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap K L k)) =
      w.valuation L (algebraMap K L k) := valuedAdicCompletion_eq_valuation' _ _
  rw [h1] at hy
  rw [h2, ← valuation_liesOver L (w.under (𝓞 K)) w]
  exact pow_le_one' hy _
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under :
    Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) cofinite cofinite := by
  intro s hs
  rw [mem_cofinite] at hs
  rw [mem_map, mem_cofinite]
  rw [← Set.preimage_compl]
  refine hs.preimage' fun v _ => ?_
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩
def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (fun w => w.under (𝓞 K)) (tendsto_under K L) (finiteCompletionMap K L)
    (Eventually.of_forall (finiteCompletionMap_mapsTo K L))
def infiniteAdeleMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  Pi.ringHom fun w : InfinitePlace L =>
    (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))
def adeleMap : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infiniteAdeleMap K L) (finiteAdeleMap K L)
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap (x : K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L (algebraMap K _ x) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x) := by
  refine Prod.ext ?_ ?_
  · funext w
    exact LiesOver.completionMap_coe _
  · ext w : 1
    exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe K L w x
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L) :=
  (continuous_pi fun w => LiesOver.continuous_completionMap.comp (continuous_apply _)).prodMap
    (RestrictedProduct.mapAlong_continuous _ _ _
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L) _
      (Eventually.of_forall (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo K L))
      fun w => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap K L w)
def ideleMap : Idele K →* Idele L := Units.map (adeleMap K L).toMonoidHom
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L) :=
  Continuous.units_map _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L)
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele (x : Kˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele K x) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele L (Units.map (algebraMap K L).toMonoidHom x) :=
  Units.ext (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L x)
end Extension
def ideleConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsCMExtension F E] : Idele E →* Idele E :=
  @ideleMap E E _ _ _ _ (conj F E).toRingEquiv.toRingHom.toAlgebra
example : IsCMExtension (maximalRealSubfield (CyclotomicField 4 ℚ)) (CyclotomicField 4 ℚ) :=
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  haveI : IsCMField (CyclotomicField 4 ℚ) :=
    IsCyclotomicExtension.Rat.isCMField _ (S := {4}) ⟨4, rfl, by norm_num⟩
  inferInstance
variable {E : Type} [Field E] [NumberField E]
open scoped Classical in

def localIdele (P : HeightOneSpectrum (𝓞 E)) : (P.adicCompletion E)ˣ →* Idele E :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).comp
    { toFun := fun x => RestrictedProduct.mulSingle
        (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletionIntegers E) P x
      map_one' := RestrictedProduct.mulSingle_one _ _
      map_mul' := RestrictedProduct.mulSingle_mul _ _ })
variable (E) in

@[ext]
structure UnitaryHeckeChar where

  toHom : Idele E →* Circle
  continuous_toHom : Continuous toHom
  map_principal : ∀ x : Eˣ, toHom (principalIdele E x) = 1
namespace UnitaryHeckeChar
def trivial (E : Type) [Field E] [NumberField E] : UnitaryHeckeChar E where
  toHom := 1
  continuous_toHom := continuous_const
  map_principal _ := rfl
def mul (χ ψ : UnitaryHeckeChar E) : UnitaryHeckeChar E where
  toHom := χ.toHom * ψ.toHom
  continuous_toHom := χ.continuous_toHom.mul ψ.continuous_toHom
  map_principal x := by simp [χ.map_principal, ψ.map_principal]
def inv (χ : UnitaryHeckeChar E) : UnitaryHeckeChar E where
  toHom := χ.toHom⁻¹
  continuous_toHom := χ.continuous_toHom.inv
  map_principal x := by simp [χ.map_principal]
def restrict (F : Type) [Field F] [NumberField F] [Algebra F E] (χ : UnitaryHeckeChar E) :
    UnitaryHeckeChar F where
  toHom := χ.toHom.comp (ideleMap F E)
  continuous_toHom := χ.continuous_toHom.comp (continuous_ideleMap F E)
  map_principal x := by
    rw [MonoidHom.comp_apply, ideleMap_principalIdele, χ.map_principal]
def IsTrivialOn (F : Type) [Field F] [NumberField F] [Algebra F E] (χ : UnitaryHeckeChar E) :
    Prop :=
  ∀ x : Idele F, χ.toHom (ideleMap F E x) = 1
def localComponent (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    (P.adicCompletion E)ˣ →* Circle :=
  χ.toHom.comp (localIdele P)
def IsUnramifiedAt (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.localComponent P u = 1
end UnitaryHeckeChar
def IsUniformiser (P : HeightOneSpectrum (𝓞 E)) (ϖ : (P.adicCompletion E)ˣ) : Prop :=
  Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ)
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsUniformiser P ϖ := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hv : Valued.v (algebraMap E (P.adicCompletion E) π) = WithZero.exp (-1 : ℤ) :=
    (valuedAdicCompletion_eq_valuation' P π).trans hπ
  have hne : algebraMap E (P.adicCompletion E) π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ hne, hv⟩
namespace UnitaryHeckeChar
open scoped Classical in

def valueAt (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) : ℂ :=
  if χ.IsUnramifiedAt P then (χ.localComponent P (exists_isUniformiser P).choose : ℂ) else 0
def eulerFactor (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂ :=
  (1 - χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹
def finiteL (χ : UnitaryHeckeChar E) (s : {s : ℂ // 1 < s.re}) : ℂ :=
  ∏' P : HeightOneSpectrum (𝓞 E), χ.eulerFactor P s
example (P : HeightOneSpectrum (𝓞 E)) : (trivial E).valueAt P = 1 := by
  have h : (trivial E).IsUnramifiedAt P := fun _ _ => rfl
  rw [valueAt, if_pos h]
  rfl
end UnitaryHeckeChar
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued {P : HeightOneSpectrum (𝓞 E)}
    {x : P.adicCompletion E} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [FinitePlace.norm_def, h]
  simp
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finite_mulSupport (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) => ‖x.val.2 v‖).Finite := by
  have hev := x.val.2.2.and x.inv.2.2
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun v hv ⟨ha, hb⟩ => hv ?_
  simp only [SetLike.mem_coe, mem_adicCompletionIntegers] at ha hb
  have hab : x.val.2 v * x.inv.2 v = 1 := congrArg (fun y : AdeleRing (𝓞 E) E => y.2 v) x.val_inv
  have hv1 : Valued.v (x.val.2 v) * Valued.v (x.inv.2 v) = 1 := by rw [← map_mul, hab, map_one]
  refine _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued (le_antisymm ha ?_)
  calc (1 : _) = Valued.v (x.val.2 v) * Valued.v (x.inv.2 v) := hv1.symm
    _ ≤ Valued.v (x.val.2 v) := mul_le_of_le_one_right' hb
def finiteIdeleNorm : Idele E →* ℝ where
  toFun x := ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖x.val.2 v‖
  map_one' := finprod_eq_one_of_forall_eq_one fun v => norm_one (α := v.adicCompletion E)
  map_mul' x y := by
    rw [← finprod_mul_distrib (finite_mulSupport x) (finite_mulSupport y)]
    exact finprod_congr fun v => norm_mul (x.val.2 v) (y.val.2 v)
def infiniteIdeleNorm : Idele E →* ℝ where
  toFun x := ∏ v : InfinitePlace E, ‖x.val.1 v‖ ^ v.mult
  map_one' := Finset.prod_eq_one fun v _ => by
    rw [show (1 : Idele E).val.1 v = 1 from rfl, norm_one, one_pow]
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [show (x * y).val.1 v = x.val.1 v * y.val.1 v from rfl, norm_mul, mul_pow]
def ideleNorm : Idele E →* ℝ := infiniteIdeleNorm * finiteIdeleNorm
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm x ≠ 0 := by
  intro h
  have hx := map_mul _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm x x⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at hx
  exact one_ne_zero hx
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_principalIdele (x : Eˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) = 1 := by
  have hinf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) =
      ∏ w : InfinitePlace E, w (x : E) ^ w.mult :=
    Finset.prod_congr rfl fun v _ => by
      congr 1
      exact InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm (x : E))
  have hfin : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) =
      ∏ᶠ w : FinitePlace E, w (x : E) := by
    refine (finprod_congr fun P => ?_).trans (finprod_comp_equiv
      FinitePlace.equivHeightOneSpectrum.symm (f := fun w : FinitePlace E => w (x : E)))
    show ‖FinitePlace.embedding P (x : E)‖ = _
    rw [← FinitePlace.mk_apply]
    rfl
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm, MonoidHom.mul_apply, hinf, hfin, prod_abs_eq_one x.ne_zero]
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)) := by
  have hinf : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm (E := E)) := by
    show Continuous fun x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E => ∏ v : InfinitePlace E, ‖x.val.1 v‖ ^ v.mult
    exact continuous_finset_prod _ fun v _ =>
      (((continuous_apply v).comp (continuous_fst.comp (Units.continuous_val (M := AdeleRing (𝓞 E) E)))).norm).pow _
  have hfin : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm (E := E)) := by
    refine continuous_of_continuousAt_one _ ?_
    have hW : IsOpen {a : FiniteAdeleRing (𝓞 E) E |
        ∀ P : HeightOneSpectrum (𝓞 E), True → a P ∈ (P.adicCompletionIntegers E : Set _)} :=
      RestrictedProduct.isOpen_forall_imp_mem fun P =>
        (Valued.isClopen_integer (P.adicCompletion E)).isOpen
    have hV := ((hW.preimage (continuous_snd.comp (Units.continuous_val (M := AdeleRing (𝓞 E) E)))).inter
      (hW.preimage (continuous_snd.comp (Units.continuous_coe_inv (M := AdeleRing (𝓞 E) E))))).mem_nhds
        (x := (1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E)) ⟨fun P _ => one_mem _, fun P _ => one_mem _⟩
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [hV] with x hx
    rw [map_one]
    refine finprod_eq_one_of_forall_eq_one fun P => ?_
    have ha := hx.1 P trivial
    have hb := hx.2 P trivial
    simp only [SetLike.mem_coe, mem_adicCompletionIntegers] at ha hb
    have hab : x.val.2 P * x.inv.2 P = 1 :=
      congrArg (fun y : AdeleRing (𝓞 E) E => y.2 P) x.val_inv
    have hv1 : Valued.v (x.val.2 P) * Valued.v (x.inv.2 P) = 1 := by rw [← map_mul, hab, map_one]
    refine _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued (le_antisymm ha ?_)
    calc (1 : _) = Valued.v (x.val.2 P) * Valued.v (x.inv.2 P) := hv1.symm
      _ ≤ Valued.v (x.val.2 P) := mul_le_of_le_one_right' hb
  show Continuous fun x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm x * _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm x
  exact hinf.mul hfin
namespace UnitaryHeckeChar
variable (E) in

def normPow (t : ℝ) : UnitaryHeckeChar E where
  toHom :=
    { toFun := fun x => Circle.exp (t * Real.log (ideleNorm x))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul ideleNorm, Real.log_mul (ideleNorm_ne_zero x) (ideleNorm_ne_zero y), mul_add,
          Circle.exp_add] }
  continuous_toHom := Circle.exp.continuous.comp
    (continuous_const.mul (continuous_ideleNorm.log ideleNorm_ne_zero))
  map_principal x := by simp [ideleNorm_principalIdele]
end UnitaryHeckeChar
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele



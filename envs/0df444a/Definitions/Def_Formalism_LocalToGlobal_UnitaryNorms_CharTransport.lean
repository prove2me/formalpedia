-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport
-- name    : Formalism_LocalToGlobal_UnitaryNorms_CharTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:37.091572+00:00
-- url     : https://prove2.me/theorems/a188615a-9379-4d72-9571-82abda950b78
-- title:
--   Char Transport
-- statement:
--   Definitions and structural lemmas for Char Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharTransport.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Theorems.Thm_Formalism_L2_Host_HChar_val_eq
import Theorems.Thm_Formalism_L2_Host_unif_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace Formalism.L2.Host.CT
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
def plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.comap ((RingOfIntegers.mapRingEquiv j).symm : 𝓞 L →+* 𝓞 E)
    (RingOfIntegers.mapRingEquiv j).symm.surjective w
theorem mem_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j x ∈ (plMap j w).asIdeal ↔ x ∈ w.asIdeal := by
  unfold plMap
  simp [IsDedekindDomain.HeightOneSpectrum.comap]
theorem mapRingEquiv_symm_apply (j : E ≃+* L) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j.symm (RingOfIntegers.mapRingEquiv j x) = x := by
  apply RingOfIntegers.ext
  simp [RingOfIntegers.mapRingEquiv]
theorem plMap_symm_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) : plMap j.symm (plMap j w) = w := by
  apply HeightOneSpectrum.ext
  ext y
  have h := mem_plMap j.symm (plMap j w) (RingOfIntegers.mapRingEquiv j y)
  rw [mapRingEquiv_symm_apply] at h
  rw [h, mem_plMap]
theorem plMap_injective (j : E ≃+* L) : Function.Injective (plMap j) := by
  intro a b h
  rw [← plMap_symm_plMap j a, h, plMap_symm_plMap]
theorem asIdeal_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    (plMap j w).asIdeal = w.asIdeal.map (RingOfIntegers.mapRingEquiv j) := by
  ext y
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hy
    refine ⟨(RingOfIntegers.mapRingEquiv j).symm y, ?_, RingEquiv.apply_symm_apply _ _⟩
    rw [← mem_plMap j w, RingEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    exact (mem_plMap j w x).2 hx
theorem mem_plMap_pow (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j x ∈ (plMap j w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [asIdeal_plMap, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [(RingOfIntegers.mapRingEquiv j).injective hxy] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩
theorem eq_of_forall_le_exp {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  have hm : m ≤ 0 := by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1
  have hk : k ≤ 0 := by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at hb1
  have e1 : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
  have e2 : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  have h1 := h (-m).toNat
  have h2 := h (-k).toNat
  rw [WithZero.exp_le_exp, WithZero.exp_le_exp, e1] at h1
  rw [WithZero.exp_le_exp, WithZero.exp_le_exp, e2] at h2
  have i1 := h1.1 (by omega)
  have i2 := h2.2 (by omega)
  congr 1
  omega
theorem intValuation_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    (plMap j w).intValuation (RingOfIntegers.mapRingEquiv j x) = w.intValuation x := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hx' : RingOfIntegers.mapRingEquiv j x ≠ 0 := (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv j).injective).2 hx
  refine eq_of_forall_le_exp ((plMap j w).intValuation_ne_zero _ hx') (w.intValuation_ne_zero _ hx) ((plMap j w).intValuation_le_one _) (w.intValuation_le_one _) ?_
  intro n
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, mem_plMap_pow]
theorem valuation_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (plMap j w).valuation L (j x) = w.valuation E x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have key : ∀ c : 𝓞 E, j (algebraMap (𝓞 E) E c) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv j c) := fun c => rfl
  rw [map_div₀, key, key, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_plMap, intValuation_plMap]
theorem continuous_withVal {R S : Type} [Field R] [Field S] {v : Valuation R (WithZero (Multiplicative ℤ))}
    {v' : Valuation S (WithZero (Multiplicative ℤ))} (hs : Function.Surjective v) (f : WithVal v →+* WithVal v')
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  intro s hs'
  rw [map_zero] at hs'
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs'
  obtain ⟨x0, hx0⟩ := hs (embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _))))
  have hpos : 0 < embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _))) := by
    rw [← map_zero (embedding (f := .ofClass (Valued.v : Valuation (WithVal v') _)))]
    exact embedding_strictMono (Units.zero_lt γ)
  have hx0' : 0 < Valued.v.restrict (WithVal.toVal v x0) := by
    rw [Valuation.restrict_pos_iff, WithVal.valued_toVal, hx0]
    exact hpos
  refine Filter.mem_map.mpr (Valued.mem_nhds_zero.mpr ⟨Units.mk0 _ hx0'.ne', fun x hx => hγ ?_⟩)
  have hx1 : Valued.v.restrict x < Valued.v.restrict (WithVal.toVal v x0) := hx
  rw [Valuation.restrict_lt_iff] at hx1
  have e0 : Valued.v (WithVal.toVal v x0) = v x0 := WithVal.valued_toVal _ _
  rw [e0, hx0] at hx1
  show Valued.v.restrict (f x) < (γ : ValueGroup₀ _)
  rw [Valuation.restrict_lt_iff_lt_embedding, hf]
  exact hx1
theorem continuous_congrVal (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective E w) (WithVal.congr _ _ j).toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j x.ofVal)) = _
    rw [WithVal.valued_toVal, valuation_plMap, WithVal.apply_ofVal]
theorem continuous_congrVal_symm (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective L (plMap j w))
    (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm.toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j.symm x.ofVal)) = _
    rw [WithVal.valued_toVal, ← WithVal.apply_ofVal, ← valuation_plMap j w, RingEquiv.apply_symm_apply]
def compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    w.adicCompletion E ≃+* (plMap j w).adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv E w).trans ((UniformSpace.Completion.mapRingEquiv
    (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) (continuous_congrVal j w)
    (continuous_congrVal_symm j w)).trans (HeightOneSpectrum.adicCompletion.equiv L (plMap j w)).symm)
theorem continuous_compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) : Continuous (compEquiv j w) := by
  have h : Continuous (fun y : w.adicCompletion E =>
      (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map
        (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) y.toCompletion) : (plMap j w).adicCompletion L)) :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L (plMap j w)).comp
      (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w))
  exact h.congr fun y => rfl
theorem continuous_compEquiv_symm (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (compEquiv j w).symm := by
  have h : Continuous (fun y : (plMap j w).adicCompletion L =>
      (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map
        (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm y.toCompletion) : w.adicCompletion E)) :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L (plMap j w)))
  exact h.congr fun y => rfl
theorem compEquiv_algebraMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    compEquiv j w (algebraMap E (w.adicCompletion E) x) = algebraMap L ((plMap j w).adicCompletion L) (j x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  show UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j)
    ((algebraMap E (w.adicCompletion E) x).toCompletion) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletion_toCompletion,
    HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (continuous_congrVal j w))]
  rfl
theorem compEquiv_symm_algebraMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (compEquiv j w).symm (algebraMap L ((plMap j w).adicCompletion L) (j x)) = algebraMap E (w.adicCompletion E) x := by
  rw [← compEquiv_algebraMap, RingEquiv.symm_apply_apply]
theorem absNorm_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (plMap j w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv j) (asIdeal_plMap j w)).toEquiv).symm
theorem toNNReal_congr {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) (z : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal ha z = WithZeroMulInt.toNNReal hb z := by
  subst h
  rfl
theorem norm_compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ‖compEquiv j w y‖ = ‖y‖ := by
  have h := (HeightOneSpectrum.denseRange_algebraMap E w).equalizer (continuous_norm.comp (continuous_compEquiv j w))
    continuous_norm (funext fun x => ?_)
  · exact congrFun h y
  simp only [Function.comp_apply]
  rw [compEquiv_algebraMap]
  show ‖NumberField.FinitePlace.embedding (plMap j w) (j x)‖ = ‖NumberField.FinitePlace.embedding w x‖
  rw [NumberField.FinitePlace.norm_embedding, NumberField.FinitePlace.norm_embedding,
    HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.adicAbv_def, valuation_plMap]
  congr 1
  exact toNNReal_congr _ _ (by rw [absNorm_plMap]) _
theorem valued_le_one_iff (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    Valued.v (compEquiv j w y) ≤ 1 ↔ Valued.v y ≤ 1 := by
  have h1 : ‖compEquiv j w y‖ ≤ 1 ↔ Valued.v (compEquiv j w y) ≤ 1 := Valued.toNormedField.norm_le_one_iff
  have h2 : ‖y‖ ≤ 1 ↔ Valued.v y ≤ 1 := Valued.toNormedField.norm_le_one_iff
  rw [← h1, ← h2, norm_compEquiv]
theorem valued_eq_one_iff_both_le_one {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (z : K) (hz : z ≠ 0) :
    Valued.v z = 1 ↔ Valued.v z ≤ 1 ∧ Valued.v z⁻¹ ≤ 1 := by
  have h0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
theorem valued_eq_one_iff (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    Valued.v (compEquiv j w y) = 1 ↔ Valued.v y = 1 := by
  by_cases hy : y = 0
  · subst hy
    simp
  have hy' : compEquiv j w y ≠ 0 := (map_ne_zero_iff _ (compEquiv j w).injective).2 hy
  rw [valued_eq_one_iff_both_le_one _ hy', valued_eq_one_iff_both_le_one _ hy, ← map_inv₀, valued_le_one_iff, valued_le_one_iff]
theorem continuous_congrAbs (j : E ≃+* L) (u : InfinitePlace L) :
    Continuous (WithAbs.congr (u.comap j.toRingHom).1 u.1 j) := by
  exact (AddMonoidHomClass.isometry_of_norm (WithAbs.congr (u.comap j.toRingHom).1 u.1 j) fun x => rfl).continuous
theorem continuous_congrAbs_symm (j : E ≃+* L) (u : InfinitePlace L) :
    Continuous (WithAbs.congr (u.comap j.toRingHom).1 u.1 j).symm := by
  exact (AddMonoidHomClass.isometry_of_norm (WithAbs.congr (u.comap j.toRingHom).1 u.1 j).symm fun x => by
    obtain ⟨y, rfl⟩ := (WithAbs.congr (u.comap j.toRingHom).1 u.1 j).surjective x
    rw [RingEquiv.symm_apply_apply]
    rfl).continuous
def infEquiv (j : E ≃+* L) (u : InfinitePlace L) : (u.comap j.toRingHom).Completion ≃+* u.Completion :=
  (InfinitePlace.Completion.equiv (u.comap j.toRingHom)).trans ((UniformSpace.Completion.mapRingEquiv
    (WithAbs.congr _ _ j) (continuous_congrAbs j u) (continuous_congrAbs_symm j u)).trans
    (InfinitePlace.Completion.equiv u).symm)
theorem continuous_infEquiv (j : E ≃+* L) (u : InfinitePlace L) : Continuous (infEquiv j u) := by
  have h : Continuous (fun y : (u.comap j.toRingHom).Completion =>
      (InfinitePlace.Completion.ofCompletion (UniformSpace.Completion.map
        (WithAbs.congr (u.comap j.toRingHom).1 u.1 j)
          y.toCompletion) : u.Completion)) :=
    (InfinitePlace.Completion.continuous_ofCompletion u).comp
      (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion _))
  exact h.congr fun y => rfl
theorem infEquiv_algebraMap (j : E ≃+* L) (u : InfinitePlace L) (x : E) :
    infEquiv j u (algebraMap E (u.comap j.toRingHom).Completion x) = algebraMap L u.Completion (j x) := by
  apply InfinitePlace.Completion.ext
  show UniformSpace.Completion.map (WithAbs.congr (u.comap j.toRingHom).1
    u.1 j) ((algebraMap E (u.comap j.toRingHom).Completion x).toCompletion) = _
  rw [InfinitePlace.Completion.algebraMap_toCompletion, InfinitePlace.Completion.algebraMap_toCompletion,
    UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (continuous_congrAbs j u))]
  rfl
theorem mapsTo_integers (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) :
    Set.MapsTo (compEquiv j.symm v).symm ((plMap j.symm v).adicCompletionIntegers E : Set _)
      (v.adicCompletionIntegers L : Set _) := by
  intro x hx
  have h := valued_le_one_iff j.symm v ((compEquiv j.symm v).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.1 hx
def finMap (j : E ≃+* L) : FiniteAdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (plMap j.symm) (plMap_injective j.symm).tendsto_cofinite
    (fun v => (compEquiv j.symm v).symm.toRingHom) (Filter.Eventually.of_forall fun v => mapsTo_integers j v)
theorem continuous_finMap (j : E ≃+* L) : Continuous (finMap j) :=
  RestrictedProduct.mapAlong_continuous (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (plMap j.symm) (plMap_injective j.symm).tendsto_cofinite
    (fun v => (compEquiv j.symm v).symm) (Filter.Eventually.of_forall fun v => mapsTo_integers j v)
    fun v => continuous_compEquiv_symm j.symm v
def infMap (j : E ≃+* L) : InfiniteAdeleRing E →+* InfiniteAdeleRing L :=
  RingHom.pi fun u => (infEquiv j u).toRingHom.comp (Pi.evalRingHom _ (u.comap j.toRingHom))
theorem continuous_infMap (j : E ≃+* L) : Continuous (infMap j) := by
  exact continuous_pi fun u => (continuous_infEquiv j u).comp (continuous_apply _)
def adMap (j : E ≃+* L) : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infMap j) (finMap j)
theorem continuous_adMap (j : E ≃+* L) : Continuous (adMap j) := by
  exact (continuous_infMap j).prodMap (continuous_finMap j)
def idMap (j : E ≃+* L) : Ideles E →* Ideles L := Units.map (adMap j).toMonoidHom
theorem continuous_idMap (j : E ≃+* L) : Continuous (idMap j) := by
  exact Units.continuous_map (continuous_adMap j)
theorem idMap_diag (j : E ≃+* L) (k : Eˣ) : idMap j (diagUnits E k) = diagUnits L (Units.map j.toMonoidHom k) := by
  apply Units.ext
  show adMap j (algebraMap E (AdeleRing (𝓞 E) E) (k : E)) = algebraMap L (AdeleRing (𝓞 L) L) (j k)
  refine Prod.ext ?_ ?_
  · funext u
    exact infEquiv_algebraMap j u (k : E)
  · ext1 v
    show (compEquiv j.symm v).symm (algebraMap E _ (k : E)) = algebraMap L _ (j k)
    have h := compEquiv_symm_algebraMap j.symm v (j (k : E))
    rw [RingEquiv.symm_apply_apply] at h
    exact h
def locMap (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) :
    ((plMap j.symm v).adicCompletion E)ˣ →* (v.adicCompletion L)ˣ :=
  Units.map (compEquiv j.symm v).symm.toMonoidHom
theorem idMap_localIdele (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) (x : ((plMap j.symm v).adicCompletion E)ˣ) :
    idMap j (localIdele E (plMap j.symm v) x) = localIdele L v (locMap j v x) := by
  classical
  apply Units.ext
  apply Prod.ext
  · show infMap j 1 = 1
    exact map_one _
  · apply RestrictedProduct.ext
    intro v'
    show (compEquiv j.symm v').symm (Pi.mulSingle (plMap j.symm v) (x : (plMap j.symm v).adicCompletion E)
      (plMap j.symm v')) = Pi.mulSingle v ((compEquiv j.symm v).symm (x : (plMap j.symm v).adicCompletion E)) v'
    by_cases h : v' = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · have h' : plMap j.symm v' ≠ plMap j.symm v := fun e => h (plMap_injective j.symm e)
      rw [Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]
theorem isUnitAt_locMap (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) (x : ((plMap j.symm v).adicCompletion E)ˣ) :
    IsUnitAt v (locMap j v x) ↔ IsUnitAt (plMap j.symm v) x := by
  have h := valued_eq_one_iff j.symm v ((compEquiv j.symm v).symm (x : (plMap j.symm v).adicCompletion E))
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm
theorem locMap_surjective (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : Function.Surjective (locMap j v) := by
  intro y
  refine ⟨Units.map (compEquiv j.symm v).toMonoidHom y, ?_⟩
  apply Units.ext
  exact (compEquiv j.symm v).symm_apply_apply (y : v.adicCompletion L)
theorem locMap_atFin (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) (k : Eˣ) :
    locMap j v (atFin (plMap j.symm v) k) = atFin v (Units.map j.toMonoidHom k) := by
  apply Units.ext
  have h := compEquiv_symm_algebraMap j.symm v (j (k : E))
  rw [RingEquiv.symm_apply_apply] at h
  exact h
def transport (j : E ≃+* L) : HChar L →* HChar E where
  toFun χ := ⟨χ.1.comp (idMap j), χ.2.1.comp (continuous_idMap j), fun k => by
    rw [MonoidHom.comp_apply, idMap_diag, χ.2.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl
theorem transport_loc (j : E ≃+* L) (χ : HChar L) (v : HeightOneSpectrum (𝓞 L))
    (x : ((plMap j.symm v).adicCompletion E)ˣ) : (transport j χ).loc (plMap j.symm v) x = χ.loc v (locMap j v x) := by
  exact congrArg χ.1 (idMap_localIdele j v x)
theorem transport_unrAt_symm (j : E ≃+* L) (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (transport j χ).UnrAt (plMap j.symm v) ↔ χ.UnrAt v := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := locMap_surjective j v y
    rw [← transport_loc]
    exact h x ((isUnitAt_locMap j v x).1 hy)
  · intro h x hx
    rw [transport_loc]
    exact h _ ((isUnitAt_locMap j v x).2 hx)
theorem transport_unrAt_iff (j : E ≃+* L) (χ : HChar L) (w : HeightOneSpectrum (𝓞 E)) :
    (transport j χ).UnrAt w ↔ χ.UnrAt (plMap j w) := by
  have h := transport_unrAt_symm j χ (plMap j w)
  rwa [plMap_symm_plMap] at h
theorem transport_val_symm (j : E ≃+* L) (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (h : χ.UnrAt v) :
    (transport j χ).val (plMap j.symm v) = χ.val v := by
  have hu := unif_spec (plMap j.symm v)
  have key : IsUnifAt v (locMap j v (atFin (plMap j.symm v) (unif (plMap j.symm v)))) := by
    rw [locMap_atFin]
    unfold IsUnifAt at hu ⊢
    rw [← hu]
    have e1 : Valued.v (algebraMap L (v.adicCompletion L) (j (unif (plMap j.symm v) : E))) = v.valuation L (j (unif (plMap j.symm v) : E)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    have e2 : Valued.v (algebraMap E ((plMap j.symm v).adicCompletion E) (unif (plMap j.symm v) : E)) = (plMap j.symm v).valuation E (unif (plMap j.symm v) : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (plMap j.symm v) _
    have e3 := valuation_plMap j.symm v (j (unif (plMap j.symm v) : E))
    rw [RingEquiv.symm_apply_apply] at e3
    exact e1.trans (e3.symm.trans e2.symm)
  rw [← χ.val_eq h _ key, ← transport_loc]
  rfl
theorem transport_val (j : E ≃+* L) (χ : HChar L) (w : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap j w)) :
    (transport j χ).val w = χ.val (plMap j w) := by
  have h' := transport_val_symm j χ (plMap j w) h
  rwa [plMap_symm_plMap] at h'
theorem transport_symm_unrAt_iff (j : E ≃+* L) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    (transport j (transport j.symm χ)).UnrAt w ↔ χ.UnrAt w := by
  rw [transport_unrAt_iff, transport_unrAt_iff, plMap_symm_plMap]
theorem transport_symm_val (j : E ≃+* L) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt w) :
    (transport j (transport j.symm χ)).val w = χ.val w := by
  have h1 : (transport j.symm χ).UnrAt (plMap j w) := by
    rw [transport_unrAt_iff, plMap_symm_plMap]
    exact h
  rw [transport_val j _ w h1, transport_val j.symm χ (plMap j w) (by rw [plMap_symm_plMap]; exact h), plMap_symm_plMap]
theorem transport_transport_symm (hS : SMOne E) (hU : UnrAE E) (j : E ≃+* L) (χ : HChar E) :
    transport j (transport j.symm χ) = χ := by
  apply hS
  filter_upwards [hU χ.1 χ.2.1] with v hv
  have hχ : χ.UnrAt v := fun x hx => hv x hx
  exact ⟨(transport_symm_unrAt_iff j χ v).2 hχ, hχ, transport_symm_val j χ v hχ⟩
def transportEquiv (hS : SMOne E) (hU : UnrAE E) (hS' : SMOne L) (hU' : UnrAE L) (j : E ≃+* L) : HChar L ≃* HChar E where
  toFun := transport j
  invFun := transport j.symm
  left_inv χ := by
    have h := transport_transport_symm hS' hU' j.symm χ
    rwa [RingEquiv.symm_symm] at h
  right_inv χ := transport_transport_symm hS hU j χ
  map_mul' := map_mul _
end Formalism.L2.Host.CT



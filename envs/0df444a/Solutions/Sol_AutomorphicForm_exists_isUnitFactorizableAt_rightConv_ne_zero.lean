-- Prove2me | solution 1 for AutomorphicForm.exists_isUnitFactorizableAt_rightConv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ec86930e-f305-5478-9127-ff749bc36010

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open IsDedekindDomain MeasureTheory

noncomputable section

namespace InfinitelyManyPlaces

open NumberField IsDedekindDomain

private theorem exists_isMaximal_comap_eq_span (K : Type) [Field K] [NumberField K] (p : Nat.Primes) :
    ∃ Q : Ideal (𝓞 K), Q.IsMaximal ∧ Q.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
  have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
  haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  refine Ideal.exists_ideal_over_maximal_of_isIntegral _ ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
  exact bot_le

private noncomputable def placeAbove (K : Type) [Field K] [NumberField K] (p : Nat.Primes) : HeightOneSpectrum (𝓞 K) :=
  ⟨(exists_isMaximal_comap_eq_span K p).choose, (exists_isMaximal_comap_eq_span K p).choose_spec.1.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField (exists_isMaximal_comap_eq_span K p).choose_spec.1
      (RingOfIntegers.not_isField K)⟩

private theorem placeAbove_injective (K : Type) [Field K] [NumberField K] : Function.Injective (placeAbove K) := by
  intro p q hpq
  have h : (placeAbove K p).asIdeal = (placeAbove K q).asIdeal := by rw [hpq]
  have hc : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by
    rw [← (exists_isMaximal_comap_eq_span K p).choose_spec.2, ← (exists_isMaximal_comap_eq_span K q).choose_spec.2]
    exact congrArg (Ideal.comap (algebraMap ℤ (𝓞 K))) h
  have ha : Associated ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := Ideal.span_singleton_eq_span_singleton.mp hc
  have hn : (p : ℕ) = (q : ℕ) := by
    have h' := Int.associated_iff_natAbs.mp ha
    rwa [Int.natAbs_natCast, Int.natAbs_natCast] at h'
  exact Subtype.ext hn

private theorem infinite_heightOneSpectrum
    (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  haveI : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOf_prime
  exact Infinite.of_injective _ (placeAbove_injective K)

end InfinitelyManyPlaces

section Basics

open AdelicDock

variable {K : Type} [Field K] [NumberField K]

private theorem continuous_val_finEmbed :
    Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      ((AdelicDock.finEmbed (𝓞 K) K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_const.prodMk (Units.continuous_val.matrix_elem i j)

private theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 K) K) :=
  Units.continuous_iff.mpr ⟨continuous_val_finEmbed,
    (continuous_val_finEmbed.comp continuous_inv).congr fun g => by
      rw [Function.comp_apply, map_inv]⟩

private theorem val_adelicArchGLIncl_apply (k : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    ((adelicArchGLIncl K k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      ((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  rfl

private theorem continuous_val_adelicArchGLIncl :
    Continuous fun k : GL (Fin 2) (InfiniteAdeleRing K) =>
      ((adelicArchGLIncl K k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [val_adelicArchGLIncl_apply]
  exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl K) :=
  Units.continuous_iff.mpr ⟨continuous_val_adelicArchGLIncl,
    (continuous_val_adelicArchGLIncl.comp continuous_inv).congr fun g => by
      rw [Function.comp_apply, map_inv]⟩

private theorem adelicGL_ext' {x y : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (h₂ : glFin (𝓞 K) K x = glFin (𝓞 K) K y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · simpa only [glArch_apply] using
      congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing K) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  · simpa only [glFin_apply] using
      congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₂

private theorem eq_archIncl_mul_finEmbed (x : AdelicGL2 (𝓞 K) K) :
    x = adelicArchGLIncl K (glArch (𝓞 K) K x) * AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K x) :=
  adelicGL_ext'
    (by rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one])
    (by rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul])

open scoped Classical in
private theorem continuous_of_isFactorizableTestFn {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f) :
    Continuous f := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩, ⟨hffl, -⟩, hfg⟩ := hf
  have hfa : Continuous fa := by
    rw [show fa = fun g => Φ (archEntries K g) from funext hfaΦ]
    refine hΦ.continuous.comp ?_
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)
  rw [show f = fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) from funext hfg]
  exact (hfa.comp (continuous_glArch (𝓞 K) K)).mul (hffl.continuous.comp (continuous_glFin (𝓞 K) K))

private theorem hasCompactSupport_of_isFactorizableTestFn {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f) :
    HasCompactSupport f := by
  obtain ⟨fa, ff, ⟨-, hfa⟩, ⟨-, hff⟩, hfg⟩ := hf
  have hK : IsCompact ((fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      adelicArchGLIncl K p.1 * AdelicDock.finEmbed (𝓞 K) K p.2) '' (tsupport fa ×ˢ tsupport ff)) :=
    (hfa.isCompact.prod hff.isCompact).image
      ((continuous_adelicArchGLIncl.comp continuous_fst).mul (continuous_finEmbed.comp continuous_snd))
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_cases ha : glArch (𝓞 K) K x ∈ tsupport fa
  · by_cases hb : glFin (𝓞 K) K x ∈ tsupport ff
    · exact absurd ⟨(glArch (𝓞 K) K x, glFin (𝓞 K) K x), ⟨ha, hb⟩, (eq_archIncl_mul_finEmbed x).symm⟩ hx
    · exact IsFactorizableTestFn.eq_zero_of_glFin K hfg (image_eq_zero_of_notMem_tsupport hb)
  · exact IsFactorizableTestFn.eq_zero_of_glArch K hfg (image_eq_zero_of_notMem_tsupport ha)

end Basics

namespace FiniteTestFactor

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel AdelicDock

section LocalAdelic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem glFin_ext {x y : GL (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R, AdelicLevel.finComponent R K w x = AdelicLevel.finComponent R K w y) :
    x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine FiniteAdeleRing.ext (R := R) (K := K) fun w => ?_
  have hw := congrArg (fun z : GL (Fin 2) (w.adicCompletion K) =>
    (z : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) (h w)
  simpa only [AdelicLevel.finComponent_apply] using hw

private theorem adelicGL_ext {x y : GL (Fin 2) (AdeleRing R K)}
    (harch : AdelicLevel.glArch R K x = AdelicLevel.glArch R K y)
    (hfin : AdelicLevel.glFin R K x = AdelicLevel.glFin R K y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h₁ := congrArg (fun z : GL (Fin 2) (InfiniteAdeleRing K) =>
    (z : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) harch
  have h₂ := congrArg (fun z : GL (Fin 2) (FiniteAdeleRing R K) =>
    (z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) hfin
  simp only [AdelicLevel.glArch_apply, AdelicLevel.glFin_apply] at h₁ h₂
  exact Prod.ext h₁ h₂

variable (v : HeightOneSpectrum R)

private def ι : GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (AdeleRing R K) :=
  (AdelicDock.finEmbed R K).comp (AdelicDock.localEmbed R K v)

private theorem ι_apply (h : GL (Fin 2) (v.adicCompletion K)) :
    ι R K v h = AdelicDock.finEmbed R K (AdelicDock.localEmbed R K v h) := rfl

private def compAt (g : GL (Fin 2) (AdeleRing R K)) : GL (Fin 2) (v.adicCompletion K) :=
  AdelicLevel.finComponent R K v (AdelicLevel.glFin R K g)

private theorem compAt_apply (g : GL (Fin 2) (AdeleRing R K)) :
    compAt R K v g = AdelicLevel.finComponent R K v (AdelicLevel.glFin R K g) := rfl

private theorem compAt_mul (g g' : GL (Fin 2) (AdeleRing R K)) :
    compAt R K v (g * g') = compAt R K v g * compAt R K v g' := by
  simp only [compAt_apply, map_mul]

private theorem compAt_inv (g : GL (Fin 2) (AdeleRing R K)) : compAt R K v g⁻¹ = (compAt R K v g)⁻¹ := by
  simp only [compAt_apply, map_inv]

private theorem glArch_ι (h : GL (Fin 2) (v.adicCompletion K)) : AdelicLevel.glArch R K (ι R K v h) = 1 :=
  AdelicDock.glArch_finEmbed R K _

private theorem glFin_ι (h : GL (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.glFin R K (ι R K v h) = AdelicDock.localEmbed R K v h :=
  AdelicDock.glFin_finEmbed R K _

private theorem compAt_ι (h : GL (Fin 2) (v.adicCompletion K)) : compAt R K v (ι R K v h) = h := by
  rw [compAt_apply, glFin_ι, AdelicDock.finComponent_localEmbed_self]

private theorem finComponent_glFin_ι_of_ne (h : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : AdelicLevel.finComponent R K w (AdelicLevel.glFin R K (ι R K v h)) = 1 := by
  rw [glFin_ι, AdelicDock.finComponent_localEmbed_of_ne R K v h hw]

private theorem inv_mul_ι_mul (g : GL (Fin 2) (AdeleRing R K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    g⁻¹ * ι R K v h * g = ι R K v ((compAt R K v g)⁻¹ * h * compAt R K v g) := by
  refine adelicGL_ext R K ?_ ?_
  · simp only [map_mul, map_inv, glArch_ι, mul_one, inv_mul_cancel, inv_one]
  · refine glFin_ext R K fun w => ?_
    by_cases hw : w = v
    · subst hw
      simp only [map_mul, map_inv, glFin_ι, AdelicDock.finComponent_localEmbed_self, compAt_apply]
    · have hne : ∀ x : GL (Fin 2) (v.adicCompletion K),
          AdelicLevel.finComponent R K w (AdelicDock.localEmbed R K v x) = 1 :=
        fun x => AdelicDock.finComponent_localEmbed_of_ne R K v x hw
      simp only [map_mul, map_inv, glFin_ι, hne, mul_one, inv_mul_cancel, inv_one]

private theorem mul_ι_conj (g : GL (Fin 2) (AdeleRing R K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    g * ι R K v ((compAt R K v g)⁻¹ * h * compAt R K v g) = ι R K v h * g := by
  rw [← inv_mul_ι_mul R K v g h, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem ι_mul_comm_of_compAt_eq_one {x : GL (Fin 2) (AdeleRing R K)} (hx : compAt R K v x = 1)
    (h : GL (Fin 2) (v.adicCompletion K)) : ι R K v h * x = x * ι R K v h := by
  have := mul_ι_conj R K v x h
  rw [hx, inv_one, one_mul, mul_one] at this
  exact this.symm

private def awayFrom (g : GL (Fin 2) (AdeleRing R K)) : GL (Fin 2) (AdeleRing R K) :=
  g * (ι R K v (compAt R K v g))⁻¹

private theorem awayFrom_mul_ι_compAt (g : GL (Fin 2) (AdeleRing R K)) :
    awayFrom R K v g * ι R K v (compAt R K v g) = g :=
  inv_mul_cancel_right g _

private theorem compAt_awayFrom (g : GL (Fin 2) (AdeleRing R K)) : compAt R K v (awayFrom R K v g) = 1 := by
  rw [awayFrom, compAt_mul, compAt_inv, compAt_ι, mul_inv_cancel]

private theorem finComponent_glFin_awayFrom_of_ne (g : GL (Fin 2) (AdeleRing R K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : AdelicLevel.finComponent R K w (AdelicLevel.glFin R K (awayFrom R K v g))
      = AdelicLevel.finComponent R K w (AdelicLevel.glFin R K g) := by
  rw [awayFrom]
  simp only [map_mul, map_inv]
  rw [finComponent_glFin_ι_of_ne R K v _ hw, inv_one, mul_one]

private theorem glArch_awayFrom (g : GL (Fin 2) (AdeleRing R K)) :
    AdelicLevel.glArch R K (awayFrom R K v g) = AdelicLevel.glArch R K g := by
  rw [awayFrom]
  simp only [map_mul, map_inv, glArch_ι, inv_one, mul_one]

private theorem ι_mul_awayFrom_comm (g : GL (Fin 2) (AdeleRing R K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    ι R K v h * awayFrom R K v g = awayFrom R K v g * ι R K v h :=
  ι_mul_comm_of_compAt_eq_one R K v (compAt_awayFrom R K v g) h

end LocalAdelic

section LevelComponents

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem mem_U_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, IsLocalLevelOne (𝓞 F) F w N
          (finComponent (𝓞 F) F w (glFin (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) _)
        ∧ IsLocalLevelOne (𝓞 F) F w N
          ((finComponent (𝓞 F) F w (glFin (𝓞 F) F h))⁻¹ : GL (Fin 2) _) := by
      intro w
      exact (mem_localLevelOne_iff (𝓞 F) F w (finComponent (𝓞 F) F w (glFin (𝓞 F) F h))).mp
        (hfin w)
    constructor
    · exact ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩,
        fun w => by
          rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
          exact (hlocal w).1.lowerRight⟩
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · exact (mem_finiteAdelicGL2Subgroup_iff F h).mpr harch

private theorem components_of_mem_U {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hh : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    glArch (𝓞 F) F h = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  refine ⟨(mem_finiteAdelicGL2Subgroup_iff F h).mp h2, fun w => ?_⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  rw [mem_localLevelOne_iff]
  obtain ⟨ha, hb⟩ := h1
  constructor
  · exact ⟨fun i j => ha.integral i j w, ha.lowerLeft w, by
      have := ha.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩
  · rw [← map_inv]
    exact ⟨fun i j => hb.integral i j w, hb.lowerLeft w, by
      have := hb.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩

private theorem comp_self (z : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = z := by
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem comp_of_ne (z : GL (Fin 2) (v.adicCompletion F)) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = 1 := by
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

omit [NumberField F] in
private theorem ne_bot_of_not_dvd {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) : N ≠ ⊥ := by
  rintro rfl
  exact hv (dvd_zero _)

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) : IsLocalLevelOne (𝓞 F) F v N m := by
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd (ne_bot_of_not_dvd F v hv) hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

private theorem mem_localLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      i j ∈ v.adicCompletionIntegers F) :
    k ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral F v hv hk, isLocalLevelOne_of_integral F v hv hk'⟩

private noncomputable abbrev wc (w : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (w.adicCompletion F) :=
  finComponent (𝓞 F) F w (glFin (𝓞 F) F (weyl (𝓞 F) F))

private theorem weyl_mul_self : weyl (𝓞 F) F * weyl (𝓞 F) F = 1 :=
  Units.ext (by simp [weyl, Matrix.one_fin_two])

private theorem wc_mul_self (w : HeightOneSpectrum (𝓞 F)) : wc F w * wc F w = 1 := by
  simp only [wc, ← map_mul, weyl_mul_self, map_one]

private theorem weyl_entry_mem (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (wc F w : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j ∈ w.adicCompletionIntegers F := by
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j <;> simp [weyl] <;>
    first
      | exact zero_mem_integralFiniteAdeles w
      | exact one_mem_integralFiniteAdeles w

private theorem wc_mem {N : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} (hw : ¬ w.asIdeal ∣ N) :
    wc F w ∈ localLevelOne (𝓞 F) F w N := by
  refine mem_localLevelOne_of_integral F w hw (weyl_entry_mem F w) fun i j => ?_
  rw [inv_eq_of_mul_eq_one_right (wc_mul_self F w)]
  exact weyl_entry_mem F w i j

private theorem comp_conj (w : HeightOneSpectrum (𝓞 F)) (h : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F))
      = (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w := by
  simp only [wc, map_mul, map_inv]

private theorem mem_P_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hU : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (hconj : ∀ w : HeightOneSpectrum (𝓞 F),
      (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hU
  refine Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 F) F N).mpr ⟨h1, ?_⟩, h2⟩
  have harch : glArch (𝓞 F) F h = 1 := (components_of_mem_U F hU).1
  have hz : (weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F ?_ fun w => ?_
    · simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
    · rw [comp_conj]
      exact hconj w
  refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F, (Subgroup.mem_inf.mp hz).1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem components_of_mem_P {N : Ideal (𝓞 F)} {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (w : HeightOneSpectrum (𝓞 F)) :
    (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p) * wc F w ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hp
  obtain ⟨-, hmap⟩ := (mem_principalLevel_iff (𝓞 F) F N).mp h1
  obtain ⟨z, hz, hzp⟩ := Subgroup.mem_map.mp hmap
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzp
  have hz' : (weyl (𝓞 F) F)⁻¹ * p * weyl (𝓞 F) F = z := by
    rw [← hzp]; group
  have harch : glArch (𝓞 F) F p = 1 := (mem_finiteAdelicGL2Subgroup_iff F p).mp h2
  have hzU : z ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine Subgroup.mem_inf.mpr ⟨hz, (mem_finiteAdelicGL2Subgroup_iff F z).mpr ?_⟩
    rw [← hz']
    simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
  rw [← comp_conj, hz']
  exact (components_of_mem_U F hzU).2 w

private theorem P_le_U (N : Ideal (𝓞 F)) :
    principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
  inf_le_inf_right _ (principalLevel_le_levelOne (𝓞 F) F N)

private theorem supported_mem_P {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {z : GL (Fin 2) (v.adicCompletion F)} (hz : z ∈ localLevelOne (𝓞 F) F v N) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z) ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  have hU : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F (glArch_finEmbed _ _ _) fun w => ?_
    by_cases hw : w = v
    · rw [hw, comp_self]
      exact hz
    · rw [comp_of_ne F v z hw]
      exact one_mem _
  refine mem_P_of_components F hU fun w => ?_
  by_cases hw : w = v
  · rw [hw, comp_self]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (wc_mem F hv)) hz) (wc_mem F hv)
  · rw [comp_of_ne F v z hw, mul_one, inv_mul_cancel]
    exact one_mem _

end LevelComponents

section Local

variable {F : Type} [Field F] [NumberField F]

private def levelMatrixSet (w : HeightOneSpectrum (𝓞 F)) (N : Ideal (𝓞 F)) :
    Set (Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) :=
  {m | IsLocalLevelOne (𝓞 F) F w N m}

private theorem levelMatrixSet_eq (w : HeightOneSpectrum (𝓞 F)) (N : Ideal (𝓞 F)) :
    levelMatrixSet w N
      = (⋂ i : Fin 2, ⋂ j : Fin 2, (fun m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F) => m i j) ⁻¹'
            (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
        ∩ (fun m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F) => m 1 0) ⁻¹'
            {y | Valued.v y ≤ idealBound (𝓞 F) N w}
        ∩ (fun m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F) => m 1 1 - 1) ⁻¹'
            {y | Valued.v y ≤ idealBound (𝓞 F) N w} := by
  ext m
  simp only [levelMatrixSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe]
  exact ⟨fun h => ⟨⟨h.integral, h.lowerLeft⟩, h.lowerRight⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

private theorem continuous_entry (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F) => m i j :=
  (continuous_apply j).comp (continuous_apply i)

private theorem isOpen_levelMatrixSet (w : HeightOneSpectrum (𝓞 F)) {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsOpen (levelMatrixSet w N) := by
  rw [levelMatrixSet_eq]
  refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (Valued.isOpen_valuationSubring _).preimage (continuous_entry w i j)
  · exact (isOpen_setOf_valued_le_idealBound w hN).preimage (continuous_entry w 1 0)
  · exact (isOpen_setOf_valued_le_idealBound w hN).preimage ((continuous_entry w 1 1).sub continuous_const)

private theorem isClosed_levelMatrixSet
    (w : HeightOneSpectrum (𝓞 F)) (N : Ideal (𝓞 F)) : IsClosed (levelMatrixSet w N) := by
  rw [levelMatrixSet_eq]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (isClosed_adicCompletionIntegers w).preimage (continuous_entry w i j)
  · exact (isClosed_setOf_valued_le_idealBound w N).preimage (continuous_entry w 1 0)
  · exact (isClosed_setOf_valued_le_idealBound w N).preimage ((continuous_entry w 1 1).sub continuous_const)

private theorem coe_localLevelOne_eq (w : HeightOneSpectrum (𝓞 F)) (N : Ideal (𝓞 F)) :
    (localLevelOne (𝓞 F) F w N : Set (GL (Fin 2) (w.adicCompletion F)))
      = (fun z : GL (Fin 2) (w.adicCompletion F) => (z : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) ⁻¹'
          levelMatrixSet w N
        ∩ (fun z : GL (Fin 2) (w.adicCompletion F) => ((z⁻¹ : GL (Fin 2) (w.adicCompletion F)) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) ⁻¹' levelMatrixSet w N := by
  ext z
  rw [SetLike.mem_coe, mem_localLevelOne_iff]
  rfl

private theorem isOpen_localLevelOne (w : HeightOneSpectrum (𝓞 F)) {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsOpen (localLevelOne (𝓞 F) F w N : Set (GL (Fin 2) (w.adicCompletion F))) := by
  rw [coe_localLevelOne_eq]
  exact ((isOpen_levelMatrixSet w hN).preimage Units.continuous_val).inter
    ((isOpen_levelMatrixSet w hN).preimage (Units.continuous_val.comp continuous_inv))

private theorem isClosed_localLevelOne (w : HeightOneSpectrum (𝓞 F)) (N : Ideal (𝓞 F)) :
    IsClosed (localLevelOne (𝓞 F) F w N : Set (GL (Fin 2) (w.adicCompletion F))) := by
  rw [coe_localLevelOne_eq]
  exact ((isClosed_levelMatrixSet w N).preimage Units.continuous_val).inter
    ((isClosed_levelMatrixSet w N).preimage (Units.continuous_val.comp continuous_inv))

private theorem mem_localIntegralSet_of_mem_localLevelOne {w : HeightOneSpectrum (𝓞 F)} {N : Ideal (𝓞 F)}
    {z : GL (Fin 2) (w.adicCompletion F)} (hz : z ∈ localLevelOne (𝓞 F) F w N) : z ∈ localIntegralSet F w := by
  obtain ⟨h1, h2⟩ := (mem_localLevelOne_iff (𝓞 F) F w z).mp hz
  exact (mem_localIntegralSet F w).mpr ⟨h1.integral, h2.integral⟩

private def localGroup (N₁ N₂ : Ideal (𝓞 F)) (w : HeightOneSpectrum (𝓞 F)) : Set (GL (Fin 2) (w.adicCompletion F)) :=
  {z | z ∈ localLevelOne (𝓞 F) F w N₁ ∧ z ∈ localLevelOne (𝓞 F) F w N₂ ∧
    (wc F w)⁻¹ * z * wc F w ∈ localLevelOne (𝓞 F) F w N₂}

private theorem localGroup_eq (N₁ N₂ : Ideal (𝓞 F)) (w : HeightOneSpectrum (𝓞 F)) :
    localGroup N₁ N₂ w
      = (localLevelOne (𝓞 F) F w N₁ : Set (GL (Fin 2) (w.adicCompletion F)))
        ∩ (localLevelOne (𝓞 F) F w N₂ : Set (GL (Fin 2) (w.adicCompletion F)))
        ∩ (fun z : GL (Fin 2) (w.adicCompletion F) => (wc F w)⁻¹ * z * wc F w) ⁻¹'
            (localLevelOne (𝓞 F) F w N₂ : Set (GL (Fin 2) (w.adicCompletion F))) := by
  ext z
  simp only [localGroup, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, and_assoc]

private theorem continuous_conj_wc (w : HeightOneSpectrum (𝓞 F)) :
    Continuous fun z : GL (Fin 2) (w.adicCompletion F) => (wc F w)⁻¹ * z * wc F w :=
  (continuous_const.mul continuous_id).mul continuous_const

private theorem isOpen_localGroup {N₁ N₂ : Ideal (𝓞 F)} (h₁ : N₁ ≠ ⊥) (h₂ : N₂ ≠ ⊥) (w : HeightOneSpectrum (𝓞 F)) :
    IsOpen (localGroup N₁ N₂ w) := by
  rw [localGroup_eq]
  exact ((isOpen_localLevelOne w h₁).inter (isOpen_localLevelOne w h₂)).inter
    ((isOpen_localLevelOne w h₂).preimage (continuous_conj_wc w))

private theorem isClosed_localGroup
    (N₁ N₂ : Ideal (𝓞 F)) (w : HeightOneSpectrum (𝓞 F)) : IsClosed (localGroup N₁ N₂ w) := by
  rw [localGroup_eq]
  exact ((isClosed_localLevelOne w N₁).inter (isClosed_localLevelOne w N₂)).inter
    ((isClosed_localLevelOne w N₂).preimage (continuous_conj_wc w))

private theorem localGroup_subset (N₁ N₂ : Ideal (𝓞 F)) (w : HeightOneSpectrum (𝓞 F)) :
    localGroup N₁ N₂ w ⊆ localIntegralSet F w :=
  fun _ hz => mem_localIntegralSet_of_mem_localLevelOne hz.1

private theorem isCompact_localGroup
    (N₁ N₂ : Ideal (𝓞 F)) (w : HeightOneSpectrum (𝓞 F)) : IsCompact (localGroup N₁ N₂ w) :=
  (isCompact_localIntegralSet F w).of_isClosed_subset (isClosed_localGroup N₁ N₂ w) (localGroup_subset N₁ N₂ w)

private theorem isLocalTestFn_indicator_localGroup {N₁ N₂ : Ideal (𝓞 F)} (h₁ : N₁ ≠ ⊥) (h₂ : N₂ ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 F)) :
    IsLocalTestFn F w ((localGroup N₁ N₂ w).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_localGroup h₁ h₂ w) (isClosed_localGroup N₁ N₂ w),
    HasCompactSupport.intro (isCompact_localGroup N₁ N₂ w) fun _ hz => by simp [hz]⟩

private theorem mem_localGroup_iff_of_not_dvd
    {N₁ N₂ : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} (hw₁ : ¬ w.asIdeal ∣ N₁)
    (hw₂ : ¬ w.asIdeal ∣ N₂) (z : GL (Fin 2) (w.adicCompletion F)) :
    z ∈ localGroup N₁ N₂ w ↔ z ∈ localIntegralSet F w := by
  refine ⟨fun hz => localGroup_subset N₁ N₂ w hz, fun hz => ?_⟩
  obtain ⟨hz1, hz2⟩ := (mem_localIntegralSet F w).mp hz
  have h₂ : z ∈ localLevelOne (𝓞 F) F w N₂ := mem_localLevelOne_of_integral F w hw₂ hz1 hz2
  refine ⟨mem_localLevelOne_of_integral F w hw₁ hz1 hz2, h₂, ?_⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (wc_mem F hw₂)) h₂) (wc_mem F hw₂)

private theorem finEmbed_mem_iff (N₁ N₂ : Ideal (𝓞 F)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finEmbed (𝓞 F) F h ∈ levelOne (𝓞 F) F N₁ ⊓ principalLevel (𝓞 F) F N₂ ⊓ finiteAdelicGL2Subgroup F
      ↔ ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w h ∈ localGroup N₁ N₂ w := by
  constructor
  · intro hU
    obtain ⟨⟨h1, h2⟩, hfin⟩ := Subgroup.mem_inf.mp hU
    have hU₁ : finEmbed (𝓞 F) F h ∈ levelOne (𝓞 F) F N₁ ⊓ finiteAdelicGL2Subgroup F := Subgroup.mem_inf.mpr ⟨h1, hfin⟩
    have hP : finEmbed (𝓞 F) F h ∈ principalLevel (𝓞 F) F N₂ ⊓ finiteAdelicGL2Subgroup F :=
      Subgroup.mem_inf.mpr ⟨h2, hfin⟩
    intro w
    have e1 := (components_of_mem_U F hU₁).2 w
    have e2 := (components_of_mem_U F (P_le_U F N₂ hP)).2 w
    have e3 := components_of_mem_P F hP w
    rw [glFin_finEmbed] at e1 e2 e3
    exact ⟨e1, e2, e3⟩
  · intro hw
    have hU₁ : finEmbed (𝓞 F) F h ∈ levelOne (𝓞 F) F N₁ ⊓ finiteAdelicGL2Subgroup F :=
      mem_U_of_components F (glArch_finEmbed (𝓞 F) F h) fun w => by rw [glFin_finEmbed]; exact (hw w).1
    have hU₂ : finEmbed (𝓞 F) F h ∈ levelOne (𝓞 F) F N₂ ⊓ finiteAdelicGL2Subgroup F :=
      mem_U_of_components F (glArch_finEmbed (𝓞 F) F h) fun w => by rw [glFin_finEmbed]; exact (hw w).2.1
    have hP : finEmbed (𝓞 F) F h ∈ principalLevel (𝓞 F) F N₂ ⊓ finiteAdelicGL2Subgroup F :=
      mem_P_of_components F hU₂ fun w => by rw [glFin_finEmbed]; exact (hw w).2.2
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hU₁).1, (Subgroup.mem_inf.mp hP).1⟩,
      (Subgroup.mem_inf.mp hU₁).2⟩

end Local

section Tier

variable {F : Type} [Field F] [NumberField F]

private def finSet (N₁ N₂ : Ideal (𝓞 F)) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  {h | finEmbed (𝓞 F) F h ∈ levelOne (𝓞 F) F N₁ ⊓ principalLevel (𝓞 F) F N₂ ⊓ finiteAdelicGL2Subgroup F}

private theorem finSet_eq {N₁ N₂ : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS₁ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₁)
    (hS₂ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₂) :
    finSet N₁ N₂
      = (⋂ w ∈ S, finComponent (𝓞 F) F w ⁻¹' localGroup N₁ N₂ w) ∩ unitFinSet F := by
  ext h
  simp only [finSet, Set.mem_setOf_eq, finEmbed_mem_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    unitFinSet]
  constructor
  · intro hw
    exact ⟨fun w _ => hw w, fun w => localGroup_subset N₁ N₂ w (hw w)⟩
  · rintro ⟨hS, hint⟩ w
    by_cases hwS : w ∈ S
    · exact hS w hwS
    · exact (mem_localGroup_iff_of_not_dvd (hS₁ w hwS) (hS₂ w hwS) _).mpr (hint w)

private theorem isOpen_finSet {N₁ N₂ : Ideal (𝓞 F)} (h₁ : N₁ ≠ ⊥) (h₂ : N₂ ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS₁ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₁)
    (hS₂ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₂) : IsOpen (finSet N₁ N₂) := by
  rw [finSet_eq hS₁ hS₂]
  exact (isOpen_biInter_finset fun w _ =>
    (isOpen_localGroup h₁ h₂ w).preimage (continuous_finComponent (𝓞 F) F w)).inter (isOpen_unitFinSet F)

private theorem isClosed_finSet {N₁ N₂ : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS₁ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₁)
    (hS₂ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₂) : IsClosed (finSet N₁ N₂) := by
  rw [finSet_eq hS₁ hS₂]
  exact (isClosed_biInter fun w _ =>
    (isClosed_localGroup N₁ N₂ w).preimage (continuous_finComponent (𝓞 F) F w)).inter (isCompact_unitFinSet F).isClosed

private theorem isCompact_finSet {N₁ N₂ : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS₁ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₁)
    (hS₂ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₂) : IsCompact (finSet N₁ N₂) :=
  (isCompact_unitFinSet F).of_isClosed_subset (isClosed_finSet hS₁ hS₂)
    (by rw [finSet_eq hS₁ hS₂]; exact Set.inter_subset_right)

private def finFactor (N₁ N₂ : Ideal (𝓞 F)) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (finSet N₁ N₂).indicator fun _ => (1 : ℂ)

private theorem isFinTestFactor_finFactor {N₁ N₂ : Ideal (𝓞 F)} (h₁ : N₁ ≠ ⊥) (h₂ : N₂ ≠ ⊥)
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS₁ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₁)
    (hS₂ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₂) : IsFinTestFactor F (finFactor N₁ N₂) :=
  ⟨isLocallyConstant_indicator_one (isOpen_finSet h₁ h₂ hS₁ hS₂) (isClosed_finSet hS₁ hS₂),
    HasCompactSupport.intro (isCompact_finSet hS₁ hS₂) fun _ hh => by simp [finFactor, hh]⟩

private def tensor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (N₁ N₂ : Ideal (𝓞 F))
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) : ℂ :=
  fa (glArch (𝓞 F) F g) * finFactor N₁ N₂ (glFin (𝓞 F) F g)

private theorem isUnitFactorizableAt_tensor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    {N₁ N₂ : Ideal (𝓞 F)} (h₁ : N₁ ≠ ⊥) (h₂ : N₂ ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS₁ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₁)
    (hS₂ : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ¬ w.asIdeal ∣ N₂) :
    IsUnitFactorizableAt F ⊥ S (tensor fa N₁ N₂) := by
  refine ⟨isBiInvariantUnder_bot F _, fa, finFactor N₁ N₂, fun w => (localGroup N₁ N₂ w).indicator fun _ => (1 : ℂ),
    hfa, isFinTestFactor_finFactor h₁ h₂ hS₁ hS₂, fun w _ => isLocalTestFn_indicator_localGroup h₁ h₂ w, ?_, ?_,
    fun _ => rfl⟩
  ·
    intro h hint
    have hmem : h ∈ finSet N₁ N₂ ↔ ∀ w ∈ S, finComponent (𝓞 F) F w h ∈ localGroup N₁ N₂ w := by
      rw [finSet_eq hS₁ hS₂]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, unitFinSet, Set.mem_setOf_eq]
      constructor
      · exact fun hh => hh.1
      · intro hh
        refine ⟨hh, fun w => ?_⟩
        by_cases hwS : w ∈ S
        · exact localGroup_subset N₁ N₂ w (hh w hwS)
        · exact hint w hwS
    by_cases hall : ∀ w ∈ S, finComponent (𝓞 F) F w h ∈ localGroup N₁ N₂ w
    · rw [finFactor, Set.indicator_of_mem (hmem.mpr hall)]
      exact (Finset.prod_eq_one fun w hw => Set.indicator_of_mem (hall w hw) _).symm
    · rw [finFactor, Set.indicator_of_notMem (fun hh => hall (hmem.mp hh))]
      obtain ⟨w, hwS, hw⟩ : ∃ w ∈ S, finComponent (𝓞 F) F w h ∉ localGroup N₁ N₂ w := by simpa using hall
      exact (Finset.prod_eq_zero hwS (Set.indicator_of_notMem hw _)).symm
  ·
    rintro h ⟨w, hw, hwh⟩
    have hnot : h ∉ finSet N₁ N₂ := by
      intro hh
      rw [finSet_eq hS₁ hS₂] at hh
      exact hwh (hh.2 w)
    exact Set.indicator_of_notMem hnot _

private theorem finEmbed_glFin_of_mem_fin {u : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hu : u ∈ finiteAdelicGL2Subgroup F) :
    finEmbed (𝓞 F) F (glFin (𝓞 F) F u) = u := by
  refine adelicGL_ext (𝓞 F) F ?_ ?_
  · rw [glArch_finEmbed, (mem_finiteAdelicGL2Subgroup_iff F u).mp hu]
  · rw [glFin_finEmbed]

private theorem tensor_mul_left (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (N₁ N₂ : Ideal (𝓞 F))
    {u : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hu : u ∈ levelOne (𝓞 F) F N₁ ⊓ principalLevel (𝓞 F) F N₂ ⊓ finiteAdelicGL2Subgroup F)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) : tensor fa N₁ N₂ (u * g) = tensor fa N₁ N₂ g := by
  have hfin : u ∈ finiteAdelicGL2Subgroup F := (Subgroup.mem_inf.mp hu).2
  have harch : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hfin
  have hset : glFin (𝓞 F) F (u * g) ∈ finSet N₁ N₂ ↔ glFin (𝓞 F) F g ∈ finSet N₁ N₂ := by
    simp only [finSet, Set.mem_setOf_eq, map_mul, finEmbed_glFin_of_mem_fin hfin]
    exact Subgroup.mul_mem_cancel_left _ hu
  unfold tensor finFactor
  rw [map_mul, harch, one_mul]
  congr 1
  by_cases hg : glFin (𝓞 F) F g ∈ finSet N₁ N₂
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hset.mpr hg)]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun hh => hg (hset.mp hh))]

private theorem mem_of_ne_zero (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (N₁ N₂ : Ideal (𝓞 F))
    {x : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hx : tensor fa N₁ N₂ x ≠ 0) :
    finEmbed (𝓞 F) F (glFin (𝓞 F) F x)
      ∈ levelOne (𝓞 F) F N₁ ⊓ principalLevel (𝓞 F) F N₂ ⊓ finiteAdelicGL2Subgroup F := by
  by_contra hnot
  apply hx
  unfold tensor finFactor
  rw [Set.indicator_of_notMem (show glFin (𝓞 F) F x ∉ finSet N₁ N₂ from hnot), mul_zero]

private theorem tensor_eq_of_mem (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (N₁ N₂ : Ideal (𝓞 F))
    {x : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hx : glFin (𝓞 F) F x ∈ finSet N₁ N₂) :
    tensor fa N₁ N₂ x = fa (glArch (𝓞 F) F x) := by
  unfold tensor finFactor
  rw [Set.indicator_of_mem hx, mul_one]

private theorem tensor_eq_zero_of_notMem (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (N₁ N₂ : Ideal (𝓞 F))
    {x : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hx : glFin (𝓞 F) F x ∉ finSet N₁ N₂) : tensor fa N₁ N₂ x = 0 := by
  unfold tensor finFactor
  rw [Set.indicator_of_notMem hx, mul_zero]

end Tier

end FiniteTestFactor

namespace ArchBump

section EntrySq
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix

variable {K : Type*} [NormedField K]

private def entrySq (m : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖m 0 0‖ ^ 2 + ‖m 0 1‖ ^ 2 + (‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2)

private theorem entrySq_nonneg (m : Matrix (Fin 2) (Fin 2) K) : 0 ≤ entrySq m := by
  unfold entrySq
  positivity

private theorem entrySq_mul_of_isRowIsometry (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : entrySq (m * (k : Matrix (Fin 2) (Fin 2) K)) = entrySq m := by
  simp only [entrySq, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hk.2 (m 0 0) (m 0 1), hk.2 (m 1 0) (m 1 1)]

private theorem entrySq_adjugate (m : Matrix (Fin 2) (Fin 2) K) : entrySq m.adjugate = entrySq m := by
  rw [Matrix.adjugate_fin_two]
  simp only [entrySq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, norm_neg]
  ring

private theorem adjugate_eq_inv_of_mem {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) :
    (k : Matrix (Fin 2) (Fin 2) K).adjugate = ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have hdet : (k : Matrix (Fin 2) (Fin 2) K).det = 1 := ((mem_rowIsometrySubgroup₀_iff K).mp hk).1
  rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]

private theorem entrySq_mul_of_mem {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (m : Matrix (Fin 2) (Fin 2) K) : entrySq ((k : Matrix (Fin 2) (Fin 2) K) * m) = entrySq m := by
  have hk' : IsRowIsometry (k⁻¹ : GL (Fin 2) K) :=
    ((mem_rowIsometrySubgroup₀_iff K).mp (inv_mem hk)).2
  rw [← entrySq_adjugate, Matrix.adjugate_mul_distrib, adjugate_eq_inv_of_mem hk,
    entrySq_mul_of_isRowIsometry _ hk', entrySq_adjugate]

private theorem entrySq_mul_of_mem' (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K}
    (hk : k ∈ rowIsometrySubgroup₀ K) : entrySq (m * (k : Matrix (Fin 2) (Fin 2) K)) = entrySq m :=
  entrySq_mul_of_isRowIsometry m ((mem_rowIsometrySubgroup₀_iff K).mp hk).2

private theorem entrySq_conj {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) (m : Matrix (Fin 2) (Fin 2) K) :
    entrySq ((k : Matrix (Fin 2) (Fin 2) K) * m * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = entrySq m := by
  rw [entrySq_mul_of_mem' _ (inv_mem hk), entrySq_mul_of_mem hk]

private theorem det_mul_of_mem {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) (m : Matrix (Fin 2) (Fin 2) K) :
    ((k : Matrix (Fin 2) (Fin 2) K) * m).det = m.det := by
  rw [Matrix.det_mul, ((mem_rowIsometrySubgroup₀_iff K).mp hk).1, one_mul]

private theorem det_mul_of_mem' (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) :
    (m * (k : Matrix (Fin 2) (Fin 2) K)).det = m.det := by
  rw [Matrix.det_mul, ((mem_rowIsometrySubgroup₀_iff K).mp hk).1, mul_one]

private theorem conj_sub_one (k : GL (Fin 2) K) (g : Matrix (Fin 2) (Fin 2) K) :
    (k : Matrix (Fin 2) (Fin 2) K) * g * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1
      = (k : Matrix (Fin 2) (Fin 2) K) * (g - 1) * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have h : (k : Matrix (Fin 2) (Fin 2) K) * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, h]

private theorem entrySq_conj_sub_one {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (g : Matrix (Fin 2) (Fin 2) K) :
    entrySq ((k : Matrix (Fin 2) (Fin 2) K) * g * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1)
      = entrySq (g - 1) := by
  rw [conj_sub_one, entrySq_conj hk]

private def localBump (β₁ β₂ : ℝ → ℝ) (m : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  β₁ (entrySq m) * β₂ (‖m.det‖ ^ 2)

private theorem localBump_mul_of_mem (β₁ β₂ : ℝ → ℝ) {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (m : Matrix (Fin 2) (Fin 2) K) :
    localBump β₁ β₂ ((k : Matrix (Fin 2) (Fin 2) K) * m) = localBump β₁ β₂ m := by
  rw [localBump, localBump, entrySq_mul_of_mem hk, det_mul_of_mem hk]

private theorem localBump_mul_of_mem' (β₁ β₂ : ℝ → ℝ) (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K}
    (hk : k ∈ rowIsometrySubgroup₀ K) :
    localBump β₁ β₂ (m * (k : Matrix (Fin 2) (Fin 2) K)) = localBump β₁ β₂ m := by
  rw [localBump, localBump, entrySq_mul_of_mem' m hk, det_mul_of_mem' m hk]

end EntrySq

section WitnessGeneric
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix NumberField NumberField.InfinitePlace
open scoped Classical

variable {K : Type*} [NormedField K]

variable {L : Type*} [NormedField L]

private theorem localBump_map (β₁ β₂ : ℝ → ℝ) (f : K →+* L) (hf : Isometry f) (m : Matrix (Fin 2) (Fin 2) K) :
    localBump β₁ β₂ (m.map f) = localBump β₁ β₂ m := by
  have hn : ∀ x : K, ‖f x‖ = ‖x‖ := fun x => by
    simpa [dist_eq_norm] using hf.dist_eq x 0
  have hdet : (m.map f).det = f m.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  simp only [localBump, entrySq, Matrix.map_apply, hn, hdet]

end WitnessGeneric

section Witness
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix NumberField NumberField.InfinitePlace
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private def realCoord (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsReal w}) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => (X i j).1 v

private def complexCoord (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
    (v : {w : InfinitePlace F // IsComplex w}) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => (X i j).2 v

private noncomputable def witness (β₁ β₂ : ℝ → ℝ) (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) : ℂ :=
  (∏ v : {w : InfinitePlace F // IsReal w}, (localBump β₁ β₂ (realCoord F X v) : ℂ)) *
    ∏ v : {w : InfinitePlace F // IsComplex w}, (localBump β₁ β₂ (complexCoord F X v) : ℂ)

private noncomputable def archFactor (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  ∏ w : InfinitePlace F,
    (localBump β₁ β₂ (AdelicLevel.archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) : ℂ)

omit [NumberField F] in
private theorem realCoord_archEntries (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsReal w}) :
    localBump β₁ β₂ (realCoord F (archEntries F g) v)
      = localBump β₁ β₂ (AdelicLevel.archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) := by
  rw [← localBump_map β₁ β₂ (Completion.extensionEmbeddingOfIsReal v.2)
    (Completion.isometry_extensionEmbeddingOfIsReal v.2)]
  congr 1

omit [NumberField F] in
private theorem complexCoord_archEntries (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsComplex w}) :
    localBump β₁ β₂ (complexCoord F (archEntries F g) v)
      = localBump β₁ β₂ (AdelicLevel.archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) := by
  rw [← localBump_map β₁ β₂ (Completion.extensionEmbedding v.1) (Completion.isometry_extensionEmbedding v.1)]
  congr 1

private theorem archFactor_eq_witness (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archFactor F β₁ β₂ g = witness F β₁ β₂ (archEntries F g) := by
  unfold archFactor witness
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => IsReal w)]
  congr 1
  · exact Fintype.prod_congr _ _ fun v => by rw [realCoord_archEntries]
  · exact Fintype.prod_equiv (Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ IsReal w)
      (q := fun w : InfinitePlace F => IsComplex w) fun _ => not_isReal_iff_isComplex) _ _
      fun v => by rw [complexCoord_archEntries]; rfl

private theorem contDiff_det_of {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedCommRing 𝔸]
    [NormedAlgebra ℝ 𝔸] {a b c d : E → 𝔸} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => (Matrix.of ![![a x, b x], ![c x, d x]]).det := by
  simp only [Matrix.det_fin_two_of]
  exact (ha.mul hd).sub (hb.mul hc)

private theorem contDiff_localBump_of {E 𝕂 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕂]
    {β₁ β₂ : ℝ → ℝ} (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂) {a b c d : E → 𝕂}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => localBump β₁ β₂ (Matrix.of ![![a x, b x], ![c x, d x]]) := by
  have hsq : ContDiff ℝ (⊤ : ℕ∞) fun x => entrySq (Matrix.of ![![a x, b x], ![c x, d x]]) := by
    simp only [entrySq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ((ha.norm_sq (𝕜 := 𝕂)).add (hb.norm_sq (𝕜 := 𝕂))).add
      ((hc.norm_sq (𝕜 := 𝕂)).add (hd.norm_sq (𝕜 := 𝕂)))
  have hdet : ContDiff ℝ (⊤ : ℕ∞) fun x => ‖(Matrix.of ![![a x, b x], ![c x, d x]]).det‖ ^ 2 :=
    (contDiff_det_of ha hb hc hd).norm_sq (𝕜 := 𝕂)
  exact (hβ₁.comp hsq).mul (hβ₂.comp hdet)

private theorem contDiff_coord_real (v : {w : InfinitePlace F // IsReal w}) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => (X i j).1 v := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => X i j :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedEmbedding.mixedSpace F) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → mixedEmbedding.mixedSpace F) i)).contDiff
  exact (ContinuousLinearMap.proj (R := ℝ) v).contDiff.comp h.fst

private theorem contDiff_coord_complex (v : {w : InfinitePlace F // IsComplex w}) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => (X i j).2 v := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => X i j :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedEmbedding.mixedSpace F) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → mixedEmbedding.mixedSpace F) i)).contDiff
  exact (ContinuousLinearMap.proj (R := ℝ) v).contDiff.comp h.snd

omit [NumberField F] in
private theorem realCoord_eq
    (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsReal w}) :
    realCoord F X v = Matrix.of ![![(X 0 0).1 v, (X 0 1).1 v], ![(X 1 0).1 v, (X 1 1).1 v]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] in
private theorem complexCoord_eq (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
    (v : {w : InfinitePlace F // IsComplex w}) :
    complexCoord F X v = Matrix.of ![![(X 0 0).2 v, (X 0 1).2 v], ![(X 1 0).2 v, (X 1 1).2 v]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem contDiff_witness {β₁ β₂ : ℝ → ℝ} (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂) :
    ContDiff ℝ (⊤ : ℕ∞) (witness F β₁ β₂) := by
  unfold witness
  refine ContDiff.mul (contDiff_prod fun v _ => ?_) (contDiff_prod fun v _ => ?_)
  · simp only [realCoord_eq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_localBump_of hβ₁ hβ₂ (contDiff_coord_real F v 0 0)
      (contDiff_coord_real F v 0 1) (contDiff_coord_real F v 1 0) (contDiff_coord_real F v 1 1))
  · simp only [complexCoord_eq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_localBump_of hβ₁ hβ₂ (contDiff_coord_complex F v 0 0)
      (contDiff_coord_complex F v 0 1) (contDiff_coord_complex F v 1 0) (contDiff_coord_complex F v 1 1))

private theorem archFactor_smooth {β₁ β₂ : ℝ → ℝ} (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ ∀ g, archFactor F β₁ β₂ g = Φ (archEntries F g) :=
  ⟨witness F β₁ β₂, contDiff_witness F hβ₁ hβ₂, archFactor_eq_witness F β₁ β₂⟩

end Witness

section EntryBounds
open AutomorphicForm Matrix NumberField NumberField.InfinitePlace NumberField.AdelicLevel

variable {K : Type*} [NormedField K]

private theorem sq_norm_entry_le (m : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) : ‖m i j‖ ^ 2 ≤ entrySq m := by
  have h00 := sq_nonneg ‖m 0 0‖
  have h01 := sq_nonneg ‖m 0 1‖
  have h10 := sq_nonneg ‖m 1 0‖
  have h11 := sq_nonneg ‖m 1 1‖
  fin_cases i <;> fin_cases j <;> simp only [entrySq, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> linarith

private theorem norm_entry_le_sqrt {m : Matrix (Fin 2) (Fin 2) K} {A : ℝ} (hm : entrySq m ≤ A) (i j : Fin 2) :
    ‖m i j‖ ≤ Real.sqrt A :=
  Real.le_sqrt_of_sq_le ((sq_norm_entry_le m i j).trans hm)

private theorem norm_inv_entry_le {m : Matrix (Fin 2) (Fin 2) K} {A a : ℝ} (ha : 0 < a) (hm : entrySq m ≤ A)
    (hd : a ≤ ‖m.det‖ ^ 2) (i j : Fin 2) : ‖m⁻¹ i j‖ ≤ Real.sqrt A / Real.sqrt a := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul]
  have hadj : ‖m.adjugate i j‖ ≤ Real.sqrt A :=
    norm_entry_le_sqrt (by rw [entrySq_adjugate]; exact hm) i j
  have hdet : Real.sqrt a ≤ ‖m.det‖ := by
    calc Real.sqrt a ≤ Real.sqrt (‖m.det‖ ^ 2) := Real.sqrt_le_sqrt hd
      _ = ‖m.det‖ := Real.sqrt_sq (norm_nonneg _)
  rw [Ring.inverse_eq_inv, norm_inv, div_eq_inv_mul]
  exact mul_le_mul (inv_anti₀ (Real.sqrt_pos.mpr ha) hdet) hadj (norm_nonneg _)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

end EntryBounds

section Support
open AutomorphicForm Matrix NumberField NumberField.InfinitePlace NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]

private def compMat (w : InfinitePlace F) (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) w.Completion :=
  m.map fun x => x w

omit [NumberField F] in
private theorem compMat_coe (w : InfinitePlace F) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    compMat F w (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      = (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) := by
  ext i j
  rfl

omit [NumberField F] in
private theorem continuous_compMat (w : InfinitePlace F) : Continuous (compMat F w) :=
  show Continuous (fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) => m.map fun x => x w) from
    continuous_id.matrix_map (continuous_apply w)

private def boundedSet (A a : ℝ) : Set (GL (Fin 2) (InfiniteAdeleRing F)) :=
  {g | ∀ w : InfinitePlace F, entrySq (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) ≤ A ∧
    a ≤ ‖(archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2}

private theorem support_archFactor_subset {β₁ β₂ : ℝ → ℝ} {A a : ℝ} (hβ₁ : ∀ t, A < t → β₁ t = 0)
    (hβ₂ : ∀ t, t < a → β₂ t = 0) : Function.support (archFactor F β₁ β₂) ⊆ boundedSet F A a := by
  intro g hg w
  by_contra hw
  apply hg
  unfold archFactor
  refine Finset.prod_eq_zero (Finset.mem_univ w) ?_
  rw [not_and_or] at hw
  rcases hw with hw | hw
  · rw [localBump, hβ₁ _ (not_le.mp hw), zero_mul, Complex.ofReal_zero]
  · rw [localBump, hβ₂ _ (not_le.mp hw), mul_zero, Complex.ofReal_zero]

private def entryBall (r : ℝ) : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
    (Set.pi Set.univ (fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) r) :
      Set (InfiniteAdeleRing F))

omit [NumberField F] in
private theorem mem_entryBall {r : ℝ} {m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ (i j : Fin 2) (w : InfinitePlace F), ‖m i j w‖ ≤ r) : m ∈ entryBall F r :=
  Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => Set.mem_univ_pi.mpr fun w => by
    simpa [Metric.mem_closedBall, dist_zero_right] using h i j w

omit [NumberField F] in
private theorem isCompact_entryBall (r : ℝ) : IsCompact (entryBall F r) := by
  have hball : ∀ w : InfinitePlace F, IsCompact (Metric.closedBall (0 : w.Completion) r) := fun w => by
    have h := (Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall (0 : ℂ) r)
    rwa [← map_zero (Completion.extensionEmbedding w),
      (Completion.isometry_extensionEmbedding w).preimage_closedBall] at h
  have hB : IsCompact (Set.pi Set.univ (fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) r) :
      Set (InfiniteAdeleRing F)) :=
    isCompact_univ_pi fun w => hball w
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hB

omit [NumberField F] in

private theorem isCompact_boundedSet {A a : ℝ} (ha : 0 < a) : IsCompact (boundedSet F A a) := by
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  set M := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)
  let C : Set (M × Mᵐᵒᵖ) :=
    {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1 ∧
      ∀ w : InfinitePlace F, entrySq (compMat F w p.1) ≤ A ∧ a ≤ ‖(compMat F w p.1).det‖ ^ 2}
  have himage : Units.embedProduct M '' boundedSet F A a = C := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨?_, ?_, fun w => ?_⟩
      · simp [Units.embedProduct_apply]
      · simp [Units.embedProduct_apply]
      · simpa [Units.embedProduct_apply, compMat_coe] using hg w
    · rintro ⟨h₁, h₂, hw⟩
      refine ⟨⟨p.1, MulOpposite.unop p.2, h₁, h₂⟩, fun w => ?_, ?_⟩
      · simpa [← compMat_coe] using hw w
      · simp [Units.embedProduct_apply]
  rw [himage]
  have hclosed : IsClosed C := by
    have h1 : IsClosed {p : M × Mᵐᵒᵖ | p.1 * MulOpposite.unop p.2 = 1} :=
      isClosed_eq (continuous_fst.mul MulOpposite.continuous_unop.snd') continuous_const
    have h2 : IsClosed {p : M × Mᵐᵒᵖ | MulOpposite.unop p.2 * p.1 = 1} :=
      isClosed_eq (MulOpposite.continuous_unop.snd'.mul continuous_fst) continuous_const
    have h3 : IsClosed {p : M × Mᵐᵒᵖ | ∀ w : InfinitePlace F,
        entrySq (compMat F w p.1) ≤ A ∧ a ≤ ‖(compMat F w p.1).det‖ ^ 2} := by
      rw [Set.setOf_forall]
      refine isClosed_iInter fun w => ?_
      have hc : Continuous fun p : M × Mᵐᵒᵖ => compMat F w p.1 := (continuous_compMat F w).comp continuous_fst
      have he : ∀ i j : Fin 2, Continuous fun p : M × Mᵐᵒᵖ => compMat F w p.1 i j := fun i j =>
        hc.matrix_elem i j
      have hsq : Continuous fun p : M × Mᵐᵒᵖ => entrySq (compMat F w p.1) :=
        (((he 0 0).norm.pow 2).add ((he 0 1).norm.pow 2)).add
          (((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2))
      have hdet : Continuous fun p : M × Mᵐᵒᵖ => ‖(compMat F w p.1).det‖ ^ 2 := (hc.matrix_det.norm).pow 2
      exact (isClosed_le hsq continuous_const).inter (isClosed_le continuous_const hdet)
    exact h1.inter (h2.inter h3)
  have hsub : C ⊆ entryBall F (Real.sqrt A) ×ˢ (MulOpposite.op '' entryBall F (Real.sqrt A / Real.sqrt a)) := by
    rintro ⟨x, y⟩ ⟨h₁, h₂, hw⟩
    refine ⟨mem_entryBall F fun i j w => ?_, MulOpposite.unop y, mem_entryBall F fun i j w => ?_,
      MulOpposite.op_unop y⟩
    · have := norm_entry_le_sqrt (hw w).1 i j
      simpa [compMat, Matrix.map_apply] using this
    · have hinv : compMat F w (MulOpposite.unop y) = (compMat F w x)⁻¹ := by
        have hmul : compMat F w x * compMat F w (MulOpposite.unop y) = 1 := by
          calc compMat F w x * compMat F w (MulOpposite.unop y)
              = compMat F w (x * MulOpposite.unop y) :=
                (Matrix.map_mul (f := Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w)).symm
            _ = compMat F w 1 := by rw [h₁]
            _ = 1 := Matrix.map_one _ rfl rfl
        exact (Matrix.inv_eq_right_inv hmul).symm
      have := norm_inv_entry_le ha (hw w).1 (hw w).2 i j
      rw [← hinv] at this
      simpa [compMat, Matrix.map_apply] using this
  exact ((isCompact_entryBall F _).prod ((isCompact_entryBall F _).image MulOpposite.continuous_op)).of_isClosed_subset
    hclosed hsub

private theorem hasCompactSupport_archFactor {β₁ β₂ : ℝ → ℝ} {A a : ℝ} (ha : 0 < a) (hβ₁ : ∀ t, A < t → β₁ t = 0)
    (hβ₂ : ∀ t, t < a → β₂ t = 0) : HasCompactSupport (archFactor F β₁ β₂) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_boundedSet F ha) (support_archFactor_subset F hβ₁ hβ₂)

end Support

section PlaceProduct
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix NumberField NumberField.AdelicLevel IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

private noncomputable def placeProduct (φ : ∀ w : InfinitePlace F, Matrix (Fin 2) (Fin 2) w.Completion → ℝ)
    (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  ∏ w : InfinitePlace F, (φ w (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) : ℂ)

omit [NumberField F] in
private theorem archRowIsometryInclAt₀_apply (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    archRowIsometryInclAt₀ F w k = archGLIncl F w (k : GL (Fin 2) w.Completion) :=
  rfl

private theorem tensor_conj {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = fa y)
    (ffn : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F),
      fa (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹)) *
          ffn (glFin (𝓞 F) F (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹))
        = fa (glArch (𝓞 F) F y) * ffn (glFin (𝓞 F) F y) := by
  intro w k y
  rw [map_mul, map_mul, map_inv, glArch_rowIsometryInclAt₀, hfa, map_mul, map_mul, map_inv,
    glFin_rowIsometryInclAt₀, one_mul, inv_one, mul_one]

end PlaceProduct

end ArchBump

namespace ArchLocalizer

open ArchBump AutomorphicForm AutomorphicForm.WindowedSiegel Matrix NumberField NumberField.InfinitePlace
open NumberField.AdelicLevel
open scoped Classical

section Shift

variable {K : Type*} [NormedField K]

private def shiftBump (β : ℝ → ℝ) (m : Matrix (Fin 2) (Fin 2) K) : ℝ := β (entrySq (m - 1))

private theorem shiftBump_conj (β : ℝ → ℝ) {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (m : Matrix (Fin 2) (Fin 2) K) :
    shiftBump β ((k : Matrix (Fin 2) (Fin 2) K) * m * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = shiftBump β m := by
  unfold shiftBump
  rw [entrySq_conj_sub_one hk]

private theorem localBump_conj (β₁ β₂ : ℝ → ℝ) {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (m : Matrix (Fin 2) (Fin 2) K) :
    localBump β₁ β₂ ((k : Matrix (Fin 2) (Fin 2) K) * m * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = localBump β₁ β₂ m := by
  rw [localBump_mul_of_mem' β₁ β₂ _ (inv_mem hk), localBump_mul_of_mem β₁ β₂ hk]

private def localA (β₁ β₂ β₃ : ℝ → ℝ) (m : Matrix (Fin 2) (Fin 2) K) : ℝ := localBump β₁ β₂ m * shiftBump β₃ m

private theorem localA_conj (β₁ β₂ β₃ : ℝ → ℝ) {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (m : Matrix (Fin 2) (Fin 2) K) :
    localA β₁ β₂ β₃ ((k : Matrix (Fin 2) (Fin 2) K) * m * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = localA β₁ β₂ β₃ m := by
  unfold localA
  rw [localBump_conj β₁ β₂ hk, shiftBump_conj β₃ hk]

private theorem localA_conj' (β₁ β₂ β₃ : ℝ → ℝ) (k : rowIsometrySubgroup₀ K) (y : GL (Fin 2) K) :
    localA β₁ β₂ β₃ (((k : GL (Fin 2) K) * y * (k : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = localA β₁ β₂ β₃ (y : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, Units.val_mul]
  exact localA_conj β₁ β₂ β₃ k.2 _

private theorem localA_nonneg {β₁ β₂ β₃ : ℝ → ℝ} (h₁ : ∀ t, 0 ≤ β₁ t) (h₂ : ∀ t, 0 ≤ β₂ t) (h₃ : ∀ t, 0 ≤ β₃ t)
    (m : Matrix (Fin 2) (Fin 2) K) : 0 ≤ localA β₁ β₂ β₃ m :=
  mul_nonneg (mul_nonneg (h₁ _) (h₂ _)) (h₃ _)

private theorem entrySq_one : entrySq (1 : Matrix (Fin 2) (Fin 2) K) = 2 := by
  norm_num [entrySq]

private theorem entrySq_zero : entrySq (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  simp [entrySq]

private theorem localA_one {β₁ β₂ β₃ : ℝ → ℝ} (h₁ : β₁ 2 = 1) (h₂ : β₂ 1 = 1) (h₃ : β₃ 0 = 1) :
    localA β₁ β₂ β₃ (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp only [localA, localBump, shiftBump, entrySq_one, Matrix.det_one, norm_one, one_pow, sub_self, entrySq_zero,
    h₁, h₂, h₃, mul_one]

private theorem shift_ne_zero_of_localA_ne_zero {β₁ β₂ β₃ : ℝ → ℝ} {m : Matrix (Fin 2) (Fin 2) K}
    (h : localA β₁ β₂ β₃ m ≠ 0) : β₃ (entrySq (m - 1)) ≠ 0 :=
  fun h3 => h (by simp [localA, shiftBump, h3])

private theorem shiftBump_map {L : Type*} [NormedField L] (β : ℝ → ℝ) (f : K →+* L) (hf : Isometry f)
    (m : Matrix (Fin 2) (Fin 2) K) : shiftBump β (m.map f) = shiftBump β m := by
  have hn : ∀ x : K, ‖f x‖ = ‖x‖ := fun x => by
    simpa [dist_eq_norm] using hf.dist_eq x 0
  have h1 : m.map f - 1 = (m - 1).map f := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  unfold shiftBump
  rw [h1]
  simp only [entrySq, Matrix.map_apply, hn]

private theorem contDiff_shiftBump_of {E 𝕂 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕂] {β : ℝ → ℝ}
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) {a b c d : E → 𝕂} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => shiftBump β (Matrix.of ![![a x, b x], ![c x, d x]]) := by
  have hm : ∀ x, (Matrix.of ![![a x, b x], ![c x, d x]] : Matrix (Fin 2) (Fin 2) 𝕂) - 1
      = Matrix.of ![![a x - 1, b x], ![c x, d x - 1]] := by
    intro x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  have hsq : ContDiff ℝ (⊤ : ℕ∞) fun x => entrySq (Matrix.of ![![a x - 1, b x], ![c x, d x - 1]]) := by
    simp only [entrySq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact (((ha.sub contDiff_const).norm_sq (𝕜 := 𝕂)).add (hb.norm_sq (𝕜 := 𝕂))).add
      ((hc.norm_sq (𝕜 := 𝕂)).add ((hd.sub contDiff_const).norm_sq (𝕜 := 𝕂)))
  unfold shiftBump
  simp_rw [hm]
  exact hβ.comp hsq

end Shift

section ArchA

variable (F : Type) [Field F] [NumberField F]

private noncomputable def archShift (β : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  ∏ w : InfinitePlace F, (shiftBump β (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) : ℂ)

private noncomputable def shiftWitness (β : ℝ → ℝ) (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) : ℂ :=
  (∏ v : {w : InfinitePlace F // IsReal w}, (shiftBump β (realCoord F X v) : ℂ)) *
    ∏ v : {w : InfinitePlace F // IsComplex w}, (shiftBump β (complexCoord F X v) : ℂ)

omit [NumberField F] in
private theorem realCoord_shift
    (β : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsReal w}) :
    shiftBump β (realCoord F (archEntries F g) v)
      = shiftBump β (archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) := by
  rw [← shiftBump_map β (Completion.extensionEmbeddingOfIsReal v.2)
    (Completion.isometry_extensionEmbeddingOfIsReal v.2)]
  congr 1

omit [NumberField F] in
private theorem complexCoord_shift (β : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsComplex w}) :
    shiftBump β (complexCoord F (archEntries F g) v)
      = shiftBump β (archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) := by
  rw [← shiftBump_map β (Completion.extensionEmbedding v.1) (Completion.isometry_extensionEmbedding v.1)]
  congr 1

private theorem archShift_eq_witness (β : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archShift F β g = shiftWitness F β (archEntries F g) := by
  unfold archShift shiftWitness
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => IsReal w)]
  congr 1
  · exact Fintype.prod_congr _ _ fun v => by rw [realCoord_shift]
  · exact Fintype.prod_equiv (Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ IsReal w)
      (q := fun w : InfinitePlace F => IsComplex w) fun _ => not_isReal_iff_isComplex) _ _
      fun v => by rw [complexCoord_shift]; rfl

private theorem contDiff_shiftWitness
    {β : ℝ → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) : ContDiff ℝ (⊤ : ℕ∞) (shiftWitness F β) := by
  unfold shiftWitness
  refine ContDiff.mul (contDiff_prod fun v _ => ?_) (contDiff_prod fun v _ => ?_)
  · simp only [realCoord_eq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_shiftBump_of hβ (contDiff_coord_real F v 0 0)
      (contDiff_coord_real F v 0 1) (contDiff_coord_real F v 1 0) (contDiff_coord_real F v 1 1))
  · simp only [complexCoord_eq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_shiftBump_of hβ (contDiff_coord_complex F v 0 0)
      (contDiff_coord_complex F v 0 1) (contDiff_coord_complex F v 1 0) (contDiff_coord_complex F v 1 1))

private noncomputable def archAReal (β₁ β₂ β₃ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ w : InfinitePlace F, localA β₁ β₂ β₃ (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion)

private noncomputable def archA (β₁ β₂ β₃ : ℝ → ℝ) : GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  placeProduct F fun _ => localA β₁ β₂ β₃

private theorem archA_eq_ofReal (β₁ β₂ β₃ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archA F β₁ β₂ β₃ g = (archAReal F β₁ β₂ β₃ g : ℂ) := by
  unfold archA placeProduct archAReal
  rw [Complex.ofReal_prod]

private theorem archA_eq_mul (β₁ β₂ β₃ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archA F β₁ β₂ β₃ g = archFactor F β₁ β₂ g * archShift F β₃ g := by
  unfold archA placeProduct archFactor archShift localA
  simp only [Complex.ofReal_mul, Finset.prod_mul_distrib]

private theorem archA_eq_mul_fun (β₁ β₂ β₃ : ℝ → ℝ) : archA F β₁ β₂ β₃ = archFactor F β₁ β₂ * archShift F β₃ :=
  funext fun g => archA_eq_mul F β₁ β₂ β₃ g

private theorem archA_conj (β₁ β₂ β₃ : ℝ → ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archA F β₁ β₂ β₃ (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = archA F β₁ β₂ β₃ y := by
  unfold archA placeProduct
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [map_mul, map_mul, map_inv, archRowIsometryInclAt₀_apply]
  by_cases hu : u = w
  · subst hu
    rw [archComponent_archGLIncl_self]
    exact congrArg _ (localA_conj' β₁ β₂ β₃ k (archComponent F u y))
  · rw [archComponent_archGLIncl_of_ne F hu, one_mul, inv_one, mul_one]

private theorem isArchTestFactor_archA {β₁ β₂ β₃ : ℝ → ℝ} (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂)
    (hβ₃ : ContDiff ℝ (⊤ : ℕ∞) β₃) {A a : ℝ} (ha : 0 < a) (hA : ∀ t, A < t → β₁ t = 0) (hav : ∀ t, t < a → β₂ t = 0) :
    IsArchTestFactor F (archA F β₁ β₂ β₃) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, hΦ, hΦe⟩ := archFactor_smooth F hβ₁ hβ₂
    refine ⟨fun X => Φ X * shiftWitness F β₃ X, hΦ.mul (contDiff_shiftWitness F hβ₃), fun g => ?_⟩
    rw [archA_eq_mul, hΦe, archShift_eq_witness]
  · rw [archA_eq_mul_fun]
    exact (hasCompactSupport_archFactor F ha hA hav).mul_right

private theorem archAReal_nonneg {β₁ β₂ β₃ : ℝ → ℝ} (h₁ : ∀ t, 0 ≤ β₁ t) (h₂ : ∀ t, 0 ≤ β₂ t) (h₃ : ∀ t, 0 ≤ β₃ t)
    (g : GL (Fin 2) (InfiniteAdeleRing F)) : 0 ≤ archAReal F β₁ β₂ β₃ g :=
  Finset.prod_nonneg fun _ _ => localA_nonneg h₁ h₂ h₃ _

private theorem archAReal_one {β₁ β₂ β₃ : ℝ → ℝ} (h₁ : β₁ 2 = 1) (h₂ : β₂ 1 = 1) (h₃ : β₃ 0 = 1) :
    archAReal F β₁ β₂ β₃ 1 = 1 := by
  unfold archAReal
  refine Finset.prod_eq_one fun w _ => ?_
  rw [map_one, Units.val_one]
  exact localA_one h₁ h₂ h₃

private theorem shift_of_archAReal_ne_zero {β₁ β₂ β₃ : ℝ → ℝ} {g : GL (Fin 2) (InfiniteAdeleRing F)}
    (hg : archAReal F β₁ β₂ β₃ g ≠ 0) (w : InfinitePlace F) :
    β₃ (entrySq ((archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) - 1)) ≠ 0 :=
  shift_ne_zero_of_localA_ne_zero (Finset.prod_ne_zero_iff.mp hg w (Finset.mem_univ w))

end ArchA

section Bumps

private noncomputable def bump₁ : ContDiffBump (0 : ℝ) := ⟨3, 4, by norm_num, by norm_num⟩

private noncomputable def bump₂ : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private noncomputable def bump₃ {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩

private theorem bump₁_eq_zero (t : ℝ) (ht : (4 : ℝ) < t) : (bump₁ : ℝ → ℝ) t = 0 := by
  apply bump₁.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
  show (4 : ℝ) ≤ t
  exact le_of_lt ht

private theorem bump₁_two : (bump₁ : ℝ → ℝ) 2 = 1 := by
  apply bump₁.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  norm_num [bump₁]

private theorem bump₂_eq_zero (t : ℝ) (ht : t < (1 / 2 : ℝ)) : (bump₂ : ℝ → ℝ) t = 0 := by
  apply bump₂.zero_of_le_dist
  rw [Real.dist_eq, abs_of_neg (by linarith)]
  show (1 / 2 : ℝ) ≤ -(t - 1)
  linarith

private theorem bump₂_one : (bump₂ : ℝ → ℝ) 1 = 1 := by
  apply bump₂.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_self]
  norm_num [bump₂]

private theorem bump₃_zero {δ : ℝ} (hδ : 0 < δ) : (bump₃ hδ : ℝ → ℝ) 0 = 1 := by
  apply (bump₃ hδ).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_self]
  show (0 : ℝ) ≤ δ / 2
  positivity

private theorem lt_of_bump₃_ne_zero {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : (bump₃ hδ : ℝ → ℝ) t ≠ 0) : t < δ := by
  have hmem : t ∈ Function.support (bump₃ hδ : ℝ → ℝ) := ht
  rw [(bump₃ hδ).support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  exact (le_abs_self t).trans_lt hmem

variable (F : Type) [Field F] [NumberField F]

private theorem exists_archA {δ : ℝ} (hδ : 0 < δ) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (r : GL (Fin 2) (InfiniteAdeleRing F) → ℝ),
      IsArchTestFactor F fa ∧
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
        fa (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = fa y) ∧
      (∀ g, fa g = (r g : ℂ)) ∧ (∀ g, 0 ≤ r g) ∧ r 1 = 1 ∧
      ∀ g : GL (Fin 2) (InfiniteAdeleRing F), r g ≠ 0 → ∀ w : InfinitePlace F,
        entrySq ((archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) - 1) < δ := by
  refine ⟨archA F bump₁ bump₂ (bump₃ hδ), archAReal F bump₁ bump₂ (bump₃ hδ), ?_, archA_conj F _ _ _,
    archA_eq_ofReal F _ _ _,
    archAReal_nonneg F (fun _ => bump₁.nonneg) (fun _ => bump₂.nonneg) (fun _ => (bump₃ hδ).nonneg),
    archAReal_one F bump₁_two bump₂_one (bump₃_zero hδ), fun g hg w => ?_⟩
  · exact isArchTestFactor_archA F bump₁.contDiff bump₂.contDiff (bump₃ hδ).contDiff
      (by norm_num : (0 : ℝ) < 1 / 2) bump₁_eq_zero bump₂_eq_zero
  · exact lt_of_bump₃_ne_zero hδ (shift_of_archAReal_ne_zero F hg w)

end Bumps

section Bridge

variable (F : Type) [Field F] [NumberField F]

private abbrev PlaceProd : Type := ∀ w : InfinitePlace F, w.Completion

private theorem inverse_continuousAt_placeProd (u : (PlaceProd F)ˣ) :
    ContinuousAt (Ring.inverse : PlaceProd F → PlaceProd F) (u : PlaceProd F) :=
  NormedRing.inverse_continuousAt u

private theorem exists_matrixNhd (V : Set (GL (Fin 2) (InfiniteAdeleRing F)))
    (hV : V ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ W ∈ nhds (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)),
      ∀ g : GL (Fin 2) (InfiniteAdeleRing F), (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ W → g ∈ V := by
  have hemb : Topology.IsEmbedding
      (Units.val : GL (Fin 2) (InfiniteAdeleRing F) → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ fun u => (Matrix.coe_units_inv u).symm
    intro A hA
    obtain ⟨d, hd⟩ := (Matrix.isUnit_iff_isUnit_det A).mp hA
    refine (continuousAt_matrix_inv A ?_).continuousWithinAt
    rw [← hd]
    exact inverse_continuousAt_placeProd F d
  have hV' : V ∈ Filter.comap
      (Units.val : GL (Fin 2) (InfiniteAdeleRing F) → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      (nhds (Units.val (1 : GL (Fin 2) (InfiniteAdeleRing F)))) := by
    rw [← hemb.toIsInducing.nhds_eq_comap]
    exact hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV'
  rw [Units.val_one] at hW
  exact ⟨W, hW, fun g hg => hWV hg⟩

omit [NumberField F] in
private theorem one_entry_apply (w : InfinitePlace F) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) w = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

omit [NumberField F] in

private theorem dist_entry_eq (g : GL (Fin 2) (InfiniteAdeleRing F)) (w : InfinitePlace F) (i j : Fin 2) :
    dist (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) w)
        (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) w)
      = ‖((archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) - 1) i j‖ := by
  rw [dist_eq_norm, ← compMat_coe, Matrix.sub_apply, one_entry_apply]
  rfl

private abbrev EntryProd : Type := ∀ p : Fin 2 × Fin 2 × InfinitePlace F, p.2.2.Completion

private def reindex (c : EntryProd F) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  Matrix.of fun i j => (fun w => c (i, j, w) : InfiniteAdeleRing F)

omit [NumberField F] in
private theorem continuous_reindex : Continuous (reindex F) :=
  continuous_matrix fun i j => continuous_pi fun w => continuous_apply (i, j, w)

private def entriesOf (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) : EntryProd F :=
  fun p => m p.1 p.2.1 p.2.2

omit [NumberField F] in
private theorem reindex_entriesOf (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) : reindex F (entriesOf F m) = m :=
  Matrix.ext fun _ _ => rfl

omit [NumberField F] in
private theorem dist_entriesOf (g : GL (Fin 2) (InfiniteAdeleRing F)) (p : Fin 2 × Fin 2 × InfinitePlace F) :
    dist (entriesOf F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) p) (entriesOf F 1 p)
      = ‖((archComponent F p.2.2 g : Matrix (Fin 2) (Fin 2) p.2.2.Completion) - 1) p.1 p.2.1‖ :=
  dist_entry_eq F g p.2.2 p.1 p.2.1

private theorem exists_entry_bound (W : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))
    (hW : W ∈ nhds (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) :
    ∃ δ > (0 : ℝ), ∀ g : GL (Fin 2) (InfiniteAdeleRing F),
      (∀ w : InfinitePlace F, entrySq ((archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) - 1) < δ) →
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ W := by
  have h1 : reindex F ⁻¹' W ∈ nhds (entriesOf F 1) := by
    apply (continuous_reindex F).continuousAt.preimage_mem_nhds
    rw [reindex_entriesOf]
    exact hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h1
  refine ⟨(ε / 2) ^ 2, by positivity, fun g hg => ?_⟩
  have hε2 : (0 : ℝ) ≤ ε / 2 := by positivity
  have hmem : entriesOf F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ Metric.ball (entriesOf F 1) ε := by
    rw [Metric.mem_ball]
    refine lt_of_le_of_lt ((dist_pi_le_iff hε2).mpr fun p => ?_) (half_lt_self hε)
    rw [dist_entriesOf]
    have h := norm_entry_le_sqrt (hg p.2.2).le p.1 p.2.1
    rwa [Real.sqrt_sq hε2] at h
  have h2 := hball hmem
  rwa [Set.mem_preimage, reindex_entriesOf] at h2

private theorem exists_archA_nhds (V : Set (GL (Fin 2) (InfiniteAdeleRing F)))
    (hV : V ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (r : GL (Fin 2) (InfiniteAdeleRing F) → ℝ),
      IsArchTestFactor F fa ∧
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
        fa (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = fa y) ∧
      (∀ y, fa y = (r y : ℂ)) ∧ (∀ y, 0 ≤ r y) ∧ r 1 = 1 ∧ ∀ y, r y ≠ 0 → y ∈ V := by
  obtain ⟨W, hW, hWV⟩ := exists_matrixNhd F V hV
  obtain ⟨δ, hδ, hδW⟩ := exists_entry_bound F W hW
  obtain ⟨fa, r, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_archA F hδ
  exact ⟨fa, r, h₁, h₂, h₃, h₄, h₅, fun y hy => hWV y (hδW y (h₆ y hy))⟩

end Bridge

end ArchLocalizer

namespace TestFunctionEstimate

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel
open IsDedekindDomain MeasureTheory AdelicDock

variable {K : Type} [Field K] [NumberField K]

private def tensor (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ffn : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  fa (glArch (𝓞 K) K g) * ffn (glFin (𝓞 K) K g)

private theorem tensor_conj {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing K)),
      fa (archRowIsometryInclAt₀ K w k * y * (archRowIsometryInclAt₀ K w k)⁻¹) = fa y)
    (ffn : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 K) K) :
    tensor fa ffn (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = tensor fa ffn y := by
  unfold tensor
  rw [map_mul, map_mul, map_inv, glArch_rowIsometryInclAt₀, hfa, map_mul, map_mul, map_inv,
    glFin_rowIsometryInclAt₀, one_mul, inv_one, mul_one]

open scoped Classical in

private theorem exists_testFn_rightConv_ne_zero
    (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (ffn : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hffn₁ : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K), finEmbed (𝓞 K) K h ∈ U → ffn h = 1)
    (hffn₀ : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K), finEmbed (𝓞 K) K h ∉ U → ffn h = 0)
    (htier : ∀ fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa →
      IsUnitFactorizableAt K ⊥ S (tensor fa ffn))
    (hleft : ∀ fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, ∀ x ∈ U, ∀ g : AdelicGL2 (𝓞 K) K,
      tensor fa ffn (x * g) = tensor fa ffn g)
    (harch : ∀ V ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing K)),
      ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (r : GL (Fin 2) (InfiniteAdeleRing K) → ℝ),
        IsArchTestFactor K fa ∧
        (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing K)),
          fa (archRowIsometryInclAt₀ K w k * y * (archRowIsometryInclAt₀ K w k)⁻¹) = fa y) ∧
        (∀ y, fa y = (r y : ℂ)) ∧ (∀ y, 0 ≤ r y) ∧ r 1 = 1 ∧ ∀ y, r y ≠ 0 → y ∈ V)
    (hcont : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f → Continuous f)
    (hsupp : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f → HasCompactSupport f)
    (hincl : Continuous (adelicArchGLIncl K))
    (hdecomp : ∀ x : AdelicGL2 (𝓞 K) K,
      x = adelicArchGLIncl K (glArch (𝓞 K) K x) * finEmbed (𝓞 K) K (glFin (𝓞 K) K x))
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ x ∈ U, φ (g * x) = φ g)
    (hφ0 : φ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsUnitFactorizableAt K ⊥ S f ∧ (∀ x ∈ U, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) ∧
      (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) ∧
      rightConv K φ f ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hφ0
  have hg₀' : φ g₀ ≠ 0 := hg₀
  have hε : 0 < ‖φ g₀‖ / 2 := half_pos (norm_pos_iff.mpr hg₀')

  have hΨ : Continuous fun y : GL (Fin 2) (InfiniteAdeleRing K) => φ (g₀ * adelicArchGLIncl K y) :=
    hφc.comp (continuous_const.mul hincl)
  have hV : (fun y : GL (Fin 2) (InfiniteAdeleRing K) => φ (g₀ * adelicArchGLIncl K y)) ⁻¹'
      Metric.ball (φ g₀) (‖φ g₀‖ / 2) ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing K)) := by
    refine hΨ.continuousAt.preimage_mem_nhds ?_
    simp only [map_one, mul_one]
    exact Metric.ball_mem_nhds _ hε
  obtain ⟨fa, r, hfa, hconj, hfar, hr0, hr1, hrV⟩ := harch _ hV
  set f : AdelicGL2 (𝓞 K) K → ℂ := tensor fa ffn with hf_def
  have htf : IsFactorizableTestFn K f := (htier fa hfa).isFactorizableTestFn
  have hfc : Continuous f := hcont f htf
  have hfs : HasCompactSupport f := hsupp f htf

  set fr : AdelicGL2 (𝓞 K) K → ℝ :=
    fun x => r (glArch (𝓞 K) K x) * (if finEmbed (𝓞 K) K (glFin (𝓞 K) K x) ∈ U then 1 else 0) with hfr_def
  have hf_eq : ∀ x, f x = (fr x : ℂ) := by
    intro x
    by_cases hx : finEmbed (𝓞 K) K (glFin (𝓞 K) K x) ∈ U
    · simp only [hf_def, tensor, hfr_def, hfar, hffn₁ _ hx, if_pos hx, mul_one]
    · simp only [hf_def, tensor, hfr_def, hfar, hffn₀ _ hx, if_neg hx, mul_zero, Complex.ofReal_zero]
  have hfr_nonneg : ∀ x, 0 ≤ fr x := fun x =>
    mul_nonneg (hr0 _) (by split_ifs <;> norm_num)
  have hfr_one : fr 1 = 1 := by
    simp [hfr_def, hr1]
  have hfr_eq : fr = fun x => (f x).re := by
    funext x
    rw [hf_eq x, Complex.ofReal_re]
  have hfrc : Continuous fr := by
    rw [hfr_eq]
    exact Complex.continuous_re.comp hfc
  have hfrs : HasCompactSupport fr := by
    rw [hfr_eq]
    exact hfs.comp_left Complex.zero_re

  have hclose : ∀ x, ‖φ (g₀ * x) * f x - φ g₀ * f x‖ ≤ ‖φ g₀‖ / 2 * fr x := by
    intro x
    by_cases hx : fr x = 0
    · rw [hf_eq x, hx]
      simp
    · have hx' : r (glArch (𝓞 K) K x) ≠ 0 ∧ finEmbed (𝓞 K) K (glFin (𝓞 K) K x) ∈ U := by
        by_contra hcon
        apply hx
        simp only [hfr_def]
        by_cases hr : r (glArch (𝓞 K) K x) = 0
        · rw [hr, zero_mul]
        · have hU : finEmbed (𝓞 K) K (glFin (𝓞 K) K x) ∉ U := fun hU => hcon ⟨hr, hU⟩
          rw [if_neg hU, mul_zero]
      have hφx : φ (g₀ * x) = φ (g₀ * adelicArchGLIncl K (glArch (𝓞 K) K x)) := by
        conv_lhs => rw [hdecomp x, ← mul_assoc]
        exact hφU _ _ hx'.2
      have hball := hrV _ hx'.1
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hball
      rw [← sub_mul, hφx, norm_mul, hf_eq x, Complex.norm_real, Real.norm_of_nonneg (hfr_nonneg x)]
      exact mul_le_mul_of_nonneg_right hball.le (hfr_nonneg x)
  refine ⟨f, htier fa hfa, hleft fa, tensor_conj hconj ffn, fun hzero => ?_⟩

  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ_def
  have h0 : ∫ x, φ (g₀ * x) * f x ∂μ = 0 := by
    have := congrFun hzero g₀
    rw [rightConv_apply] at this
    exact this

  have hfr_int : Integrable fr μ := hfrc.integrable_of_hasCompactSupport hfrs
  have hI : 0 < ∫ x, fr x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hfr_nonneg hfr_int]
    exact (hfrc.isOpen_support).measure_pos μ ⟨1, by simp [Function.mem_support, hfr_one]⟩
  have hf_int : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have h1_int : Integrable (fun x => φ (g₀ * x) * f x) μ :=
    ((hφc.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have h2_int : Integrable (fun x => φ g₀ * f x) μ := hf_int.const_mul _
  have hint_f : ∫ x, f x ∂μ = ((∫ x, fr x ∂μ : ℝ) : ℂ) := by
    simp_rw [hf_eq]
    exact integral_ofReal
  have hbound : ‖∫ x, (φ (g₀ * x) * f x - φ g₀ * f x) ∂μ‖ ≤ ‖φ g₀‖ / 2 * ∫ x, fr x ∂μ := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hfr_int.const_mul _) (Filter.Eventually.of_forall hclose)
  rw [integral_sub h1_int h2_int, h0, integral_const_mul, hint_f, zero_sub, norm_neg, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hI.le] at hbound
  have hlt : ‖φ g₀‖ / 2 * ∫ x, fr x ∂μ < ‖φ g₀‖ * ∫ x, fr x ∂μ :=
    mul_lt_mul_of_pos_right (half_lt_self (norm_pos_iff.mpr hg₀')) hI
  exact absurd hbound (not_le.mpr hlt)

end TestFunctionEstimate

private theorem finFactor_of_mem {K : Type} [Field K] [NumberField K] {N₁ N₂ : Ideal (𝓞 K)}
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hh : AdelicDock.finEmbed (𝓞 K) K h
      ∈ levelOne (𝓞 K) K N₁ ⊓ principalLevel (𝓞 K) K N₂ ⊓ finiteAdelicGL2Subgroup K) :
    FiniteTestFactor.finFactor N₁ N₂ h = 1 := by
  unfold FiniteTestFactor.finFactor
  exact Set.indicator_of_mem (show h ∈ FiniteTestFactor.finSet N₁ N₂ from hh) (fun _ => (1 : ℂ))

private theorem finFactor_of_notMem {K : Type} [Field K] [NumberField K] {N₁ N₂ : Ideal (𝓞 K)}
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hh : AdelicDock.finEmbed (𝓞 K) K h
      ∉ levelOne (𝓞 K) K N₁ ⊓ principalLevel (𝓞 K) K N₂ ⊓ finiteAdelicGL2Subgroup K) :
    FiniteTestFactor.finFactor N₁ N₂ h = 0 := by
  unfold FiniteTestFactor.finFactor
  exact Set.indicator_of_notMem (show h ∉ FiniteTestFactor.finSet N₁ N₂ from hh) (fun _ => (1 : ℂ))

theorem solution
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ)
    (v : HeightOneSpectrum (𝓞 K))
    (D E₀ : Ideal (𝓞 K)) (k : ℕ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ (D * E₀ * v.asIdeal ^ k) S π φ)
    (hφD : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        φ (g * x) = φ g)
    (hφ0 : φ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsUnitFactorizableAt K ⊥ S f ∧
      (∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) ∧
      (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) ∧
      rightConv K φ f ≠ 0 := by

  have hbot : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ¬ w.asIdeal ∣ D * E₀ * v.asIdeal ^ k := by
    intro w hwS hdvd
    have hzero := isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd K w _ _ ξ _ S π hwS hdvd
    have hmem := hφ.mem_isotypicCuspSubmodule
    rw [hzero, Submodule.mem_bot] at hmem
    exact hφ0 hmem
  obtain ⟨w₀, hw₀⟩ : ∃ w : HeightOneSpectrum (𝓞 K), w ∉ S := by
    haveI := InfinitelyManyPlaces.infinite_heightOneSpectrum K
    exact Infinite.exists_notMem_finset S
  have hD : D ≠ ⊥ := fun h => hbot w₀ hw₀ (by rw [h, ← Ideal.zero_eq_bot, zero_mul, zero_mul]; exact dvd_zero _)
  have hE : E₀ * v.asIdeal ^ k ≠ ⊥ := fun h =>
    hbot w₀ hw₀ (by rw [mul_assoc, h, ← Ideal.zero_eq_bot, mul_zero]; exact dvd_zero _)
  have hS₁ : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ¬ w.asIdeal ∣ D := fun w hw h =>
    hbot w hw (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hS₂ : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ¬ w.asIdeal ∣ E₀ * v.asIdeal ^ k := fun w hw h =>
    hbot w hw (by rw [mul_assoc]; exact dvd_mul_of_dvd_right h _)
  exact TestFunctionEstimate.exists_testFn_rightConv_ne_zero S _ (FiniteTestFactor.finFactor D (E₀ * v.asIdeal ^ k))
    (fun _ hh => finFactor_of_mem hh) (fun _ hh => finFactor_of_notMem hh)
    (fun fa hfa => FiniteTestFactor.isUnitFactorizableAt_tensor hfa hD hE hS₁ hS₂)
    (fun fa x hx g => FiniteTestFactor.tensor_mul_left fa D (E₀ * v.asIdeal ^ k) hx g)
    (ArchLocalizer.exists_archA_nhds K) (fun _ hf => continuous_of_isFactorizableTestFn hf)
    (fun _ hf => hasCompactSupport_of_isFactorizableTestFn hf) continuous_adelicArchGLIncl eq_archIncl_mul_finEmbed
    φ hφ.continuous hφD hφ0

end

end S_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero (solution)

-- Prove2me | Definitions.Def_AutomorphicForm_ProductionPinsGeneral
-- name    : AutomorphicForm_ProductionPinsGeneral
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d00882dd-d749-53e3-a79b-1b7afbc9a4c7
-- title:
--   Class-group translates of the centre-cut Siegel set; general pins
-- statement:
--   Throughout, $F$ is a number field. For a height-one prime $v$ of $\mathcal{O}_F$ and a unit $\delta$ of the finite adele ring, `finIdeleExponentAt F v δ` is the integer $-\log$ of the valuation of the $v$-component of $\delta$, i.e. the normalised order $\operatorname{ord}_v(\delta_v)$; it is additive in $\delta$, vanishes at $\delta=1$, has finite support, and takes the value $\delta_{wv}$ on the idele which is a uniformiser unit at $v$ and $1$ elsewhere. `finAssocFracIdeal F δ` is the multipliable product $\prod_v (v)^{\operatorname{ord}_v(\delta_v)}$ as a fractional ideal of $F$; it is nonzero, its `FractionalIdeal.count` at $v$ is that exponent, and it is multiplicative. Hence `contentHomFin F` is the monoid homomorphism from the finite idele units to $\mathrm{Cl}(\mathcal{O}_F)$ sending $\delta$ to the class of $\mathrm{finAssocFracIdeal}$, and it is surjective. With `classSq F` the squaring endomorphism $C \mapsto C^2$ of the class group, `classRepFinIdele F C` chooses, for each coset $C$ in $\mathrm{Cl}(\mathcal{O}_F)/\mathrm{Cl}(\mathcal{O}_F)^2$, a finite idele whose content lies over $C$ (and $1$ for the trivial coset). `finIdeleDiag F` sends a finite idele $\delta$ to $\mathrm{diag}(\delta,1)$ in the adelic $\mathrm{GL}_2$, with trivial archimedean part, and is injective; composing gives the injection `classRepEmbedding` of $\mathrm{Cl}/\mathrm{Cl}^2$ into adelic $\mathrm{GL}_2$, whose image is the finset `classRepTranslates F`, of cardinality $\#(\mathrm{Cl}/\mathrm{Cl}^2)$ and containing $1$. `classRepSiegelSet F c u d₁ d₂` is the union of the right translates $\mathfrak{S}\cdot x$, $x$ ranging over those representatives, of the centre-cut Siegel set $\mathfrak{S}$ (finite part integral, local height $\ge c$, $x$-window $\le u^2$, archimedean determinant norms in $[d_1,d_2]$). `productionPinsGeneralOf F c u d₁ d₂` (with $d_1<d_2$) feeds this set, the levels $\mathrm{levelOne}(N)\sqcap$ the finite adelic subgroup, the local Hecke generators and the adelic box into `productionPinsOf`; `productionPinsGeneral F` takes $(c,u,d_1,d_2)=(1/2,1,1/2,2)$. For odd class number the squaring map is onto, the quotient is trivial, and `productionPinsGeneral F = productionPinsCompact F`. The Haar measure of the domain is positive (it contains the Siegel set) and finite (a sum over the finitely many translates). Finally, `IsGenuineCuspRealizationAt F pins Φ R` asserts exactly that the realising function `R.toFun` of a smooth cusp realisation is continuous, `IsGenuineCuspRealizable` its existential, `IsArithGenuineCuspRealizable` the same for the renormalised eigensystem $\Phi.\mathrm{toRawCentral}$ (the $b_v$ divided by $\#(\mathcal{O}_F/v)$), `IsArithGenuineCuspRealizableVia` its pullback along a ring homomorphism $R \to \mathbb{C}$, and `genuineCuspNotionOf` packages this as a cuspidality notion over $\mathbb{C}$; each such realisability implies the corresponding smooth/arithmetic one. An auxiliary measure-theoretic lemma records that a continuous function nonvanishing at an interior point of $C$ is not almost everywhere zero for an open-positive measure restricted to $C$.
--
--   **Relation to Mathlib.** Mathlib supplies the class group, fractional ideals with their `count` at a height-one prime and the factorisation of a nonzero fractional ideal as a finprod over height-one primes; the content homomorphism on finite idele units built from them, the Siegel-set constructions and the realisability predicates are the project's own.
--
--   **Where it is used.** These definitions fix the global domain on which adelic automorphic functions for $\mathrm{GL}_2$ over a number field are tested: a finite union of right translates of a centre-cut Siegel set, one per class in $\mathrm{Cl}(\mathcal{O}_F)/\mathrm{Cl}(\mathcal{O}_F)^2$, which is what the determinant of the diagonal representatives reaches. Over fields of odd class number the single Siegel set suffices, and the general pins then coincide with the compact ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ProductionPinsGeneral.lean

import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

open scoped nonZeroDivisors in

noncomputable def finIdeleExponentAt (v : HeightOneSpectrum (𝓞 F))
    (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) : ℤ :=
  -WithZero.log (Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v))

private theorem valued_finIdele_ne_zero (v : HeightOneSpectrum (𝓞 F))
    (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  intro h
  have : ((δ * δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := by
    rw [mul_inv_cancel, Units.val_one, coe_one_apply]
  rw [Units.val_mul, coe_mul_apply, h, zero_mul] at this
  exact zero_ne_one this

@[simp] theorem finIdeleExponentAt_one (v : HeightOneSpectrum (𝓞 F)) :
    finIdeleExponentAt F v 1 = 0 := by
  unfold finIdeleExponentAt
  rw [Units.val_one, coe_one_apply, map_one, WithZero.log_one, neg_zero]

theorem finIdeleExponentAt_mul (v : HeightOneSpectrum (𝓞 F))
    (δ₁ δ₂ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finIdeleExponentAt F v (δ₁ * δ₂) = finIdeleExponentAt F v δ₁ + finIdeleExponentAt F v δ₂ := by
  unfold finIdeleExponentAt
  rw [Units.val_mul, coe_mul_apply, map_mul,
    WithZero.log_mul (valued_finIdele_ne_zero F v δ₁) (valued_finIdele_ne_zero F v δ₂), neg_add]

private theorem finite_support_finIdeleExponentAt (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    {v | finIdeleExponentAt F v δ ≠ 0}.Finite := by
  have hδ : ∀ᶠ v in Filter.cofinite, (δ : FiniteAdeleRing (𝓞 F) F) v
      ∈ v.adicCompletionIntegers F := (δ : FiniteAdeleRing (𝓞 F) F).2
  have hδi : ∀ᶠ v in Filter.cofinite, ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F).2
  refine Set.Finite.subset (Filter.eventually_cofinite.mp (hδ.and hδi)) ?_
  intro v hv hgood
  apply hv

  have hprod : Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, coe_one_apply, map_one]
  have heq : Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) = 1 :=
    le_antisymm hgood.1 (le_of_eq_of_le hprod.symm (mul_le_of_le_one_right' hgood.2))
  simp [finIdeleExponentAt, heq]

open scoped nonZeroDivisors in

noncomputable def finAssocFracIdeal (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    FractionalIdeal (𝓞 F)⁰ F :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ finIdeleExponentAt F v δ

open scoped nonZeroDivisors in
theorem finAssocFracIdeal_ne_zero (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finAssocFracIdeal F δ ≠ 0 := by
  classical
  unfold finAssocFracIdeal
  rw [finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_support_finIdeleExponentAt F δ).toFinset)
    (fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h
      exact hv (by simp only [h, zpow_zero]))]
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

open scoped nonZeroDivisors in
theorem count_finAssocFracIdeal (v : HeightOneSpectrum (𝓞 F))
    (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    FractionalIdeal.count F v (finAssocFracIdeal F δ) = finIdeleExponentAt F v δ :=
  FractionalIdeal.count_finprod F v _ (Filter.eventually_cofinite.mpr
    (by simpa using finite_support_finIdeleExponentAt F δ))

open scoped nonZeroDivisors in
theorem finAssocFracIdeal_mul (δ₁ δ₂ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finAssocFracIdeal F (δ₁ * δ₂) = finAssocFracIdeal F δ₁ * finAssocFracIdeal F δ₂ := by
  have h0 : finAssocFracIdeal F (δ₁ * δ₂) ≠ 0 := finAssocFracIdeal_ne_zero F _
  have h12 : finAssocFracIdeal F δ₁ * finAssocFracIdeal F δ₂ ≠ 0 :=
    mul_ne_zero (finAssocFracIdeal_ne_zero F _) (finAssocFracIdeal_ne_zero F _)
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 F) (K := F) h0,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 F) (K := F) h12]
  refine finprod_congr fun v => ?_
  rw [count_finAssocFracIdeal, finIdeleExponentAt_mul,
    FractionalIdeal.count_mul F v
      (finAssocFracIdeal_ne_zero F δ₁) (finAssocFracIdeal_ne_zero F δ₂),
    count_finAssocFracIdeal, count_finAssocFracIdeal]

open scoped nonZeroDivisors Classical in
theorem finIdeleExponentAt_localUnit_uniformizer (v w : HeightOneSpectrum (𝓞 F)) :
    finIdeleExponentAt F w (localUnit (𝓞 F) F v (uniformizerUnit F v)) =
      if w = v then 1 else 0 := by
  unfold finIdeleExponentAt
  by_cases hw : w = v
  · subst hw
    rw [if_pos rfl, localUnit_apply_self, valued_uniformizerUnit, WithZero.log_exp]
    ring
  · rw [if_neg hw, localUnit_apply_of_ne (𝓞 F) F v _ hw, map_one, WithZero.log_one, neg_zero]

open scoped nonZeroDivisors in

noncomputable def contentHomFin : (FiniteAdeleRing (𝓞 F) F)ˣ →* ClassGroup (𝓞 F) where
  toFun δ := ClassGroup.mk F (Units.mk0 (finAssocFracIdeal F δ) (finAssocFracIdeal_ne_zero F δ))
  map_one' := by
    rw [← map_one (ClassGroup.mk (R := 𝓞 F) (K := F))]
    congr 1
    refine Units.ext ?_
    simp only [Units.val_mk0, Units.val_one, finAssocFracIdeal]
    exact finprod_eq_one_of_forall_eq_one fun v => by rw [finIdeleExponentAt_one, zpow_zero]
  map_mul' δ₁ δ₂ := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by simpa using finAssocFracIdeal_mul F δ₁ δ₂)

open scoped nonZeroDivisors in
theorem contentHomFin_apply (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    contentHomFin F δ =
      ClassGroup.mk F (Units.mk0 (finAssocFracIdeal F δ) (finAssocFracIdeal_ne_zero F δ)) := rfl

open scoped nonZeroDivisors Classical in

theorem contentHomFin_surjective : Function.Surjective (contentHomFin F) := by
  classical
  intro c
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
  have hI0 : ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I)
  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors _)
  set s : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset with hs
  refine ⟨∏ v ∈ s, (localUnit (𝓞 F) F v (uniformizerUnit F v)) ^
      (FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)).toNat, ?_⟩
  show ClassGroup.mk F _ = c
  rw [← hI, ← ClassGroup.mk_mk0 F]
  refine congrArg (ClassGroup.mk F) (Units.ext ?_)
  show finAssocFracIdeal F _ = ((FractionalIdeal.mk0 F I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    FractionalIdeal (𝓞 F)⁰ F)
  rw [FractionalIdeal.coe_mk0]
  conv_rhs =>
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 F) (K := F) hI0]
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := 𝓞 F) (K := F)
      (finAssocFracIdeal_ne_zero F _)]
  refine finprod_congr fun w => congrArg _ ?_
  rw [count_finAssocFracIdeal]

  have hprod : finIdeleExponentAt F w (∏ v ∈ s, (localUnit (𝓞 F) F v (uniformizerUnit F v)) ^
        (FractionalIdeal.count F v ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)).toNat)
      = ∑ v ∈ s, (FractionalIdeal.count F v
          ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)).toNat *
            finIdeleExponentAt F w (localUnit (𝓞 F) F v (uniformizerUnit F v)) := by
    induction s using Finset.induction_on with
    | empty => simp [finIdeleExponentAt_one]
    | insert v t hvt ih =>
        rw [Finset.prod_insert hvt, finIdeleExponentAt_mul, ih, Finset.sum_insert hvt]
        congr 1
        induction (FractionalIdeal.count F v _).toNat with
        | zero => simp [finIdeleExponentAt_one]
        | succ n ihn => rw [pow_succ, finIdeleExponentAt_mul, ihn]; push_cast; ring
  rw [hprod]
  simp_rw [finIdeleExponentAt_localUnit_uniformizer, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq s w]
  by_cases hws : w ∈ s
  · rw [if_pos hws, Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg F w _)]
  · rw [if_neg hws]
    simp only [hs, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hws
    exact hws.symm

def classSq : ClassGroup (𝓞 F) →* ClassGroup (𝓞 F) := powMonoidHom 2

omit [NumberField F] in
@[simp] theorem classSq_apply (C : ClassGroup (𝓞 F)) : classSq F C = C ^ 2 := rfl

open scoped Classical in

noncomputable def classRepFinIdele (C : ClassGroup (𝓞 F) ⧸ (classSq F).range) :
    (FiniteAdeleRing (𝓞 F) F)ˣ :=
  if C = 1 then 1
  else Function.surjInv
    ((QuotientGroup.mk'_surjective (classSq F).range).comp (contentHomFin_surjective F)) C

theorem classRepFinIdele_spec (C : ClassGroup (𝓞 F) ⧸ (classSq F).range) :
    QuotientGroup.mk' (classSq F).range (contentHomFin F (classRepFinIdele F C)) = C := by
  classical
  unfold classRepFinIdele
  split_ifs with hC
  · simp [hC]
  · exact Function.surjInv_eq
      ((QuotientGroup.mk'_surjective (classSq F).range).comp (contentHomFin_surjective F)) C

@[simp] theorem classRepFinIdele_one : classRepFinIdele F 1 = 1 := by
  classical
  unfold classRepFinIdele
  rw [if_pos rfl]

noncomputable def finIdeleDiag : (FiniteAdeleRing (𝓞 F) F)ˣ →* AdelicGL2 (𝓞 F) F :=
  diagOne.comp (Units.map (finIncl (𝓞 F) F))

theorem glArch_finIdeleDiag (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    glArch (𝓞 F) F (finIdeleDiag F δ) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_

  fin_cases i <;> fin_cases j <;> rfl

theorem injective_finIdeleDiag : Function.Injective (finIdeleDiag F) := by
  intro δ₁ δ₂ h
  have h00 := congrArg (fun g : AdelicGL2 (𝓞 F) F =>
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2) h
  simp only [finIdeleDiag, MonoidHom.comp_apply, diagOne_coe_apply, Matrix.diagonal_apply_eq,
    Matrix.cons_val_zero, Units.coe_map, finIncl_apply_snd] at h00
  exact Units.ext h00

noncomputable def classRepEmbedding :
    (ClassGroup (𝓞 F) ⧸ (classSq F).range) ↪ AdelicGL2 (𝓞 F) F :=
  ⟨fun C => finIdeleDiag F (classRepFinIdele F C),
    (injective_finIdeleDiag F).comp (Function.LeftInverse.injective
      (g := fun δ => QuotientGroup.mk' (classSq F).range (contentHomFin F δ))
      (classRepFinIdele_spec F))⟩

theorem classRepEmbedding_apply (C : ClassGroup (𝓞 F) ⧸ (classSq F).range) :
    classRepEmbedding F C = finIdeleDiag F (classRepFinIdele F C) := rfl

theorem glArch_classRepEmbedding (C : ClassGroup (𝓞 F) ⧸ (classSq F).range) :
    glArch (𝓞 F) F (classRepEmbedding F C) = 1 :=
  glArch_finIdeleDiag F _

@[simp] theorem classRepEmbedding_one :
    classRepEmbedding F 1 = 1 := by
  rw [classRepEmbedding_apply, classRepFinIdele_one, map_one]

noncomputable def classRepTranslates : Finset (AdelicGL2 (𝓞 F) F) :=
  haveI := Fintype.ofFinite (ClassGroup (𝓞 F) ⧸ (classSq F).range)
  Finset.univ.map (classRepEmbedding F)

theorem card_classRepTranslates :
    (classRepTranslates F).card = Nat.card (ClassGroup (𝓞 F) ⧸ (classSq F).range) := by
  letI := Fintype.ofFinite (ClassGroup (𝓞 F) ⧸ (classSq F).range)
  rw [classRepTranslates, Finset.card_map, Finset.card_univ, Nat.card_eq_fintype_card]

theorem one_mem_classRepTranslates : (1 : AdelicGL2 (𝓞 F) F) ∈ classRepTranslates F := by
  letI := Fintype.ofFinite (ClassGroup (𝓞 F) ⧸ (classSq F).range)
  rw [classRepTranslates, Finset.mem_map]
  exact ⟨1, Finset.mem_univ _, classRepEmbedding_one F⟩

noncomputable def classRepSiegelSet (c u d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  ⋃ x ∈ classRepTranslates F, (· * x) '' centreCutSiegelSet F c u d₁ d₂

theorem surjective_classSq_of_odd (h : Odd (classNumber F)) :
    Function.Surjective (classSq F) := by
  intro C
  obtain ⟨k, hk⟩ := h
  refine ⟨C ^ (k + 1), ?_⟩
  have hcard : C ^ classNumber F = 1 := pow_card_eq_one
  simp only [classSq, powMonoidHom_apply, ← pow_mul]
  have h2 : (k + 1) * 2 = classNumber F + 1 := by omega
  rw [h2, pow_succ, hcard, one_mul]

theorem subsingleton_quotient_classSq_of_odd (h : Odd (classNumber F)) :
    Subsingleton (ClassGroup (𝓞 F) ⧸ (classSq F).range) := by
  have hr : (classSq F).range = ⊤ := MonoidHom.range_eq_top.mpr (surjective_classSq_of_odd F h)
  rw [hr]
  exact QuotientGroup.subsingleton_quotient_top

theorem classRepTranslates_eq_singleton_one_of_odd (h : Odd (classNumber F)) :
    classRepTranslates F = {1} := by
  letI := Fintype.ofFinite (ClassGroup (𝓞 F) ⧸ (classSq F).range)
  haveI := subsingleton_quotient_classSq_of_odd F h
  rw [classRepTranslates]
  have huniv : (Finset.univ : Finset (ClassGroup (𝓞 F) ⧸ (classSq F).range)) = {1} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim x 1⟩
  rw [huniv, Finset.map_singleton, classRepEmbedding_one]

theorem classRepSiegelSet_eq_of_odd (h : Odd (classNumber F)) (c u d₁ d₂ : ℝ) :
    classRepSiegelSet F c u d₁ d₂ = centreCutSiegelSet F c u d₁ d₂ := by
  unfold classRepSiegelSet
  rw [classRepTranslates_eq_singleton_one_of_odd F h]
  ext g
  simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop, exists_eq_left, Set.mem_image,
    mul_one]
  exact ⟨fun ⟨x, hx, hxg⟩ => hxg ▸ hx, fun hg => ⟨g, hg, rfl⟩⟩

def productionPinsGeneralOf (c u d₁ d₂ : ℝ) (_hd : d₁ < d₂) : CarrierPins F :=
  productionPinsOf F
    (classRepSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

def productionPinsGeneral : CarrierPins F :=
  productionPinsGeneralOf F (1/2 : ℝ) 1 (1/2) 2 (by norm_num)

@[simp] theorem productionPinsGeneralOf_D (c u d₁ d₂ : ℝ) (hd : d₁ < d₂) :
    (productionPinsGeneralOf F c u d₁ d₂ hd).D = classRepSiegelSet F c u d₁ d₂ := rfl

@[simp] theorem productionPinsGeneralOf_μ (c u d₁ d₂ : ℝ) (hd : d₁ < d₂) :
    (productionPinsGeneralOf F c u d₁ d₂ hd).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPinsGeneralOf_U (c u d₁ d₂ : ℝ) (hd : d₁ < d₂) (N : Ideal (𝓞 F)) :
    (productionPinsGeneralOf F c u d₁ d₂ hd).U N =
      levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl

@[simp] theorem productionPinsGeneral_D :
    (productionPinsGeneral F).D = classRepSiegelSet F (1/2 : ℝ) 1 (1/2) 2 := rfl

theorem productionPinsGeneral_eq_compact_of_odd (h : Odd (classNumber F)) :
    productionPinsGeneral F = productionPinsCompact F := by
  unfold productionPinsGeneral productionPinsGeneralOf productionPinsCompact
  rw [classRepSiegelSet_eq_of_odd F h]

theorem centreCutSiegelSet_subset_classRepSiegelSet (c u d₁ d₂ : ℝ) :
    centreCutSiegelSet F c u d₁ d₂ ⊆ classRepSiegelSet F c u d₁ d₂ := by
  intro g hg
  rw [classRepSiegelSet, Set.mem_iUnion]
  exact ⟨1, Set.mem_iUnion.mpr ⟨one_mem_classRepTranslates F, g, hg, mul_one g⟩⟩

theorem adelicGLHaar_mul_right_centreCutSiegelSet_lt_top
    {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    (letI := glBorel (Fin 2) (𝓞 F) F;
      adelicGLHaar (Fin 2) (𝓞 F) F ((· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤) := by
  letI := glBorel (Fin 2) (𝓞 F) F
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  have himg : (· * x) '' centreCutSiegelSet F c u d₁ d₂
      = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg, ← Measure.map_apply (measurable_mul_const x⁻¹)
    (measurableSet_centreCutSiegelSet c u d₁ d₂)]

  haveI : (Measure.map (· * x⁻¹) (adelicGLHaar (Fin 2) (𝓞 F) F)).IsMulLeftInvariant :=
    isMulLeftInvariant_map_mul_right _
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * x⁻¹) (adelicGLHaar (Fin 2) (𝓞 F) F)) :=
    Measure.IsFiniteMeasureOnCompacts.map _ (Homeomorph.mulRight x⁻¹)
  exact measure_centreCutSiegelSet_lt_top _ hc u hd₁ d₂

theorem productionPinsGeneral_μ_D_pos_lt_top :
    (letI := (productionPinsGeneral F).mS;
      0 < (productionPinsGeneral F).μ (productionPinsGeneral F).D ∧
        (productionPinsGeneral F).μ (productionPinsGeneral F).D < ⊤) := by
  letI := glBorel (Fin 2) (𝓞 F) F
  have hcompact := productionPinsCompact_μ_D_pos_lt_top F
  constructor
  · refine lt_of_lt_of_le hcompact.1 (measure_mono ?_)
    exact centreCutSiegelSet_subset_classRepSiegelSet F (1/2) 1 (1/2) 2
  · calc (productionPinsGeneral F).μ (productionPinsGeneral F).D
        = adelicGLHaar (Fin 2) (𝓞 F) F (classRepSiegelSet F (1/2) 1 (1/2) 2) := rfl
      _ ≤ ∑ x ∈ classRepTranslates F,
            adelicGLHaar (Fin 2) (𝓞 F) F ((· * x) '' centreCutSiegelSet F (1/2) 1 (1/2) 2) := by
          unfold classRepSiegelSet
          exact measure_biUnion_finset_le _ _
      _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ =>
          adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F (by norm_num) 1 (by norm_num) 2 x

theorem not_ae_zero_restrict_of_continuous_of_mem_interior
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {μ : Measure G} [μ.IsOpenPosMeasure]
    {φ : G → ℂ} (hφ : Continuous φ) {g₀ : G} (hg₀ : φ g₀ ≠ 0)
    {C : Set G} (hC : g₀ ∈ interior C) :
    ¬ (φ =ᵐ[μ.restrict C] 0) := by
  intro hae
  set U : Set G := interior C ∩ {g | φ g ≠ 0} with hU
  have hUopen : IsOpen U := isOpen_interior.inter (isOpen_ne.preimage hφ)
  have hUne : U.Nonempty := ⟨g₀, hC, hg₀⟩
  have hUpos : 0 < μ U := hUopen.measure_pos μ hUne
  have hUsub : U ⊆ C := (Set.inter_subset_left).trans interior_subset
  have hres : 0 < (μ.restrict C) U := by
    rw [Measure.restrict_apply hUopen.measurableSet, Set.inter_eq_self_of_subset_left hUsub]
    exact hUpos
  have hzero : U ⊆ {g | ¬ (φ g = (0 : G → ℂ) g)} := fun g hg => by
    simpa using hg.2
  exact absurd (measure_mono_null hzero hae) hres.ne'

def IsGenuineCuspRealizationAt (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F pins Φ) : Prop :=
  Continuous R.toFun

def IsGenuineCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ R : SmoothCuspRealizationAt F pins Φ, IsGenuineCuspRealizationAt F pins Φ R

def IsArithGenuineCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsGenuineCuspRealizable F pins Φ.toRawCentral

def IsArithGenuineCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsArithGenuineCuspRealizable F pins (Φ.map ι)

def genuineCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => @IsArithGenuineCuspRealizable F _i1 _i2 (pins F) Φ

theorem isGenuineCuspRealizable_iff (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) :
    IsGenuineCuspRealizable F pins Φ ↔
      ∃ R : SmoothCuspRealizationAt F pins Φ, Continuous R.toFun := Iff.rfl

theorem IsGenuineCuspRealizable.isSmoothCuspRealizable {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (h : IsGenuineCuspRealizable F pins Φ) :
    IsSmoothCuspRealizable F pins Φ :=
  ⟨h.choose⟩

theorem IsArithGenuineCuspRealizable.isArithCuspRealizable {pins : CarrierPins F}
    {Φ : HeckeEigensystem F ℂ} (h : IsArithGenuineCuspRealizable F pins Φ) :
    IsArithCuspRealizable F pins Φ :=
  h.isSmoothCuspRealizable

end AutomorphicForm

end

section Battery
open AutomorphicForm
#check @finIdeleExponentAt
#check @finAssocFracIdeal
#check @contentHomFin
#check @contentHomFin_apply
#check @contentHomFin_surjective
#check @classSq
#check @classRepFinIdele
#check @classRepFinIdele_spec
#check @finIdeleDiag
#check @classRepEmbedding
#check @classRepEmbedding_apply
#check @classRepSiegelSet
#check @card_classRepTranslates
#check @productionPinsGeneralOf
#check @productionPinsGeneral
#check @IsGenuineCuspRealizationAt
#check @IsGenuineCuspRealizable
#check @IsArithGenuineCuspRealizable
#check @IsArithGenuineCuspRealizableVia
#check @genuineCuspNotionOf
#print axioms AutomorphicForm.finAssocFracIdeal_ne_zero
#print axioms AutomorphicForm.count_finAssocFracIdeal
#print axioms AutomorphicForm.finAssocFracIdeal_mul
#print axioms AutomorphicForm.finIdeleExponentAt_localUnit_uniformizer
#print axioms AutomorphicForm.contentHomFin_surjective
#print axioms AutomorphicForm.classRepFinIdele_spec
#print axioms AutomorphicForm.glArch_finIdeleDiag
#print axioms AutomorphicForm.injective_finIdeleDiag
#print axioms AutomorphicForm.glArch_classRepEmbedding
#print axioms AutomorphicForm.classRepEmbedding_one
#print axioms AutomorphicForm.productionPinsGeneral_eq_compact_of_odd
#print axioms AutomorphicForm.IsGenuineCuspRealizable.isSmoothCuspRealizable
#print axioms AutomorphicForm.classRepSiegelSet_eq_of_odd
#print axioms AutomorphicForm.card_classRepTranslates
#print axioms AutomorphicForm.one_mem_classRepTranslates
#print axioms AutomorphicForm.classRepTranslates_eq_singleton_one_of_odd
#print axioms AutomorphicForm.not_ae_zero_restrict_of_continuous_of_mem_interior
#print axioms AutomorphicForm.productionPinsGeneral_μ_D_pos_lt_top
end Battery



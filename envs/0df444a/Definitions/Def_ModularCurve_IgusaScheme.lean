-- Prove2me | Definitions.Def_ModularCurve_IgusaScheme
-- name    : ModularCurve_IgusaScheme
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/20784cae-1918-5697-a430-e388297a8f85
-- title:
--   Igusa integral model of X0​(N) over Z(ℓ)​
-- statement:
--   Fix $N \ge 1$ and a prime $\ell$. Write $\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt ℓ`](../def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $\ell$, and $F$ for `modularFunctionFieldFull N`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $j(q^d)$ for the divisors $d$ of $N$; $F$ is made a $\mathbb{Z}_{(\ell)}$-algebra through $\mathbb{Z}_{(\ell)} \to \mathbb{Q} \to F$. The element `jFull N` is the $q$-expansion $j(q)$ viewed in $F$, and it is nonzero (its coefficient in degree $-1$ is $1$).
--
--   For a subset $S \subseteq F$, `chartAlg N ℓ S` is the $\mathbb{Z}_{(\ell)}$-subalgebra of $F$ consisting of the elements integral over $\mathbb{Z}_{(\ell)}[S]$; it contains $\mathbb{Z}_{(\ell)}[S]$ and is monotone in $S$, with `chartIncl` the induced injective inclusions. Taking $S = \{j\}$, $\{j^{-1}\}$, $\{j, j^{-1}\}$ gives `chartAlgFin`, `chartAlgInf`, `chartAlgMid`. A denominator-clearing argument (a monic equation is rescaled by a power of $j$ via `Polynomial.scaleRoots`) shows that `chartAlgMid` is the localization of `chartAlgFin` away from $j$, and also the localization of `chartAlgInf` away from $j^{-1}$; consequently the two morphisms `fFin`, `fInf` from `XMid` $= \operatorname{Spec}$ `chartAlgMid` to `XFin`, `XInf` are open immersions.
--
--   [`ModularCurve.IgusaScheme N ℓ`](../def/ModularCurve_IgusaScheme.html#L255) is defined as the pushout of `fFin` and `fInf` in schemes. Its two structure maps `ιFin`, `ιInf` are open immersions satisfying the gluing identity `glue_condition`, the morphism `igusaTo` to $\operatorname{Spec}\mathbb{Z}_{(\ell)}$ is obtained from the two structure maps of the charts, and `chartFinOpen`, `chartInfOpen` are the corresponding affine open subschemes, which cover the whole space (`igusaCover`).
--
--   **Relation to Mathlib.** Mathlib has no integral model of a modular curve; the construction here is the project's own, built from Mathlib's `Spec`, pushouts of schemes, `IsLocalization.Away` and `IsOpenImmersion`. The base ring $\mathbb{Z}_{(\ell)}$ is the project's subring [`GaloisRep.ratLocalizedAt`](../def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ rather than a Mathlib localization.
--
--   **Where it is used.** This provides the scheme over $\mathbb{Z}_{(\ell)}$ on which the arithmetic of $X_0(N)$ at the prime $\ell$ is formulated: the normalisation of $\mathbb{P}^1_{\mathbb{Z}_{(\ell)}}$ in the function field $F$ along the $j$-line, presented by two affine charts over $j$ and $j^{-1}$. It underlies the geometric statements about reduction of modular curves and their Jacobians used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_IgusaScheme.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts
import Definitions.Def_ModularCurve_X0
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace ModularCurve

namespace IgusaScheme

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

scoped instance igusaAlgebra :
    Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) :=
  ((algebraMap ℚ ↥(modularFunctionFieldFull N)).comp
    (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)).toAlgebra

scoped instance igusaScalarTower :
    IsScalarTower ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N) :=
  IsScalarTower.of_algebraMap_eq' rfl

set_option quotPrecheck false in

local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

set_option quotPrecheck false in

local notation "F" => ↥(modularFunctionFieldFull N)

def jFull : F := ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩

@[simp] theorem coe_jFull : (jFull N : LaurentSeries ℚ) = jq := rfl

theorem jFull_ne_zero : jFull N ≠ 0 :=
  fun h => jq_ne_zero (by simpa using congrArg Subtype.val h)

instance fact_jFull_ne_zero : Fact (jFull N ≠ 0) := ⟨jFull_ne_zero N⟩

def chartAlg (S : Set F) : Subalgebra ℤℓ F where
  carrier := {x | IsIntegral (Algebra.adjoin ℤℓ S) x}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isIntegral_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  algebraMap_mem' a := by
    have : IsIntegral (Algebra.adjoin ℤℓ S)
        (algebraMap (Algebra.adjoin ℤℓ S) F (algebraMap ℤℓ (Algebra.adjoin ℤℓ S) a)) :=
      isIntegral_algebraMap
    simpa [← IsScalarTower.algebraMap_apply] using this

theorem mem_chartAlg_iff {S : Set F} {x : F} :
    x ∈ chartAlg N ℓ S ↔ IsIntegral (Algebra.adjoin ℤℓ S) x := Iff.rfl

theorem adjoin_le_chartAlg (S : Set F) : Algebra.adjoin ℤℓ S ≤ chartAlg N ℓ S := fun x hx => by
  rw [mem_chartAlg_iff]
  exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin ℤℓ S))

theorem subset_chartAlg (S : Set F) : S ⊆ (chartAlg N ℓ S : Set F) := fun _ hx =>
  adjoin_le_chartAlg N ℓ S (Algebra.subset_adjoin hx)

theorem chartAlg_mono {S S' : Set F} (h : S ⊆ S') : chartAlg N ℓ S ≤ chartAlg N ℓ S' := by
  intro x hx
  rw [mem_chartAlg_iff] at hx ⊢
  exact hx.map_of_comp_eq
    (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom (RingHom.id F) (by ext; rfl)

abbrev chartIncl {S S' : Set F} (h : S ⊆ S') : chartAlg N ℓ S →ₐ[ℤℓ] chartAlg N ℓ S' :=
  Subalgebra.inclusion (chartAlg_mono N ℓ h)

theorem coe_chartIncl {S S' : Set F} (h : S ⊆ S') (x : chartAlg N ℓ S) :
    (chartIncl N ℓ h x : F) = x :=
  Subalgebra.coe_inclusion _ x

theorem chartIncl_injective {S S' : Set F} (h : S ⊆ S') :
    Function.Injective (chartIncl N ℓ h) :=
  Subalgebra.inclusion_injective _

variable {N ℓ}

theorem exists_pow_mul_mem_adjoin {S : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) {x : F}
    (hx : x ∈ Algebra.adjoin ℤℓ (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin ℤℓ S := by
  have hsA : s ∈ Algebra.adjoin ℤℓ S := Algebra.subset_adjoin hs
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hs0]; exact one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap a => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ a⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y + z) = s ^ n * (s ^ m * y) + s ^ m * (s ^ n * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hsA n) hm) (mul_mem (pow_mem hsA m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y * z) = (s ^ m * y) * (s ^ n * z) := by ring
    rw [this]
    exact mul_mem hm hn

theorem exists_pow_mul_mem_chartAlg {S : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) {x : F}
    (hx : x ∈ chartAlg N ℓ (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ chartAlg N ℓ S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartAlg_iff N ℓ).mp hx
  have hcoeff : ∀ i, ∃ n : ℕ, s ^ n * (p.coeff i : F) ∈ Algebra.adjoin ℤℓ S :=
    fun i => exists_pow_mul_mem_adjoin hs hs0 (p.coeff i).2
  choose n hn using hcoeff
  set M : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hM
  have hnM : ∀ i ≤ p.natDegree, n i ≤ M := fun i hi =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set q : F[X] := (p.map (algebraMap (Algebra.adjoin ℤℓ (insert s⁻¹ S)) F)).scaleRoots (s ^ M)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (s ^ M * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin ℤℓ S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · have hle : n i ≤ M * (p.natDegree - i) := by
        calc n i ≤ M := hnM i hi.le
          _ = M * 1 := (mul_one M).symm
          _ ≤ M * (p.natDegree - i) := Nat.mul_le_mul_left M (Nat.one_le_iff_ne_zero.mpr (by omega))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have : (s ^ M) ^ (p.natDegree - i) = s ^ k * s ^ n i := by
        rw [← pow_mul, hk, pow_add, mul_comm]
      rw [this, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : F) * (s ^ k * s ^ n i) = s ^ k * (s ^ n i * (p.coeff i : F)) by ring]
      exact mul_mem (pow_mem (Algebra.subset_adjoin hs) k) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin ℤℓ S) F) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨M, (mem_chartAlg_iff N ℓ).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

variable (N ℓ)

theorem sFin_subset : ({jFull N} : Set F) ⊆ {jFull N, (jFull N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

theorem sInf_subset : ({(jFull N)⁻¹} : Set F) ⊆ {jFull N, (jFull N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)

abbrev chartAlgFin : Subalgebra ℤℓ F := chartAlg N ℓ {jFull N}

abbrev chartAlgInf : Subalgebra ℤℓ F := chartAlg N ℓ {(jFull N)⁻¹}

abbrev chartAlgMid : Subalgebra ℤℓ F := chartAlg N ℓ {jFull N, (jFull N)⁻¹}

def jChartFin : chartAlgFin N ℓ := ⟨jFull N, subset_chartAlg N ℓ _ rfl⟩

def jInvChartInf : chartAlgInf N ℓ := ⟨(jFull N)⁻¹, subset_chartAlg N ℓ _ rfl⟩

@[simp] theorem coe_jChartFin : (jChartFin N ℓ : F) = jFull N := rfl
@[simp] theorem coe_jInvChartInf : (jInvChartInf N ℓ : F) = (jFull N)⁻¹ := rfl

abbrev inclFin : chartAlgFin N ℓ →ₐ[ℤℓ] chartAlgMid N ℓ := chartIncl N ℓ (sFin_subset N)

abbrev inclInf : chartAlgInf N ℓ →ₐ[ℤℓ] chartAlgMid N ℓ := chartIncl N ℓ (sInf_subset N)

theorem isUnit_inclFin_jChartFin : IsUnit (inclFin N ℓ (jChartFin N ℓ)) := by
  refine .of_mul_eq_one ⟨(jFull N)⁻¹, subset_chartAlg N ℓ _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jChartFin]
  exact mul_inv_cancel₀ (jFull_ne_zero N)

theorem isUnit_inclInf_jInvChartInf : IsUnit (inclInf N ℓ (jInvChartInf N ℓ)) := by
  refine .of_mul_eq_one ⟨jFull N, subset_chartAlg N ℓ _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jInvChartInf]
  exact inv_mul_cancel₀ (jFull_ne_zero N)

theorem isLocalization_away_inclFin :
    letI := (inclFin N ℓ).toRingHom.toAlgebra
    IsLocalization.Away (jChartFin N ℓ) (chartAlgMid N ℓ) := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclFin_jChartFin N ℓ).pow n
  · intro z
    have hz : (z : F) ∈ chartAlg N ℓ (insert (jFull N)⁻¹ {jFull N}) := by
      rw [show insert (jFull N)⁻¹ ({jFull N} : Set F) = {jFull N, (jFull N)⁻¹}
        from Set.pair_comm _ _]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _) (jFull_ne_zero N) hz
    refine ⟨(⟨(jFull N) ^ n * z, hn⟩, ⟨jChartFin N ℓ ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jChartFin]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective N ℓ _ h]

theorem isLocalization_away_inclInf :
    letI := (inclInf N ℓ).toRingHom.toAlgebra
    IsLocalization.Away (jInvChartInf N ℓ) (chartAlgMid N ℓ) := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclInf_jInvChartInf N ℓ).pow n
  · intro z
    have hz : (z : F) ∈ chartAlg N ℓ (insert (jFull N)⁻¹⁻¹ {(jFull N)⁻¹}) := by
      rw [inv_inv]; exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _)
      (inv_ne_zero (jFull_ne_zero N)) hz
    refine ⟨(⟨(jFull N)⁻¹ ^ n * z, hn⟩, ⟨jInvChartInf N ℓ ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jInvChartInf]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective N ℓ _ h]

abbrev XFin : Scheme.{0} := Spec (CommRingCat.of (chartAlgFin N ℓ))

abbrev XInf : Scheme.{0} := Spec (CommRingCat.of (chartAlgInf N ℓ))

abbrev XMid : Scheme.{0} := Spec (CommRingCat.of (chartAlgMid N ℓ))

abbrev fFin : XMid N ℓ ⟶ XFin N ℓ := Spec.map (CommRingCat.ofHom (inclFin N ℓ).toRingHom)

abbrev fInf : XMid N ℓ ⟶ XInf N ℓ := Spec.map (CommRingCat.ofHom (inclInf N ℓ).toRingHom)

instance isOpenImmersion_fFin : IsOpenImmersion (fFin N ℓ) := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact IsOpenImmersion.of_isLocalization (jChartFin N ℓ)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf N ℓ) := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact IsOpenImmersion.of_isLocalization (jInvChartInf N ℓ)

def _root_.ModularCurve.IgusaScheme : Scheme.{0} := pushout (fFin N ℓ) (fInf N ℓ)

def ιFin : XFin N ℓ ⟶ ModularCurve.IgusaScheme N ℓ := pushout.inl (fFin N ℓ) (fInf N ℓ)

def ιInf : XInf N ℓ ⟶ ModularCurve.IgusaScheme N ℓ := pushout.inr (fFin N ℓ) (fInf N ℓ)

theorem glue_condition : fFin N ℓ ≫ ιFin N ℓ = fInf N ℓ ≫ ιInf N ℓ := pushout.condition

instance isOpenImmersion_ιFin : IsOpenImmersion (ιFin N ℓ) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf N ℓ) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))).map_prop WalkingSpan.right

theorem fFin_toBase_eq_fInf_toBase :
    fFin N ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgFin N ℓ))) =
      fInf N ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgInf N ℓ))) := by
  have h : (inclFin N ℓ).toRingHom.comp (algebraMap ℤℓ (chartAlgFin N ℓ)) =
      (inclInf N ℓ).toRingHom.comp (algebraMap ℤℓ (chartAlgInf N ℓ)) :=
    RingHom.ext fun a => ((inclFin N ℓ).commutes a).trans ((inclInf N ℓ).commutes a).symm
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

def igusaTo : ModularCurve.IgusaScheme N ℓ ⟶ Spec (CommRingCat.of ℤℓ) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgFin N ℓ))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgInf N ℓ))))
    (fFin_toBase_eq_fInf_toBase N ℓ)

@[reassoc (attr := simp)]
theorem ιFin_igusaTo : ιFin N ℓ ≫ igusaTo N ℓ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgFin N ℓ))) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem ιInf_igusaTo : ιInf N ℓ ≫ igusaTo N ℓ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgInf N ℓ))) :=
  pushout.inr_desc _ _ _

theorem mem_range_ιFin_or_mem_range_ιInf (x : ModularCurve.IgusaScheme N ℓ) :
    x ∈ Set.range (ιFin N ℓ).base ∨ x ∈ Set.range (ιInf N ℓ).base := by
  obtain ⟨i, y, hy⟩ :=
    (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))).exists_eq x
  rcases i with (_ | _ | _)
  · have hw : (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))).f none =
        fFin N ℓ ≫ ιFin N ℓ :=
      (colimit.w (span (fFin N ℓ) (fInf N ℓ)) WalkingSpan.Hom.fst).symm
    refine Or.inl ⟨(fFin N ℓ).base y, ?_⟩
    rw [← hy, hw]; rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

def chartFinOpen : (ModularCurve.IgusaScheme N ℓ).Opens := (ιFin N ℓ).opensRange

def chartInfOpen : (ModularCurve.IgusaScheme N ℓ).Opens := (ιInf N ℓ).opensRange

theorem isAffineOpen_chartFinOpen : IsAffineOpen (chartFinOpen N ℓ) :=
  isAffineOpen_opensRange (ιFin N ℓ)

theorem isAffineOpen_chartInfOpen : IsAffineOpen (chartInfOpen N ℓ) :=
  isAffineOpen_opensRange (ιInf N ℓ)

theorem igusaCover : chartFinOpen N ℓ ⊔ chartInfOpen N ℓ = ⊤ := by
  rw [chartFinOpen, chartInfOpen, ← TopologicalSpace.Opens.coe_inj]
  ext x
  simpa using mem_range_ιFin_or_mem_range_ιInf N ℓ x

end IgusaScheme

end ModularCurve

end



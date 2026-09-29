-- Prove2me | Definitions.Def_ModularCurve_CharLDegeneracyHecke
-- name    : ModularCurve_CharLDegeneracyHecke
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/b405a6db-16dc-5d2f-812b-e560706dd01c
-- title:
--   Degeneracy Hecke operators on Pic⁰ in characteristic ℓ
-- statement:
--   Three groups of definitions. First, a total descent device for divisor correspondences: for an extension $F/K$ of fields, `DescendsToPic0 T` asserts of an additive endomorphism $T$ of the divisor group $\mathrm{Div}(F/K)$ that it maps degree-zero divisors to degree-zero divisors and principal divisors to principal divisors; `degZeroEnd` is then the induced endomorphism of the degree-zero subgroup, and `toPic0End T` is the induced endomorphism of $\mathrm{Pic}^0$ when `DescendsToPic0 T` holds and the zero map otherwise, with the two branches recorded by rewriting lemmas. Second, for $K$ of characteristic $\ell$ and level $N$, `heckePic0FibreChar` is the $\mathbb{Z}$-linear endomorphism of $\mathrm{Pic}^0$ of the level-$N$ fibre function field obtained by applying this device to the divisor-level operator `heckeFibreGeomLevel` attached to a `ModularPolynomialData` satisfying `KroneckerCongruence`; it is shown independent of that data, to satisfy `DescendsToPic0` when $K$ is $\ell$-divisible and all places have degree one, and, for $K$ algebraically closed with the curve hypothesis, to agree with the geometric-level $\mathrm{Pic}^0$ operator. Given an arbitrary family $T^{\mathrm{ne}}$ indexed by primes, `heckeFamilyFibreOf` takes `heckePic0FibreChar` at the prime $\ell$ and $T^{\mathrm{ne}}_q$ elsewhere; `HeckeOperatorsCommuteFibreOf` asserts pairwise commutation of this family, and `heckeModuleFibreOf` is a total `HeckeAlg`-module structure on $\mathrm{Pic}^0$ — the module induced by the commuting family when commutation holds, and otherwise the action through the constant term — whose generator normal forms and agreement with `SpecialFibreHeckeModuleMatch` are recorded. Third, the degeneracy legs: `charLDegeneracyRoof` is the subfield of $k((t))$-type Laurent series generated over $k$ by the four $j$-type elements at levels $1, N, q, Nq$; `heckeAlphaC` is the inclusion of the level-$N$ fibre field, `heckeBetaC` is the $q$-power substitution on $q$-expansions into the roof, `HeckeAlphaCIntegral`/`HeckeBetaCIntegral` assert integrality of these legs, and `heckeDivFibre` is the push–pull correspondence of the two legs. `HeckeDivFibreDescends` and `HeckeInputsFibre` are the universal and existential forms of the input package (principal divisors on the roof, both integrality witnesses, descent), `heckePic0Fibre` is the descended operator at such a witness and zero otherwise, and `heckeFamilyFibre`, `HeckeOperatorsCommuteFibre`, `heckeModuleFibre` instantiate the family at these operators for $q \neq \ell$.
--
--   **Relation to Mathlib.** The Hecke algebra is Mathlib's `MvPolynomial Nat.Primes ℤ` and the $\mathrm{Pic}^0$ descent uses `QuotientAddGroup.map`; places, divisors, principal divisors, $\mathrm{Pic}^0$ of a function field, modular function fields and divisor correspondences are the project's own notions, with no Mathlib counterpart.
--
--   **Where it is used.** These operators supply the Hecke action on $\mathrm{Pic}^0$ of the characteristic-$\ell$ fibre of $X_0(N)$ in which the $\ell$-slot is the geometric Frobenius operator, so that the Eichler–Shimura congruence relation $F^2 - T_\ell F + \ell = 0$ holds on the special fibre. That relation is the `relation` field of the specialisation witness used to produce the local conditions (unramifiedness outside the level, Frobenius quadratic relation) on the Galois representations attached to modular curves in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_CharLDegeneracyHecke.lean

import Definitions.Def_ModularCurve_CharLSpecialFibrePic0CommutingFamilyBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

namespace Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def DescendsToPic0 (T : Divisor K F →+ Divisor K F) : Prop :=
  (∀ D : Divisor K F, D ∈ Divisor.degZero (K := K) (F := F) → T D ∈ Divisor.degZero (K := K) (F := F)) ∧
    ∀ D : Divisor K F, D.IsPrincipal → (T D).IsPrincipal

def degZeroEnd (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  (T.domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _ (fun D => h.1 D D.2)

@[simp]
theorem coe_degZeroEnd (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T)
    (D : Divisor.degZero (K := K) (F := F)) : (degZeroEnd T h D : Divisor K F) = T D :=
  rfl

open Classical in

def toPic0End (T : Divisor K F →+ Divisor K F) : Pic0 K F →+ Pic0 K F :=
  if h : DescendsToPic0 T then
    QuotientAddGroup.map _ _ (degZeroEnd T h) (by
      rintro ⟨D, hD0⟩ hD
      simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
      exact h.2 D hD)
  else 0

theorem toPic0End_eq (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T) :
    toPic0End T = QuotientAddGroup.map _ _ (degZeroEnd T h) (by
      rintro ⟨D, hD0⟩ hD
      simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
      exact h.2 D hD) := by
  rw [toPic0End, dif_pos h]

theorem toPic0End_mk (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T)
    (D : Divisor.degZero (K := K) (F := F)) :
    toPic0End T (Pic0.mk D) = Pic0.mk (degZeroEnd T h D) := by
  rw [toPic0End_eq T h]
  rfl

theorem toPic0End_of_not (T : Divisor K F →+ Divisor K F) (h : ¬ DescendsToPic0 T) : toPic0End T = 0 := by
  rw [toPic0End, dif_neg h]

end Divisor

end AlgebraicCurve

namespace ModularCurve

section CharSlot

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def heckePic0FibreChar : Module.End ℤ (Pic0 K (modularFunctionFieldC K N)) :=
  (Divisor.toPic0End (heckeFibreGeomLevel K N data hKr)).toIntLinearMap

theorem heckePic0FibreChar_apply (x : Pic0 K (modularFunctionFieldC K N)) :
    heckePic0FibreChar K N data hKr x = Divisor.toPic0End (heckeFibreGeomLevel K N data hKr) x :=
  rfl

theorem heckeFibreGeomLevel_indep (data' : ModularPolynomialData ℓ) (hKr' : KroneckerCongruence ℓ data') :
    heckeFibreGeomLevel K N data hKr = heckeFibreGeomLevel K N data' hKr' :=
  rfl

theorem heckePic0FibreChar_indep (data' : ModularPolynomialData ℓ) (hKr' : KroneckerCongruence ℓ data') :
    heckePic0FibreChar K N data hKr = heckePic0FibreChar K N data' hKr' :=
  rfl

theorem descendsToPic0_heckeFibreGeomLevel (hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c)
    (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1) :
    Divisor.DescendsToPic0 (heckeFibreGeomLevel K N data hKr) :=
  ⟨fun _ hD => heckeFibreGeomLevel_mem_degZero K N data hKr hdeg1 hD,
    fun _ hD => isPrincipal_heckeFibreGeomLevel' K N data hKr hperf
      (frobOnPlacesGeomLevel_surjective K N data hKr hperf) hD⟩

theorem heckePic0FibreChar_eq_heckeFibreGeomLevelPic0OfIsCurveOver [IsAlgClosed K]
    [IsCurveOver K (modularFunctionFieldC K N)] :
    heckePic0FibreChar K N data hKr = (heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr).toIntLinearMap := by
  have h := descendsToPic0_heckeFibreGeomLevel K N data hKr (perfect_of_isAlgClosed K)
    (deg_eq_one_modularFunctionFieldC K N)
  refine LinearMap.ext fun x => ?_
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [heckePic0FibreChar_apply, Divisor.toPic0End_mk _ h, AddMonoidHom.coe_toIntLinearMap,
    heckeFibreGeomLevelPic0OfIsCurveOver_eq, heckeFibreGeomLevelPic0_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

end CharSlot

section Family

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (Tne : Nat.Primes → Module.End ℤ (Pic0 K (modularFunctionFieldC K N)))

def heckeFamilyFibreOf (q : Nat.Primes) : Module.End ℤ (Pic0 K (modularFunctionFieldC K N)) :=
  if (q : ℕ) = ℓ then heckePic0FibreChar K N data hKr else Tne q

theorem heckeFamilyFibreOf_of_eq {q : Nat.Primes} (hq : (q : ℕ) = ℓ) :
    heckeFamilyFibreOf K N data hKr Tne q = heckePic0FibreChar K N data hKr :=
  if_pos hq

theorem heckeFamilyFibreOf_of_ne {q : Nat.Primes} (hq : (q : ℕ) ≠ ℓ) :
    heckeFamilyFibreOf K N data hKr Tne q = Tne q :=
  if_neg hq

def HeckeOperatorsCommuteFibreOf : Prop :=
  ∀ q q' : Nat.Primes, Commute (heckeFamilyFibreOf K N data hKr Tne q) (heckeFamilyFibreOf K N data hKr Tne q')

variable {K N data hKr Tne} in

def heckeCommutingFamilyFibreOf (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)) :=
  ⟨heckeFamilyFibreOf K N data hKr Tne, h⟩

open Classical in

@[implicit_reducible]
def heckeModuleFibreOf : Module HeckeAlg (Pic0 K (modularFunctionFieldC K N)) :=
  if h : HeckeOperatorsCommuteFibreOf K N data hKr Tne then (heckeCommutingFamilyFibreOf h).module
  else Module.compHom (Pic0 K (modularFunctionFieldC K N))
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

variable {K N data hKr Tne}

theorem heckeModuleFibreOf_smul_def (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) (t : HeckeAlg)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; t • x) = (heckeCommutingFamilyFibreOf h).endHom t x := by
  have e : heckeModuleFibreOf K N data hKr Tne = (heckeCommutingFamilyFibreOf h).module := dif_pos h
  rw [e]
  rfl

theorem heckeModuleFibreOf_heckeGen_smul (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) (q : Nat.Primes)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = heckeFamilyFibreOf K N data hKr Tne q x := by
  rw [heckeModuleFibreOf_smul_def h, CommutingHeckeFamily.endHom_heckeGen]
  rfl

theorem heckeModuleFibreOf_heckeGen_smul_char (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) {q : Nat.Primes}
    (hq : (q : ℕ) = ℓ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = heckePic0FibreChar K N data hKr x := by
  rw [heckeModuleFibreOf_heckeGen_smul h, heckeFamilyFibreOf_of_eq K N data hKr Tne hq]

theorem heckeModuleFibreOf_heckeGen_smul_of_ne (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) {q : Nat.Primes}
    (hq : (q : ℕ) ≠ ℓ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = Tne q x := by
  rw [heckeModuleFibreOf_heckeGen_smul h, heckeFamilyFibreOf_of_ne K N data hKr Tne hq]

theorem heckeModuleFibreOf_smul_of_not (h : ¬ HeckeOperatorsCommuteFibreOf K N data hKr Tne) (t : HeckeAlg)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleFibreOf K N data hKr Tne =
      Module.compHom (Pic0 K (modularFunctionFieldC K N))
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ)) :=
    dif_neg h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]

theorem heckeModuleFibreOf_heckeGen_smul_of_not (h : ¬ HeckeOperatorsCommuteFibreOf K N data hKr Tne)
    (q : Nat.Primes) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = 0 := by
  rw [heckeModuleFibreOf_smul_of_not h, heckeGen, MvPolynomial.constantCoeff_X, zero_zsmul]

private theorem endHom_C' {J' : Type*} [AddCommGroup J'] (fam : CommutingHeckeFamily J') (a : ℤ) :
    fam.endHom (MvPolynomial.C a) = (a : Module.End ℤ J') := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

theorem heckeModuleFibreOf_C_smul (a : ℤ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; (MvPolynomial.C a : HeckeAlg) • x) = a • x := by
  by_cases h : HeckeOperatorsCommuteFibreOf K N data hKr Tne
  · rw [heckeModuleFibreOf_smul_def h, endHom_C', Module.End.intCast_apply]
  · rw [heckeModuleFibreOf_smul_of_not h, MvPolynomial.constantCoeff_C]

end Family

section Match

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (Tne : Nat.Primes → Module.End ℤ (Pic0 K (modularFunctionFieldC K N)))

theorem pic0SpecialFibreCommutingFamilyMatch_heckeCommutingFamilyFibreOf
    (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    Pic0SpecialFibreCommutingFamilyMatch K N data hKr (heckeCommutingFamilyFibreOf h) := by
  show heckeFamilyFibreOf K N data hKr Tne ⟨ℓ, hℓ.out⟩ = _
  rw [heckeFamilyFibreOf_of_eq K N data hKr Tne rfl,
    heckePic0FibreChar_eq_heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr]

theorem specialFibreHeckeModuleMatch_heckeModuleFibreOf (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    SpecialFibreHeckeModuleMatch K N data hKr (heckeModuleFibreOf K N data hKr Tne) := by
  have e : heckeModuleFibreOf K N data hKr Tne = (heckeCommutingFamilyFibreOf h).module := dif_pos h
  rw [e]
  exact specialFibreHeckeModuleMatch_of_commutingFamily K N data hKr _
    (pic0SpecialFibreCommutingFamilyMatch_heckeCommutingFamilyFibreOf K N data hKr Tne h)

end Match

end ModularCurve

namespace ModularCurve

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]

def charLDegeneracyRoof : IntermediateField k (LaurentSeries k) :=
  IntermediateField.adjoin k
    {jqModC k, jqNModC k N, jqNModC k q, jqNModC k (N * q)}

theorem modularFunctionFieldC_le_charLDegeneracyRoof :
    modularFunctionFieldC k N ≤ charLDegeneracyRoof k N q := by
  unfold modularFunctionFieldC charLDegeneracyRoof
  apply IntermediateField.adjoin.mono
  intro x hx
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem qExpand_image_le_charLDegeneracyRoof :
    (modularFunctionFieldC k N).map (qExpandAlgC k q) ≤ charLDegeneracyRoof k N q := by
  unfold modularFunctionFieldC
  rw [IntermediateField.adjoin_map]
  apply IntermediateField.adjoin.mono
  rintro x hx
  simp only [Set.image_insert_eq, Set.image_singleton, qExpandAlgC_apply] at hx
  rcases hx with h | h
  · subst h
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [Set.mem_singleton_iff] at h
    subst h
    refine Or.inr (Or.inr (Or.inr ?_))
    rw [Set.mem_singleton_iff]
    show qExpand k q (jqNModC k N) = jqNModC k (N * q)
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm q N]

def heckeAlphaC :
    modularFunctionFieldC k N →ₐ[k] charLDegeneracyRoof k N q :=
  IntermediateField.inclusion (modularFunctionFieldC_le_charLDegeneracyRoof k N q)

@[simp]
theorem coe_heckeAlphaC (x : modularFunctionFieldC k N) :
    (heckeAlphaC k N q x : LaurentSeries k) = (x : LaurentSeries k) :=
  IntermediateField.coe_inclusion _ x

def heckeBetaCRingHom :
    modularFunctionFieldC k N →+* charLDegeneracyRoof k N q where
  toFun x := ⟨qExpand k q (x : LaurentSeries k),
    qExpand_image_le_charLDegeneracyRoof k N q ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand k q))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand k q) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand k q))
  map_add' _ _ := Subtype.ext (map_add (qExpand k q) _ _)

def heckeBetaC :
    modularFunctionFieldC k N →ₐ[k] charLDegeneracyRoof k N q :=
  { heckeBetaCRingHom k N q with
    commutes' := fun a => Subtype.ext <| by
      show qExpand k q (algebraMap k (LaurentSeries k) a) = algebraMap k (LaurentSeries k) a
      rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_heckeBetaC (x : modularFunctionFieldC k N) :
    (heckeBetaC k N q x : LaurentSeries k) = qExpand k q (x : LaurentSeries k) :=
  rfl

def HeckeAlphaCIntegral : Prop := (heckeAlphaC k N q).toRingHom.IsIntegral

def HeckeBetaCIntegral : Prop := (heckeBetaC k N q).toRingHom.IsIntegral

def heckeDivFibre [HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q) :
    Divisor k (modularFunctionFieldC k N) →+ Divisor k (modularFunctionFieldC k N) :=
  Divisor.correspondence (heckeBetaC k N q) (heckeAlphaC k N q) hβ hα

def HeckeDivFibreDescends : Prop :=
  ∀ (hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q))
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q),
    letI := hP
    AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)

def HeckeInputsFibre : Prop :=
  ∃ (hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q))
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q),
    letI := hP
    AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)

open Classical in

def heckePic0Fibre : Module.End ℤ (Pic0 k (modularFunctionFieldC k N)) :=
  if h : HeckeInputsFibre k N q then
    letI := h.fst
    (AlgebraicCurve.Divisor.toPic0End (heckeDivFibre k N q h.snd.fst h.snd.snd.fst)).toIntLinearMap
  else 0

theorem heckeInputsFibre_intro
    [hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q)
    (hdesc : AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)) :
    HeckeInputsFibre k N q :=
  ⟨hP, hβ, hα, hdesc⟩

theorem heckePic0Fibre_eq
    [hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q)
    (hdesc : AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)) :
    heckePic0Fibre k N q
      = (AlgebraicCurve.Divisor.toPic0End (heckeDivFibre k N q hβ hα)).toIntLinearMap := by
  rw [heckePic0Fibre, dif_pos (heckeInputsFibre_intro k N q hβ hα hdesc)]

theorem heckePic0Fibre_of_not (h : ¬ HeckeInputsFibre k N q) : heckePic0Fibre k N q = 0 := by
  rw [heckePic0Fibre, dif_neg h]

section Instantiated

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP k ℓ]
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def heckeFamilyFibre (q' : Nat.Primes) : Module.End ℤ (Pic0 k (modularFunctionFieldC k N)) :=
  heckeFamilyFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ)) q'

def HeckeOperatorsCommuteFibre : Prop :=
  HeckeOperatorsCommuteFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ))

@[implicit_reducible]
def heckeModuleFibre : Module HeckeAlg (Pic0 k (modularFunctionFieldC k N)) :=
  heckeModuleFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ))

theorem heckeModuleFibre_heckeGen_smul (h : HeckeOperatorsCommuteFibre k N data hKr)
    (q' : Nat.Primes) (x : Pic0 k (modularFunctionFieldC k N)) :
    (letI := heckeModuleFibre k N data hKr; heckeGen q' • x)
      = heckeFamilyFibre k N data hKr q' x :=
  heckeModuleFibreOf_heckeGen_smul (K := k) (N := N) (data := data) (hKr := hKr)
    (Tne := fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ)) h q' x

theorem specialFibreHeckeModuleMatch_heckeModuleFibre [IsAlgClosed k]
    [AlgebraicCurve.IsCurveOver k (modularFunctionFieldC k N)]
    (h : HeckeOperatorsCommuteFibre k N data hKr) :
    SpecialFibreHeckeModuleMatch k N data hKr (heckeModuleFibre k N data hKr) :=
  specialFibreHeckeModuleMatch_heckeModuleFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ)) h

end Instantiated

example : Prop :=
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  HeckeInputsFibre (ZMod 5) 7 2

example : Prop :=
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  HeckeDivFibreDescends (ZMod 5) 7 2

end ModularCurve

end



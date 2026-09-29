-- Prove2me | Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
-- name    : AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/1772a5ce-cf67-5cc8-ba0f-1224e2b6177b
-- title:
--   Component-group carriers from special-fibre intersection tables
-- statement:
--   Two scheme-level predicates open the module. For a morphism $f : X \to Y$ of schemes, `PushforwardStructureSheafIso f` asserts that for every open $U \subseteq Y$ the component map $f.app\ U$ of the unit $\mathcal{O}_Y \to f_*\mathcal{O}_X$ is an isomorphism in `CommRingCat`; `CohomologicallyFlatInDimZero f` asserts that this holds for every base change, i.e. for `pullback.snd f g` for all $g : T \to Y$. Both hold when $f$ is an isomorphism.
--
--   The combinatorial core is `SpecialFibreComponentTable ι` over a finite index type $\iota$: data of multiplicities $\mathrm{mult} : \iota \to \mathbb{N}$ and an intersection matrix $\mathrm{inter} : \iota \to \iota \to \mathbb{Z}$, subject to positivity of each multiplicity, symmetry of $\mathrm{inter}$, and the fibre relation $\sum_j \mathrm{inter}\,i\,j \cdot \mathrm{mult}\,j = 0$ for each $i$. From a table one forms the additive maps $\alpha =$ `intersectionAlpha`, $\alpha(c)_j = \sum_i c_i\,\mathrm{inter}\,i\,j$, and $\beta =$ `multiplicityBeta`, $\beta(a) = \sum_i a_i\,\mathrm{mult}\,i$; the fibre relation gives $\beta \circ \alpha = 0$. `degreeZeroSublattice` is $\ker\beta \le \mathbb{Z}^\iota$, `imageOfIntersectionAlpha` is the image of $\alpha$ viewed inside it, and `AppendixComponentGroup` is the quotient $\ker\beta/\operatorname{im}\alpha$, with `appendixComponentGroupClass` the (surjective) quotient map. `GcdOfMultiplicitiesIsOne` says the gcd of the multiplicities is $1$.
--
--   Two explicit tables are recorded: `goodReductionTable` (one component, multiplicity $1$, zero intersection), whose degree-zero sublattice and hence component group are trivial, and `twoComponentTable` (two components of multiplicity $1$, self-intersections $-5$, mutual intersection $5$), where the vector $(1,-1)$ lies in $\ker\beta$ but not in $\operatorname{im}\alpha$, so the component group is nontrivial.
--
--   Finally, over a Dedekind domain $R$ with fraction field $K$, three Prop-valued structures package hypotheses. `Thm13RaynaudPicNeronInput` for $f : X \to \operatorname{Spec} R$ and $\nu : N \to \operatorname{Spec} R$ with a table $t$ carries: $f$ proper and flat, the gcd condition on $t$, `PushforwardStructureSheafIso f`, `CohomologicallyFlatInDimZero f`, and `NeronModelPropertyBundle R K ν` (smoothness, separatedness, locally of finite type, quasi-compactness and the unique-extension property of $\nu$). `Prop14ComponentPresentationInput` takes an abelian group $P$ with a degree map $\mathrm{degRestrict} : P \to \mathbb{Z}^\iota$, a subgroup $E \le P$ and a specialisation $\mathrm{specialise} : P \to \Phi$, and requires that $\mathrm{degRestrict}$ kill $E$, that it be surjective, and that there exist an additive equivalence $\mathrm{AppendixComponentGroup}\ t \simeq \Phi$ carrying the class of $\mathrm{degRestrict}\,x$ to $\mathrm{specialise}\,x$ whenever $\mathrm{degRestrict}\,x \in \ker\beta$; so the presentation is a field of the structure, not a theorem proved here. Its consequences drawn here are that $\mathrm{specialise}$ is surjective, vanishes on $E$, and vanishes on all degree-zero elements in the good-reduction case. `MazurRapoportAppendixPackage` conjoins the two, and instances of all three are exhibited for the identity morphism of $\operatorname{Spec}\mathbb{Z}_p$ with the good-reduction table, and of the second for the two-component table.
--
--   **Relation to Mathlib.** Mathlib has no Néron model, special-fibre component group or cohomological-flatness API; these are the project's own notions. Note that `PushforwardStructureSheafIso` is phrased concretely as invertibility of each component of the sheaf map $\mathcal{O}_Y \to f_*\mathcal{O}_X$, and `CohomologicallyFlatInDimZero` as stability of that condition under all base changes, rather than via higher direct images.
--
--   **Where it is used.** The definitions feed the combinatorial treatment of component groups of Jacobians of modular curves at primes of bad reduction, which is where the appendix results of Mazur and Rapoport are used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace MazurRapoportAppendix

section SchemeLevelClauses

variable {X Y : Scheme.{u}}

def PushforwardStructureSheafIso (f : X ⟶ Y) : Prop :=
  ∀ U : Y.Opens, IsIso (f.app U)

theorem pushforwardStructureSheafIso_iff (f : X ⟶ Y) :
    PushforwardStructureSheafIso f ↔ ∀ U : Y.Opens, IsIso (f.app U) :=
  Iff.rfl

theorem pushforwardStructureSheafIso_of_isIso (f : X ⟶ Y) [IsIso f] :
    PushforwardStructureSheafIso f :=
  fun _ => inferInstance

def CohomologicallyFlatInDimZero (f : X ⟶ Y) : Prop :=
  ∀ (T : Scheme.{u}) (g : T ⟶ Y), PushforwardStructureSheafIso (pullback.snd f g)

theorem cohomologicallyFlatInDimZero_of_isIso (f : X ⟶ Y) [IsIso f] :
    CohomologicallyFlatInDimZero f :=
  fun _ g => pushforwardStructureSheafIso_of_isIso (pullback.snd f g)

end SchemeLevelClauses

section ComponentTable

variable {ι : Type*} [Fintype ι]

structure SpecialFibreComponentTable (ι : Type*) [Fintype ι] where

  mult : ι → ℕ

  inter : ι → ι → ℤ

  mult_pos : ∀ i, 0 < mult i

  inter_symm : ∀ i j, inter i j = inter j i

  fibre_inter_zero : ∀ i, ∑ j, inter i j * (mult j : ℤ) = 0

def GcdOfMultiplicitiesIsOne (t : SpecialFibreComponentTable ι) : Prop :=
  Finset.univ.gcd t.mult = 1

theorem gcdOfMultiplicitiesIsOne_of_mult_eq_one (t : SpecialFibreComponentTable ι) (i : ι)
    (hi : t.mult i = 1) : GcdOfMultiplicitiesIsOne t :=
  Nat.dvd_one.mp (hi ▸ Finset.gcd_dvd (Finset.mem_univ i))

def intersectionAlpha (t : SpecialFibreComponentTable ι) : (ι → ℤ) →+ (ι → ℤ) where
  toFun c := fun j => ∑ i, c i * t.inter i j
  map_zero' := by
    funext j
    simp
  map_add' a b := by
    funext j
    simp [add_mul, Finset.sum_add_distrib]

@[simp]
theorem intersectionAlpha_apply (t : SpecialFibreComponentTable ι) (c : ι → ℤ) (j : ι) :
    intersectionAlpha t c j = ∑ i, c i * t.inter i j :=
  rfl

def multiplicityBeta (t : SpecialFibreComponentTable ι) : (ι → ℤ) →+ ℤ where
  toFun a := ∑ i, a i * (t.mult i : ℤ)
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

@[simp]
theorem multiplicityBeta_apply (t : SpecialFibreComponentTable ι) (a : ι → ℤ) :
    multiplicityBeta t a = ∑ i, a i * (t.mult i : ℤ) :=
  rfl

theorem multiplicityBeta_intersectionAlpha (t : SpecialFibreComponentTable ι) (c : ι → ℤ) :
    multiplicityBeta t (intersectionAlpha t c) = 0 := by
  have key : ∀ i : ι, c i * ∑ j, t.inter i j * (t.mult j : ℤ) = 0 := fun i => by
    rw [t.fibre_inter_zero i, mul_zero]
  calc multiplicityBeta t (intersectionAlpha t c)
      = ∑ j, (∑ i, c i * t.inter i j) * (t.mult j : ℤ) := by
        simp only [multiplicityBeta_apply, intersectionAlpha_apply]
    _ = ∑ j, ∑ i, c i * t.inter i j * (t.mult j : ℤ) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
    _ = ∑ i, ∑ j, c i * t.inter i j * (t.mult j : ℤ) := Finset.sum_comm
    _ = ∑ i, c i * ∑ j, t.inter i j * (t.mult j : ℤ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := Finset.sum_eq_zero fun i _ => key i

def degreeZeroSublattice (t : SpecialFibreComponentTable ι) : AddSubgroup (ι → ℤ) :=
  (multiplicityBeta t).ker

theorem mem_degreeZeroSublattice {t : SpecialFibreComponentTable ι} {a : ι → ℤ} :
    a ∈ degreeZeroSublattice t ↔ ∑ i, a i * (t.mult i : ℤ) = 0 := by
  simp only [degreeZeroSublattice, AddMonoidHom.mem_ker, multiplicityBeta_apply]

theorem intersectionAlpha_mem_degreeZeroSublattice (t : SpecialFibreComponentTable ι)
    (c : ι → ℤ) : intersectionAlpha t c ∈ degreeZeroSublattice t := by
  rw [degreeZeroSublattice, AddMonoidHom.mem_ker]
  exact multiplicityBeta_intersectionAlpha t c

def imageOfIntersectionAlpha (t : SpecialFibreComponentTable ι) :
    AddSubgroup ↥(degreeZeroSublattice t) :=
  ((intersectionAlpha t).range).addSubgroupOf (degreeZeroSublattice t)

theorem mem_imageOfIntersectionAlpha {t : SpecialFibreComponentTable ι}
    {x : ↥(degreeZeroSublattice t)} :
    x ∈ imageOfIntersectionAlpha t ↔ ∃ c : ι → ℤ, intersectionAlpha t c = (x : ι → ℤ) := by
  simp only [imageOfIntersectionAlpha, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

abbrev AppendixComponentGroup (t : SpecialFibreComponentTable ι) : Type _ :=
  ↥(degreeZeroSublattice t) ⧸ imageOfIntersectionAlpha t

def appendixComponentGroupClass (t : SpecialFibreComponentTable ι) :
    ↥(degreeZeroSublattice t) →+ AppendixComponentGroup t :=
  QuotientAddGroup.mk' (imageOfIntersectionAlpha t)

theorem appendixComponentGroupClass_surjective (t : SpecialFibreComponentTable ι) :
    Function.Surjective (appendixComponentGroupClass t) :=
  QuotientAddGroup.mk'_surjective (imageOfIntersectionAlpha t)

end ComponentTable

section GoodReductionGate

def goodReductionTable : SpecialFibreComponentTable (Fin 1) where
  mult := fun _ => 1
  inter := fun _ _ => 0
  mult_pos := fun _ => Nat.one_pos
  inter_symm := fun _ _ => rfl
  fibre_inter_zero := fun _ => by simp

theorem gcdOfMultiplicitiesIsOne_goodReductionTable :
    GcdOfMultiplicitiesIsOne goodReductionTable :=
  gcdOfMultiplicitiesIsOne_of_mult_eq_one goodReductionTable 0 rfl

theorem subsingleton_appendixComponentGroup_goodReductionTable :
    Subsingleton (AppendixComponentGroup goodReductionTable) := by
  have hmem : ∀ x : ↥(degreeZeroSublattice goodReductionTable), x = 0 := by
    rintro ⟨a, ha⟩
    have h0 : a 0 = 0 := by
      have h1 := mem_degreeZeroSublattice.mp ha
      simpa [goodReductionTable, Fin.sum_univ_one] using h1
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    simp [hi, h0]
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := appendixComponentGroupClass_surjective goodReductionTable a
  obtain ⟨y, rfl⟩ := appendixComponentGroupClass_surjective goodReductionTable b
  rw [hmem x, hmem y]

end GoodReductionGate

section TwoComponentGate

def twoComponentTable : SpecialFibreComponentTable (Fin 2) where
  mult := fun _ => 1
  inter := fun i j => if i = j then -5 else 5
  mult_pos := fun _ => Nat.one_pos
  inter_symm := by decide
  fibre_inter_zero := by decide

theorem gcdOfMultiplicitiesIsOne_twoComponentTable :
    GcdOfMultiplicitiesIsOne twoComponentTable :=
  gcdOfMultiplicitiesIsOne_of_mult_eq_one twoComponentTable 0 rfl

def twoComponentWitness : Fin 2 → ℤ := fun i => if i = 0 then 1 else -1

theorem twoComponentWitness_mem_degreeZero :
    twoComponentWitness ∈ degreeZeroSublattice twoComponentTable := by
  rw [mem_degreeZeroSublattice]
  decide

theorem twoComponentWitness_not_mem_image :
    (⟨twoComponentWitness, twoComponentWitness_mem_degreeZero⟩ :
        ↥(degreeZeroSublattice twoComponentTable)) ∉
      imageOfIntersectionAlpha twoComponentTable := by
  rw [mem_imageOfIntersectionAlpha]
  rintro ⟨c, hc⟩
  have hc' : intersectionAlpha twoComponentTable c = twoComponentWitness := hc
  have h0 := congrFun hc' 0
  rw [intersectionAlpha_apply, Fin.sum_univ_two] at h0
  have e1 : twoComponentTable.inter 0 0 = -5 := rfl
  have e2 : twoComponentTable.inter 1 0 = 5 := rfl
  have e3 : twoComponentWitness 0 = 1 := rfl
  rw [e1, e2, e3] at h0
  omega

theorem appendixComponentGroupClass_twoComponentWitness_ne_zero :
    appendixComponentGroupClass twoComponentTable
        ⟨twoComponentWitness, twoComponentWitness_mem_degreeZero⟩ ≠ 0 := by
  intro h
  have hker : (⟨twoComponentWitness, twoComponentWitness_mem_degreeZero⟩ :
      ↥(degreeZeroSublattice twoComponentTable)) ∈
      (QuotientAddGroup.mk' (imageOfIntersectionAlpha twoComponentTable)).ker :=
    AddMonoidHom.mem_ker.mpr h
  rw [QuotientAddGroup.ker_mk'] at hker
  exact twoComponentWitness_not_mem_image hker

theorem nontrivial_appendixComponentGroup_twoComponentTable :
    Nontrivial (AppendixComponentGroup twoComponentTable) :=
  nontrivial_of_ne _ _ appendixComponentGroupClass_twoComponentWitness_ne_zero

end TwoComponentGate

section HeldCarriers

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X N : Scheme.{u}}

structure Thm13RaynaudPicNeronInput
    (f : X ⟶ Spec (CommRingCat.of R)) (ν : N ⟶ Spec (CommRingCat.of R))
    {ι : Type*} [Fintype ι] (t : SpecialFibreComponentTable ι) : Prop where

  model_proper : IsProper f

  model_flat : Flat f

  gcd_multiplicities : GcdOfMultiplicitiesIsOne t

  pushforward_structure_sheaf : PushforwardStructureSheafIso f

  cohomologically_flat : CohomologicallyFlatInDimZero f

  neron_bundle : NeronModelPropertyBundle R K ν

structure Prop14ComponentPresentationInput
    {ι : Type*} [Fintype ι] (t : SpecialFibreComponentTable ι)
    (P : Type*) [AddCommGroup P] (degRestrict : P →+ (ι → ℤ)) (E : AddSubgroup P)
    (Φ : Type*) [AddCommGroup Φ] (specialise : P →+ Φ) : Prop where

  unitClosure_deg_zero : ∀ x ∈ E, degRestrict x = 0

  degRestrict_surjective : Function.Surjective degRestrict

  presentation : ∃ e : AppendixComponentGroup t ≃+ Φ,
    ∀ (x : P) (hx : degRestrict x ∈ degreeZeroSublattice t),
      e (appendixComponentGroupClass t ⟨degRestrict x, hx⟩) = specialise x

structure MazurRapoportAppendixPackage
    (f : X ⟶ Spec (CommRingCat.of R)) (ν : N ⟶ Spec (CommRingCat.of R))
    {ι : Type*} [Fintype ι] (t : SpecialFibreComponentTable ι)
    (P : Type*) [AddCommGroup P] (degRestrict : P →+ (ι → ℤ)) (E : AddSubgroup P)
    (Φ : Type*) [AddCommGroup Φ] (specialise : P →+ Φ) : Prop where

  thm13 : Thm13RaynaudPicNeronInput R K f ν t

  prop14 : Prop14ComponentPresentationInput t P degRestrict E Φ specialise

end HeldCarriers

namespace Prop14ComponentPresentationInput

variable {ι : Type*} [Fintype ι] {t : SpecialFibreComponentTable ι}
variable {P : Type*} [AddCommGroup P] {degRestrict : P →+ (ι → ℤ)} {E : AddSubgroup P}
variable {Φ : Type*} [AddCommGroup Φ] {specialise : P →+ Φ}

theorem specialise_surjective
    (h : Prop14ComponentPresentationInput t P degRestrict E Φ specialise) :
    Function.Surjective specialise := by
  obtain ⟨e, he⟩ := h.presentation
  intro φ
  obtain ⟨q, hq⟩ : ∃ q : AppendixComponentGroup t, e q = φ := ⟨e.symm φ, e.apply_symm_apply φ⟩
  obtain ⟨⟨w, hw⟩, rfl⟩ := appendixComponentGroupClass_surjective t q
  obtain ⟨x, hx⟩ := h.degRestrict_surjective w
  refine ⟨x, ?_⟩
  have hxmem : degRestrict x ∈ degreeZeroSublattice t := by rw [hx]; exact hw
  have hclass : (⟨degRestrict x, hxmem⟩ : ↥(degreeZeroSublattice t)) = ⟨w, hw⟩ :=
    Subtype.ext hx
  have hkey := he x hxmem
  rw [hclass] at hkey
  rw [← hkey]
  exact hq

theorem specialise_eq_zero_of_mem_unitClosure
    (h : Prop14ComponentPresentationInput t P degRestrict E Φ specialise)
    {x : P} (hx : x ∈ E) : specialise x = 0 := by
  obtain ⟨e, he⟩ := h.presentation
  have hdeg : degRestrict x = 0 := h.unitClosure_deg_zero x hx
  have hmem : degRestrict x ∈ degreeZeroSublattice t := by
    rw [hdeg]; exact zero_mem _
  have hkey := he x hmem
  have hzero : (⟨degRestrict x, hmem⟩ : ↥(degreeZeroSublattice t)) = 0 := by
    apply Subtype.ext
    simpa using hdeg
  rw [hzero, map_zero, map_zero] at hkey
  exact hkey.symm

theorem specialise_eq_zero_at_goodReduction
    {P : Type*} [AddCommGroup P] {degRestrict : P →+ (Fin 1 → ℤ)} {E : AddSubgroup P}
    {Φ : Type*} [AddCommGroup Φ] {specialise : P →+ Φ}
    (h : Prop14ComponentPresentationInput goodReductionTable P degRestrict E Φ specialise)
    (x : P) (hx : degRestrict x ∈ degreeZeroSublattice goodReductionTable) :
    specialise x = 0 := by
  obtain ⟨e, he⟩ := h.presentation
  have hkey := he x hx
  haveI := subsingleton_appendixComponentGroup_goodReductionTable
  have hzero : appendixComponentGroupClass goodReductionTable ⟨degRestrict x, hx⟩ = 0 :=
    Subsingleton.elim _ _
  rw [hzero, map_zero] at hkey
  exact hkey.symm

end Prop14ComponentPresentationInput

section SatGates

theorem gate_thm13RaynaudPicNeronInput_trivialModel_zp (p : ℕ) [Fact p.Prime] :
    Thm13RaynaudPicNeronInput ℤ_[p] ℚ_[p]
      (𝟙 (Spec (CommRingCat.of ℤ_[p]))) (𝟙 (Spec (CommRingCat.of ℤ_[p])))
      goodReductionTable :=
  { model_proper := inferInstance
    model_flat := inferInstance
    gcd_multiplicities := gcdOfMultiplicitiesIsOne_goodReductionTable
    pushforward_structure_sheaf :=
      pushforwardStructureSheafIso_of_isIso (𝟙 (Spec (CommRingCat.of ℤ_[p])))
    cohomologically_flat :=
      cohomologicallyFlatInDimZero_of_isIso (𝟙 (Spec (CommRingCat.of ℤ_[p])))
    neron_bundle := gate_neronModelPropertyBundle_trivialGroupScheme_zp p }

theorem gate_prop14ComponentPresentationInput_goodReduction :
    Prop14ComponentPresentationInput goodReductionTable
      (Fin 1 → ℤ) (AddMonoidHom.id _) ⊥
      (AppendixComponentGroup goodReductionTable) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simpa using hx
  · exact fun w => ⟨w, rfl⟩
  · refine ⟨AddEquiv.refl _, fun x hx => ?_⟩
    haveI := subsingleton_appendixComponentGroup_goodReductionTable
    exact Subsingleton.elim _ _

def twoComponentRetract : (Fin 2 → ℤ) →+ ↥(degreeZeroSublattice twoComponentTable) :=
  AddMonoidHom.mk'
    (fun v =>
      ⟨v - (multiplicityBeta twoComponentTable v) • Pi.single (0 : Fin 2) (1 : ℤ), by
        have hsingle : multiplicityBeta twoComponentTable (Pi.single (0 : Fin 2) (1 : ℤ)) = 1 := by
          decide
        have hβ : multiplicityBeta twoComponentTable
            (v - (multiplicityBeta twoComponentTable v) • Pi.single (0 : Fin 2) (1 : ℤ)) = 0 := by
          rw [map_sub, map_zsmul, hsingle, smul_eq_mul, mul_one, sub_self]
        rw [degreeZeroSublattice, AddMonoidHom.mem_ker]
        exact hβ⟩)
    (fun a b => by
      apply Subtype.ext
      show (a + b) - (multiplicityBeta twoComponentTable (a + b)) •
            Pi.single (0 : Fin 2) (1 : ℤ) =
          (a - (multiplicityBeta twoComponentTable a) • Pi.single (0 : Fin 2) (1 : ℤ)) +
          (b - (multiplicityBeta twoComponentTable b) • Pi.single (0 : Fin 2) (1 : ℤ))
      rw [map_add, add_smul]
      abel)

theorem gate_prop14ComponentPresentationInput_twoComponent :
    Prop14ComponentPresentationInput twoComponentTable
      (Fin 2 → ℤ) (AddMonoidHom.id _) ⊥
      (AppendixComponentGroup twoComponentTable)
      ((appendixComponentGroupClass twoComponentTable).comp twoComponentRetract) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simpa using hx
  · exact fun w => ⟨w, rfl⟩
  · refine ⟨AddEquiv.refl _, fun x hx => ?_⟩
    have hβ : multiplicityBeta twoComponentTable x = 0 := by
      have hx' : (AddMonoidHom.id (Fin 2 → ℤ)) x ∈ (multiplicityBeta twoComponentTable).ker := hx
      simpa [AddMonoidHom.mem_ker] using hx'
    have hretract : twoComponentRetract x = ⟨x, hx⟩ := by
      apply Subtype.ext
      show x - (multiplicityBeta twoComponentTable x) • Pi.single (0 : Fin 2) (1 : ℤ) = x
      rw [hβ, zero_smul, sub_zero]
    show appendixComponentGroupClass twoComponentTable ⟨x, hx⟩ =
      appendixComponentGroupClass twoComponentTable (twoComponentRetract x)
    rw [hretract]

theorem gate_mazurRapoportAppendixPackage_trivialModel_zp (p : ℕ) [Fact p.Prime] :
    MazurRapoportAppendixPackage ℤ_[p] ℚ_[p]
      (𝟙 (Spec (CommRingCat.of ℤ_[p]))) (𝟙 (Spec (CommRingCat.of ℤ_[p])))
      goodReductionTable
      (Fin 1 → ℤ) (AddMonoidHom.id _) ⊥
      (AppendixComponentGroup goodReductionTable) 0 :=
  ⟨gate_thm13RaynaudPicNeronInput_trivialModel_zp p,
    gate_prop14ComponentPresentationInput_goodReduction⟩

end SatGates

end MazurRapoportAppendix

/--
info: 'MazurRapoportAppendix.multiplicityBeta_intersectionAlpha' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.multiplicityBeta_intersectionAlpha

/--
info: 'MazurRapoportAppendix.pushforwardStructureSheafIso_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.pushforwardStructureSheafIso_of_isIso

/--
info: 'MazurRapoportAppendix.cohomologicallyFlatInDimZero_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.cohomologicallyFlatInDimZero_of_isIso

/--
info: 'MazurRapoportAppendix.subsingleton_appendixComponentGroup_goodReductionTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.subsingleton_appendixComponentGroup_goodReductionTable

/--
info: 'MazurRapoportAppendix.appendixComponentGroupClass_twoComponentWitness_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.appendixComponentGroupClass_twoComponentWitness_ne_zero

/--
info: 'MazurRapoportAppendix.nontrivial_appendixComponentGroup_twoComponentTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.nontrivial_appendixComponentGroup_twoComponentTable

/--
info: 'MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_surjective

/--
info: 'MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_of_mem_unitClosure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_of_mem_unitClosure

/--
info: 'MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_at_goodReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_at_goodReduction

/--
info: 'MazurRapoportAppendix.gate_thm13RaynaudPicNeronInput_trivialModel_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_thm13RaynaudPicNeronInput_trivialModel_zp

/--
info: 'MazurRapoportAppendix.gate_prop14ComponentPresentationInput_goodReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_prop14ComponentPresentationInput_goodReduction

/--
info: 'MazurRapoportAppendix.gate_prop14ComponentPresentationInput_twoComponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_prop14ComponentPresentationInput_twoComponent

/--
info: 'MazurRapoportAppendix.gate_mazurRapoportAppendixPackage_trivialModel_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_mazurRapoportAppendixPackage_trivialModel_zp



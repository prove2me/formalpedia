-- Prove2me | Definitions.Def_RPLib_S4_EtShGenBr
-- name    : RPLib_S4_EtShGenBr
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:17:14.371933+00:00
-- url     : https://prove2.me/theorems/c320d248-30b3-498a-a3b8-da64cffcffcc
-- title:
--   The generic Galois group maps onto $\pi_1(\mathrm{Spec}\,A)$
-- statement:
--   Let $A$ be a domain with fraction field $K$, $K_U \subseteq \overline K$ the maximal extension of $K$ unramified over $A$, and $\pi_1 = \mathrm{Gal}(K_U/K)$ with its Krull topology. For a field $\kappa$ with a homomorphism $K \to \kappa$ and a separably closed field $\Omega \supseteq \kappa$, $K_U$ embeds into $\Omega$ over $K$, and restriction along this embedding is a continuous homomorphism $\mathrm{Gal}(\Omega/\kappa) \to \pi_1$, surjective when $K \to \kappa$ is onto, whose kernel consists of the automorphisms fixing the image of $K_U$. At the generic point $\eta$ of $\mathrm{Spec}\,A$ (where $\kappa(\eta) \cong K$) this is the comparison map $\mathrm{Gal}(\kappa(\eta)^{\mathrm{sep}}/\kappa(\eta)) \twoheadrightarrow \pi_1(\mathrm{Spec}\,A)$ from the group acting on generic stalks to the fundamental group.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V, Section 8; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5

import Mathlib
import Definitions.Def_RPLib_S4_GalCover
import Definitions.Def_RPLib_S4_EtShGalAct

/-!
# S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`

For a field `K` (a fraction field of `A`), a field `κ` with `K → κ`, and a separably closed `Ω/κ`, the maximal
unramified extension `K_U = maxUnram A K` embeds into `Ω` over `K` (`emb`), and restriction along this embedding is a
continuous group homomorphism `toPi1 : Gal(Ω/κ) →* Pi1 A K` (`emb_toPi1`), surjective when `K → κ` is onto
(`toPi1_surjective`), with kernel the automorphisms fixing `emb(K_U)` (`toPi1_eq_one_iff`).

Specialised to the generic point `η = ⊥` of `Spec A` (`κ(η) ≅ K`, `fracIso`), this is the bridge
`genToPi1 : Gal η →* Pi1 A K` from the Galois group acting on stalks at `η̄` (`galRep`) to `GalCover`'s `π₁`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves

namespace GenBr

section Abstract

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- `K_U = maxUnram A K` embeds into the separably closed field `Ω` over `K`. -/
def emb : maxUnram A K →ₐ[K] Ω := IsSepClosed.lift

/-- `Ω` as a `K_U`-algebra through `emb`. -/
def embAlg : Algebra (maxUnram A K) Ω := (emb A K Ω).toRingHom.toAlgebra

attribute [local instance] embAlg

theorem embTower : IsScalarTower K (maxUnram A K) Ω :=
  IsScalarTower.of_algebraMap_eq (fun x => ((emb A K Ω).commutes x).symm)

attribute [local instance] embTower

variable (κ : Type) [Field κ] [Algebra K κ] [Algebra κ Ω] [IsScalarTower K κ Ω]

/-- Restriction `Gal(Ω/κ) → Gal(K_U/K) = π₁(Spec A)` along `emb`. -/
def toPi1 : (Ω ≃ₐ[κ] Ω) →* Pi1 A K :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnram A K)).comp (AlgEquiv.restrictScalarsHom K)

theorem emb_toPi1 (σ : Ω ≃ₐ[κ] Ω) (x : maxUnram A K) :
    emb A K Ω (toPi1 A K Ω κ σ x) = σ (emb A K Ω x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) (maxUnram A K) x

theorem toPi1_eq_one_iff (σ : Ω ≃ₐ[κ] Ω) :
    toPi1 A K Ω κ σ = 1 ↔ ∀ x : maxUnram A K, σ (emb A K Ω x) = emb A K Ω x := by
  constructor
  · intro h x
    have := emb_toPi1 A K Ω κ σ x
    rw [h] at this
    exact this.symm
  · intro h
    refine AlgEquiv.ext fun x => ?_
    apply (emb A K Ω).toRingHom.injective
    show emb A K Ω (toPi1 A K Ω κ σ x) = emb A K Ω x
    rw [emb_toPi1, h]

/-- If `K → κ` is onto and `Ω/κ` is Galois, every element of `π₁` comes from `Gal(Ω/κ)`. -/
theorem toPi1_surjective [IsGalois κ Ω] (h : Function.Surjective (algebraMap K κ)) :
    Function.Surjective (toPi1 A K Ω κ) := by
  have hb : Function.Bijective (algebraMap K κ) := ⟨(algebraMap K κ).injective, h⟩
  haveI : IsGalois K Ω := IsGalois.of_equiv_equiv (F := κ) (E := Ω)
    (f := (RingEquiv.ofBijective (algebraMap K κ) hb).symm) (g := RingEquiv.refl Ω) (by
      ext c
      show algebraMap K Ω ((RingEquiv.ofBijective (algebraMap K κ) hb).symm c) = algebraMap κ Ω c
      rw [IsScalarTower.algebraMap_apply K κ Ω]
      congr 1
      exact (RingEquiv.ofBijective (algebraMap K κ) hb).apply_symm_apply c)
  intro τ
  have hσ : ∀ c : κ, (τ.liftNormal Ω) (algebraMap κ Ω c) = algebraMap κ Ω c := by
    intro c
    obtain ⟨k, rfl⟩ := h c
    rw [← IsScalarTower.algebraMap_apply K κ Ω]
    exact (τ.liftNormal Ω).commutes k
  refine ⟨AlgEquiv.ofRingEquiv (f := (τ.liftNormal Ω).toRingEquiv) hσ, ?_⟩
  refine AlgEquiv.ext fun x => ?_
  apply (emb A K Ω).toRingHom.injective
  show emb A K Ω (toPi1 A K Ω κ _ x) = emb A K Ω (τ x)
  rw [emb_toPi1]
  exact τ.liftNormal_commutes Ω x

/-- An automorphism of `K_U/K` fixing a `K`-basis of a finite subextension fixes the subextension. -/
theorem mem_fixingSubgroup_of_basis (L : IntermediateField K (maxUnram A K)) [FiniteDimensional K L]
    (τ : Pi1 A K) (hτ : ∀ i, τ ((Module.finBasis K L i : L) : maxUnram A K) = (Module.finBasis K L i : L)) :
    τ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have h2 : y = ∑ i, (Module.finBasis K L).repr ⟨y, hy⟩ i • ((Module.finBasis K L i : L) : maxUnram A K) := by
    calc y = L.val ⟨y, hy⟩ := rfl
      _ = L.val (∑ i, (Module.finBasis K L).repr ⟨y, hy⟩ i • Module.finBasis K L i) := by
          rw [(Module.finBasis K L).sum_repr]
      _ = _ := by simp only [map_sum, map_smul, IntermediateField.coe_val]
  rw [h2, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, hτ i]

/-- `toPi1` is continuous for the Krull topologies. -/
theorem toPi1_continuous [Algebra.IsSeparable κ Ω] : Continuous (toPi1 A K Ω κ) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L, hL, hO⟩ := hN
  let S : Set Ω := Set.range (fun i => emb A K Ω ((Module.finBasis K L i : L) : maxUnram A K))
  haveI : Finite S := Finite.Set.finite_range _
  haveI : FiniteDimensional κ (IntermediateField.adjoin κ S) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsSeparable.isIntegral κ x)
  apply mem_nhds_iff.mpr
  refine ⟨((IntermediateField.adjoin κ S).fixingSubgroup : Set (Ω ≃ₐ[κ] Ω)), ?_,
    IntermediateField.fixingSubgroup_isOpen _, (IntermediateField.adjoin κ S).fixingSubgroup.one_mem⟩
  intro σ hσ
  apply hO
  simp only [SetLike.mem_coe] at hσ ⊢
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  apply mem_fixingSubgroup_of_basis
  intro i
  apply (emb A K Ω).toRingHom.injective
  show emb A K Ω (toPi1 A K Ω κ σ _) = emb A K Ω _
  rw [emb_toPi1]
  exact hσ _ (IntermediateField.subset_adjoin κ S ⟨i, rfl⟩)

end Abstract

section Generic

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The generic point `η = ⊥` of `Spec A`. -/
abbrev genPt : Spec (CommRingCat.of A) := (⊥ : PrimeSpectrum A)

theorem genPt_eq : genPt A = genericPoint (Spec (CommRingCat.of A)) := by
  haveI : IsDomain (CommRingCat.of A) := ‹IsDomain A›
  exact (genericPoint_eq_bot_of_affine (CommRingCat.of A)).symm

/-- The residue field `κ(η)` of `Spec A` at its generic point. -/
abbrev genField : Type := (Spec (CommRingCat.of A)).residueField (genPt A)

/-- `K ≅ κ(η)`: both are fraction fields of `A`. -/
def fracIso : K ≃+* genField A :=
  (IsLocalization.algEquiv (nonZeroDivisors A) K (⊥ : Ideal A).ResidueField).toRingEquiv.trans
    (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).commRingCatIsoToRingEquiv.symm

/-- `κ(η)` as a `K`-algebra through `fracIso`. -/
def genAlg : Algebra K (genField A) := (fracIso A K).toRingHom.toAlgebra

attribute [local instance] genAlg

/-- `κ(η)^sep` as a `K`-algebra. -/
def genAlgSep : Algebra K (SeparableClosure (genField A)) :=
  ((algebraMap (genField A) (SeparableClosure (genField A))).comp (algebraMap K (genField A))).toAlgebra

attribute [local instance] genAlgSep

theorem genTower : IsScalarTower K (genField A) (SeparableClosure (genField A)) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] genTower

/-- The bridge `Gal(κ(η)^sep/κ(η)) →* π₁(Spec A) = Gal(K_U/K)` at the generic point. -/
def genToPi1 : Gal (genPt A) →* Pi1 A K := toPi1 A K (SeparableClosure (genField A)) (genField A)

/-- The embedding `K_U → κ(η)^sep` underlying `genToPi1`. -/
def genEmb : maxUnram A K →+* SeparableClosure (genField A) :=
  (emb A K (SeparableClosure (genField A))).toRingHom

theorem genEmb_algebraMap (k : K) :
    genEmb A K (algebraMap K (maxUnram A K) k) =
      algebraMap (genField A) (SeparableClosure (genField A)) (fracIso A K k) :=
  (emb A K (SeparableClosure (genField A))).commutes k

theorem genEmb_genToPi1 (σ : Gal (genPt A)) (x : maxUnram A K) :
    genEmb A K (genToPi1 A K σ x) = σ (genEmb A K x) :=
  emb_toPi1 A K (SeparableClosure (genField A)) (genField A) σ x

theorem genToPi1_eq_one_iff (σ : Gal (genPt A)) :
    genToPi1 A K σ = 1 ↔ ∀ x : maxUnram A K, σ (genEmb A K x) = genEmb A K x :=
  toPi1_eq_one_iff A K (SeparableClosure (genField A)) (genField A) σ

theorem genToPi1_surjective : Function.Surjective (genToPi1 A K) :=
  toPi1_surjective A K (SeparableClosure (genField A)) (genField A) (fracIso A K).surjective

theorem genToPi1_continuous : Continuous (genToPi1 A K) :=
  toPi1_continuous A K (SeparableClosure (genField A)) (genField A)

end Generic

end GenBr

end RamanujanPetersson.EtSheaves



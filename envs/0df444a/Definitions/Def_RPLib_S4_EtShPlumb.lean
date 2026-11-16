-- Prove2me | Definitions.Def_RPLib_S4_EtShPlumb
-- name    : RPLib_S4_EtShPlumb
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:36:40.779526+00:00
-- url     : https://prove2.me/theorems/d502e6e2-3de7-447a-b2a3-222d1bc224cd
-- title:
--   From a lisse sheaf to a standard etale chart
-- statement:
--   Let $A$ be an integrally closed domain, $\eta$ the generic point of $\mathrm{Spec}\,A$ and $\Omega = \kappa(\eta)^{\mathrm{sep}}$, an $A$-algebra through $A \to \kappa(\eta)$; $\mathrm{Spec}$ of this map is the generic geometric point $\bar\eta$. For a lisse etale sheaf $F$ of $\Lambda$-modules on $\mathrm{Spec}\,A$ and a prime $P$ of $A$ there are a standard etale $A$-algebra $R'$ and a prime $\mathfrak u$ of $R'$ over $P$ such that every $\sigma \in \mathrm{Gal}(\Omega/\kappa(\eta))$ fixing the image of an $A$-algebra map $\psi : R' \to \Omega$ acts trivially on the generic stalk $F_{\bar\eta}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 3; M. Raynaud, Anneaux locaux henseliens, Lecture Notes in Math. 169, Springer (1970), Chapters V and VIII

import Mathlib
import Definitions.Def_RPLib_S4_EtShConstFix
import Definitions.Def_RPLib_S4_EtShGenBr

/-!
# S4-EtSheaves, O10c part 4: from `IsLisse` to a standard etale chart

`κ(η)^sep` is an `A`-algebra through `A → κ(η)` (`genAlgA`), and `Spec` of this map is the generic geometric point
`η̄` (`spec_algebraMap`). For a lisse `F` on `Spec A` and a prime `P` of `A` there are a standard etale `A`-algebra
`R'` and a prime `u` of `R'` over `P` such that every `σ ∈ Gal(κ(η)^sep/κ(η))` fixing the image of an `A`-algebra
map `ψ : R' → κ(η)^sep` acts trivially on the generic stalk `F_η̄` (`exists_chart`).
-/

set_option autoImplicit false
set_option warn.classDefReducibility false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.Plumb

open GenBr

variable (A : Type) [CommRing A] [IsDomain A]

/-- The map `A → κ(η)` to the residue field at the generic point. -/
def toGen : A →+* genField A :=
  (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom.comp
    (algebraMap A (genPt A).asIdeal.ResidueField)

/-- `κ(η)^sep` as an `A`-algebra through `κ(η)`. -/
def genAlgA : Algebra A (SeparableClosure (genField A)) :=
  ((algebraMap (genField A) (SeparableClosure (genField A))).comp (toGen A)).toAlgebra

attribute [local instance] genAlgA

theorem genAlgA_apply (a : A) :
    algebraMap A (SeparableClosure (genField A)) a =
      algebraMap (genField A) (SeparableClosure (genField A)) (toGen A a) := rfl

/-- `Spec (A → κ(η)^sep)` is the generic geometric point `η̄`. -/
theorem spec_algebraMap :
    Spec.map (CommRingCat.ofHom (algebraMap A (SeparableClosure (genField A)))) =
      (geomPtAt (genPt A)).pt := by
  change _ = Spec.map (CommRingCat.ofHom (algebraMap (genField A) (SeparableClosure (genField A)))) ≫
    (Spec (CommRingCat.of A)).fromSpecResidueField (genPt A)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- **HEADLINE (O10c, F4)**: a lisse `F` on `Spec A` has, over every prime `P`, a standard etale chart
`A → R'` with a prime `u` over `P`, such that any `σ` fixing an `A`-point `ψ : R' → κ(η)^sep` acts trivially on
`F_η̄`. -/
theorem exists_chart {Λ : Type} [CommRing Λ] (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F)
    (P : PrimeSpectrum A) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra A R') (_ : StandardEtalePresentation A R') (u : Ideal R'),
      u.IsPrime ∧ u.comap (algebraMap A R') = P.asIdeal ∧
      ∀ (ψ : R' →ₐ[A] SeparableClosure (genField A)) (σ : Gal (genPt A)), (∀ r, σ (ψ r) = ψ r) →
        galRep Λ F (genPt A) σ = LinearMap.id := by
  obtain ⟨U, v, hv, M, -, ⟨e⟩⟩ := hF P
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, -⟩ :=
    U.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have : Etale U.hom := U.prop
  let φ : CommRingCat.of A ⟶ Γ(U.left, V) := Spec.preimage (hV'.fromSpec ≫ U.hom)
  have hφ : hV'.fromSpec ≫ U.hom = Spec.map φ := (Spec.map_preimage _).symm
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), ← hφ]
    infer_instance
  let _ : Algebra A Γ(U.left, V) := φ.hom.toAlgebra
  have : Algebra.Etale A Γ(U.left, V) := hφe
  let w : PrimeSpectrum Γ(U.left, V) := hV'.primeIdealOf ⟨v, hvV⟩
  have hw : hV'.fromSpec w = v := hV'.fromSpec_primeIdealOf ⟨v, hvV⟩
  have : w.asIdeal.IsPrime := w.isPrime
  have : Algebra.IsEtaleAt A w.asIdeal :=
    Algebra.FormallyEtale.comp A Γ(U.left, V) (Localization.AtPrime w.asIdeal)
  obtain ⟨f, hfw, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) w.asIdeal
  have hdisj : Disjoint (Submonoid.powers f : Set Γ(U.left, V)) w.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfw
  have hPw : (Spec.map φ) w = P := by
    rw [← hφ]
    change U.hom (hV'.fromSpec w) = P
    rw [hw, hv]
  refine ⟨Localization.Away f, inferInstance, inferInstance, hstd.nonempty_standardEtalePresentation.some,
    w.asIdeal.map (algebraMap Γ(U.left, V) (Localization.Away f)),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ w.asIdeal w.isPrime hdisj, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq A Γ(U.left, V) (Localization.Away f), ← Ideal.comap_comap]
    have h1 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f)
      w.isPrime hdisj
    rw [Ideal.under] at h1
    rw [h1, ← hPw]
    rfl
  · intro ψ σ hσ
    have hl : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, V) (Localization.Away f))) ≫ hV'.fromSpec) ≫
          U.hom = (geomPtAt (genPt A)).pt := by
      rw [Category.assoc, Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_comp, ← spec_algebraMap A]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      change ψ (algebraMap Γ(U.left, V) (Localization.Away f) (algebraMap A Γ(U.left, V) a)) = _
      rw [← IsScalarTower.algebraMap_apply A Γ(U.left, V) (Localization.Away f)]
      exact ψ.commutes a
    refine galRep_eq_id_of_etale F (genPt A) U M e _ hl σ ?_
    rw [galSpec, ← Category.assoc, ← Spec.map_comp]
    refine congrArg (· ≫ _) (congrArg Spec.map ?_)
    exact CommRingCat.hom_ext (RingHom.ext fun r => hσ r)

end RamanujanPetersson.EtSheaves.Plumb



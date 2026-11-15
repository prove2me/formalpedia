-- Prove2me | Definitions.Def_RPLib_S3_SBGalB
-- name    : RPLib_S3_SBGalB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:35:14.830873+00:00
-- url     : https://prove2.me/theorems/990284dd-42a1-472e-95aa-e707226a22cf
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, E2b part B (generic half): Frobenius degree, lifting points, counting on `Fq[X]`
-- statement:
--   S3-ZetaSB, E2b part B (generic half): Frobenius degree, lifting points, counting on `Fq[X]`.
--
--   * `finrank_dvd_of_fixed` (B0): a finite field embedded in `L` with image fixed by `x ↦ x ^ (q ^ m)` has
--     degree dividing `m`;
--   * `exists_algHom_comp_eq`, `exists_lift` (B2): `Fq`-points of `R` lift to `S` (integral, free of finite rank)
--     when `m * (rank)! ∣ [L : Fq]`;
--   * `card_fixed_poly_ge` (B1): at least `q ^ m` points `Fq[X] → L` are fixed by `Frob^m`;
--   * group and constant-field facts used in the assembly.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBGalA

/-!
# S3-ZetaSB, E2b part B (generic half): Frobenius degree, lifting points, counting on `Fq[X]`

* `finrank_dvd_of_fixed` (B0): a finite field embedded in `L` with image fixed by `x ↦ x ^ (q ^ m)` has
  degree dividing `m`;
* `exists_algHom_comp_eq`, `exists_lift` (B2): `Fq`-points of `R` lift to `S` (integral, free of finite rank)
  when `m * (rank)! ∣ [L : Fq]`;
* `card_fixed_poly_ge` (B1): at least `q ^ m` points `Fq[X] → L` are fixed by `Frob^m`;
* group and constant-field facts used in the assembly.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.ZetaSB

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- (B0) A finite field embedded in `L` with image fixed by `x ↦ x ^ (q ^ m)` has degree dividing `m`. -/
theorem finrank_dvd_of_fixed {κ L : Type*} [Field κ] [Algebra Fq κ] [Finite κ] [Field L] [Algebra Fq L]
    (χ : κ →ₐ[Fq] L) (m : ℕ) (hχ : ∀ x, χ x ^ (Fintype.card Fq ^ m) = χ x) :
    finrank Fq κ ∣ m := by
  have h : ∀ x : κ, x ^ (Fintype.card Fq ^ m) = x := fun x => by
    have := hχ x
    rw [← map_pow] at this
    exact (χ : κ →+* L).injective this
  have h1 : FiniteField.frobeniusAlgHom Fq κ ^ m = 1 := by
    refine AlgHom.ext fun x => ?_
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply]
    exact h x
  rw [← FiniteField.orderOf_frobeniusAlgHom Fq κ]
  exact orderOf_dvd_of_pow_eq_one h1

/-- Abstract lifting: an embedding `κ → L` extends along `κ → κ'` when `[κ' : Fq] ∣ [L : Fq]`. -/
theorem exists_algHom_comp_eq {κ κ' L : Type*} [Field κ] [Field κ'] [Field L] [Algebra Fq κ] [Algebra Fq κ']
    [Algebra Fq L] [Finite L] [Module.Finite Fq κ'] (ι : κ →ₐ[Fq] κ') (z : κ →ₐ[Fq] L)
    (h : finrank Fq κ' ∣ finrank Fq L) : ∃ ψ : κ' →ₐ[Fq] L, ψ.comp ι = z := by
  letI : Algebra κ κ' := ι.toRingHom.toAlgebra
  letI : Algebra κ L := z.toRingHom.toAlgebra
  haveI : IsScalarTower Fq κ κ' := IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  haveI : IsScalarTower Fq κ L := IsScalarTower.of_algebraMap_eq fun c => (z.commutes c).symm
  haveI : Module.Finite Fq L := Module.Finite.of_finite
  haveI : Module.Finite Fq κ := Module.Finite.of_injective (ι.toLinearMap) (ι : κ →+* κ').injective
  have h1 := Module.finrank_mul_finrank Fq κ κ'
  have h2 := Module.finrank_mul_finrank Fq κ L
  have hpos : 0 < finrank Fq κ := Module.finrank_pos
  have hd : finrank κ κ' ∣ finrank κ L := by
    rw [← h1, ← h2] at h
    exact (Nat.mul_dvd_mul_iff_left hpos).mp h
  obtain ⟨ψ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
  exact ⟨ψ.restrictScalars Fq, AlgHom.ext fun x => ψ.commutes x⟩

/-- The images of an `R`-basis of `S` span a residue field of `S` over a residue field of `R`. -/
theorem span_basis_quot_eq_top {R S k k' : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] [Field k] [CommRing k'] (π : R →+* k) (π' : S →+* k') (hπ' : Function.Surjective π')
    (ι : k →+* k') (hcomm : ∀ r, ι (π r) = π' (algebraMap R S r)) :
    letI := ι.toAlgebra
    Submodule.span k (Set.range fun i => π' (Module.Free.chooseBasis R S i)) = ⊤ := by
  letI := ι.toAlgebra
  classical
  set b := Module.Free.chooseBasis R S
  rw [eq_top_iff]
  rintro x -
  obtain ⟨s, rfl⟩ := hπ' x
  rw [← b.sum_repr s, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, ← hcomm]
  have := Submodule.smul_mem (Submodule.span k (Set.range fun i => π' (b i))) (π (b.repr s i))
    (Submodule.subset_span ⟨i, rfl⟩)
  rw [Algebra.smul_def] at this
  exact this

/-- (B2) Points of `R` fixed by `Frob^m` lift to `S` when `m * (rank_R S)! ∣ [L : Fq]`. -/
theorem exists_lift {R S L : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S] [Algebra Fq R] [Algebra Fq S]
    [IsScalarTower Fq R S] [Algebra.IsIntegral R S] [Module.Free R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [Field L] [Algebra Fq L] [Finite L] (m : ℕ)
    (z : R →ₐ[Fq] L) (hz : ∀ r, z r ^ (Fintype.card Fq ^ m) = z r)
    (hL : m * (finrank R S).factorial ∣ finrank Fq L) :
    ∃ y : S →ₐ[Fq] L, y.comp (IsScalarTower.toAlgHom Fq R S) = z := by
  classical
  set p := RingHom.ker z with hp
  haveI : p.IsPrime := RingHom.ker_isPrime z
  let zb : R ⧸ p →ₐ[Fq] L := Ideal.kerLiftAlg z
  have zb_inj : Function.Injective zb := Ideal.kerLiftAlg_injective z
  haveI : Finite (R ⧸ p) := Finite.of_injective zb zb_inj
  haveI hpmax : p.IsMaximal := Ideal.Quotient.maximal_of_isField p (Finite.isField_of_domain _)
  have hle : RingHom.ker (algebraMap R S) ≤ p := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le
  obtain ⟨P, hPmax, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p hle
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  have hle' : p ≤ P.comap (IsScalarTower.toAlgHom Fq R S) := hPp.ge
  let ι : R ⧸ p →ₐ[Fq] S ⧸ P := Ideal.quotientMapₐ P (IsScalarTower.toAlgHom Fq R S) hle'
  have hdeg1 : finrank Fq (R ⧸ p) ∣ m := by
    refine finrank_dvd_of_fixed zb m fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hz a
  letI : Algebra (R ⧸ p) (S ⧸ P) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower Fq (R ⧸ p) (S ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  have hspan := span_basis_quot_eq_top (Ideal.Quotient.mk p) (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    ι.toRingHom (fun r => rfl)
  haveI : Module.Finite (R ⧸ p) (S ⧸ P) := by
    refine ⟨⟨Finset.univ.image fun i => Ideal.Quotient.mk P (Module.Free.chooseBasis R S i), ?_⟩⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspan
  haveI : Module.Finite Fq (R ⧸ p) := Module.Finite.of_finite
  haveI : Module.Finite Fq (S ⧸ P) := Module.Finite.trans (R ⧸ p) (S ⧸ P)
  have hrel : finrank (R ⧸ p) (S ⧸ P) ≤ finrank R S := by
    rw [Module.finrank_eq_card_chooseBasisIndex R S]
    exact finrank_le_of_span_eq_top hspan
  have hdvd2 : finrank (R ⧸ p) (S ⧸ P) ∣ (finrank R S).factorial :=
    Nat.dvd_factorial Module.finrank_pos hrel
  have htow : finrank Fq (S ⧸ P) = finrank Fq (R ⧸ p) * finrank (R ⧸ p) (S ⧸ P) :=
    (Module.finrank_mul_finrank Fq (R ⧸ p) (S ⧸ P)).symm
  have hdvd : finrank Fq (S ⧸ P) ∣ finrank Fq L := by
    rw [htow]; exact (Nat.mul_dvd_mul hdeg1 hdvd2).trans hL
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_eq ι zb hdvd
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ Fq P), AlgHom.ext fun r => ?_⟩
  have := congrArg (fun f : R ⧸ p →ₐ[Fq] L => f (Ideal.Quotient.mk p r)) hψ
  exact this

/-- (B1) At least `q ^ m` points `Fq[X] → L` are fixed by `φ = Frob^m` when `m ∣ [L : Fq]`. -/
theorem card_fixed_poly_ge (p : ℕ) [Fact p.Prime] [CharP Fq p] {L : Type*} [Field L] [Algebra Fq L] [Finite L]
    [Fintype (Fq[X] →ₐ[Fq] L)] [DecidableEq (Fq[X] →ₐ[Fq] L)] (m : ℕ) (hm : m ≠ 0)
    (hL : m ∣ finrank Fq L) (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m)) :
    Fintype.card Fq ^ m ≤ (Finset.univ.filter fun z : Fq[X] →ₐ[Fq] L => φ.comp z = z).card := by
  classical
  haveI : NeZero m := ⟨hm⟩
  let Lm := FiniteField.Extension Fq p m
  letI : Fintype Lm := Fintype.ofFinite Lm
  obtain ⟨χ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := Fq) (K := Lm) (L := L)
    (by rw [FiniteField.finrank_extension]; exact hL)
  have hcard : Fintype.card Lm = Fintype.card Fq ^ m := by
    rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  let f : Lm → (Fq[X] →ₐ[Fq] L) := fun c => Polynomial.aeval (χ c)
  calc Fintype.card Fq ^ m = (Finset.univ : Finset Lm).card := by rw [Finset.card_univ, hcard]
    _ ≤ _ := by
      refine Finset.card_le_card_of_injOn f (fun c _ => ?_) (fun c _ c' _ h => ?_)
      · rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, Polynomial.algHom_ext ?_⟩
        rw [AlgHom.comp_apply, Polynomial.aeval_X, hφ, ← map_pow, ← hcard, FiniteField.pow_card]
      · have := congrArg (fun z : Fq[X] →ₐ[Fq] L => z X) h
        simp only [f, Polynomial.aeval_X] at this
        exact (χ : Lm →+* L).injective this

/-- In a finite group, `|H| ≤ |A| · |H ∩ ker ρ|`. -/
theorem card_le_mul_card_inf_ker {G A : Type*} [Group G] [Group A] [Finite G] [Finite A] (ρ : G →* A)
    (H : Subgroup G) : Nat.card H ≤ Nat.card A * Nat.card (H ⊓ ρ.ker : Subgroup G) := by
  let ρ' := ρ.comp H.subtype
  have h1 : Nat.card ρ'.ker * Nat.card ρ'.range = Nat.card H := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have h2 : Nat.card ρ'.range ≤ Nat.card A := Subgroup.card_le_card_group _
  have h3 : Nat.card ρ'.ker = Nat.card (H ⊓ ρ.ker : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.1.2, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩,
          MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [← h1, h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

/-- Polynomials integral over the constants are constant. -/
theorem eq_C_of_isIntegral {p : Fq[X]} (h : IsIntegral Fq p) : p = C (p.coeff 0) := by
  obtain ⟨f, hf, hfp⟩ := h
  have hcomp : f.comp p = 0 := by rw [Polynomial.comp, ← Polynomial.algebraMap_eq]; exact hfp
  have hdeg : f.natDegree * p.natDegree = 0 := by rw [← Polynomial.natDegree_comp, hcomp, natDegree_zero]
  have hf0 : f.natDegree ≠ 0 := by
    intro h0
    have h1 : f = 1 := (Polynomial.Monic.natDegree_eq_zero hf).mp h0
    rw [h1, Polynomial.one_comp] at hcomp
    exact one_ne_zero hcomp
  have h2 : p.natDegree = 0 := by
    rcases Nat.mul_eq_zero.mp hdeg with h | h
    · exact absurd h hf0
    · exact h
  exact Polynomial.eq_C_of_natDegree_eq_zero h2

/-- Rational functions integral over the constants are constants. -/
theorem ratFunc_eq_of_isIntegral {r : RatFunc Fq} (h : IsIntegral Fq r) :
    ∃ a : Fq, algebraMap Fq (RatFunc Fq) a = r := by
  have h2 : IsIntegral Fq[X] r := h.tower_top
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have h3 : IsIntegral Fq p := by
    rw [← hp] at h
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom Fq Fq[X] (RatFunc Fq))
      (IsFractionRing.injective Fq[X] (RatFunc Fq))).mp h
  refine ⟨p.coeff 0, ?_⟩
  rw [← hp, IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq), Polynomial.algebraMap_eq,
    ← eq_C_of_isIntegral h3]

/-- `Hom_Fq(S, L)` is finite for a Dedekind `S` with finite residue fields and an element of infinite order. -/
theorem finite_algHom_of_pow {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S]
    [Places.FiniteQuot S] [Infinite S] {t : S} (ht : ∀ N : ℕ, 2 ≤ N → t ^ N ≠ t)
    (L : Type*) [Field L] [Algebra Fq L] [Finite L] : Finite (S →ₐ[Fq] L) := by
  classical
  have : Module.Finite Fq L := Module.Finite.of_finite
  set T := (Places.finite_deg_dvd_of Fq ht (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset
  have hmem : ∀ φ : S →ₐ[Fq] L, Places.kerPlace Fq L φ ∈ T := fun φ => by
    rw [Set.Finite.mem_toFinset]
    have := (Places.kerPlace Fq L φ).isMaximal
    letI : Field (S ⧸ (Places.kerPlace Fq L φ).asIdeal) := Ideal.Quotient.field _
    exact Places.finrank_dvd_of_algHom_field Fq (Places.fiberEquiv Fq L _ ⟨φ, rfl⟩)
  have hfib : ∀ P, {φ : S →ₐ[Fq] L | Places.kerPlace Fq L φ = P}.Finite := fun P => by
    have : Finite (S ⧸ P.asIdeal →ₐ[Fq] L) := Places.finite_algHom Fq
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (Places.fiberEquiv Fq L P).symm)
  exact Set.finite_univ_iff.mp ((T.finite_toSet.biUnion fun P _ => hfib P).subset fun φ _ =>
    Set.mem_biUnion (hmem φ) rfl)

/-- The kernel of a `Frob^m`-fixed point has degree dividing `m`. -/
theorem deg_kerPlace_dvd {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S]
    [Places.FiniteQuot S] [Infinite S] (L : Type*) [Field L] [Algebra Fq L] [Finite L] (m : ℕ)
    (w : S →ₐ[Fq] L) (hw : ∀ a, w a ^ (Fintype.card Fq ^ m) = w a) :
    Places.deg Fq (Places.kerPlace Fq L w) ∣ m := by
  have := (Places.kerPlace Fq L w).isMaximal
  letI : Field (S ⧸ (Places.kerPlace Fq L w).asIdeal) := Ideal.Quotient.field _
  refine finrank_dvd_of_fixed (Places.fiberEquiv Fq L _ ⟨w, rfl⟩) m fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hw a

end Generic

end RamanujanPetersson.ZetaSB



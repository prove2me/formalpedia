-- Prove2me | Definitions.Def_AlgebraicCurve_ConstantReduction
-- name    : AlgebraicCurve_ConstantReduction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/34d13f65-9128-5fd7-8799-f7d0ae4356a4
-- title:
--   Constant reduction of a function field along a valuation ring
-- statement:
--   Fix a field $L$ with a valuation subring $A \subseteq L$ and residue field $k = A/\mathfrak m_A$, an extension $F/L$ and an extension $\bar F/k$. The structure `ConstantReduction A F Fbar` packages the data of a reduction of $F/L$ to $\bar F/k$ over $A$: a valuation subring $\mathcal O \subseteq F$ (`integers`), a ring homomorphism $\mathcal O \to \bar F$ (`residue`), and a map $P \mapsto \bar P$ from places of $F/L$ to places of $\bar F/k$ (`placeMap`), where a place is, as in the project's divisor-theoretic set-up, a valuation subring of the big field containing the constants, different from the whole field and a principal ideal ring, hence a discrete valuation ring, with $\deg$ the residue degree over the constants and $\mathrm{ord}$ the associated normalised order. The axioms carried as fields are: $\mathcal O$ contracts to $A$ on constants, i.e. $\lambda \in A \iff \lambda \in \mathcal O$ for $\lambda \in L$; `residue` is surjective with kernel the maximal ideal of $\mathcal O$, so $\bar F$ is the residue field of $\mathcal O$; `residue` restricted to $A$ is the composite $A \to k \to \bar F$; every $f \in F^{\times}$ has a constant multiple $c f$ ($c \in L$) lying in $\mathcal O$ with nonzero residue; $\deg \bar P = \deg P$ for every place $P$; and if $f \in \mathcal O$ has nonzero residue and $D$ is a (finitely supported) divisor with $D(P) = \mathrm{ord}_P(f)$ for all $P$, then the pushforward of $D$ along `placeMap` has $Q$-coefficient $\mathrm{ord}_Q(\mathrm{residue}\,f)$ for every $Q$.
--
--   `IsGood R` is the assertion that the repartition genus `genusFF` of $\bar F/k$ equals that of $F/L$, the argument $R$ only fixing the ambient data; `isGood_iff` records this unfolding. The remaining declarations develop the pushforward of divisors: constants have order $0$ at every place (`ord_algebraMap`, `ord_smul`); pushforward along `placeMap` preserves degree and hence the degree-zero subgroup, and carries principal divisors to principal divisors (using the existence of unit constant multiples); accordingly `divMap`, `degZeroMap` and `pic0Map` are the induced additive maps on divisors, degree-zero divisors and the degree-zero class group $\mathrm{Pic}^0(F/L) \to \mathrm{Pic}^0(\bar F/k)$, with `pic0Map_mk` describing `pic0Map` on classes of representatives.
--
--   **Relation to Mathlib.** Mathlib has no notion of constant reduction of a function field; this structure is the project's own, built on the project's `Place`, `Divisor`, `Pic0` and repartition genus `genusFF`, and using Mathlib's `ValuationSubring`, `IsLocalRing.ResidueField`, `Finsupp.mapDomain` and `QuotientAddGroup.map`.
--
--   **Where it is used.** The reduction map `pic0Map` on degree-zero divisor classes, together with the good-reduction predicate `IsGood`, provides the purely function-field framework in which torsion in the degree-zero class group of a curve in characteristic zero is compared with its reduction; this is the form in which good reduction of modular curves is stated and used later in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_ConstantReduction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure ConstantReduction where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  placeMap : Place L F → Place (ResidueField A) Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

  deg_placeMap : ∀ P, (placeMap P).deg = P.deg

  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

namespace ConstantReduction

variable {A F Fbar}

set_option linter.unusedVariables false in

def IsGood (R : ConstantReduction A F Fbar) : Prop :=
  genusFF (ResidueField A) Fbar = genusFF L F

theorem isGood_iff (R : ConstantReduction A F Fbar) :
    R.IsGood ↔ genusFF (ResidueField A) Fbar = genusFF L F :=
  Iff.rfl

variable (R : ConstantReduction A F Fbar)

theorem ord_algebraMap (P : Place L F) {c : L} (hc : c ≠ 0) : P.ord (algebraMap L F c) = 0 := by
  have hu : IsUnit (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) :=
    ⟨⟨⟨algebraMap L F c, P.algebraMap_mem' c⟩, ⟨algebraMap L F c⁻¹, P.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

theorem ord_smul (P : Place L F) {c : L} (hc : c ≠ 0) (f : F) : P.ord (c • f) = P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap P hc, zero_add]

theorem mapDomain_mem_principal {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.principal (K := ResidueField A) (F := Fbar) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  exact ⟨R.residue ⟨c • f, hc⟩, hres, fun Q =>
    R.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P => by rw [hDf P]; exact (ord_smul P hc0 f).symm) Q⟩

theorem degree_mapDomain (D : Divisor L F) :
    Divisor.degree (Finsupp.mapDomain R.placeMap D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, R.deg_placeMap]

theorem mapDomain_mem_degZero {D : Divisor L F}
    (hD : D ∈ Divisor.degZero (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.degZero (K := ResidueField A) (F := Fbar) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [R.degree_mapDomain, hD]

def divMap : Divisor L F →+ Divisor (ResidueField A) Fbar :=
  Finsupp.mapDomain.addMonoidHom R.placeMap

@[simp]
theorem divMap_apply (D : Divisor L F) : R.divMap D = Finsupp.mapDomain R.placeMap D := rfl

def degZeroMap :
    Divisor.degZero (K := L) (F := F) →+ Divisor.degZero (K := ResidueField A) (F := Fbar) :=
  (R.divMap.domRestrict (Divisor.degZero (K := L) (F := F))).codRestrict _ fun D => R.mapDomain_mem_degZero D.2

@[simp]
theorem coe_degZeroMap (D : Divisor.degZero (K := L) (F := F)) :
    (R.degZeroMap D : Divisor (ResidueField A) Fbar) = Finsupp.mapDomain R.placeMap (D : Divisor L F) :=
  rfl

def pic0Map : Pic0 L F →+ Pic0 (ResidueField A) Fbar :=
  QuotientAddGroup.map _ _ R.degZeroMap (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact R.mapDomain_mem_principal hD)

theorem pic0Map_mk (D : Divisor.degZero (K := L) (F := F)) :
    R.pic0Map (Pic0.mk D) = Pic0.mk (R.degZeroMap D) :=
  rfl

end ConstantReduction

end AlgebraicCurve

end



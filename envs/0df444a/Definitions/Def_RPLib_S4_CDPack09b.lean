-- Prove2me | Definitions.Def_RPLib_S4_CDPack09b
-- name    : RPLib_S4_CDPack09b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:14:04.333009+00:00
-- url     : https://prove2.me/theorems/7a9fef28-294d-4a63-8e16-65c6e8f8c643
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 9b of 71
-- statement:
--   Part 9b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResOrb`: S4-PD (4), E4B part 3(iii): boundary primes over one place of a level are geometrically conjugate
--   * `Def_RP_Cone_LevProd`: S4-PD (4), E4B part 1: the product formula at a finite level
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack09
import Definitions.Def_RPLib_S3_PlacesB
import Definitions.Def_RPLib_S3_SBTransport

/-!
# Curve-duality library package, part 9b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResOrb`: S4-PD (4), E4B part 3(iii): boundary primes over one place of a level are geometrically conjugate
* `Def_RP_Cone_LevProd`: S4-PD (4), E4B part 1: the product formula at a finite level
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResOrb =====
section

/-!
# S4-PD (4), E4B part 3(iii): boundary primes over one place of a level are geometrically conjugate

Any chart `(A, K, R0)` and a finite level `L ≤ K_U`.
* `smul_inclU_of_fix`, `comap_smul_of_fix`: `Gal(K_U/L)` fixes `B_L`, so conjugate primes have the same trace on `B_L`.
* `exists_fix_smul`: `Gal(K_U/L)` is transitive on the primes of the pro-chart over one prime of `B_L` (profinite).
* `exists_fix_stab`: the stabilizer of `Q` in `Gal(K_U/L)` surjects onto the ring automorphisms of `B ⧸ Q` fixing `B_L`.
* `exists_geo_fix_smul`: if `L ⊇ K(𝔽_{p^k})` and `y ^ (p^k) ≡ y` on `B_L` modulo `Q` (the residue field of `L` at `Q`
  is `𝔽_{p^k}`), two boundary-type primes over the same prime of `B_L` are conjugate under `π₁^geo ∩ Gal(K_U/L)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a

noncomputable section

section AbsStab

variable {G B A' : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CommRing A'] [Algebra A' B] [SMulCommClass H A' B] [Algebra.IsInvariant A' B H]
  [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

/-- A ring automorphism of `B ⧸ P` fixing `A'` comes from the stabilizer of `P` in `H` (profinite). -/
theorem exists_stab_mem (P : Ideal B) [P.IsPrime] (eR : (B ⧸ P) ≃+* (B ⧸ P))
    (heR : ∀ a : A', eR (Ideal.Quotient.mk P (algebraMap A' B a)) = Ideal.Quotient.mk P (algebraMap A' B a)) :
    ∃ h : H, (h : G) • P = P ∧ ∀ b : B, Ideal.Quotient.mk P ((h : G) • b) = eR (Ideal.Quotient.mk P b) := by
  let σ : (B ⧸ P) ≃ₐ[A' ⧸ P.under A'] (B ⧸ P) := AlgEquiv.ofRingEquiv (f := eR) (fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact heR a)
  obtain ⟨⟨h2, hh2⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H) (P.under A') P σ
  refine ⟨h2, hh2, fun b => ?_⟩
  have h3 : Ideal.Quotient.mk P (h2 • b) = σ (Ideal.Quotient.mk P b) := by
    rw [← hσ]
    rfl
  exact h3

end AbsStab

section AbsStabFix

variable {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

/-- `exists_stab_mem` with `A' = B^H`. -/
theorem exists_stab_mem_fix {R0 : Type*} [CommRing R0] [Algebra R0 B] [SMulCommClass G R0 B]
    (P : Ideal B) [P.IsPrime] (eR : (B ⧸ P) ≃+* (B ⧸ P))
    (heR : ∀ b : B, (∀ h ∈ H, h • b = b) → eR (Ideal.Quotient.mk P b) = Ideal.Quotient.mk P b) :
    ∃ h ∈ H, h • P = P ∧ ∀ b : B, Ideal.Quotient.mk P (h • b) = eR (Ideal.Quotient.mk P b) := by
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra R0 B H) B H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨h, hh, hh'⟩ := exists_stab_mem (A' := FixedPoints.subalgebra R0 B H) H P eR
    (fun a => heR (a : B) fun σ hσ => (a.2 : ∀ g : H, g • (a : B) = a) ⟨σ, hσ⟩)
  exact ⟨h, h.2, hh, hh'⟩

end AbsStabFix

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- `Gal(K_U/L)` fixes the image of `B_L`. -/
theorem smul_inclU_of_fix {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) {σ : Pi1 A K}
    (hσ : σ ∈ (IntermediateField.restrict hLU).fixingSubgroup) (y : integralClosure R0 L) :
    σ • inclU R0 hLU y = inclU R0 hLU y :=
  Subtype.ext ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
    ((IntermediateField.mem_restrict hLU _).2 (y : L).2))

/-- `Gal(K_U/L)`-conjugate primes have the same trace on `B_L`. -/
theorem comap_smul_of_fix {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) {σ : Pi1 A K}
    (hσ : σ ∈ (IntermediateField.restrict hLU).fixingSubgroup) (Q : Ideal (proChart A K R0)) :
    (σ • Q).comap (inclU R0 hLU) = Q.comap (inclU R0 hLU) := by
  ext y
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    smul_inclU_of_fix hLU (inv_mem hσ) y]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- **Transitivity over a level** (profinite): primes of the pro-chart with the same trace on `B_L` are
`Gal(K_U/L)`-conjugate. -/
theorem exists_fix_smul {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] (Q Q' : Ideal (proChart A K R0)) [Q.IsPrime] [Q'.IsPrime]
    (h : Q.comap (inclU R0 hLU) = Q'.comap (inclU R0 hLU)) :
    ∃ σ ∈ (IntermediateField.restrict hLU).fixingSubgroup, Q' = σ • Q := by
  haveI : FiniteDimensional K (IntermediateField.restrict hLU) :=
    (IntermediateField.restrictAlgEquiv hLU).toLinearEquiv.finiteDimensional
  letI : TopologicalSpace (proChart A K R0) := ⊥
  haveI : DiscreteTopology (proChart A K R0) := ⟨rfl⟩
  haveI : ContinuousSMul (Pi1 A K) (proChart A K R0) := by
    refine (continuousSMul_iff_stabilizer_isOpen).2 fun x => ?_
    refine Subgroup.isOpen_mono (H₁ := fixElt A K (x : maxUnram A K)) (fun σ hσ => ?_) (fixElt_isOpen A K _)
    exact Subtype.ext hσ
  haveI : CompactSpace (IntermediateField.restrict hLU).fixingSubgroup :=
    isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed _).isCompact
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra R0 (proChart A K R0) (IntermediateField.restrict hLU).fixingSubgroup)
      (proChart A K R0) (IntermediateField.restrict hLU).fixingSubgroup := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have hu : Q.under (FixedPoints.subalgebra R0 (proChart A K R0) (IntermediateField.restrict hLU).fixingSubgroup) =
      Q'.under (FixedPoints.subalgebra R0 (proChart A K R0) (IntermediateField.restrict hLU).fixingSubgroup) := by
    ext b
    obtain ⟨y, hy⟩ := exists_inclU_eq hLU (b : proChart A K R0) fun σ hσ =>
      congrArg Subtype.val ((b.2 : ∀ g : (IntermediateField.restrict hLU).fixingSubgroup,
        g • (b : proChart A K R0) = b) ⟨σ, hσ⟩)
    have h1 : y ∈ Q.comap (inclU R0 hLU) ↔ y ∈ Q'.comap (inclU R0 hLU) := by rw [h]
    rw [Ideal.mem_comap, Ideal.mem_comap, hy] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (G := (IntermediateField.restrict hLU).fixingSubgroup) Q Q' hu
  exact ⟨σ, σ.2, hσ⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- **Decomposition over a level**: a ring automorphism of `B ⧸ Q` fixing the image of `B_L` comes from the
stabilizer of `Q` in `Gal(K_U/L)`. -/
theorem exists_fix_stab {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] (Q : Ideal (proChart A K R0)) [Q.IsPrime]
    (eR : (proChart A K R0 ⧸ Q) ≃+* (proChart A K R0 ⧸ Q))
    (heR : ∀ y : integralClosure R0 L,
      eR (Ideal.Quotient.mk Q (inclU R0 hLU y)) = Ideal.Quotient.mk Q (inclU R0 hLU y)) :
    ∃ δ ∈ (IntermediateField.restrict hLU).fixingSubgroup, δ • Q = Q ∧
      ∀ b, Ideal.Quotient.mk Q (δ • b) = eR (Ideal.Quotient.mk Q b) := by
  haveI : FiniteDimensional K (IntermediateField.restrict hLU) :=
    (IntermediateField.restrictAlgEquiv hLU).toLinearEquiv.finiteDimensional
  letI : TopologicalSpace (proChart A K R0) := ⊥
  haveI : DiscreteTopology (proChart A K R0) := ⟨rfl⟩
  haveI : ContinuousSMul (Pi1 A K) (proChart A K R0) := by
    refine (continuousSMul_iff_stabilizer_isOpen).2 fun x => ?_
    refine Subgroup.isOpen_mono (H₁ := fixElt A K (x : maxUnram A K)) (fun σ hσ => ?_) (fixElt_isOpen A K _)
    exact Subtype.ext hσ
  haveI : CompactSpace (IntermediateField.restrict hLU).fixingSubgroup :=
    isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed _).isCompact
  refine exists_stab_mem_fix (R0 := R0) (IntermediateField.restrict hLU).fixingSubgroup Q eR fun b hb => ?_
  obtain ⟨y, rfl⟩ := exists_inclU_eq hLU b fun σ hσ => congrArg Subtype.val (hb σ hσ)
  exact heR y

variable {p e : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Geometric transitivity over a level**: if `L ⊇ K(𝔽_{p^k})` and `y ^ (p^k) ≡ y` on `B_L` modulo `Q`, two
boundary-type primes with the same trace on `B_L` are conjugate under `π₁^geo ∩ Gal(K_U/L)`. -/
theorem exists_geo_fix_smul [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K] (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [FiniteDimensional K L]
    {k : ℕ} (hk : 0 < k) (hC : constLevel K p k ≤ L)
    {Q Q' : Ideal (proChart A K R0)} [Q.IsPrime] [Q'.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
    (hres : ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ Q.comap (inclU R0 hLU))
    (h : Q.comap (inclU R0 hLU) = Q'.comap (inclU R0 hLU)) :
    ∃ γ ∈ pi1geo A K (p ^ e), γ ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q' = γ • Q := by
  obtain ⟨σ, hσL, hσ⟩ := exists_fix_smul hLU Q Q' h
  let e0 := resEquiv A K R0 p e he hζ Q hcard
  let eR : (proChart A K R0 ⧸ Q) ≃+* (proChart A K R0 ⧸ Q) := e0.symm.trans ((constSmul R0 p e σ).trans e0)
  have heR : ∀ c ∈ constSub A K R0 p e,
      eR (Ideal.Quotient.mk Q c) = Ideal.Quotient.mk Q (σ • c) := by
    intro c hc
    show e0 (constSmul R0 p e σ (e0.symm (e0 ⟨c, hc⟩))) = _
    rw [e0.symm_apply_apply]
    rfl
  have hfixc : ∀ c ∈ constSub A K R0 p e, c ^ (p ^ k) = c → σ • c = c := by
    intro c hc hck
    have h1 : ((c : maxUnram A K) : AlgebraicClosure K) ^ (p ^ k) = ((c : maxUnram A K) : AlgebraicClosure K) := by
      exact_mod_cast hck
    exact Subtype.ext ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσL _
      ((IntermediateField.mem_restrict hLU _).2 (hC (mem_constLevel hk h1))))
  have hcomm : ∀ y : integralClosure R0 L,
      eR (Ideal.Quotient.mk Q (inclU R0 hLU y)) = Ideal.Quotient.mk Q (inclU R0 hLU y) := by
    intro y
    obtain ⟨c, hc, hyc⟩ := exists_const_sub_mem he hζ hcard (inclU R0 hLU y)
    have hq : Ideal.Quotient.mk Q (inclU R0 hLU y) = Ideal.Quotient.mk Q c := Ideal.Quotient.eq.2 hyc
    have hck : c ^ (p ^ k) = c := by
      refine const_eq_of_sub_mem (Q := Q) he (Ideal.IsPrime.ne_top ‹_›) (pow_mem hc _) hc (Ideal.Quotient.eq.1 ?_)
      have h1 : Ideal.Quotient.mk Q (inclU R0 hLU y ^ (p ^ k)) = Ideal.Quotient.mk Q (inclU R0 hLU y) := by
        refine Ideal.Quotient.eq.2 ?_
        have h2 := hres y
        rw [Ideal.mem_comap, map_sub, map_pow] at h2
        exact h2
      rw [map_pow, hq] at h1
      rw [map_pow]
      exact h1
    rw [hq, heR c hc, hfixc c hc hck]
  obtain ⟨δ, hδL, hδQ, hδ⟩ := exists_fix_stab hLU Q eR hcomm
  have hδc : ∀ c ∈ constSub A K R0 p e, δ • c = σ • c := by
    intro c hc
    have h1 : Ideal.Quotient.mk Q (δ • c) = Ideal.Quotient.mk Q (σ • c) := by
      rw [hδ]
      exact heR c hc
    exact const_eq_of_sub_mem (Q := Q) he (Ideal.IsPrime.ne_top ‹_›) ((mem_constSub.1 hc).map δ)
      ((mem_constSub.1 hc).map σ) (Ideal.Quotient.eq.1 h1)
  refine ⟨σ * δ⁻¹, ?_, mul_mem hσL (inv_mem hδL), ?_⟩
  · rw [mem_pi1geo]
    intro y hy
    have h2 := hδc (mkConst he (σ⁻¹ • y) (hy.map σ⁻¹)) (mkConst_mem he _ _)
    have hv : δ • (σ⁻¹ • y) = y := (congrArg Subtype.val h2).trans (smul_inv_smul σ y)
    show (σ * δ⁻¹) • y = y
    rw [mul_smul, inv_smul_eq_iff.2 hv.symm, smul_inv_smul]
  · exact hσ.trans (mul_inv_smul_of_smul_eq hδQ).symm

end Chart

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_LevProd =====
section

/-!
# S4-PD (4), E4B part 1: the product formula at a finite level

For a function field `F / Fq` (S3 setting) and a finite separable level `M / F` inside `F̄`, the places of `M` are
the primes of `B_M = integralClosure (Rfin Fq F) M` (finite) and `B∞_M = integralClosure (Rinf Fq F) M` (over `∞`).
* `valuation_equiv'`, `card_equiv'`: valuations and residue cardinalities are transported along a ring isomorphism of
  Dedekind domains with the same fraction field.
* `finEquivM`, `infEquivM`: `Rfin Fq M ≃+* B_M` and `Rinf Fq M ≃+* B∞_M` (same carrier in `M`).
* `dvd_sum_bdry` (residue sum at a level): if `N ∣ v_y(f)` at every finite place, every finite residue field has
  cardinality `(q^m)^k` and every boundary residue field has cardinality `q^m`, then `N ∣ Σ_w v_w(f)` over the
  boundary places. From the S3 product formula `degS_fin_add_degS_inf` for `M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Residue

noncomputable section

section Transport

variable {S S' : Type*} [CommRing S] [IsDedekindDomain S] [CommRing S'] [IsDedekindDomain S']

theorem equiv_asIdeal' (e : S ≃+* S') (P : HeightOneSpectrum S) :
    (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal = P.asIdeal.map e := by
  rw [← Ideal.comap_symm]; rfl

theorem mem_equiv_pow_iff' (e : S ≃+* S') (P : HeightOneSpectrum S) (r : S) (n : ℕ) :
    e r ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ^ n ↔ r ∈ P.asIdeal ^ n := by
  rw [equiv_asIdeal', ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap]
  simp

theorem intValuation_equiv' (e : S ≃+* S') (P : HeightOneSpectrum S) (r : S) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e r) = P.intValuation r := by
  refine ZetaSB.eq_of_forall_le_exp_neg_iff (HeightOneSpectrum.intValuation_le_one _ _)
    (HeightOneSpectrum.intValuation_le_one _ _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
    mem_equiv_pow_iff']

theorem card_equiv' (e : S ≃+* S') (P : HeightOneSpectrum S) :
    Nat.card (S' ⧸ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal) = Nat.card (S ⧸ P.asIdeal) :=
  (Nat.card_congr (Ideal.quotientEquiv P.asIdeal _ e (equiv_asIdeal' e P)).toEquiv).symm

variable {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K] [Algebra S' K] [IsFractionRing S' K]

/-- Valuations are transported along a ring isomorphism compatible with the maps to `K`. -/
theorem valuation_equiv' (e : S ≃+* S') (he : ∀ r : S, algebraMap S' K (e r) = algebraMap S K r)
    (P : HeightOneSpectrum S) (f : K) :
    (HeightOneSpectrum.equivOfRingEquiv e P).valuation K f = P.valuation K f := by
  have h1 : ∀ r : S, (HeightOneSpectrum.equivOfRingEquiv e P).valuation K (algebraMap S K r) =
      P.valuation K (algebraMap S K r) := fun r => by
    conv_lhs => rw [← he r]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      intValuation_equiv']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) f
  rw [map_div₀, map_div₀, h1, h1]

end Transport

section Level

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (M : IntermediateField F (AlgebraicClosure F))

instance isScalarTower_polyM : IsScalarTower Fq[X] (RatFunc Fq) M :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext <| by
    show algebraMap Fq[X] (AlgebraicClosure F) c =
      algebraMap (RatFunc Fq) (AlgebraicClosure F) (algebraMap Fq[X] (RatFunc Fq) c)
    rw [IsScalarTower.algebraMap_apply Fq[X] F (AlgebraicClosure F),
      IsScalarTower.algebraMap_apply (RatFunc Fq) F (AlgebraicClosure F),
      ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F]

instance isScalarTower_FqM : IsScalarTower Fq Fq[X] M :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext <| by
    show algebraMap Fq (AlgebraicClosure F) c =
      algebraMap Fq[X] (AlgebraicClosure F) (algebraMap Fq Fq[X] c)
    rw [IsScalarTower.algebraMap_apply Fq F (AlgebraicClosure F),
      IsScalarTower.algebraMap_apply Fq[X] F (AlgebraicClosure F),
      ← IsScalarTower.algebraMap_apply Fq Fq[X] F]

instance towerFinM : IsScalarTower Fq[X] (Places.Rfin Fq F) M :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply Fq[X] F M, IsScalarTower.algebraMap_apply (Places.Rfin Fq F) F M]
    rfl

instance towerInfM : IsScalarTower (Places.Oinf Fq) (Places.Rinf Fq F) M :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply (Places.Oinf Fq) F M,
      IsScalarTower.algebraMap_apply (Places.Rinf Fq F) F M]
    rfl

theorem mem_fin_iff (x : M) :
    x ∈ integralClosure Fq[X] M ↔ x ∈ integralClosure (Places.Rfin Fq F) M := by
  have : Algebra.IsIntegral Fq[X] (Places.Rfin Fq F) := ⟨fun x => integralClosure.isIntegral x⟩
  rw [mem_integralClosure_iff, mem_integralClosure_iff]
  exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩

theorem mem_inf_iff (x : M) :
    x ∈ integralClosure (Places.Oinf Fq) M ↔ x ∈ integralClosure (Places.Rinf Fq F) M := by
  have : Algebra.IsIntegral (Places.Oinf Fq) (Places.Rinf Fq F) := ⟨fun x => integralClosure.isIntegral x⟩
  rw [mem_integralClosure_iff, mem_integralClosure_iff]
  exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩

/-- `Rfin Fq M ≃+* integralClosure (Rfin Fq F) M` (same carrier). -/
def finEquivM : Places.Rfin Fq M ≃+* integralClosure (Places.Rfin Fq F) M where
  toFun x := ⟨x.1, (mem_fin_iff Fq M x.1).1 x.2⟩
  invFun y := ⟨y.1, (mem_fin_iff Fq M y.1).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `Rinf Fq M ≃+* integralClosure (Rinf Fq F) M` (same carrier). -/
def infEquivM : Places.Rinf Fq M ≃+* integralClosure (Places.Rinf Fq F) M where
  toFun x := ⟨x.1, (mem_inf_iff Fq M x.1).1 x.2⟩
  invFun y := ⟨y.1, (mem_inf_iff Fq M y.1).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable [FiniteDimensional F M] [Algebra.IsSeparable F M]

instance functionField_M : FunctionField Fq M := Module.Finite.trans F M

instance isSeparable_M : Algebra.IsSeparable (RatFunc Fq) M := Algebra.IsSeparable.trans (RatFunc Fq) F M

variable [IsDedekindDomain (integralClosure (Places.Rfin Fq F) M)]
  [IsFractionRing (integralClosure (Places.Rfin Fq F) M) M]
  [IsDedekindDomain (integralClosure (Places.Rinf Fq F) M)]
  [IsFractionRing (integralClosure (Places.Rinf Fq F) M) M]

set_option maxHeartbeats 800000 in
/-- **Residue sum at a level**: `N ∣ Σ_w v_w(f)` over the boundary places of `M` when `N` divides `f`'s orders at all
finite places, every finite residue field has `(q^m)^k` elements and every boundary residue field `q^m`. -/
theorem dvd_sum_bdry {N m : ℕ} (hm : 0 < m) {f : M} (hf : f ≠ 0)
    (hfin : ∀ y : HeightOneSpectrum (integralClosure (Places.Rfin Fq F) M),
      (N : ℤ) ∣ WithZero.log (y.valuation M f))
    (hdf : ∀ y : HeightOneSpectrum (integralClosure (Places.Rfin Fq F) M),
      ∃ k : ℕ, Nat.card (integralClosure (Places.Rfin Fq F) M ⧸ y.asIdeal) = Fintype.card Fq ^ (m * k))
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      Nat.card (integralClosure (Places.Rinf Fq F) M ⧸ w.asIdeal) = Fintype.card Fq ^ m) :
    (N : ℤ) ∣ ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      WithZero.log (w.valuation M f) := by
  have hq : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hpf := Places.degS_fin_add_degS_inf Fq M hf
  have hv1 : ∀ P : HeightOneSpectrum (Places.Rfin Fq M),
      (HeightOneSpectrum.equivOfRingEquiv (finEquivM Fq M) P).valuation M f = P.valuation M f :=
    fun P => valuation_equiv' _ (fun _ => rfl) P f
  have hv2 : ∀ P : HeightOneSpectrum (Places.Rinf Fq M),
      (HeightOneSpectrum.equivOfRingEquiv (infEquivM Fq M) P).valuation M f = P.valuation M f :=
    fun P => valuation_equiv' _ (fun _ => rfl) P f
  have hd1 : ∀ P : HeightOneSpectrum (Places.Rfin Fq M), ∃ k : ℕ, Places.deg Fq P = m * k := fun P => by
    obtain ⟨k, hk⟩ := hdf (HeightOneSpectrum.equivOfRingEquiv (finEquivM Fq M) P)
    refine ⟨k, Nat.pow_right_injective hq ?_⟩
    show Fintype.card Fq ^ Places.deg Fq P = Fintype.card Fq ^ (m * k)
    rw [← Places.card_residue_eq Fq P,
      ← card_equiv' (S' := integralClosure (Places.Rfin Fq F) M) (finEquivM Fq M) P]
    exact hk
  have hd2 : ∀ P : HeightOneSpectrum (Places.Rinf Fq M), Places.deg Fq P = m := fun P => by
    refine Nat.pow_right_injective hq ?_
    show Fintype.card Fq ^ Places.deg Fq P = Fintype.card Fq ^ m
    rw [← Places.card_residue_eq Fq P,
      ← card_equiv' (S' := integralClosure (Places.Rinf Fq F) M) (infEquivM Fq M) P]
    exact hdi _
  -- the finite part is divisible by `N * m`
  have h1 : ((N : ℤ) * m) ∣ Places.degS Fq (Places.divS (Places.Rfin Fq M) f) := by
    rw [Places.degS, Finsupp.sum]
    refine Finset.dvd_sum fun P _ => ?_
    obtain ⟨k, hk⟩ := hd1 P
    rw [Places.divS_apply, hk, Places.ord, ← hv1 P, Nat.cast_mul]
    exact mul_dvd_mul (dvd_neg.2 (hfin _)) (dvd_mul_right _ _)
  -- the boundary part is `m * (-Σ_w v_w(f))`
  have hs : (∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      WithZero.log (w.valuation M f)) =
      ∑ᶠ P : HeightOneSpectrum (Places.Rinf Fq M), WithZero.log (P.valuation M f) := by
    rw [← finsum_comp_equiv (HeightOneSpectrum.equivOfRingEquiv (infEquivM Fq M))]
    exact finsum_congr fun P => by rw [hv2 P]
  have hsub : Function.support (fun P : HeightOneSpectrum (Places.Rinf Fq M) => WithZero.log (P.valuation M f)) ⊆
      ↑(Places.divS (Places.Rinf Fq M) f).support := fun P hP => by
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Places.divS_apply, Places.ord]
    exact neg_ne_zero.2 hP
  have h2 : Places.degS Fq (Places.divS (Places.Rinf Fq M) f) =
      (m : ℤ) * -∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
        WithZero.log (w.valuation M f) := by
    rw [hs, finsum_eq_sum_of_support_subset _ hsub, Places.degS, Finsupp.sum, ← Finset.sum_neg_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Places.divS_apply, hd2 P, Places.ord]
    ring
  rw [h2] at hpf
  have h3 : ((m : ℤ) * N) ∣ (m : ℤ) * ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      WithZero.log (w.valuation M f) := by
    have he : (m : ℤ) * ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
        WithZero.log (w.valuation M f) = Places.degS Fq (Places.divS (Places.Rfin Fq M) f) := by
      linear_combination -hpf
    rw [he, mul_comm]
    exact h1
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hm.ne')).1 h3

end Level

end

end Residue
end RamanujanPetersson

end



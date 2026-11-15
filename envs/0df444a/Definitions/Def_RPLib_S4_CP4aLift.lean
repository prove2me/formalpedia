-- Prove2me | Definitions.Def_RPLib_S4_CP4aLift
-- name    : RPLib_S4_CP4aLift
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:43:34.440821+00:00
-- url     : https://prove2.me/theorems/ce8c1a94-5e23-4e90-9f43-47418eaa2501
-- title:
--   Inertia groups of a profinite extension surject onto inertia groups of finite levels
-- statement:
--   Let a group $H$ act on a ring $B$ with invariants $A'$, and let $g_1$ act trivially on $A'/(P \cap A')$ for a prime $P$ of $B$. The file proves that some $g_1 h$ ($h \in H$) lies in the inertia group of $P$, proves lying-over along injective integral maps, and deduces that for every chart ring $R_0$ the inertia groups of finite Galois levels $L \le K_U$ at nonzero primes are the restrictions of inertia groups of primes of the pro-chart: $$I(Q \cap B_L) = I(Q)|_L.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter I, Section 7, Proposition 22; J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9

import Definitions.Def_RPLib_S4_KummerInf

/-!
# S4-CP4a, part f4: inertia lifting (`BdryLift`) holds

* `exists_mul_mem_inertia` (abstract, profinite): if `H` acts on `B` with invariants `A'` and `g₁` acts trivially on
  `A' / (P ∩ A')`, then some `g₁ h` (`h ∈ H`) lies in the inertia group of `P`.
* `exists_prime_comap_eq`: lying over along an injective integral algebra map.
* `bdryLift`: `BdryLift A K R0` for every chart ring `R0`: inertia groups of finite levels `L ≤ K_U` at nonzero primes
  are restrictions of inertia groups of boundary primes of the pro-chart.
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

section AbsLift

variable {G B A' : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CommRing A'] [Algebra A' B] [SMulCommClass H A' B] [Algebra.IsInvariant A' B H]
  [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

/-- **Abstract inertia lifting**: if `g₁` acts trivially on `A' / (P ∩ A')` (`A' = B^H`, `H` profinite), then
`g₁ h ∈ I(P)` for some `h ∈ H`. -/
theorem exists_mul_mem_inertia (P : Ideal B) [hP : P.IsPrime] (g1 : G)
    (hg1 : ∀ a : A', g1 • algebraMap A' B a - algebraMap A' B a ∈ P) :
    ∃ h : H, ∀ b : B, (g1 * (h : G)) • b - b ∈ P := by
  have hmem : ∀ a : A', g1 • algebraMap A' B a ∈ P ↔ algebraMap A' B a ∈ P := by
    intro a
    constructor
    · intro h
      have h2 := P.sub_mem h (hg1 a)
      rwa [sub_sub_cancel] at h2
    · intro h
      have h2 := P.add_mem (hg1 a) h
      rwa [sub_add_cancel] at h2
  haveI : (g1⁻¹ • P).IsPrime := Ideal.IsPrime.smul g1⁻¹
  have hunder : P.under A' = (g1⁻¹ • P).under A' := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap]
    rw [Ideal.mem_inv_pointwise_smul_iff, hmem]
  obtain ⟨h1, hh1⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G := H) P (g1⁻¹ • P) hunder
  have hh1' : ((h1 : G) • P) = g1⁻¹ • P := by
    rw [hh1]
    rfl
  have hstab : (g1 * (h1 : G)) • P = P := by
    rw [mul_smul, hh1', smul_inv_smul]
  have hin : ∀ x, (g1 * (h1 : G)) • x ∈ P ↔ x ∈ P := by
    intro x
    constructor
    · intro hx
      have h' : (g1 * (h1 : G)) • x ∈ (g1 * (h1 : G)) • P := by rw [hstab]; exact hx
      have h'' := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 h'
      rwa [inv_smul_smul] at h''
    · intro hx
      have h' := Ideal.smul_mem_pointwise_smul (g1 * (h1 : G)) x P hx
      rwa [hstab] at h'
  have hPP : P = P.map (MulSemiringAction.toRingEquiv G B (g1 * (h1 : G)) : B →+* B) := by
    ext x
    change x ∈ P ↔ x ∈ Ideal.map (MulSemiringAction.toRingEquiv G B (g1 * (h1 : G))) P
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      refine ⟨(g1 * (h1 : G))⁻¹ • x, (hin _).1 ?_, smul_inv_smul (g1 * (h1 : G)) x⟩
      rwa [smul_inv_smul]
    · rintro ⟨y, hy, rfl⟩
      exact (hin y).2 hy
  have hg2a : ∀ a : A', (g1 * (h1 : G)) • algebraMap A' B a - algebraMap A' B a ∈ P := by
    intro a
    have h := smul_algebraMap (A := B) h1 a
    have h' : (g1 * (h1 : G)) • algebraMap A' B a = g1 • algebraMap A' B a := by
      rw [mul_smul]
      exact congrArg (g1 • ·) h
    rw [h']
    exact hg1 a
  let σ0 : (B ⧸ P) ≃+* (B ⧸ P) := Ideal.quotientEquiv P P (MulSemiringAction.toRingEquiv G B (g1 * (h1 : G))) hPP
  have hσ0 : ∀ b, σ0 (Ideal.Quotient.mk P b) = Ideal.Quotient.mk P ((g1 * (h1 : G)) • b) := fun b => rfl
  let σ : (B ⧸ P) ≃ₐ[A' ⧸ P.under A'] (B ⧸ P) := AlgEquiv.ofRingEquiv (f := σ0) (fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change σ0 (Ideal.Quotient.mk P (algebraMap A' B a)) = Ideal.Quotient.mk P (algebraMap A' B a)
    rw [hσ0]
    exact Ideal.Quotient.eq.2 (hg2a a))
  obtain ⟨⟨h2, hh2⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H) (P.under A') P σ
  have key : ∀ b, Ideal.Quotient.mk P (h2 • b) = Ideal.Quotient.mk P ((g1 * (h1 : G)) • b) := by
    intro b
    have h3 : Ideal.Quotient.mk P (h2 • b) = σ (Ideal.Quotient.mk P b) := by
      rw [← hσ]
      rfl
    rw [h3]
    rfl
  refine ⟨h1 * h2⁻¹, fun b => ?_⟩
  have h3 := Ideal.Quotient.eq.1 (key (h2⁻¹ • b))
  rw [smul_inv_smul] at h3
  have h4 : (g1 * ((h1 * h2⁻¹ : H) : G)) • b = (g1 * (h1 : G)) • (h2⁻¹ • b) := by
    show (g1 * ((h1 : G) * ((h2⁻¹ : H) : G))) • b = (g1 * (h1 : G)) • (((h2⁻¹ : H) : G) • b)
    rw [← mul_assoc, mul_smul]
  rw [h4]
  have h5 := P.neg_mem h3
  rwa [neg_sub] at h5

end AbsLift

section AbsLiftFix

variable {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

/-- `exists_mul_mem_inertia` with `A' = B^H` (as `FixedPoints.subalgebra`). -/
theorem exists_mul_mem_inertia_fix {R0 : Type*} [CommRing R0] [Algebra R0 B] [SMulCommClass G R0 B]
    (P : Ideal B) [P.IsPrime] (g1 : G) (hg1 : ∀ b : B, (∀ h ∈ H, h • b = b) → g1 • b - b ∈ P) :
    ∃ h ∈ H, ∀ b : B, (g1 * h) • b - b ∈ P := by
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra R0 B H) B H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨h, hh⟩ := exists_mul_mem_inertia (A' := FixedPoints.subalgebra R0 B H) H P g1
    (fun a => hg1 (a : B) fun σ hσ => (a.2 : ∀ g : H, g • (a : B) = a) ⟨σ, hσ⟩)
  exact ⟨h, h.2, hh⟩

end AbsLiftFix

/-- Lying over along an injective `R0`-algebra map into an integral `R0`-algebra. -/
theorem exists_prime_comap_eq {R0 R S : Type*} [CommRing R0] [CommRing R] [CommRing S] [Algebra R0 R]
    [Algebra R0 S] [Algebra.IsIntegral R0 S] (f : R →ₐ[R0] S) (hf : Function.Injective f) (Q : Ideal R)
    [Q.IsPrime] : ∃ P : Ideal S, P.IsPrime ∧ P.comap f = Q := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  haveI : IsScalarTower R0 R S := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.IsIntegral R S := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R0) x).tower_top⟩
  obtain ⟨P, -, hP, hPQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal S) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have hx0 : x = 0 := hf (by rw [map_zero]; exact hx)
    rw [hx0]
    exact Q.zero_mem)
  exact ⟨P, hP, hPQ⟩

section Concrete

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

theorem inclU_injective {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) :
    Function.Injective (inclU R0 hLU) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : proChart A K R0 => ((z : maxUnram A K) : AlgebraicClosure K)) h

/-- A Frobenius-type lift: every `τ ∈ Gal(L/K)` extends to `π₁(U)`. -/
theorem exists_lift_level {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    (τ : L ≃ₐ[K] L) : ∃ g1 : Pi1 A K, ∀ y : L,
      g1 (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (τ y) := by
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  exact ⟨τ.liftNormal (maxUnram A K), fun y => AlgEquiv.liftNormal_commutes τ (maxUnram A K) y⟩

/-- Elements of the pro-chart fixed by `Gal(K_U/L)` come from the integral closure of `R0` in `L`. -/
theorem exists_inclU_eq {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    (b : proChart A K R0)
    (hb : ∀ σ ∈ (IntermediateField.restrict hLU).fixingSubgroup, σ (b : maxUnram A K) = b) :
    ∃ y : integralClosure R0 L, inclU R0 hLU y = b := by
  have hmemF : (b : maxUnram A K) ∈ IntermediateField.restrict hLU := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.restrict hLU)]
    exact (IntermediateField.mem_fixedField_iff _ _).2 hb
  have hmemL : ((b : maxUnram A K) : AlgebraicClosure K) ∈ L :=
    (IntermediateField.mem_restrict hLU _).1 hmemF
  let yL : L := ⟨_, hmemL⟩
  have hint : IsIntegral R0 yL := by
    have h1 : IsIntegral R0 (((IntermediateField.inclusion hLU).restrictScalars R0) yL) := b.2
    exact (isIntegral_algHom_iff ((IntermediateField.inclusion hLU).restrictScalars R0)
      (IntermediateField.inclusion hLU).injective).1 h1
  exact ⟨⟨yL, hint⟩, Subtype.ext (Subtype.ext rfl)⟩

/-- A lift `g₁` of an inertia element `τ` acts trivially modulo `P` on the image of the finite level. -/
theorem inclU_sub_mem {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {Q : Ideal (integralClosure R0 L)} {τ : L ≃ₐ[K] L} (hτ : τ ∈ Q.inertia (L ≃ₐ[K] L))
    {P : Ideal (proChart A K R0)} (hPQ : P.comap (inclU R0 hLU) = Q) {g1 : Pi1 A K}
    (hg1L : ∀ y : L, g1 (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (τ y))
    (y : integralClosure R0 L) : g1 • inclU R0 hLU y - inclU R0 hLU y ∈ P := by
  have hτy : τ • y - y ∈ Q := AddSubgroup.mem_inertia.1 hτ y
  rw [← hPQ, Ideal.mem_comap] at hτy
  convert hτy using 1
  apply Subtype.ext
  apply Subtype.ext
  show ((g1 (IntermediateField.inclusion hLU (y : L)) : maxUnram A K) : AlgebraicClosure K) -
      ((y : L) : AlgebraicClosure K) = ((τ (y : L) : L) : AlgebraicClosure K) - ((y : L) : AlgebraicClosure K)
  rw [hg1L]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- The profinite step at the pro-chart: `g₁` trivial on `B^{Gal(K_U/L)}` mod `P` ⇒ `g₁ h ∈ I(P)`, `h ∈ Gal(K_U/L)`. -/
theorem exists_fix_mul_mem_inertia {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] (P : Ideal (proChart A K R0)) [P.IsPrime] (g1 : Pi1 A K)
    (hg1 : ∀ b : proChart A K R0, (∀ σ ∈ (IntermediateField.restrict hLU).fixingSubgroup,
      σ (b : maxUnram A K) = b) → g1 • b - b ∈ P) :
    ∃ h ∈ (IntermediateField.restrict hLU).fixingSubgroup, ∀ b : proChart A K R0, (g1 * h) • b - b ∈ P := by
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
  exact exists_mul_mem_inertia_fix (R0 := R0) (IntermediateField.restrict hLU).fixingSubgroup P g1
    fun b hb => hg1 b fun σ hσ => congrArg Subtype.val (hb σ hσ)

/-- **`BdryLift` holds** at every chart ring `R0` (inertia lifting through the profinite Galois group). -/
theorem bdryLift : BdryLift A K R0 := by
  intro L hLU hfin hgal Q hQ hQ0 τ hτ
  have := hfin
  obtain ⟨P, hP, hPQ⟩ := exists_prime_comap_eq (inclU R0 hLU) (inclU_injective hLU) Q
  have hPB : IsBdryPrime A K R0 P := by
    refine ⟨hP, fun h => hQ0 ?_⟩
    rw [← hPQ, h]
    exact Ideal.comap_bot_of_injective _ (inclU_injective hLU)
  obtain ⟨g1, hg1L⟩ := exists_lift_level hLU τ
  have := hP
  obtain ⟨h, hhH, hh⟩ := exists_fix_mul_mem_inertia hLU P g1 fun b hb => by
    obtain ⟨y, rfl⟩ := exists_inclU_eq hLU b hb
    exact inclU_sub_mem hLU hτ hPQ hg1L y
  refine ⟨P, hPB, g1 * h, AddSubgroup.mem_inertia.2 hh, fun y => ?_⟩
  have hfix : h (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hhH _ ((IntermediateField.mem_restrict hLU _).2 y.2)
  show _ = ((g1 (h (IntermediateField.inclusion hLU y)) : maxUnram A K) : AlgebraicClosure K)
  rw [hfix, hg1L]
  rfl

end Concrete

end

end RamanujanPetersson.CP4a



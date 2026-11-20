-- Prove2me | Definitions.Def_RPLib_F2_006
-- name    : RPLib_F2_006
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T06:41:34.633724+00:00
-- url     : https://prove2.me/theorems/aa22eead-d74f-4181-9406-2ba8dd9676d2
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 006 of 70
-- statement:
--   File 006 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CP4a_Lift`: S4-CP4a, part f4: inertia lifting (`BdryLift`) holds
--   * `S4.Def_RP_JacRRFam_A`: Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)
--   * `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
--   * `S4.Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
--   * `S4.Def_RP_JacComplete_Sep`: The Jacobian (unit S4-JacComplete), part `Sep` (tools for separating elements; Mathlib only)
--   * `S4.Def_RP_JacComplete_Sep2`: The Jacobian (unit S4-JacComplete), part `Sep2` (separating elements; Mathlib only)
--   * `S4.Def_RP_JacComplete_PlaceVal`: The Jacobian (unit S4-JacComplete), part `PlaceVal` (dictionary D1, generic valuation theory)
--   * `S4.Def_RP_JacRRFam_C`: Places over an arbitrary field, part C: dimensions of quotients of Dedekind domains
--   * `S4.Def_RP_JacRRFam_D`: Places over an arbitrary field, part D: Dedekind domains with finite-dimensional quotients
--   * `S4.Def_RP_JacRRFam_E`: Places over an arbitrary field, part E: function fields over `K` and the product formula
--   * `S4.Def_RP_JacRRFam_F`: Places over an arbitrary field, part F: divisors, the product formula, the constant field
--   * `S4.Def_RP_JacComplete_PlaceF`: The Jacobian (unit S4-JacComplete), part `PlaceF` (dictionary D1 for a function field `F / K(x)`)
--   * `S4.Def_RP_JacComplete_GenF`: The Jacobian (unit S4-JacComplete), part `GenF` (the synonym with coordinate `h`)
--   * `S4.Def_RP_JacRRFam_G`: Riemann-Roch over an arbitrary field, part G: the local axioms for function fields over `K`
--   * `S4.Def_RP_JacRRFam_B`: Riemann-Roch over an arbitrary constant field (S4-JacRRFam, part B)
--   * `S4.Def_RP_JacRRFam_H`: Riemann-Roch over an arbitrary field, part H: the Riemann input and Riemann-Roch for function fields
--   * `S4.Def_RP_JacRRFam_I`: Riemann-Roch over an arbitrary field, part I: the classical statements for function fields
--   * `S4.Def_RP_JacLaw_RRk`: S4-JacLaw, file O4c: the Riemann-Roch dictionary for the chart ring `B = Rfin K F`
--   * `S4.Def_RP_JacLaw_Exact`: S4-JacLaw, file O6a: exact poles from hyperplane conditions
--   * `S4.Def_RP_JacLaw_RRkH`: S4-JacLaw, file X2: exact pole divisors `Hn` at infinity (generalising `N • P∞`)
--   * `S4.Def_RP_IsogDegA_Fib1`: S4-IsogDegA, file Fib1: generic fibre count, part 1 (finite dimensionality, fibres, upper bound)
--   * `S4.Def_RP_IsogDegA_Fib2`: S4-IsogDegA, file Fib2: generic fibre count, part 2 (lower bound via going-up, exact count)
--   * `S4.Def_RP_IsogDegA_Fib3`: S4-IsogDegA, file Fib3: generic fibre count, part 3 (choice of a generic primitive element)
--   * `S4.Def_RP_IsogDegA_Fib4`: S4-IsogDegA, file Fib4: the generic fibre has `finSepDegree` points (O1 headline)
--   * `S4.Def_RP_JacLaw_GenFib`: S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets
--   * `S4.Def_RP_JacSymA_A`: S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`
--   * `S4.Def_RP_JacDivisors_Q`: S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_004

/-!
# Ramanujan-Petersson curve library (flat edition), file 006 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CP4a_Lift`: S4-CP4a, part f4: inertia lifting (`BdryLift`) holds
* `S4.Def_RP_JacRRFam_A`: Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)
* `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
* `S4.Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
* `S4.Def_RP_JacComplete_Sep`: The Jacobian (unit S4-JacComplete), part `Sep` (tools for separating elements; Mathlib only)
* `S4.Def_RP_JacComplete_Sep2`: The Jacobian (unit S4-JacComplete), part `Sep2` (separating elements; Mathlib only)
* `S4.Def_RP_JacComplete_PlaceVal`: The Jacobian (unit S4-JacComplete), part `PlaceVal` (dictionary D1, generic valuation theory)
* `S4.Def_RP_JacRRFam_C`: Places over an arbitrary field, part C: dimensions of quotients of Dedekind domains
* `S4.Def_RP_JacRRFam_D`: Places over an arbitrary field, part D: Dedekind domains with finite-dimensional quotients
* `S4.Def_RP_JacRRFam_E`: Places over an arbitrary field, part E: function fields over `K` and the product formula
* `S4.Def_RP_JacRRFam_F`: Places over an arbitrary field, part F: divisors, the product formula, the constant field
* `S4.Def_RP_JacComplete_PlaceF`: The Jacobian (unit S4-JacComplete), part `PlaceF` (dictionary D1 for a function field `F / K(x)`)
* `S4.Def_RP_JacComplete_GenF`: The Jacobian (unit S4-JacComplete), part `GenF` (the synonym with coordinate `h`)
* `S4.Def_RP_JacRRFam_G`: Riemann-Roch over an arbitrary field, part G: the local axioms for function fields over `K`
* `S4.Def_RP_JacRRFam_B`: Riemann-Roch over an arbitrary constant field (S4-JacRRFam, part B)
* `S4.Def_RP_JacRRFam_H`: Riemann-Roch over an arbitrary field, part H: the Riemann input and Riemann-Roch for function fields
* `S4.Def_RP_JacRRFam_I`: Riemann-Roch over an arbitrary field, part I: the classical statements for function fields
* `S4.Def_RP_JacLaw_RRk`: S4-JacLaw, file O4c: the Riemann-Roch dictionary for the chart ring `B = Rfin K F`
* `S4.Def_RP_JacLaw_Exact`: S4-JacLaw, file O6a: exact poles from hyperplane conditions
* `S4.Def_RP_JacLaw_RRkH`: S4-JacLaw, file X2: exact pole divisors `Hn` at infinity (generalising `N • P∞`)
* `S4.Def_RP_IsogDegA_Fib1`: S4-IsogDegA, file Fib1: generic fibre count, part 1 (finite dimensionality, fibres, upper bound)
* `S4.Def_RP_IsogDegA_Fib2`: S4-IsogDegA, file Fib2: generic fibre count, part 2 (lower bound via going-up, exact count)
* `S4.Def_RP_IsogDegA_Fib3`: S4-IsogDegA, file Fib3: generic fibre count, part 3 (choice of a generic primitive element)
* `S4.Def_RP_IsogDegA_Fib4`: S4-IsogDegA, file Fib4: the generic fibre has `finSepDegree` points (O1 headline)
* `S4.Def_RP_JacLaw_GenFib`: S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets
* `S4.Def_RP_JacSymA_A`: S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`
* `S4.Def_RP_JacDivisors_Q`: S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_Lift =====
section

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


end

-- ===== S4.Def_RP_JacRRFam_A =====
section

/-!
# Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)

The abstract repartition calculus of `RamanujanPetersson.RR` (lib/S3/RR_A, RR_B) counts with
`AddSubgroup.relIndex` over a FINITE field.  Here the counting layer is redone over an ARBITRARY
field `K` (for instance a non-perfect function field `K = k(V)`) with the `ℕ∞`-valued codimension
`cd H H' = dim_K H' / (H ∩ H')`.  The definitions of part A of S3 (`Data`, `ball`, `AD`, `adeles`,
`Fs`, `LD`, `ell`, `div`, `degD`) are reused unchanged.

Main results: the codimension calculus (`cd_add`, `cd_split`, `cd_comap`, `cd_map_of_injective`,
`cd_eq_zero_iff`, `cd_of_le_fd`, `fd_of_cd`), the axioms `Data.AxiomsK0` / `Data.AxiomsK`
(local index `cd (ball i n) (ball i (n+1)) = deg i`), and the global index computation
`cd_AD_le`, `finite_LDK`, `ell_sub_leK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero Module

namespace RamanujanPetersson.RR

/-! ### The codimension of two subspaces -/

section Codim

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem cd_ker {W : Type*} [AddCommGroup W] [Module K W] (g : V →ₗ[K] W) (H' : Submodule K V) :
    cd (LinearMap.ker g) H' = Cardinal.toENat (Module.rank K (H'.map g)) := by
  have e1 : (LinearMap.ker g).comap H'.subtype = LinearMap.ker (g.domRestrict H') :=
    (LinearMap.ker_domRestrict H' g).symm
  have h := (g.domRestrict H').quotKerEquivRange.lift_rank_eq
  rw [LinearMap.range_domRestrict, ← e1] at h
  have h2 := congrArg Cardinal.toENat h
  simp only [Cardinal.toENat_lift] at h2
  exact h2

theorem cd_eq_map (H H' : Submodule K V) :
    cd H H' = Cardinal.toENat (Module.rank K (H'.map H.mkQ)) := by
  rw [← cd_ker, Submodule.ker_mkQ]

theorem cd_sup_left (H X : Submodule K V) : cd H (H ⊔ X) = cd H X := by
  rw [cd_eq_map, cd_eq_map, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

theorem cd_comap {W : Type*} [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (B : Submodule K W)
    (H' : Submodule K V) : cd (B.comap f) H' = cd B (H'.map f) := by
  rw [cd_eq_map B, ← Submodule.map_comp, ← cd_ker, LinearMap.ker_comp, Submodule.ker_mkQ]

theorem cd_map_of_injective {W : Type*} [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    (hf : Function.Injective f) (H H' : Submodule K V) : cd (H.map f) (H'.map f) = cd H H' := by
  rw [← cd_comap, Submodule.comap_map_eq_of_injective hf]

theorem cd_eq_zero_iff {H H' : Submodule K V} : cd H H' = 0 ↔ H' ≤ H := by
  rw [cd_eq_map, Cardinal.toENat_eq_zero, Submodule.rank_eq_zero, ← LinearMap.le_ker_iff_map,
    Submodule.ker_mkQ]

@[simp] theorem cd_self (H : Submodule K V) : cd H H = 0 := cd_eq_zero_iff.2 le_rfl

/-- Additivity of codimension along `H1 ≤ H2 ≤ H3`. -/
theorem cd_add {H1 H2 H3 : Submodule K V} (h12 : H1 ≤ H2) (h23 : H2 ≤ H3) :
    cd H1 H2 + cd H2 H3 = cd H1 H3 := by
  rw [cd_eq_map, cd_eq_map, cd_eq_map]
  have hq : H1 ≤ H2.comap LinearMap.id := by rw [Submodule.comap_id]; exact h12
  set φ : (V ⧸ H1) →ₗ[K] (V ⧸ H2) := H1.mapQ H2 LinearMap.id hq
  set S := H3.map H1.mkQ with hS
  have hr : LinearMap.range (φ.domRestrict S) = H3.map H2.mkQ := by
    rw [LinearMap.range_domRestrict, hS, ← Submodule.map_comp, Submodule.mapQ_mkQ,
      LinearMap.comp_id]
  have hk : LinearMap.ker (φ.domRestrict S) = (H2.map H1.mkQ).comap S.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mapQ, Submodule.comap_id]
  have hle : H2.map H1.mkQ ≤ S := Submodule.map_mono h23
  have h := LinearMap.rank_range_add_rank_ker (φ.domRestrict S)
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hle).rank_eq] at h
  rw [← h, map_add, add_comm]

/-- `cd H H' = cd (H ⊓ C) (H' ⊓ C) + cd (H ⊔ C) (H' ⊔ C)` for `H ≤ H'`. -/
theorem cd_split {H H' : Submodule K V} (C : Submodule K V) (h : H ≤ H') :
    cd H H' = cd (H ⊓ C) (H' ⊓ C) + cd (H ⊔ C) (H' ⊔ C) := by
  have h1 : H ≤ H ⊔ (H' ⊓ C) := le_sup_left
  have h2 : H ⊔ (H' ⊓ C) ≤ H' := sup_le h inf_le_left
  rw [← cd_add h1 h2]
  congr 1
  · rw [cd_sup_left, ← cd_inf_right H (H' ⊓ C), ← inf_assoc, inf_eq_left.2 h]
  · have hmod : H ⊔ (H' ⊓ C) = (H ⊔ C) ⊓ H' := by rw [inf_comm]; exact (sup_inf_assoc_of_le C h).symm
    rw [hmod, cd_inf_right, ← cd_sup_left (H ⊔ C) H']
    congr 1
    apply le_antisymm
    · exact sup_le (sup_le (h.trans le_sup_left) le_sup_right) le_sup_left
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)

/-- For `H ≤ H'` with `H'` finite-dimensional, `cd H H' = dim H' - dim H`. -/
theorem cd_of_le_fd {H H' : Submodule K V} (h : H ≤ H') [FiniteDimensional K H'] :
    finrank K H ≤ finrank K H' ∧ cd H H' = ((finrank K H' - finrank K H : ℕ) : ℕ∞) := by
  have h1 := Submodule.finrank_quotient_add_finrank (H.comap H'.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq] at h1
  refine ⟨by omega, ?_⟩
  unfold cd
  rw [← Module.finrank_eq_rank, map_natCast]
  congr 1
  omega

/-- If `H ≤ H'`, `H` is finite-dimensional and `cd H H' < ⊤`, then `H'` is finite-dimensional. -/
theorem fd_of_cd {H H' : Submodule K V} (h : H ≤ H') [FiniteDimensional K H] (hc : cd H H' ≠ ⊤) :
    FiniteDimensional K H' := by
  have h1 := rank_quotient_add_rank_of_divisionRing (H.comap H'.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe h).rank_eq] at h1
  have hq : Module.rank K (H' ⧸ H.comap H'.subtype) < Cardinal.aleph0 := by
    unfold cd at hc
    rw [Ne, Cardinal.toENat_eq_top, not_le] at hc
    exact hc
  have hH : Module.rank K H < Cardinal.aleph0 := Module.rank_lt_aleph0 K H
  have hH' : Module.rank K H' < Cardinal.aleph0 := h1 ▸ Cardinal.add_lt_aleph0 hq hH
  exact Module.rank_lt_aleph0_iff.1 hH'

theorem enat_add_eq {m n : ℕ} {b : ℕ∞} (h : (m : ℕ∞) + b = n) :
    m ≤ n ∧ b = ((n - m : ℕ) : ℕ∞) := by
  have hb : b ≠ ⊤ := by
    rintro rfl
    simp at h
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hb
  have : m + k = n := by exact_mod_cast h
  refine ⟨by omega, ?_⟩
  congr 1
  omega

end Codim

/-! ### The axioms over an arbitrary field and the global index -/

namespace Data

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F] (d : Data K F ι)

theorem cd_AD_single (D : ι →₀ ℤ) (i : ι) :
    cd (d.AD D) (d.AD (D + Finsupp.single i 1)) = cd (d.ball i (D i)) (d.ball i (D i + 1)) := by
  classical
  set D' := D + Finsupp.single i 1 with hD'
  have hsi : ∀ j, j ≠ i → D' j = D j := fun j hj => by
    simp [hD', Ne.symm hj]
  have hii : D' i = D i + 1 := by simp [hD']
  let ev : (ι → F) →ₗ[K] F := LinearMap.proj i
  have hAD : d.AD D = (d.ball i (D i)).comap ev ⊓ d.AD D' := by
    ext α
    simp only [Submodule.mem_inf, Submodule.mem_comap, mem_AD, mem_ball, ev, LinearMap.proj_apply]
    constructor
    · intro h
      refine ⟨h i, fun j => (h j).trans (exp_le_exp.2 ?_)⟩
      by_cases hj : j = i
      · subst hj; rw [hii]; omega
      · rw [hsi j hj]
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h1
      · simpa [hsi j hj] using h2 j
  have hmap : (d.AD D').map ev = d.ball i (D i + 1) := by
    ext f
    simp only [Submodule.mem_map, mem_AD, mem_ball, ev, LinearMap.proj_apply]
    constructor
    · rintro ⟨α, hα, rfl⟩; simpa [hii] using hα i
    · intro hf
      refine ⟨Pi.single i f, fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simpa [hii] using hf
      · simp [hj]
  rw [hAD, cd_inf_right, cd_comap, hmap]

/-- The local axioms over an arbitrary field `K`: places exist and have positive degree, the
local index `dim (ball i (n+1) / ball i n) = deg i`, the product formula and `dim L(0) < ∞`. -/
structure AxiomsK0 : Prop where
  nonempty : Nonempty ι
  deg_pos : ∀ i, 0 < d.deg i
  localIndex : ∀ i (n : ℤ), cd (d.ball i n) (d.ball i (n + 1)) = d.deg i
  deg_div : ∀ f : F, f ≠ 0 → d.degD (d.div f) = 0
  finite_L0 : FiniteDimensional K (d.LD 0)

/-- The axioms over an arbitrary field: the local axioms plus the input for Riemann's inequality
(as in `Data.Axioms`). -/
structure AxiomsK : Prop extends AxiomsK0 d where
  riemannInput : ∃ B : ι →₀ ℤ, 0 ≤ B ∧ 0 < d.degD B ∧ ∃ C : ι →₀ ℤ, 0 ≤ C ∧
    ∃ c : ℤ, ∀ n : ℕ, (n : ℤ) * d.degD B - c ≤ d.ell (n • B + C)

variable {d}

theorem cd_AD_add_single_nat (hd : d.AxiomsK0) (D : ι →₀ ℤ) (i : ι) (n : ℕ) :
    cd (d.AD D) (d.AD (D + Finsupp.single i (n : ℤ))) = ((n * d.deg i : ℕ) : ℕ∞) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : D + Finsupp.single i ((n + 1 : ℕ) : ℤ) =
        (D + Finsupp.single i (n : ℤ)) + Finsupp.single i 1 := by
      rw [Nat.cast_succ, Finsupp.single_add, add_assoc]
    rw [e, ← cd_add (d.AD_mono (le_add_of_nonneg_right
        (Finsupp.single_nonneg.2 (Nat.cast_nonneg _))))
      (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one))), ih,
      d.cd_AD_single, hd.localIndex]
    push_cast
    ring

theorem cd_AD_add (hd : d.AxiomsK0) {E : ι →₀ ℤ} (hE : 0 ≤ E) (D : ι →₀ ℤ) :
    cd (d.AD D) (d.AD (D + E)) = ((d.degD E).toNat : ℕ∞) := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero => simp
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have hb0 : 0 ≤ b := by have := hE a; simpa [hfa] using this
    have hf0 : 0 ≤ f := fun j => by
      by_cases hj : j = a
      · subst hj; simp [hfa]
      · have := hE j; simpa [Finsupp.single_apply, Ne.symm hj] using this
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
    rw [← add_assoc, ← cd_add (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 hb0)))
      (d.AD_mono (le_add_of_nonneg_right hf0)), cd_AD_add_single_nat hd, ih hf0, ← Nat.cast_add,
      degD_add, degD_single]
    congr 1
    have hdf := d.degD_nonneg hf0
    have hm : ((k : ℤ) * (d.deg a : ℤ)) = ((k * d.deg a : ℕ) : ℤ) := by push_cast; ring
    rw [hm]
    generalize k * d.deg a = m
    omega

/-- `dim A(D') / A(D) = deg D' - deg D`. -/
theorem cd_AD_le (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    cd (d.AD D) (d.AD D') = ((d.degD D' - d.degD D).toNat : ℕ∞) := by
  have := cd_AD_add hd (sub_nonneg.2 h) D
  rwa [add_sub_cancel, degD_sub] at this

theorem cd_LD [Nonempty ι] (D E : ι →₀ ℤ) :
    cd (d.LD D) (d.LD E) = cd (d.AD D ⊓ d.Fs) (d.AD E ⊓ d.Fs) := by
  rw [← d.map_LD, ← d.map_LD, cd_map_of_injective _ d.const_injective]

theorem cd_LD_add (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    cd (d.LD D) (d.LD D') + cd (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      ((d.degD D' - d.degD D).toNat : ℕ∞) := by
  have := hd.nonempty
  rw [cd_LD, ← cd_split _ (d.AD_mono h), cd_AD_le hd h]

/-- `L(D)` is finite-dimensional. -/
theorem finite_LDK (hd : d.AxiomsK0) (D : ι →₀ ℤ) : FiniteDimensional K (d.LD D) := by
  have := hd.finite_L0
  have h1 : (0 : ι →₀ ℤ) ≤ D ⊔ 0 := le_sup_right
  have h2 : D ≤ D ⊔ 0 := le_sup_left
  have hne : cd (d.LD 0) (d.LD (D ⊔ 0)) ≠ ⊤ := by
    intro h0
    have := cd_LD_add hd h1
    rw [h0, top_add] at this
    exact ENat.top_ne_natCast _ this
  have : FiniteDimensional K (d.LD (D ⊔ 0)) := fd_of_cd (d.LD_mono h1) hne
  exact Submodule.finiteDimensional_of_le (d.LD_mono h2)

theorem ell_le_of_leK (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    d.ell D ≤ d.ell D' ∧ cd (d.LD D) (d.LD D') = ((d.ell D' - d.ell D : ℕ) : ℕ∞) := by
  have := finite_LDK hd D'
  exact cd_of_le_fd (d.LD_mono h)

/-- `ℓ(D') - ℓ(D) ≤ deg D' - deg D` for `D ≤ D'`, and the codimension of `A(D) + F` in `A(D') + F`. -/
theorem ell_sub_leK (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    (d.ell D' : ℤ) - d.ell D ≤ d.degD D' - d.degD D ∧
    cd (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      (((d.degD D' - d.degD D).toNat - (d.ell D' - d.ell D) : ℕ) : ℕ∞) := by
  obtain ⟨hle, hr⟩ := ell_le_of_leK hd h
  have := cd_LD_add hd h
  rw [hr] at this
  obtain ⟨h1, h2⟩ := enat_add_eq this
  refine ⟨?_, h2⟩
  have := d.degD_mono h
  omega

end Data

end RamanujanPetersson.RR


end

-- ===== S4.Def_RP_CP4a_BdryInf =====
section

/-!
# S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`

For the chart `Rinf` at infinity of a function field `F/𝔽_q`, with `𝔽_{q^m} ⊆ K_U` for all `m` (`hζc`):
* `good_inf`: residue rings of boundary primes are finite of `q`-power order.
* `card_fix_inf`: `#{s | τ^m s = s} = #Hom_{𝔽_q}(Rinf, 𝔽_{q^m})` for the true boundary permutation `τ` of `φ⁻¹`.
* `numPoints_eq_add_fix`: `N_m = #U(𝔽_{q^m}) + #{s | τ^m s = s}`, `#U(L) := #Hom_{𝔽_q}(Rfin, L)`, `[L : 𝔽_q] = m`.
* `lefschetz_count`: `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n` (Core B as a hypothesis).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section BdryInf

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq in
/-- Residue rings at boundary primes over `∞` are finite of `q`-power order. -/
theorem good_inf (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) :
    Finite (Rinf Fq F ⧸ Q.under (Rinf Fq F)) ∧
      ∃ d, Nat.card (Rinf Fq F ⧸ Q.under (Rinf Fq F)) = (p ^ e) ^ d := by
  have := hQ.1
  have hne : Q.under (Rinf Fq F) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  let P : IsDedekindDomain.HeightOneSpectrum (Rinf Fq F) := ⟨Q.under (Rinf Fq F), inferInstance, hne⟩
  refine ⟨Places.finite_residue P, deg Fq P, ?_⟩
  rw [← hq]
  exact card_residue_eq Fq P

end BdryInf

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_FrobLift =====
section

/-!
# S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist

For a function field `F/𝔽_q` (`q = p ^ e`) with `constField = 𝔽_q`:
* `cast_ne_zero_of_not_dvd`, `isUnit_cast_Rfin`, `isUnit_cast_Rinf`: `N = l ^ n` with `l ∤ q` is a unit;
* `exists_zeta_geo`: a primitive `N`-th root of unity `ζ ∈ K_U` fixed by `π₁^geo`;
* `exists_zeta_level`: primitive `(q ^ a - 1)`-th roots of unity in `K_U`;
* `exists_frobLift`: there is `φ ∈ π₁(U)` with `φ x = x ^ q` on all constants (a compactness argument over the
  closed sets `T_m = {σ | σ x = x ^ q whenever x ^ (q ^ m) = x}`, each nonempty by lifting `frobF` on `F_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places PicDescent CurveCoh Kummer GalCover

noncomputable section

section FrobSet

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem pow_pow_iter {M : Type*} [Monoid M] {x : M} {n : ℕ} (h : x ^ n = x) (b : ℕ) : x ^ n ^ b = x := by
  induction b with
  | zero => rw [pow_zero, pow_one]
  | succ b ih => rw [pow_succ, pow_mul, ih, h]

/-- `{σ | σ x = y}` is closed in `π₁(U)`. -/
theorem isClosed_setOf_apply_eq (x y : maxUnram A K) : IsClosed {σ : Pi1 A K | σ x = y} := by
  by_cases h : ∃ σ0 : Pi1 A K, σ0 x = y
  · obtain ⟨σ0, hσ0⟩ := h
    have hs : {σ : Pi1 A K | σ x = y} = (fun σ => σ0⁻¹ * σ) ⁻¹' (fixElt A K x : Set (Pi1 A K)) := by
      ext σ
      show σ x = y ↔ σ0.symm (σ x) = x
      rw [AlgEquiv.symm_apply_eq, hσ0]
    rw [hs]
    exact (Subgroup.isClosed_of_isOpen _ (fixElt_isOpen A K x)).preimage (continuous_mul_left _)
  · push_neg at h
    have hs : {σ : Pi1 A K | σ x = y} = ∅ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact h σ
    rw [hs]
    exact isClosed_empty

end FrobSet

section Exist

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

theorem isUnit_cast_Rfin {N : ℕ} (hN : (N : F) ≠ 0) : IsUnit (N : Rfin Fq F) := by
  have h : (N : Fq) ≠ 0 := by
    intro h0
    apply hN
    rw [← map_natCast (algebraMap Fq F), h0, map_zero]
  have h1 := (Ne.isUnit h).map (algebraMap Fq (Rfin Fq F))
  rwa [map_natCast] at h1

theorem isUnit_cast_Rinf {N : ℕ} (hN : (N : F) ≠ 0) : IsUnit (N : Rinf Fq F) := by
  have h : (N : Fq) ≠ 0 := by
    intro h0
    apply hN
    rw [← map_natCast (algebraMap Fq F), h0, map_zero]
  have h1 := (Ne.isUnit h).map (algebraMap Fq (Rinf Fq F))
  rwa [map_natCast] at h1

include hq he in
theorem exists_zeta_geo {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) :
    ∃ ζ : maxUnram (Rfin Fq F) F, IsPrimitiveRoot ζ N ∧
      ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ := by
  obtain ⟨ζ, hζ, hc⟩ := exists_zeta (Rfin Fq F) F p he N hN
  refine ⟨ζ, hζ, ?_⟩
  rw [hq]
  exact zeta_fixed hc

include he in
theorem exists_zeta_level : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1) := by
  intro a ha
  have h1 : 1 < (p ^ e) ^ a := Nat.one_lt_pow ha.ne' (Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt)
  have : NeZero ((p ^ e) ^ a - 1) := ⟨by omega⟩
  have hN : (((p ^ e) ^ a - 1 : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_sub h1.le, Nat.cast_pow, Nat.cast_pow, CharP.cast_eq_zero, zero_pow he.ne', zero_pow ha.ne',
      Nat.cast_one, zero_sub, neg_ne_zero]
    exact one_ne_zero
  obtain ⟨ζ, hζ, -⟩ := exists_zeta (Rfin Fq F) F p he _ hN
  exact ⟨ζ, hζ⟩

end Exist

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_JacComplete_Sep =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Sep` (tools for separating elements; Mathlib only)

* `finiteDimensional_adjoin_of_transcendental`: if `F` is finite over `K⟮x⟯` and `h` is transcendental
  over `K`, then `F` is finite over `K⟮h⟯` (transcendence degree one);
* `eq_zero_of_sum_pow_mul`: if a valuation has `v h = exp (-1)`, the elements `1, h, ..., h^(p-1)`
  are linearly independent over the `p`-th powers.
-/

set_option autoImplicit false

open IntermediateField Polynomial Cardinal
open scoped WithZero

universe u

namespace RamanujanPetersson.JacComplete

section Fin

variable {K : Type*} {F : Type u} [Field K] [Field F] [Algebra K F]

/-- Transcendence degree one: `F` finite over `K⟮x⟯` and `h` transcendental give `F` finite over `K⟮h⟯`. -/
theorem finiteDimensional_adjoin_of_transcendental {x h : F} [FiniteDimensional K⟮x⟯ F]
    (hh : Transcendental K h) : FiniteDimensional K⟮h⟯ F := by
  open scoped algebraAdjoinAdjoin in
  have h1 : Algebra.IsAlgebraic (Algebra.adjoin K ({x} : Set F)) F :=
    IntermediateField.isAlgebraic_adjoin_iff_top.1 (Algebra.IsAlgebraic.of_finite K⟮x⟯ F)
  have h2 : Algebra.trdeg K F ≤ #({x} : Set F) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({x} : Set F)
  have hind : AlgebraicIndependent K (fun _ : PUnit.{u+1} => h) := algebraicIndependent_unique_type_iff.2 hh
  have hb : IsTranscendenceBasis K (fun _ : PUnit.{u+1} => h) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite
      (h2.trans (by rw [Cardinal.mk_singleton, Cardinal.mk_punit]))
  have halg := hb.isAlgebraic_field
  have hr : Set.range (fun _ : PUnit.{u+1} => h) = {h} := Set.range_const
  rw [hr] at halg
  have hxi : IsIntegral K⟮h⟯ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let L : IntermediateField K⟮h⟯ F := K⟮h⟯⟮x⟯
  have hL : FiniteDimensional K⟮h⟯ L := IntermediateField.adjoin.finiteDimensional hxi
  have hle : K⟮x⟯ ≤ L.restrictScalars K :=
    IntermediateField.adjoin_simple_le_iff.2 (IntermediateField.mem_adjoin_simple_self K⟮h⟯ x)
  letI : Algebra K⟮x⟯ L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K⟮x⟯ L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite K⟮x⟯ L F
  exact Module.Finite.trans L F

end Fin

section Val

variable {F : Type*} [Field F]

/-- The value of `h ^ r * c ^ p` when `v h = exp (-1)` and `c ≠ 0`. -/
theorem val_pow_mul_pow (v : Valuation F ℤᵐ⁰) {h c : F} (hv : v h = WithZero.exp (-1 : ℤ)) (hc : c ≠ 0)
    (r p : ℕ) : ∃ n : ℤ, v (h ^ r * c ^ p) = WithZero.exp (-(r : ℤ) + p * n) := by
  have h0 : v c ≠ 0 := (Valuation.ne_zero_iff v).2 hc
  refine ⟨WithZero.log (v c), ?_⟩
  rw [map_mul, map_pow, map_pow, hv, ← WithZero.exp_log h0, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_add, WithZero.log_exp]
  congr 1
  simp only [nsmul_eq_mul, mul_neg, mul_one]

/-- **Independence over `p`-th powers.** If `v h = exp (-1)` then `Σ_{r < p} h^r c_r^p = 0` forces all
`c_r = 0`. -/
theorem eq_zero_of_sum_pow_mul (p : ℕ) [hp : Fact p.Prime] (v : Valuation F ℤᵐ⁰) {h : F}
    (hv : v h = WithZero.exp (-1 : ℤ)) (c : Fin p → F) (hc : ∑ r : Fin p, h ^ (r : ℕ) * c r ^ p = 0) :
    ∀ r, c r = 0 := by
  classical
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  by_contra hne
  push_neg at hne
  obtain ⟨r0, hr0⟩ := hne
  have hpos : (Finset.univ : Finset (Fin p)).Nonempty := ⟨r0, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun r : Fin p => v (h ^ (r : ℕ) * c r ^ p)) hpos
  have hfne : ∀ r, c r ≠ 0 → v (h ^ (r : ℕ) * c r ^ p) ≠ 0 := fun r hr =>
    (Valuation.ne_zero_iff v).2 (mul_ne_zero (pow_ne_zero _ hh0) (pow_ne_zero _ hr))
  have hcj : c j ≠ 0 := by
    intro h0
    have hle := hj r0 (Finset.mem_univ _)
    rw [h0, zero_pow hp.out.ne_zero, mul_zero, map_zero] at hle
    exact hfne r0 hr0 (le_antisymm hle zero_le')
  have hlt : ∀ i ∈ (Finset.univ : Finset (Fin p)) \ {j},
      v (h ^ (i : ℕ) * c i ^ p) < v (h ^ (j : ℕ) * c j ^ p) := by
    intro i hi
    have hij : i ≠ j := by simpa using hi
    refine lt_of_le_of_ne (hj i (Finset.mem_univ _)) ?_
    by_cases hci : c i = 0
    · rw [hci, zero_pow hp.out.ne_zero, mul_zero, map_zero]
      exact (hfne j hcj).symm
    obtain ⟨a, ha⟩ := val_pow_mul_pow v hv hci (i : ℕ) p
    obtain ⟨b, hb⟩ := val_pow_mul_pow v hv hcj (j : ℕ) p
    rw [ha, hb, Ne, WithZero.exp_inj]
    intro heq
    have hd : (p : ℤ) ∣ (j : ℤ) - (i : ℤ) := ⟨b - a, by linear_combination heq⟩
    have hz := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]
      have := i.isLt
      have := j.isLt
      constructor <;> omega)
    exact hij (Fin.ext (by omega))
  have hsum := Valuation.map_sum_eq_of_lt v (Finset.mem_univ j) hlt
  rw [hc, map_zero] at hsum
  exact hfne j hcj hsum.symm

end Val

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_Sep2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Sep2` (separating elements; Mathlib only)

* `fp K F p`: the field of `p`-th powers of `F`, as an intermediate field over the perfect field `K`;
* `adjoin_fp_eq_top`, `finrank_fp_le`: `F = F^p⟮x⟯` and `[F : F^p] ≤ p` when `F / K⟮x⟯` is separable;
* `exists_sum_pow`: every `y` is `Σ_{r<p} h^r c_r^p` when a valuation has `v h = exp (-1)`;
* `mem_range_of_sum_pow`, `isSeparable_of_sum_pow`: then `F` is separable over `K⟮h⟯`;
* **`isSeparable_adjoin_of_val`**: `F / K⟮h⟯` is separable for every `h` of valuation `exp (-1)` (any
  characteristic, `K` perfect, `F` finite separable over `K⟮x⟯`, `h` transcendental).
-/

set_option autoImplicit false

open IntermediateField Polynomial Module
open scoped WithZero

universe u

namespace RamanujanPetersson.JacComplete

section Fp

variable (K : Type*) (F : Type u) [Field K] [Field F] [Algebra K F] (p : ℕ) [Fact p.Prime]
  [CharP K p] [PerfectRing K p] [CharP F p]

/-- The field of `p`-th powers of `F`, as an intermediate field over the perfect field `K`. -/
noncomputable def fp : IntermediateField K F :=
  (frobenius F p).fieldRange.toIntermediateField fun k => by
    obtain ⟨k', hk'⟩ := surjective_frobenius K p k
    exact RingHom.mem_fieldRange.2 ⟨algebraMap K F k', by
      rw [← hk', frobenius_def, frobenius_def, map_pow]⟩

theorem mem_fp (y : F) : y ∈ fp K F p ↔ ∃ z : F, z ^ p = y := by
  change y ∈ (frobenius F p).fieldRange ↔ _
  simp only [RingHom.mem_fieldRange, frobenius_def]

/-- `F = F^p⟮x⟯` when `F` is separable over `K⟮x⟯`. -/
theorem adjoin_fp_eq_top (x : F) [Algebra.IsSeparable K⟮x⟯ F] : (fp K F p)⟮x⟯ = ⊤ := by
  let L : IntermediateField K F := ((fp K F p)⟮x⟯).restrictScalars K
  have hle : K⟮x⟯ ≤ L := IntermediateField.adjoin_simple_le_iff.2
    ((IntermediateField.mem_restrictScalars K).2 (IntermediateField.mem_adjoin_simple_self _ x))
  letI : Algebra K⟮x⟯ L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower K⟮x⟯ L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K⟮x⟯ L F
  have hmem : ∀ y : F, y ^ p ∈ L := fun y => (IntermediateField.mem_restrictScalars K).2
    (((fp K F p)⟮x⟯).algebraMap_mem ⟨y ^ p, (mem_fp K F p (y ^ p)).2 ⟨y, rfl⟩⟩)
  have : IsPurelyInseparable L F := (isPurelyInseparable_iff_pow_mem L p).2 fun y =>
    ⟨1, ⟨y ^ p ^ 1, by rw [pow_one]; exact hmem y⟩, rfl⟩
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨z, hz⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L F y
  rw [← hz]
  exact (IntermediateField.mem_restrictScalars K).1 z.2

/-- The element `x ^ p` of `F^p`. -/
theorem aeval_fp (x : F) :
    aeval x (X ^ p - C (⟨x ^ p, (mem_fp K F p (x ^ p)).2 ⟨x, rfl⟩⟩ : fp K F p)) = 0 := by
  simp

theorem isIntegral_fp (x : F) : IsIntegral (fp K F p) x :=
  ⟨_, monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero, by rw [← aeval_def]; exact aeval_fp K F p x⟩

theorem finrank_fp_eq (x : F) [Algebra.IsSeparable K⟮x⟯ F] :
    finrank (fp K F p) F = (minpoly (fp K F p) x).natDegree := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_fp K F p x), adjoin_fp_eq_top K F p x,
    IntermediateField.finrank_top']

/-- `[F : F^p] ≤ p`. -/
theorem finrank_fp_le (x : F) [Algebra.IsSeparable K⟮x⟯ F] : finrank (fp K F p) F ≤ p := by
  have hp : p.Prime := Fact.out
  rw [finrank_fp_eq K F p x]
  have h0 := X_pow_sub_C_ne_zero hp.pos (⟨x ^ p, (mem_fp K F p (x ^ p)).2 ⟨x, rfl⟩⟩ : fp K F p)
  have h1 := minpoly.degree_le_of_ne_zero (fp K F p) x h0 (aeval_fp K F p x)
  rw [degree_X_pow_sub_C hp.pos] at h1
  exact natDegree_le_of_degree_le h1

theorem finiteDimensional_fp (x : F) [Algebra.IsSeparable K⟮x⟯ F] : FiniteDimensional (fp K F p) F :=
  Module.finite_of_finrank_pos (by
    rw [finrank_fp_eq K F p x]; exact minpoly.natDegree_pos (isIntegral_fp K F p x))

/-- `1, h, ..., h^(p-1)` are independent over `F^p` when `v h = exp (-1)`. -/
theorem linearIndependent_pow_fp (v : Valuation F ℤᵐ⁰) {h : F} (hv : v h = WithZero.exp (-1 : ℤ)) :
    LinearIndependent (fp K F p) (fun r : Fin p => h ^ (r : ℕ)) := by
  have hp : p.Prime := Fact.out
  rw [Fintype.linearIndependent_iff]
  intro g hg r
  choose c hc using fun r => (mem_fp K F p _).1 (g r).2
  have h0 := eq_zero_of_sum_pow_mul p v hv c (by
    rw [← hg]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Algebra.smul_def, IntermediateField.algebraMap_apply, ← hc r, mul_comm])
  have h1 : ((g r : F)) = 0 := by rw [← hc r, h0 r, zero_pow hp.ne_zero]
  exact_mod_cast h1

/-- **`F = F^p[h]`**: every `y` is `Σ_{r<p} h^r c_r^p`. -/
theorem exists_sum_pow (x : F) [Algebra.IsSeparable K⟮x⟯ F] (v : Valuation F ℤᵐ⁰) {h : F}
    (hv : v h = WithZero.exp (-1 : ℤ)) (y : F) :
    ∃ c : Fin p → F, ∑ r : Fin p, h ^ (r : ℕ) * c r ^ p = y := by
  have := finiteDimensional_fp K F p x
  have hli := linearIndependent_pow_fp K F p v hv
  have hcard := hli.fintype_card_le_finrank
  have hle := finrank_fp_le K F p x
  rw [Fintype.card_fin] at hcard
  have htop : Submodule.span (fp K F p) (Set.range fun r : Fin p => h ^ (r : ℕ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin]; omega)
  have hy : y ∈ Submodule.span (fp K F p) (Set.range fun r : Fin p => h ^ (r : ℕ)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
  choose c hc using fun r => (mem_fp K F p _).1 (g r).2
  refine ⟨c, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Algebra.smul_def, IntermediateField.algebraMap_apply, ← hc r, mul_comm]

end Fp

section Pinsep

variable {F : Type u} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- A finite purely inseparable `F / L` with `F = F^p[h]` and `h ∈ L` is trivial. -/
theorem mem_range_of_sum_pow {L : Type*} [Field L] [Algebra L F] [FiniteDimensional L F]
    [IsPurelyInseparable L F] [ExpChar L p] {h : F} (hh : h ∈ (algebraMap L F).range)
    (hsp : ∀ y : F, ∃ c : Fin p → F, ∑ r : Fin p, h ^ (r : ℕ) * c r ^ p = y) (y : F) :
    y ∈ (algebraMap L F).range := by
  obtain ⟨a, ha⟩ := hh
  let A : ℕ → Subalgebra L F := fun n => Algebra.adjoin L (Set.range fun z : F => z ^ p ^ n)
  have hA : ∀ n, ∀ y : F, y ∈ A n := by
    intro n
    induction n with
    | zero => intro y; exact Algebra.subset_adjoin ⟨y, by simp⟩
    | succ n ih =>
      intro y
      have hle : A n ≤ A (n + 1) := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨z, rfl⟩
        show z ^ p ^ n ∈ A (n + 1)
        obtain ⟨c, hc⟩ := hsp z
        rw [← hc, sum_pow_char_pow]
        refine Subalgebra.sum_mem _ fun r _ => ?_
        rw [mul_pow, ← pow_mul (c r) p (p ^ n), ← pow_succ' p n]
        refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨c r, rfl⟩)
        rw [← ha, ← map_pow, ← map_pow]
        exact Subalgebra.algebraMap_mem _ _
      exact hle (ih y)
  have hbot : A (IsPurelyInseparable.exponent L F) ≤ ⊥ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨b, hb⟩ := IsPurelyInseparable.exponent_def' L p z
    exact Algebra.mem_bot.2 ⟨b, hb⟩
  obtain ⟨b, hb⟩ := Algebra.mem_bot.1 (hbot (hA _ y))
  exact ⟨b, hb⟩

/-- `F = F^p[h]` and `F` finite over `K⟮h⟯` give `F / K⟮h⟯` separable. -/
theorem isSeparable_of_sum_pow (K : Type*) [Field K] [Algebra K F] {h : F} [FiniteDimensional K⟮h⟯ F]
    (hsp : ∀ y : F, ∃ c : Fin p → F, ∑ r : Fin p, h ^ (r : ℕ) * c r ^ p = y) :
    Algebra.IsSeparable K⟮h⟯ F := by
  have : Algebra.IsAlgebraic K⟮h⟯ F := Algebra.IsAlgebraic.of_finite _ _
  have : FiniteDimensional (separableClosure K⟮h⟯ F) F :=
    Module.Finite.of_restrictScalars_finite K⟮h⟯ (separableClosure K⟮h⟯ F) F
  have hh : h ∈ (algebraMap (separableClosure K⟮h⟯ F) F).range :=
    ⟨⟨h, (separableClosure K⟮h⟯ F).algebraMap_mem ⟨h, IntermediateField.mem_adjoin_simple_self K h⟩⟩,
      rfl⟩
  rw [← separableClosure.eq_top_iff]
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨a, rfl⟩ := mem_range_of_sum_pow p hh hsp y
  exact a.2

end Pinsep

section Main

variable {K : Type*} {F : Type u} [Field K] [Field F] [Algebra K F]

/-- **Separating elements.** `K` perfect, `F` finite separable over `K⟮x⟯`, `h` transcendental with
`v h = exp (-1)` for some valuation `v`: then `F` is separable over `K⟮h⟯`. -/
theorem isSeparable_adjoin_of_val [PerfectField K] {x h : F} [FiniteDimensional K⟮x⟯ F]
    [Algebra.IsSeparable K⟮x⟯ F] (hh : Transcendental K h) (v : Valuation F ℤᵐ⁰)
    (hv : v h = WithZero.exp (-1 : ℤ)) : Algebra.IsSeparable K⟮h⟯ F := by
  have := finiteDimensional_adjoin_of_transcendental (x := x) hh
  obtain _ | ⟨p, hp, hpK⟩ := CharP.exists' K
  · have : CharZero K⟮h⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮h⟯).injective
    have : Algebra.IsAlgebraic K⟮h⟯ F := Algebra.IsAlgebraic.of_finite _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  · have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
    exact isSeparable_of_sum_pow p K (exists_sum_pow K F p x v hv)

end Main

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PlaceVal =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PlaceVal` (dictionary D1, generic valuation theory)

* `val_le_one_of_isIntegral`: `w ≤ 1` on the image of `S` and `y` integral over `S` give `w y ≤ 1`;
* `val_eq_of_isEquiv`: two equivalent `ℤᵐ⁰`-valuations with `exp (-1)` uniformizers are equal;
* `valuation_eq_of_le`: if `w ≤ 1` on a Dedekind domain `R ⊆ F` and `w = 1` off the prime `p`, then `v_p = w`;
* **`exists_heightOneSpectrum_valuation_eq`**: a normalized discrete valuation `w ≤ 1` on `R` is `v_p` for
  `p = {r | w r < 1}`.
-/

set_option autoImplicit false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

section PlaceVal

theorem val_le_one_of_isIntegral {F S : Type*} [Field F] [CommRing S] [Algebra S F] (w : Valuation F ℤᵐ⁰)
    (hS : ∀ s : S, w (algebraMap S F s) ≤ 1) {y : F} (hy : IsIntegral S y) : w y ≤ 1 := by
  obtain ⟨f, hm, hf⟩ := hy
  by_cases hn : f.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm hn, eval₂_one] at hf
    exact absurd hf one_ne_zero
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun w at hf
  simp only [Valuation.map_neg, map_pow] at hf
  contrapose! hf
  refine ne_of_lt (w.map_sum_lt ?_ ?_)
  · simp [hn, (hf.trans' (zero_lt_one)).ne']
  · simp only [Finset.mem_range, map_mul, map_pow]
    intro _ hi
    exact mul_lt_of_le_one_of_lt (hS _) <| pow_lt_pow_right₀ hf hi

/-- Equivalent `ℤᵐ⁰`-valuations with `exp (-1)` uniformizers are equal. -/
theorem val_eq_of_isEquiv {F : Type*} [Field F] {v w : Valuation F ℤᵐ⁰} (h : v.IsEquiv w)
    {π : F} (hπ : v π = WithZero.exp (-1 : ℤ)) {ϖ : F} (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) : v = w := by
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff v).1 (by rw [hπ]; exact WithZero.exp_ne_zero)
  have key : ∀ f : F, f ≠ 0 → w f = w π ^ (-(WithZero.log (v f))) := by
    intro f hf
    have hvf : v f = v (π ^ (-(WithZero.log (v f)))) := by
      rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul,
        show -WithZero.log (v f) * (-1 : ℤ) = WithZero.log (v f) by ring]
      exact (WithZero.exp_log ((Valuation.ne_zero_iff v).2 hf)).symm
    rw [h.eq_iff.1 hvf, map_zpow₀]
  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff w).2 hπ0
  have hwπ : w π = WithZero.exp (-1 : ℤ) := by
    have hl : w π = WithZero.exp (WithZero.log (w π)) := (WithZero.exp_log hwπ0).symm
    have hlt : w π < 1 := by
      have : v π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
      exact h.lt_one_iff_lt_one.1 this
    have hneg : WithZero.log (w π) < 0 := by
      rw [hl, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      exact hlt
    have hϖ0 : ϖ ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [hϖ]; exact WithZero.exp_ne_zero)
    have e := key ϖ hϖ0
    rw [hϖ, hl, ← WithZero.exp_zsmul, smul_eq_mul, WithZero.exp_inj] at e
    have hml : WithZero.log (v ϖ) * WithZero.log (w π) = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hml with ⟨_, h2⟩ | ⟨_, h2⟩
    · omega
    · rw [hl, h2]
  ext f
  by_cases hf : f = 0
  · rw [hf, map_zero, map_zero]
  rw [key f hf, hwπ, ← WithZero.exp_zsmul, smul_eq_mul,
    show -WithZero.log (v f) * (-1 : ℤ) = WithZero.log (v f) by ring]
  exact (WithZero.exp_log ((Valuation.ne_zero_iff v).2 hf)).symm

/-- If `w ≤ 1` on `R` and `w = 1` off `p`, then `v_p = w` (a DVR is maximal among proper valuation subrings). -/
theorem valuation_eq_of_le {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (p : HeightOneSpectrum R) (w : Valuation F ℤᵐ⁰) {ϖ : F}
    (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (hle : ∀ r : R, w (algebraMap R F r) ≤ 1)
    (hlt : ∀ r : R, r ∉ p.asIdeal → w (algebraMap R F r) = 1) : p.valuation F = w := by
  have hsub : HeightOneSpectrum.valuationSubringAtPrime F p ≤ w.valuationSubring := by
    rintro x ⟨a, s, hs, rfl⟩
    rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀, hlt s hs, inv_one, mul_one]
    exact hle a
  have hne : w.valuationSubring ≠ ⊤ := by
    intro htop
    have hmem : ϖ⁻¹ ∈ w.valuationSubring := by rw [htop]; exact ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
    omega
  have heq := ValuationSubring.eq_of_le_of_ne_top _ hsub hne
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at heq
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer F
  exact val_eq_of_isEquiv ((Valuation.isEquiv_iff_valuationSubring _ _).2 heq) hπ hϖ

/-- **A normalized discrete valuation `≤ 1` on a Dedekind domain `R` is the valuation of a height-one prime.** -/
theorem exists_heightOneSpectrum_valuation_eq {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (w : Valuation F ℤᵐ⁰) {ϖ : F} (hϖ : w ϖ = WithZero.exp (-1 : ℤ))
    (hle : ∀ r : R, w (algebraMap R F r) ≤ 1) : ∃ p : HeightOneSpectrum R, p.valuation F = w := by
  let I : Ideal R :=
    { carrier := {r | w (algebraMap R F r) < 1}
      add_mem' := fun {a b} ha hb => by
        show w (algebraMap R F (a + b)) < 1
        rw [map_add]
        exact lt_of_le_of_lt (w.map_add _ _) (max_lt ha hb)
      zero_mem' := by
        show w (algebraMap R F 0) < 1
        rw [map_zero, map_zero]
        exact zero_lt_one
      smul_mem' := fun c x hx => by
        show w (algebraMap R F (c • x)) < 1
        rw [smul_eq_mul, map_mul, map_mul]
        exact mul_lt_of_le_one_of_lt (hle c) hx }
  have hmemI : ∀ r : R, r ∈ I ↔ w (algebraMap R F r) < 1 := fun r => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmemI, map_one, map_one]
      exact lt_irrefl 1
    · intro a b hab
      rw [hmemI, map_mul, map_mul] at hab
      rw [hmemI, hmemI]
      rcases lt_or_eq_of_le (hle a) with ha | ha
      · exact Or.inl ha
      rcases lt_or_eq_of_le (hle b) with hb | hb
      · exact Or.inr hb
      rw [ha, hb, one_mul] at hab
      exact absurd hab (lt_irrefl 1)
  have hϖ0 : ϖ ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [hϖ]; exact WithZero.exp_ne_zero)
  have hne : I ≠ ⊥ := by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) ϖ
    have hb0 : algebraMap R F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    intro hbot
    have ha : a ∈ I := by
      rw [hmemI]
      have e : algebraMap R F a = ϖ * algebraMap R F b := by
        rw [← hab]
        field_simp
      rw [e, map_mul, hϖ]
      have h1 : WithZero.exp (-1 : ℤ) * w (algebraMap R F b) ≤ WithZero.exp (-1 : ℤ) := by
        first
          | exact mul_le_of_le_one_right' (hle b)
          | exact mul_le_of_le_one_right zero_le' (hle b)
      exact lt_of_le_of_lt h1 (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    rw [hbot, Ideal.mem_bot] at ha
    rw [ha, map_zero, zero_div] at hab
    exact hϖ0 hab.symm
  refine ⟨⟨I, hprime, hne⟩, valuation_eq_of_le _ w hϖ hle fun r hr => ?_⟩
  exact le_antisymm (hle r) (not_lt.1 hr)

end PlaceVal

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacRRFam_C =====
section

/-!
# Places over an arbitrary field, part C: dimensions of quotients of Dedekind domains

For a Dedekind domain `S` that is an algebra over a field `K`, `dq K I = dim_K (S ⧸ I)` (in `ℕ∞`)
is additive on products of nonzero ideals (`dq_mul`), so `dim_K S/(a) = Σ_P cnt_P(a) deg P`
(`finrank_quot_span`). This replaces the cardinality counting of S3-Places (which needs a finite
field). Also: `dim_K Oinf/(y) = -intDegree y` for the valuation ring at infinity of `K(x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.RR (cd cd_add cd_sup_left cd_comap cd_eq_zero_iff cd_eq_map)
open RamanujanPetersson.Places (Oinf piInf ord cnt ord_algebraMap mem_Oinf_iff' coe_piInf X_ne_zero' span_piInf_isMaximal residue_bijective piInf_ne_zero)

section DimQuot

variable (K : Type*) [Field K] {S : Type*} [CommRing S] [Algebra K S]

/-- `dim_K (S ⧸ I)` in `ℕ∞`. -/
noncomputable def dq (I : Ideal S) : ℕ∞ := cd (I.restrictScalars K) ⊤

variable {K}

theorem dq_eq_rank (I : Ideal S) : dq K I = Cardinal.toENat (Module.rank K (S ⧸ I)) := by
  unfold dq
  rw [cd_eq_map, Submodule.map_top, Submodule.range_mkQ, rank_top,
    (Submodule.Quotient.restrictScalarsEquiv K I).rank_eq]

theorem dq_top : dq K (⊤ : Ideal S) = 0 := by
  unfold dq; exact cd_eq_zero_iff.2 fun x _ => Submodule.mem_top

variable [IsDedekindDomain S]

theorem dq_mul_prime {I P : Ideal S} (hI' : I ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    dq K (I * P) = dq K I + dq K P := by
  have hI : I ≠ 0 := by rwa [Ideal.zero_eq_bot]
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have hle : I * P ≤ I := Ideal.mul_le_left
  have hlt : I * P < I := by
    refine lt_of_le_of_ne hle fun h => hP.ne_top ?_
    have h2 : I * P = I * ⊤ := by rw [Ideal.mul_top]; exact h
    exact mul_left_cancel₀ hI h2
  obtain ⟨x, hxI, hxIP⟩ := SetLike.exists_of_lt hlt
  have hsup : Ideal.span {x} ⊔ I * P = I := by
    have hJle : Ideal.span {x} ⊔ I * P ≤ I :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).2 hxI) hle
    obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hJle
    have hPQ : P ≤ Q := by
      have h1 : I * Q ∣ I * P := Ideal.dvd_iff_le.2 (le_sup_right.trans hQ.le)
      exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left hI).1 h1)
    by_cases hQt : Q = ⊤
    · rw [hQ, hQt, Ideal.mul_top]
    · have hPQ' := hmax.eq_of_le hQt hPQ
      have hx' : x ∈ Ideal.span {x} ⊔ I * P :=
        Submodule.mem_sup_left (Ideal.mem_span_singleton_self x)
      rw [hQ, ← hPQ'] at hx'
      exact absurd hx' hxIP
  -- the `K`-linear map `s ↦ x * s`
  set φ : S →ₗ[K] S := LinearMap.mulLeft K x with hφ
  have hrange : I.restrictScalars K = (I * P).restrictScalars K ⊔ LinearMap.range φ := by
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ Ideal.span {x} ⊔ I * P := hsup.symm ▸ hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [add_comm]
      exact Submodule.add_mem_sup hb ⟨s, by simp [hφ, mul_comm]⟩
    · refine sup_le (fun y hy => hle hy) ?_
      rintro _ ⟨s, rfl⟩
      exact I.mul_mem_right s hxI
  have hcomap : ((I * P).restrictScalars K).comap φ = P.restrictScalars K := by
    ext s
    simp only [Submodule.mem_comap, Submodule.restrictScalars_mem, hφ, LinearMap.mulLeft_apply]
    constructor
    · intro hs
      by_contra hsP
      obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
      apply hxIP
      have e : x = t * (x * s) + x * i := by
        calc x = x * (t * s + i) := by rw [hti, mul_one]
          _ = t * (x * s) + x * i := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ t hs) (Ideal.mul_mem_mul hxI hi)
    · intro hs
      exact Ideal.mul_mem_mul hxI hs
  have h12 : (I * P).restrictScalars K ≤ I.restrictScalars K := fun y hy => hle hy
  unfold dq
  rw [← cd_add h12 le_top, add_comm]
  congr 1
  rw [hrange, cd_sup_left, LinearMap.range_eq_map, ← cd_comap, hcomap]

theorem dq_mul {I J : Ideal S} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : dq K (I * J) = dq K I + dq K J := by
  have key : ∀ J : Ideal S, J ≠ ⊥ → ∀ I : Ideal S, I ≠ ⊥ → dq K (I * J) = dq K I + dq K J := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime J ?_ ?_ ?_
    · intro h; exact absurd Ideal.zero_eq_bot h
    · intro x hx _ I _
      rw [Ideal.isUnit_iff.1 hx, Ideal.mul_top, dq_top, add_zero]
    · intro a p ha hp ih _ I hI
      have hp0 : p ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero
      have ha' : a ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact ha
      have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hp0).1 hp
      have hI0 : I ≠ 0 := by rwa [Ideal.zero_eq_bot]
      have hIa : I * a ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact mul_ne_zero hI0 ha
      rw [show I * (p * a) = (I * a) * p by ring, dq_mul_prime hIa hpP hp0, ih ha' I hI,
        mul_comm p a, dq_mul_prime ha' hpP hp0, ← add_assoc]
  exact key J hJ I hI

theorem dq_pow {P : Ideal S} (hP : P ≠ ⊥) (n : ℕ) : dq K (P ^ n) = n * dq K P := by
  induction n with
  | zero => simp [dq_top]
  | succ n ih =>
    have hP0 : P ≠ 0 := by rwa [Ideal.zero_eq_bot]
    have hn : P ^ n ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact pow_ne_zero n hP0
    rw [pow_succ, dq_mul hn hP, ih]
    push_cast; ring

theorem dq_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal S) (hf : ∀ i ∈ s, f i ≠ ⊥) :
    dq K (∏ i ∈ s, f i) = ∑ i ∈ s, dq K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dq_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      dq_mul (hf a (Finset.mem_insert_self a s))
        (by
          rw [← Ideal.zero_eq_bot]
          exact Finset.prod_ne_zero_iff.2 fun i hi => by
            rw [Ideal.zero_eq_bot]; exact hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end DimQuot

end RamanujanPetersson.PlacesK


end

-- ===== S4.Def_RP_JacRRFam_D =====
section

/-!
# Places over an arbitrary field, part D: Dedekind domains with finite-dimensional quotients

`FDQ K S`: every `S ⧸ (a)`, `a ≠ 0`, is finite-dimensional over `K`. Then `deg K P = dim_K S/P > 0`,
`ord`, `divS` (Fintype-free copies of S3-Places), and `dim_K S/(a) = Σ_P cnt_P(a) deg P`
(`finrank_quot_span`). For `Oinf K`: `dim_K Oinf/(y) = -intDegree y` (`finrank_quot_Oinf`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.Places (Oinf piInf ord cnt deg degS mem_Oinf_iff' coe_piInf X_ne_zero' span_piInf_isMaximal residue_bijective piInf_ne_zero)

section Generic

variable (K : Type*) [Field K] (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra K S]

/-- Nonzero principal quotients are finite-dimensional over `K`. -/
class FDQ : Prop where
  finite : ∀ a : S, a ≠ 0 → Module.Finite K (S ⧸ Ideal.span {a})

variable {K S}

theorem moduleFinite_residue [FDQ K S] (P : HeightOneSpectrum S) :
    Module.Finite K (S ⧸ P.asIdeal) := by
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := FDQ.finite (K := K) a ha0
  have hle : Ideal.span {a} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 haP
  exact Module.Finite.of_surjective ((Ideal.Quotient.factorₐ K hle).toLinearMap)
    (Ideal.Quotient.factor_surjective hle)

theorem dq_eq_finrank {I : Ideal S} (h : Module.Finite K (S ⧸ I)) :
    dq K I = (finrank K (S ⧸ I) : ℕ∞) := by
  rw [dq_eq_rank, ← Module.finrank_eq_rank]
  simp

theorem dq_asIdeal [FDQ K S] (P : HeightOneSpectrum S) : dq K P.asIdeal = (deg K P : ℕ∞) :=
  dq_eq_finrank (moduleFinite_residue P)

theorem deg_pos [FDQ K S] (P : HeightOneSpectrum S) : 0 < deg K P := by
  have := moduleFinite_residue (K := K) P
  have : Nontrivial (S ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  exact Module.finrank_pos

variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]

theorem ord_algebraMap (P : HeightOneSpectrum S) {a : S} (ha : a ≠ 0) :
    ord P (algebraMap S L a) = cnt P a := by
  rw [ord, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg ha,
    WithZero.log_exp, neg_neg, cnt]

theorem ord_mul (P : HeightOneSpectrum S) {f g : L} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f * g) = ord P f + ord P g := by
  rw [ord, ord, ord, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem ord_div (P : HeightOneSpectrum S) {f g : L} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f / g) = ord P f - ord P g := by
  rw [ord, ord, ord, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem finite_cnt {a : S} (ha : a ≠ 0) : {P : HeightOneSpectrum S | cnt P a ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.mp (Associates.finite_factors (I := Ideal.span {a})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]))
  refine h.subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, cnt] at hP ⊢
  exact_mod_cast hP

theorem finite_ord (f : L) : {P : HeightOneSpectrum S | ord P f ≠ 0}.Finite := by
  by_cases hf : f = 0
  · simp [hf, ord]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  have ha' : algebraMap S L a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr ha0
  have hb' : algebraMap S L b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hb0
  refine ((finite_cnt ha0).union (finite_cnt hb0)).subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hP ⊢
  rw [ord_div P ha' hb', ord_algebraMap P ha0, ord_algebraMap P hb0] at hP
  by_contra hcon
  push Not at hcon
  rw [hcon.1, hcon.2] at hP
  simp at hP

variable (S) in
/-- The divisor of `f` restricted to the places of `S`. -/
noncomputable def divS (f : L) : HeightOneSpectrum S →₀ ℤ :=
  Finsupp.ofSupportFinite (fun P => ord P f) (finite_ord f)

@[simp] theorem divS_apply (f : L) (P : HeightOneSpectrum S) : divS S f P = ord P f := rfl

theorem degS_sub (D E : HeightOneSpectrum S →₀ ℤ) : degS K (D - E) = degS K D - degS K E := by
  unfold degS
  rw [Finsupp.sum_sub_index]
  intro P a b; ring

theorem divS_div {f g : L} (hf : f ≠ 0) (hg : g ≠ 0) : divS S (f / g) = divS S f - divS S g := by
  ext P; simp [ord_div P hf hg]

/-- `dim_K S/(a) = Σ_P cnt_P(a) deg P`, in `ℕ∞`. -/
theorem dq_span_eq [FDQ K S] {a : S} (ha : a ≠ 0) :
    dq K (Ideal.span {a}) = ((∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg K P : ℕ) : ℕ∞) := by
  have hI : Ideal.span {a} ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hfac := Ideal.finprod_heightOneSpectrum_factorization hI
  rw [finprod_eq_prod_of_mulSupport_subset (s := (finite_cnt ha).toFinset)] at hfac
  · conv_lhs => rw [← hfac]
    rw [dq_prod _ _ fun P _ => by
      simp only [HeightOneSpectrum.maxPowDividing]
      rw [← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact P.ne_bot)]
    push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [HeightOneSpectrum.maxPowDividing]
    rw [dq_pow P.ne_bot, dq_asIdeal, cnt]
  · intro P hP
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    apply hP
    simp [HeightOneSpectrum.maxPowDividing, cnt] at h0 ⊢
    simp [h0]

theorem finrank_quot_span [FDQ K S] {a : S} (ha : a ≠ 0) :
    finrank K (S ⧸ Ideal.span {a}) = ∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg K P := by
  have h := dq_span_eq (K := K) ha
  rw [dq_eq_finrank (FDQ.finite a ha)] at h
  exact_mod_cast h

theorem degS_divS_algebraMap {a : S} (ha : a ≠ 0) :
    degS K (divS S (algebraMap S L a)) =
      ((∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg K P : ℕ) : ℤ) := by
  unfold degS
  rw [Finsupp.sum_of_support_subset (s := (finite_cnt ha).toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [divS_apply, ord_algebraMap P ha]
  · intro P hP
    simp only [Finsupp.mem_support_iff, divS_apply, ord_algebraMap P ha] at hP
    simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    exact_mod_cast hP
  · intro P _; simp

theorem finite_of_dq_eq {I : Ideal S} {n : ℕ} (h : dq K I = n) :
    Module.Finite K (S ⧸ I) ∧ finrank K (S ⧸ I) = n := by
  rw [dq_eq_rank, Cardinal.toENat_eq_natCast] at h
  exact ⟨Module.rank_lt_aleph0_iff.1 (h ▸ Cardinal.natCast_lt_aleph0), Module.finrank_eq_of_rank_eq h⟩

end Generic

section OinfDim

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

/-- The order at infinity of a nonzero element of `Oinf` is `-intDegree`. -/
theorem span_eq_pow {y : Oinf K} (hy : y ≠ 0) :
    Ideal.span {y} = Ideal.span {piInf K} ^ (-(y : RatFunc K).intDegree).toNat := by
  set n := (-(y : RatFunc K).intDegree).toNat
  have hy' : (y : RatFunc K) ≠ 0 := fun h => hy (Subtype.ext h)
  have hdeg := (mem_Oinf_iff' K hy').mp y.2
  have hn : (n : ℤ) = -(y : RatFunc K).intDegree := Int.toNat_of_nonneg (by omega)
  have hXn : (RatFunc.X ^ n : RatFunc K).intDegree = n := by
    rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_pow]
  have hu0 : (y : RatFunc K) * RatFunc.X ^ n ≠ 0 := mul_ne_zero hy' (pow_ne_zero _ (X_ne_zero' K))
  have hudeg : ((y : RatFunc K) * RatFunc.X ^ n).intDegree = 0 := by
    rw [RatFunc.intDegree_mul hy' (pow_ne_zero _ (X_ne_zero' K)), hXn]
    omega
  have hu : (y : RatFunc K) * RatFunc.X ^ n ∈ Oinf K := (mem_Oinf_iff' K hu0).mpr hudeg.le
  have hui : ((y : RatFunc K) * RatFunc.X ^ n)⁻¹ ∈ Oinf K :=
    (mem_Oinf_iff' K (inv_ne_zero hu0)).mpr (by rw [RatFunc.intDegree_inv, hudeg]; simp)
  let u : Oinf K := ⟨_, hu⟩
  have h1 : u * ⟨_, hui⟩ = 1 := by
    ext
    show ((y : RatFunc K) * RatFunc.X ^ n) * ((y : RatFunc K) * RatFunc.X ^ n)⁻¹ = 1
    exact mul_inv_cancel₀ hu0
  have hunit : IsUnit u := isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hyu : y = u * piInf K ^ n := by
    ext
    simp only [u, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_piInf]
    rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (X_ne_zero' K)), mul_one]
  rw [hyu, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit hunit]

theorem span_piInf_ne_bot : Ideal.span {piInf K} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact piInf_ne_zero K

theorem dq_span_piInf : dq K (Ideal.span {piInf K}) = 1 := by
  have hb := residue_bijective K
  rw [← Ideal.Quotient.algebraMap_eq] at hb
  let e := LinearEquiv.ofBijective (Algebra.linearMap K (Oinf K ⧸ Ideal.span {piInf K})) hb
  rw [dq_eq_rank, ← e.rank_eq, rank_self]
  simp

variable {K}

/-- `dim_K Oinf/(y) = -intDegree y`, in `ℕ∞`. -/
theorem dq_span_Oinf {y : Oinf K} (hy : y ≠ 0) :
    dq K (Ideal.span {y}) = ((-(y : RatFunc K).intDegree).toNat : ℕ∞) := by
  rw [span_eq_pow K hy, dq_pow (span_piInf_ne_bot K), dq_span_piInf, mul_one]

theorem finrank_quot_Oinf {y : Oinf K} (hy : y ≠ 0) :
    Module.Finite K (Oinf K ⧸ Ideal.span {y}) ∧
      finrank K (Oinf K ⧸ Ideal.span {y}) = (-(y : RatFunc K).intDegree).toNat :=
  finite_of_dq_eq (dq_span_Oinf hy)

end OinfDim

end RamanujanPetersson.PlacesK


end

-- ===== S4.Def_RP_JacRRFam_E =====
section

/-!
# Places over an arbitrary field, part E: function fields over `K` and the product formula

For a function field `F / K(x)` over an arbitrary field `K`: the rings `Rfin`, `Rinf` of S3-Places have
finite-dimensional quotients (`FDQ`), `dim_K Rfin/(a) = deg_x N(a)`, `dim_K Rinf/(c) = -deg_x N(c)`
(Smith normal form over the PIDs `K[X]` and `Oinf K`), hence the product formula
`degS_fin_add_degS_inf` with no finiteness assumption on `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.Places (Oinf piInf ord cnt deg degS mem_Oinf_iff' Rfin Rinf)

section Smith

variable (K : Type*) [Field K] {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
  [IsDedekindDomain R] [Algebra K R]
  {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra K S] [IsScalarTower K R S]
  [Module.Free R S] [Module.Finite R S]

/-- Smith normal form: `S/(f)` is finite-dimensional with `dim_K S/(f) = dim_K R/(N f)`. -/
theorem dq_span_eq_dq_norm (hR : ∀ d : R, d ≠ 0 → Module.Finite K (R ⧸ Ideal.span {d}))
    {f : S} (hf : f ≠ 0) :
    Module.Finite K (S ⧸ Ideal.span {f}) ∧
      dq K (Ideal.span {f}) = dq K (Ideal.span {Algebra.norm R f}) := by
  classical
  let b := Module.Free.chooseBasis R S
  have hI : Ideal.span {f} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.2 hf
  have : ∀ i, Module.Finite K (R ⧸ Ideal.span {(Ideal.span {f}).smithCoeffs b hI i}) :=
    fun i => hR _ (Ideal.smithCoeffs_ne_zero b _ hI i)
  have hfin : Module.Finite K (S ⧸ Ideal.span {f}) :=
    Module.Finite.equiv (Ideal.quotientEquivDirectSum K b hI).symm
  refine ⟨hfin, ?_⟩
  rw [dq_eq_finrank hfin, Ideal.finrank_quotient_eq_sum K hI b,
    Ideal.span_singleton_eq_span_singleton.2 (associated_norm_prod_smith b hf),
    ← Ideal.prod_span_singleton,
    dq_prod _ _ fun i _ => Ideal.span_singleton_eq_bot.not.2 (Ideal.smithCoeffs_ne_zero b _ hI i),
    Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => (dq_eq_finrank (hR _ (Ideal.smithCoeffs_ne_zero b _ hI i))).symm

end Smith

theorem moduleFinite_polyQuot {K : Type*} [Field K] {d : K[X]} (hd : d ≠ 0) :
    Module.Finite K (K[X] ⧸ Ideal.span {d}) :=
  PowerBasis.finite (AdjoinRoot.powerBasis hd)

section FunctionFieldSetup

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

instance fdq_Rfin : FDQ K (Rfin K F) where
  finite _ ha := (dq_span_eq_dq_norm K (R := K[X]) (fun _ hd => moduleFinite_polyQuot hd) ha).1

instance fdq_Rinf : FDQ K (Rinf K F) where
  finite _ hc := (dq_span_eq_dq_norm K (R := Oinf K) (fun _ hd => (finrank_quot_Oinf hd).1) hc).1

theorem norm_bridge_fin (a : Rfin K F) :
    algebraMap K[X] (RatFunc K) (Algebra.norm K[X] a) =
      Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a) := by
  have := IsIntegralClosure.isLocalization K[X] (RatFunc K) F (Rfin K F)
  exact (Algebra.norm_localization K[X] (nonZeroDivisors K[X]) (Rₘ := RatFunc K) (Sₘ := F) a).symm

theorem norm_bridge_inf (c : Rinf K F) :
    ((Algebra.norm (Oinf K) c : Oinf K) : RatFunc K) =
      Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c) := by
  have := IsIntegralClosure.isLocalization (Oinf K) (RatFunc K) F (Rinf K F)
  exact (Algebra.norm_localization (Oinf K) (nonZeroDivisors (Oinf K)) (Rₘ := RatFunc K) (Sₘ := F) c).symm

variable {K F}

/-- Finite part: `deg (div a)|_fin = deg_x N(a)`. -/
theorem degS_fin {a : Rfin K F} (ha : a ≠ 0) :
    degS K (divS (Rfin K F) (algebraMap (Rfin K F) F a)) =
      (Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a)).intDegree := by
  have h1 := finrank_quot_span (K := K) (S := Rfin K F) ha
  have h2 := finrank_quotient_span_eq_natDegree_norm (F := K)
    (Module.Free.chooseBasis K[X] (Rfin K F)) ha
  rw [degS_divS_algebraMap ha, ← h1, h2, ← norm_bridge_fin, RatFunc.intDegree_polynomial]

/-- Infinite part: `deg (div c)|_inf = -deg_x N(c)`. -/
theorem degS_inf {c : Rinf K F} (hc : c ≠ 0) :
    degS K (divS (Rinf K F) (algebraMap (Rinf K F) F c)) =
      -(Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c)).intDegree := by
  have hN : Algebra.norm (Oinf K) c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc
  have hN' : ((Algebra.norm (Oinf K) c : Oinf K) : RatFunc K) ≠ 0 := fun h => hN (Subtype.ext h)
  have h1 := finrank_quot_span (K := K) (S := Rinf K F) hc
  have h2 := (dq_span_eq_dq_norm K (R := Oinf K) (fun _ hd => (finrank_quot_Oinf hd).1) hc).2
  rw [dq_eq_finrank (FDQ.finite c hc), dq_span_Oinf hN] at h2
  have h3 : finrank K (Rinf K F ⧸ Ideal.span {c}) =
      (-((Algebra.norm (Oinf K) c : Oinf K) : RatFunc K).intDegree).toNat := by exact_mod_cast h2
  have hle := (mem_Oinf_iff' K hN').mp (Algebra.norm (Oinf K) c).2
  rw [degS_divS_algebraMap hc, ← h1, h3, ← norm_bridge_inf]
  omega

/-- The product formula, split into the finite and the infinite places. -/
theorem degS_fin_add_degS_inf {f : F} (hf : f ≠ 0) :
    degS K (divS (Rfin K F) f) + degS K (divS (Rinf K F) f) = 0 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Rfin K F) f
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (Rinf K F) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hf hab.symm
  have hc0 : c ≠ 0 := by rintro rfl; simp at hcd; exact hf hcd.symm
  have inj1 := IsFractionRing.injective (Rfin K F) F
  have inj2 := IsFractionRing.injective (Rinf K F) F
  have ha' : algebraMap (Rfin K F) F a ≠ 0 := (map_ne_zero_iff _ inj1).mpr ha0
  have hb' : algebraMap (Rfin K F) F b ≠ 0 := (map_ne_zero_iff _ inj1).mpr hb0
  have hc' : algebraMap (Rinf K F) F c ≠ 0 := (map_ne_zero_iff _ inj2).mpr hc0
  have hd' : algebraMap (Rinf K F) F d ≠ 0 := (map_ne_zero_iff _ inj2).mpr hd0
  have e1 : Algebra.norm (RatFunc K) f * Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F b) =
      Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a) := by
    rw [← map_mul, ← hab, div_mul_cancel₀ _ hb']
  have e2 : Algebra.norm (RatFunc K) f * Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F d) =
      Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c) := by
    rw [← map_mul, ← hcd, div_mul_cancel₀ _ hd']
  have nf : Algebra.norm (RatFunc K) f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  have nb : Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F b) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb'
  have nd : Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F d) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hd'
  have i1 := congrArg RatFunc.intDegree e1
  have i2 := congrArg RatFunc.intDegree e2
  rw [RatFunc.intDegree_mul nf nb] at i1
  rw [RatFunc.intDegree_mul nf nd] at i2
  have p1 : degS K (divS (Rfin K F) f) =
      (Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a)).intDegree -
        (Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F b)).intDegree := by
    rw [← hab, divS_div ha' hb', degS_sub, degS_fin ha0, degS_fin hb0]
  have p2 : degS K (divS (Rinf K F) f) =
      -(Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c)).intDegree +
        (Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F d)).intDegree := by
    rw [← hcd, divS_div hc' hd', degS_sub, degS_inf hc0, degS_inf hd0]; ring
  rw [p1, p2]
  omega

end FunctionFieldSetup

end RamanujanPetersson.PlacesK


end

-- ===== S4.Def_RP_JacRRFam_F =====
section

/-!
# Places over an arbitrary field, part F: divisors, the product formula, the constant field

Fintype-free copies of S3-Places for a function field `F / K(x)` over an arbitrary field `K`
(reusing the S3 definitions `Place`, `Divisor`, `Place.deg`, `Place.ord`, `Divisor.deg`, `constField`):
`div`, `deg_div` (product formula), `finrank_constField_dvd`, `finiteDimensional_constField`,
`mem_constField_of_ord_nonneg` (no poles ⇒ constant), `ord_eq_zero_of_mem_constField`, `div_eq_zero_iff`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.Places (Oinf piInf ord cnt deg degS mem_Oinf_iff' Rfin Rinf Place Divisor constField valuation_le_one_of_neg_log_nonneg neg_log_nonneg_of_valuation_le_one neg_log_nonneg_algebraMap min_neg_log_le_neg_log_add)

section Divisors

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable {K F}

theorem Place.deg_pos (P : Place K F) : 0 < P.deg := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.PlacesK.deg_pos (K := K) P, _root_.RamanujanPetersson.PlacesK.deg_pos (K := K) P]

theorem Place.ord_mul (P : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f * g) = P.ord f + P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.PlacesK.ord_mul P hf hg, _root_.RamanujanPetersson.PlacesK.ord_mul P hf hg]

theorem Place.ord_div (P : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f / g) = P.ord f - P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.PlacesK.ord_div P hf hg, _root_.RamanujanPetersson.PlacesK.ord_div P hf hg]

theorem Divisor.deg_add (D E : Divisor K F) : Places.Divisor.deg (D + E) = D.deg + E.deg := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_add_index'] <;> intros <;> ring

theorem Divisor.deg_neg (D : Divisor K F) : Places.Divisor.deg (-D) = -D.deg := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_neg_index (fun _ => by ring), Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem Divisor.deg_sub (D E : Divisor K F) : Places.Divisor.deg (D - E) = D.deg - E.deg := by
  rw [sub_eq_add_neg, Divisor.deg_add, Divisor.deg_neg, sub_eq_add_neg]

theorem Divisor.deg_single (P : Place K F) (n : ℤ) : Places.Divisor.deg (Finsupp.single P n : Divisor K F) = n * P.deg := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_single_index (by ring)]

theorem Divisor.deg_sumElim (D : HeightOneSpectrum (Rfin K F) →₀ ℤ)
    (E : HeightOneSpectrum (Rinf K F) →₀ ℤ) :
    Places.Divisor.deg (D.sumElim E : Divisor K F) = degS K D + degS K E := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_sumElim]
  rfl

/-- The principal divisor of `f` (the zero divisor for `f = 0`). -/
noncomputable def div (f : F) : Divisor K F := (divS (Rfin K F) f).sumElim (divS (Rinf K F) f)

@[simp] theorem div_apply (f : F) (P : Place K F) : div f P = P.ord f := by
  rcases P with P | P <;> rfl

theorem div_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f * g) : Divisor K F) = div f + div g := by
  ext P
  simp only [div_apply, Finsupp.coe_add, Pi.add_apply, Place.ord_mul P hf hg]

theorem div_div {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f / g) : Divisor K F) = div f - div g := by
  ext P
  simp only [div_apply, Finsupp.coe_sub, Pi.sub_apply, Place.ord_div P hf hg]

/-- **Product formula**: a nonzero function has as many zeros as poles, counted with degrees. -/
theorem deg_div {f : F} (hf : f ≠ 0) : Places.Divisor.deg (div f : Divisor K F) = 0 := by
  rw [div, Divisor.deg_sumElim]
  exact degS_fin_add_degS_inf hf

end Divisors

section ConstantField

theorem moduleFinite_of_algHom (K : Type*) [Field K] {k S : Type*} [Field k] [Algebra K k]
    [CommRing S] [Algebra K S] (φ : k →ₐ[K] S) (P : Ideal S) [P.IsMaximal] [Module.Finite K (S ⧸ P)] :
    Module.Finite K k ∧ finrank K k ∣ finrank K (S ⧸ P) := by
  let : Field (S ⧸ P) := Ideal.Quotient.field P
  let ψ : k →ₐ[K] S ⧸ P := (Ideal.Quotient.mkₐ K P).comp φ
  let : Algebra k (S ⧸ P) := ψ.toRingHom.toAlgebra
  have : IsScalarTower K k (S ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have : Module.Finite k (S ⧸ P) := Module.Finite.of_restrictScalars_finite K k (S ⧸ P)
  have : Module.Finite K k :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom K k (S ⧸ P)).toLinearMap
      (algebraMap k (S ⧸ P)).injective
  exact ⟨inferInstance, Dvd.intro _ (Module.finrank_mul_finrank K k (S ⧸ P))⟩

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem algebraMap_Oinf_Rinf_injective : Function.Injective (algebraMap (Oinf K) (Rinf K F)) := by
  intro a b h
  have h2 : algebraMap (Oinf K) F a = algebraMap (Oinf K) F b := congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F,
    IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F b] at h2
  exact Subtype.ext ((algebraMap (RatFunc K) F).injective h2)

theorem isIntegral_of_mem_constField (c : constField K F) : IsIntegral K (c : F) :=
  (mem_algebraicClosure_iff.mp c.2).isIntegral

/-- Constants are regular at the finite places. -/
def constToRfin : constField K F →ₐ[K] Rfin K F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField K F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Constants are regular at the infinite places. -/
def constToRinf : constField K F →ₐ[K] Rinf K F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField K F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem not_isField_Rinf : ¬ IsField (Rinf K F) := by
  rw [← Algebra.IsIntegral.isField_iff_isField (algebraMap_Oinf_Rinf_injective K F)]
  exact IsDiscreteValuationRing.not_isField _

/-- There is at least one place over `x = ∞`. -/
theorem nonempty_infPlace : Nonempty (HeightOneSpectrum (Rinf K F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Rinf K F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (not_isField_Rinf K F)⟩⟩

theorem finrank_constField_dvd (P : Place K F) : finrank K (constField K F) ∣ P.deg := by
  rcases P with P | P
  · haveI := P.isMaximal
    haveI := moduleFinite_residue (K := K) P
    exact (moduleFinite_of_algHom K (constToRfin K F) P.asIdeal).2
  · haveI := P.isMaximal
    haveI := moduleFinite_residue (K := K) P
    exact (moduleFinite_of_algHom K (constToRinf K F) P.asIdeal).2

instance finiteDimensional_constField : FiniteDimensional K (constField K F) := by
  obtain ⟨P⟩ := nonempty_infPlace K F
  have := P.isMaximal
  have := moduleFinite_residue (K := K) P
  exact (moduleFinite_of_algHom K (constToRinf K F) P.asIdeal).1

/-- A place of degree one forces the full constant field to be `K`. -/
theorem constField_eq_bot_of_deg_one {P : Place K F} (h : P.deg = 1) : constField K F = ⊥ :=
  IntermediateField.finrank_eq_one_iff.mp (Nat.dvd_one.mp (h ▸ finrank_constField_dvd K F P))

end ConstantField

section NoPoles

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem isIntegral_poly_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rfin K F), 0 ≤ ord P f) : IsIntegral K[X] f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

theorem isIntegral_Oinf_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rinf K F), 0 ≤ ord P f) : IsIntegral (Oinf K) f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

/-- A polynomial in `x` that is regular at `x = ∞` is a constant. -/
theorem mem_range_of_mem_Oinf {p : K[X]} (h : algebraMap K[X] (RatFunc K) p ∈ Oinf K) :
    algebraMap K[X] (RatFunc K) p ∈ Set.range (algebraMap K (RatFunc K)) := by
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  have hne : algebraMap K[X] (RatFunc K) p ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]
  have h2 := (mem_Oinf_iff' K hne).mp h
  rw [RatFunc.intDegree_polynomial] at h2
  have hdeg : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq,
    ← eq_C_of_natDegree_eq_zero hdeg]

/-- Integral over `K[x]` and over the valuation ring at `∞` implies integral over `K`. -/
theorem isIntegral_of_isIntegral_poly_Oinf {f : F} (h1 : IsIntegral K[X] f)
    (h2 : IsIntegral (Oinf K) f) : IsIntegral K f := by
  have e1 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc K) h1
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc K) h2
  have hl : minpoly (RatFunc K) f ∈ lifts (algebraMap K (RatFunc K)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have hc2 : (minpoly (RatFunc K) f).coeff n ∈ Oinf K := by
      rw [e2, coeff_map]
      exact SetLike.coe_mem _
    rw [e1, coeff_map] at hc2 ⊢
    exact mem_range_of_mem_Oinf K hc2
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic h1.tower_top)
  refine ⟨q, hmon, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap (RatFunc K), hq, minpoly.aeval]

/-- **A function without poles is a constant** (Riemann-Roch's `L(0) = k`). -/
theorem mem_constField_of_ord_nonneg {f : F} (h : ∀ P : Place K F, 0 ≤ P.ord f) :
    f ∈ constField K F :=
  mem_algebraicClosure_iff.mpr (isIntegral_of_isIntegral_poly_Oinf K F
    (isIntegral_poly_of_ord_nonneg K F fun P => h (Sum.inl P))
    (isIntegral_Oinf_of_ord_nonneg K F fun P => h (Sum.inr P))).isAlgebraic

/-- Constants have no poles. -/
theorem ord_nonneg_of_mem_constField {f : F} (hf : f ∈ constField K F) (P : Place K F) :
    0 ≤ P.ord f := by
  rcases P with P | P
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRfin K F ⟨f, hf⟩)
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRinf K F ⟨f, hf⟩)

theorem Place.ord_one (P : Place K F) : P.ord (1 : F) = 0 := by
  have h := Place.ord_mul P (one_ne_zero (α := F)) (one_ne_zero (α := F))
  rw [mul_one] at h
  omega

theorem Place.ord_add (P : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  rcases P with P | P
  exacts [min_neg_log_le_neg_log_add P hf hg hfg, min_neg_log_le_neg_log_add P hf hg hfg]

/-- Nonzero constants have neither zeros nor poles. -/
theorem ord_eq_zero_of_mem_constField {f : F} (hf : f ∈ constField K F) (hf0 : f ≠ 0)
    (P : Place K F) : P.ord f = 0 := by
  have h1 := ord_nonneg_of_mem_constField K F hf P
  have h2 := ord_nonneg_of_mem_constField K F (inv_mem hf) P
  have h3 : P.ord (f * f⁻¹) = P.ord f + P.ord f⁻¹ := Place.ord_mul P hf0 (inv_ne_zero hf0)
  rw [mul_inv_cancel₀ hf0, Place.ord_one] at h3
  omega

/-- Multiplying by a nonzero constant does not change orders. -/
theorem ord_const_mul {c f : F} (hc : c ∈ constField K F) (hc0 : c ≠ 0) (hf : f ≠ 0) (P : Place K F) :
    P.ord (c * f) = P.ord f := by
  rw [Place.ord_mul P hc0 hf, ord_eq_zero_of_mem_constField K F hc hc0, zero_add]

/-- `div f = 0` exactly for the nonzero constants. -/
theorem div_eq_zero_iff {f : F} (hf : f ≠ 0) :
    (div f : Divisor K F) = 0 ↔ f ∈ constField K F := by
  constructor
  · intro h
    apply mem_constField_of_ord_nonneg
    intro P
    have h' := congrArg (fun D : Divisor K F => D P) h
    simp only [div_apply, Finsupp.coe_zero, Pi.zero_apply] at h'
    omega
  · intro h
    ext P
    rw [div_apply, Finsupp.coe_zero, Pi.zero_apply, ord_eq_zero_of_mem_constField K F h hf P]

end NoPoles

end RamanujanPetersson.PlacesK


end

-- ===== S4.Def_RP_JacComplete_PlaceF =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PlaceF` (dictionary D1 for a function field `F / K(x)`)

* `placeVal P : Valuation F ℤᵐ⁰` (the valuation of a place), `ord_eq_neg_log`;
* `placeVal_algebraMap` (trivial on `K^×`), `exists_placeVal_unif` (normalized);
* `placeVal_inl_x_le` / `one_lt_placeVal_inr_x`: finite places see `x` as integral, infinite ones as a pole;
* **`placeVal_injective`** and **`exists_placeVal_eq`**: the places of `F` are exactly the normalized discrete
  valuations of `F` trivial on `K^×` (independent of the coordinate `x`);
* **`placeEquiv σ`** for `σ : F ≃ₐ[K] F'` (two function-field structures): a bijection of places with
  `ord_placeEquiv : (placeEquiv σ P).ord (σ f) = P.ord f`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Oinf piInf Rfin Rinf Place span_piInf_isMaximal mem_Oinf_iff')

section PlaceF

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The valuation of `F` attached to a place. -/
noncomputable def placeVal : Place K F → Valuation F ℤᵐ⁰ :=
  Sum.elim (fun P => P.valuation F) (fun Q => Q.valuation F)

@[simp] theorem placeVal_inl (P : HeightOneSpectrum (Rfin K F)) :
    placeVal (Sum.inl P : Place K F) = P.valuation F := rfl

@[simp] theorem placeVal_inr (Q : HeightOneSpectrum (Rinf K F)) :
    placeVal (Sum.inr Q : Place K F) = Q.valuation F := rfl

theorem ord_eq_neg_log (P : Place K F) (f : F) : P.ord f = -WithZero.log (placeVal P f) := by
  rcases P with P | P <;> rfl

theorem placeVal_le_one_of_isIntegral (P : Place K F) {y : F} (hy : IsIntegral K y) :
    placeVal P y ≤ 1 := by
  rcases P with P | Q
  · exact P.valuation_le_one (K := F) (⟨y, hy.tower_top⟩ : Rfin K F)
  · exact Q.valuation_le_one (K := F) (⟨y, hy.tower_top⟩ : Rinf K F)

/-- A place is trivial on the constants. -/
theorem placeVal_algebraMap (P : Place K F) {c : K} (hc : c ≠ 0) :
    placeVal P (algebraMap K F c) = 1 := by
  have h1 := placeVal_le_one_of_isIntegral P (isIntegral_algebraMap (R := K) (A := F) (x := c))
  have h2 := placeVal_le_one_of_isIntegral P (isIntegral_algebraMap (R := K) (A := F) (x := c⁻¹))
  have hne : placeVal P (algebraMap K F c) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero (algebraMap K F)).2 hc)
  rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 hne)] at h2
  exact le_antisymm h1 h2

theorem exists_placeVal_unif (P : Place K F) : ∃ ϖ : F, placeVal P ϖ = WithZero.exp (-1 : ℤ) := by
  rcases P with P | Q
  · exact P.valuation_exists_uniformizer F
  · exact Q.valuation_exists_uniformizer F

theorem placeVal_inl_x_le (P : HeightOneSpectrum (Rfin K F)) :
    placeVal (Sum.inl P : Place K F) (algebraMap K[X] F X) ≤ 1 :=
  P.valuation_le_one (K := F) (⟨algebraMap K[X] F X, isIntegral_algebraMap⟩ : Rfin K F)

theorem piInf_mem_comap (Q : HeightOneSpectrum (Rinf K F)) :
    piInf K ∈ Q.asIdeal.comap (algebraMap (Oinf K) (Rinf K F)) := by
  have := Q.isPrime
  have hne : Q.asIdeal.comap (algebraMap (Oinf K) (Rinf K F)) ≠ ⊥ := by
    obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hyQ (integralClosure.isIntegral y)
  have hmax := Ideal.IsPrime.isMaximal (Ideal.comap_isPrime (algebraMap (Oinf K) (Rinf K F)) Q.asIdeal) hne
  rw [(IsLocalRing.eq_maximalIdeal hmax).trans (IsLocalRing.eq_maximalIdeal (span_piInf_isMaximal K)).symm]
  exact Ideal.subset_span rfl

theorem one_lt_placeVal_inr_x (Q : HeightOneSpectrum (Rinf K F)) :
    1 < placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X) := by
  have hlt : Q.valuation F (algebraMap (Rinf K F) F (algebraMap (Oinf K) (Rinf K F) (piInf K))) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) Q
      (algebraMap (Oinf K) (Rinf K F) (piInf K))).2 (piInf_mem_comap Q)
  have e : algebraMap (Rinf K F) F (algebraMap (Oinf K) (Rinf K F) (piInf K)) = (algebraMap K[X] F X)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply (Oinf K) (Rinf K F) F,
      IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F]
    show algebraMap (RatFunc K) F (1 / RatFunc.X) = _
    rw [one_div, map_inv₀, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F]
  rw [e, map_inv₀] at hlt
  have hX : algebraMap K[X] F X ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) F, RatFunc.algebraMap_X]
    exact (_root_.map_ne_zero _).2 RatFunc.X_ne_zero
  have hx0 : Q.valuation F (algebraMap K[X] F X) ≠ 0 := (Valuation.ne_zero_iff _).2 hX
  exact (inv_lt_one₀ (zero_lt_iff.2 hx0)).1 hlt

theorem algebraMap_eq_aeval (p : K[X]) : algebraMap K[X] F p = aeval (algebraMap K[X] F X) p := by
  have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K K[X] F) (X : K[X]) p
  rw [Polynomial.aeval_X_left_apply] at h
  simpa using h.symm

section Range

variable (w : Valuation F ℤᵐ⁰) (hK : ∀ c : K, c ≠ 0 → w (algebraMap K F c) = 1)
include hK

theorem val_const_le (c : K) : w (algebraMap K F c) ≤ 1 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero]; exact zero_le'
  · exact (hK c hc).le

theorem val_aeval_le_one {y : F} (hy : w y ≤ 1) (p : K[X]) : w (aeval y p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine w.map_sum_le fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  exact mul_le_one' (val_const_le w hK _) (pow_le_one' hy _)

theorem val_aeval_of_one_lt {y : F} (hy : 1 < w y) {p : K[X]} (hp : p ≠ 0) :
    w (aeval y p) = w y ^ p.natDegree := by
  have hlead : w (p.coeff p.natDegree • y ^ p.natDegree) = w y ^ p.natDegree := by
    rw [Algebra.smul_def, map_mul, map_pow, coeff_natDegree, hK _ (leadingCoeff_ne_zero.2 hp), one_mul]
  have hy0 : w y ^ p.natDegree ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy))
  rw [aeval_eq_sum_range, Finset.sum_range_succ, Valuation.map_add_eq_of_lt_right, hlead]
  rw [hlead]
  refine w.map_sum_lt hy0 fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Algebra.smul_def, map_mul, map_pow]
  calc w (algebraMap K F (p.coeff i)) * w y ^ i ≤ w y ^ i := by
        first
          | exact mul_le_of_le_one_left' (val_const_le w hK _)
          | exact mul_le_of_le_one_left zero_le' (val_const_le w hK _)
    _ < w y ^ p.natDegree := pow_lt_pow_right₀ hy hi

theorem val_Oinf_le_one (hx : 1 < w (algebraMap K[X] F X)) (s : Oinf K) :
    w (algebraMap (Oinf K) F s) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F]
  set f : RatFunc K := algebraMap (Oinf K) (RatFunc K) s with hfdef
  by_cases hf : f = 0
  · rw [hf, map_zero, map_zero]; exact zero_le'
  have hdeg := (mem_Oinf_iff' K hf).1 s.2
  unfold RatFunc.intDegree at hdeg
  rw [← RatFunc.num_div_denom f, map_div₀, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F, map_div₀, algebraMap_eq_aeval f.num,
    algebraMap_eq_aeval f.denom, val_aeval_of_one_lt w hK hx (RatFunc.num_ne_zero hf),
    val_aeval_of_one_lt w hK hx f.denom_ne_zero]
  exact div_le_one_of_le₀ (pow_le_pow_right₀ hx.le (by omega)) zero_le'

/-- **Every normalized discrete valuation of `F` trivial on `K^×` is a place.** -/
theorem exists_placeVal_eq {ϖ : F} (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) :
    ∃ P : Place K F, placeVal P = w := by
  by_cases hx : w (algebraMap K[X] F X) ≤ 1
  · have hS : ∀ p : K[X], w (algebraMap K[X] F p) ≤ 1 := fun p => by
      rw [algebraMap_eq_aeval]; exact val_aeval_le_one w hK hx p
    obtain ⟨P, hP⟩ := exists_heightOneSpectrum_valuation_eq (R := Rfin K F) w hϖ
      (fun r => by
        have hr : IsIntegral K[X] (r : F) := by
          first
            | exact r.2
            | exact mem_integralClosure_iff.1 r.2
        exact val_le_one_of_isIntegral w hS hr)
    exact ⟨Sum.inl P, hP⟩
  · rw [not_le] at hx
    obtain ⟨Q, hQ⟩ := exists_heightOneSpectrum_valuation_eq (R := Rinf K F) w hϖ
      (fun r => by
        have hr : IsIntegral (Oinf K) (r : F) := by
          first
            | exact r.2
            | exact mem_integralClosure_iff.1 r.2
        exact val_le_one_of_isIntegral w (val_Oinf_le_one w hK hx) hr)
    exact ⟨Sum.inr Q, hQ⟩

end Range

/-- **Places are determined by their valuations.** -/
theorem placeVal_injective : Function.Injective (placeVal : Place K F → Valuation F ℤᵐ⁰) := by
  rintro (P | Q) (P' | Q') h
  · exact congrArg Sum.inl
      (HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) (Valuation.IsEquiv.of_eq h))
  · have h1 := placeVal_inl_x_le P
    rw [h] at h1
    exact absurd h1 (not_le.2 (one_lt_placeVal_inr_x Q'))
  · have h1 := placeVal_inl_x_le P'
    rw [← h] at h1
    exact absurd h1 (not_le.2 (one_lt_placeVal_inr_x Q))
  · exact congrArg Sum.inr
      (HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) (Valuation.IsEquiv.of_eq h))

section Equiv

variable {F' : Type*} [Field F'] [Algebra K F'] [Algebra K[X] F'] [Algebra (RatFunc K) F']
  [IsScalarTower K[X] (RatFunc K) F'] [IsScalarTower K K[X] F'] [FunctionField K F']
  [Algebra.IsSeparable (RatFunc K) F']

theorem exists_placeVal_comap (σ : F ≃ₐ[K] F') (P : Place K F) :
    ∃ P' : Place K F', placeVal P' = (placeVal P).comap (σ.symm : F' →+* F) := by
  obtain ⟨ϖ, hϖ⟩ := exists_placeVal_unif P
  refine exists_placeVal_eq _ (fun c hc => ?_) (ϖ := σ ϖ) ?_
  · rw [Valuation.comap_apply]
    have e : (σ.symm : F' →+* F) (algebraMap K F' c) = algebraMap K F c := σ.symm.commutes c
    rw [e]; exact placeVal_algebraMap P hc
  · rw [Valuation.comap_apply]
    have e : (σ.symm : F' →+* F) (σ ϖ) = ϖ := σ.symm_apply_apply ϖ
    rw [e, hϖ]

/-- The place of `F'` corresponding to a place of `F` under `σ`. -/
noncomputable def placeMap (σ : F ≃ₐ[K] F') (P : Place K F) : Place K F' :=
  (exists_placeVal_comap σ P).choose

theorem placeVal_placeMap (σ : F ≃ₐ[K] F') (P : Place K F) :
    placeVal (placeMap σ P) = (placeVal P).comap (σ.symm : F' →+* F) :=
  (exists_placeVal_comap σ P).choose_spec

theorem ord_placeMap (σ : F ≃ₐ[K] F') (P : Place K F) (f : F) : (placeMap σ P).ord (σ f) = P.ord f := by
  rw [ord_eq_neg_log, ord_eq_neg_log, placeVal_placeMap, Valuation.comap_apply]
  have e : (σ.symm : F' →+* F) (σ f) = f := σ.symm_apply_apply f
  rw [e]

/-- **Places do not depend on the function-field structure.** -/
noncomputable def placeEquiv (σ : F ≃ₐ[K] F') : Place K F ≃ Place K F' where
  toFun := placeMap σ
  invFun := placeMap σ.symm
  left_inv P := placeVal_injective <| by
    rw [placeVal_placeMap, placeVal_placeMap]
    ext f
    rw [Valuation.comap_apply, Valuation.comap_apply]
    have e : (σ.symm : F' →+* F) ((σ.symm.symm : F →+* F') f) = f := σ.symm_apply_apply f
    rw [e]
  right_inv P := placeVal_injective <| by
    rw [placeVal_placeMap, placeVal_placeMap]
    ext f
    rw [Valuation.comap_apply, Valuation.comap_apply]
    have e : (σ.symm.symm : F →+* F') ((σ.symm : F' →+* F) f) = f := σ.apply_symm_apply f
    rw [e]

@[simp] theorem placeEquiv_apply (σ : F ≃ₐ[K] F') (P : Place K F) : placeEquiv σ P = placeMap σ P := rfl

theorem ord_placeEquiv (σ : F ≃ₐ[K] F') (P : Place K F) (f : F) :
    (placeEquiv σ P).ord (σ f) = P.ord f :=
  ord_placeMap σ P f

theorem ord_placeEquiv_symm (σ : F ≃ₐ[K] F') (P : Place K F') (f : F) :
    ((placeEquiv σ).symm P).ord f = P.ord (σ f) := by
  conv_rhs => rw [← (placeEquiv σ).apply_symm_apply P]
  rw [ord_placeEquiv]

end Equiv

end PlaceF

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_GenF =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `GenF` (the synonym with coordinate `h`)

* `ratHom K hh : K(X) →ₐ[K] F`, `X ↦ h` (`h` transcendental), `ratEquiv K hh : K(X) ≃+* K⟮h⟯`;
* bridge for the package coordinate `x`: `FiniteDimensional K⟮x⟯ F`, `Algebra.IsSeparable K⟮x⟯ F`;
* `GenF K F h`: a type synonym of `F` with the function-field package whose coordinate is `h`
  (`genAlg_apply`, `genAlg_X`, `FunctionField`, separability from `Algebra.IsSeparable K⟮h⟯ F`);
* `genEquiv`, `genPlace` (places of `F` and of `GenF K F h`, preserving `ord`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IntermediateField

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place)

section RatHom

variable (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] {h : F}

theorem le_comap_aeval (hh : Transcendental K h) :
    nonZeroDivisors K[X] ≤ (nonZeroDivisors F).comap (aeval h : K[X] →ₐ[K] F) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.1 hh)

/-- The `K`-algebra map `K(X) → F`, `X ↦ h`. -/
noncomputable def ratHom (hh : Transcendental K h) : RatFunc K →ₐ[K] F :=
  RatFunc.liftAlgHom (aeval h) (le_comap_aeval K hh)

theorem ratHom_algebraMap (hh : Transcendental K h) (p : K[X]) :
    ratHom K hh (algebraMap K[X] (RatFunc K) p) = aeval h p := by
  have e := RatFunc.liftAlgHom_apply_div (aeval h) (le_comap_aeval K hh) p 1
  simp only [map_one, div_one] at e
  exact e

theorem ratHom_X (hh : Transcendental K h) : ratHom K hh RatFunc.X = h := by
  rw [← RatFunc.algebraMap_X, ratHom_algebraMap, aeval_X]

theorem aeval_mem_adjoin (p : K[X]) : aeval h p ∈ K⟮h⟯ :=
  IntermediateField.algebra_adjoin_le_adjoin K {h} (Polynomial.aeval_mem_adjoin_singleton K h)

theorem ratHom_mem (hh : Transcendental K h) (r : RatFunc K) : ratHom K hh r ∈ K⟮h⟯ := by
  have e : r = algebraMap K[X] (RatFunc K) r.num / algebraMap K[X] (RatFunc K) r.denom :=
    (RatFunc.num_div_denom r).symm
  rw [e, map_div₀, ratHom_algebraMap, ratHom_algebraMap]
  exact div_mem (aeval_mem_adjoin K _) (aeval_mem_adjoin K _)

/-- `K(X) → K⟮h⟯`. -/
noncomputable def ratRestr (hh : Transcendental K h) : RatFunc K →+* K⟮h⟯ :=
  (ratHom K hh).toRingHom.codRestrict K⟮h⟯ (ratHom_mem K hh)

theorem ratRestr_surjective (hh : Transcendental K h) : Function.Surjective (ratRestr K hh) := by
  intro z
  have hle : K⟮h⟯ ≤ (ratHom K hh).fieldRange :=
    IntermediateField.adjoin_simple_le_iff.2 (AlgHom.mem_fieldRange.2 ⟨_, ratHom_X K hh⟩)
  obtain ⟨r, hr⟩ := AlgHom.mem_fieldRange.1 (hle z.2)
  exact ⟨r, Subtype.ext hr⟩

/-- `K(X) ≅ K⟮h⟯` for transcendental `h`. -/
noncomputable def ratEquiv (hh : Transcendental K h) : RatFunc K ≃+* K⟮h⟯ :=
  RingEquiv.ofBijective (ratRestr K hh) ⟨(ratRestr K hh).injective, ratRestr_surjective K hh⟩

theorem ratEquiv_coe (hh : Transcendental K h) (r : RatFunc K) : (ratEquiv K hh r : F) = ratHom K hh r :=
  rfl

theorem ratHom_ratEquiv_symm (hh : Transcendental K h) (z : K⟮h⟯) :
    ratHom K hh ((ratEquiv K hh).symm z) = z :=
  congrArg Subtype.val ((ratEquiv K hh).apply_symm_apply z)

/-- Finiteness of `K(X) → F` from finiteness over `K⟮h⟯`. -/
theorem finite_ratHom (hh : Transcendental K h) [FiniteDimensional K⟮h⟯ F] :
    (ratHom K hh).toRingHom.Finite := by
  have h1 : (algebraMap K⟮h⟯ F).Finite := RingHom.finite_algebraMap.2 inferInstance
  have h2 : (ratEquiv K hh).toRingHom.Finite := RingHom.Finite.of_surjective _ (ratEquiv K hh).surjective
  have e : (ratHom K hh).toRingHom = (algebraMap K⟮h⟯ F).comp (ratEquiv K hh).toRingHom :=
    RingHom.ext fun _ => rfl
  rw [e]
  exact h1.comp h2

end RatHom

section Bridge

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
theorem transcendental_xF : Transcendental K (algebraMap K[X] F X) :=
  (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective K[X] F)).mpr
    (Polynomial.transcendental_X K)

theorem ratHom_xF : (ratHom K (transcendental_xF K F)).toRingHom = algebraMap (RatFunc K) F := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun p => ?_)
  show ratHom K (transcendental_xF K F) (algebraMap K[X] (RatFunc K) p) =
    algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p)
  rw [ratHom_algebraMap, ← IsScalarTower.algebraMap_apply]
  exact (algebraMap_eq_aeval p).symm

/-- The package coordinate: `F` is finite over `K⟮x⟯`. -/
instance finiteDimensional_adjoin_xF : FiniteDimensional K⟮algebraMap K[X] F X⟯ F := by
  have h1 : (algebraMap (RatFunc K) F).Finite := RingHom.finite_algebraMap.2 inferInstance
  have h2 : ((ratEquiv K (transcendental_xF K F)).symm.toRingHom).Finite :=
    RingHom.Finite.of_surjective _ (ratEquiv K (transcendental_xF K F)).symm.surjective
  have e : algebraMap K⟮algebraMap K[X] F X⟯ F =
      (algebraMap (RatFunc K) F).comp (ratEquiv K (transcendental_xF K F)).symm.toRingHom := by
    rw [← ratHom_xF]
    exact RingHom.ext fun z => (ratHom_ratEquiv_symm K (transcendental_xF K F) z).symm
  refine RingHom.finite_algebraMap.1 ?_
  rw [e]
  exact h1.comp h2

/-- The package coordinate: `F` is separable over `K⟮x⟯`. -/
instance isSeparable_adjoin_xF : Algebra.IsSeparable K⟮algebraMap K[X] F X⟯ F :=
  Algebra.IsSeparable.of_equiv_equiv (ratEquiv K (transcendental_xF K F)) (RingEquiv.refl F)
    (RingHom.ext fun r => by
      show ratHom K (transcendental_xF K F) r = algebraMap (RatFunc K) F r
      rw [← ratHom_xF]
      rfl)

end Bridge

section Gen

/-- The function field `F` with the coordinate `h` (a type synonym of `F`). -/
def GenF (K : Type*) (F : Type*) (_h : F) : Type _ := F

variable (K : Type*) [Field K] (F : Type*) [Field F] [Algebra K F] (h : F)

noncomputable instance : Field (GenF K F h) := inferInstanceAs (Field F)

noncomputable instance : Algebra K (GenF K F h) := inferInstanceAs (Algebra K F)

/-- The identification `F ≃ GenF K F h` (the identity map). -/
def genEquiv : F ≃ₐ[K] GenF K F h where
  toFun y := y
  invFun y := y
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable [hh : Fact (Transcendental K h)]

/-- The new structure map `K(X) → F`, `X ↦ h`. -/
noncomputable def genMap : RatFunc K →+* GenF K F h := (ratHom K hh.out).toRingHom

noncomputable instance : Algebra (RatFunc K) (GenF K F h) := (genMap K F h).toAlgebra

noncomputable instance : Algebra K[X] (GenF K F h) :=
  ((algebraMap (RatFunc K) (GenF K F h)).comp (algebraMap K[X] (RatFunc K))).toAlgebra

instance : IsScalarTower K[X] (RatFunc K) (GenF K F h) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance : IsScalarTower K K[X] (GenF K F h) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap K F a = ratHom K hh.out (algebraMap K[X] (RatFunc K) (algebraMap K K[X] a))
    rw [ratHom_algebraMap, AlgHom.commutes])

/-- The new structure map on polynomials: `p ↦ p(h)`. -/
theorem genAlg_apply (p : K[X]) : algebraMap K[X] (GenF K F h) p = genEquiv K F h (aeval h p) :=
  ratHom_algebraMap K hh.out p

instance [FiniteDimensional K⟮h⟯ F] : FunctionField K (GenF K F h) :=
  RingHom.finite_algebraMap.1 (finite_ratHom K hh.out)

instance [Algebra.IsSeparable K⟮h⟯ F] : Algebra.IsSeparable (RatFunc K) (GenF K F h) :=
  Algebra.IsSeparable.of_equiv_equiv (ratEquiv K hh.out).symm (genEquiv K F h).toRingEquiv
    (RingHom.ext fun z => ratHom_ratEquiv_symm K hh.out z)

end Gen

section GenPlace

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]
variable (h : F) [Fact (Transcendental K h)] [FiniteDimensional K⟮h⟯ F] [Algebra.IsSeparable K⟮h⟯ F]

/-- The places of `F` and of the synonym `GenF K F h` agree. -/
noncomputable def genPlace : Place K F ≃ Place K (GenF K F h) := placeEquiv (genEquiv K F h)

theorem ord_genPlace (P : Place K F) (f : F) : (genPlace h P).ord (genEquiv K F h f) = P.ord f :=
  ord_placeEquiv _ P f

end GenPlace

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacRRFam_G =====
section

/-!
# Riemann-Roch over an arbitrary field, part G: the local axioms for function fields over `K`

`ballK K P n = {f | v_P f ≤ exp n}` as a `K`-subspace, with codimension
`cd (ballK P n) (ballK P (n+1)) = deg P = dim_K S/P` (`cd_ballK`, the dimension version of
S3's `relIndex_ballG`). The data `ffDataK K F` of a function field `F / K(x)` over an arbitrary
field `K` satisfies the local axioms `AxiomsK0` (`ffDataK_axioms0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.RR

section LocalIndexK

variable (K : Type*) [Field K] {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra K S]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [IsScalarTower K S L]

/-- The `K`-subspace `{f | v_P f ≤ exp n}`. -/
def ballK (P : HeightOneSpectrum S) (n : ℤ) : Submodule K L where
  carrier := {f | P.valuation L f ≤ exp n}
  add_mem' {a b} ha hb := ((P.valuation L).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  smul_mem' c f hf := by
    show P.valuation L (c • f) ≤ exp n
    rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply K S L]
    exact (mul_le_of_le_one_left' (P.valuation_le_one _)).trans hf

variable {K}

theorem mem_ballK {P : HeightOneSpectrum S} {n : ℤ} {f : L} :
    f ∈ ballK K P n ↔ P.valuation L f ≤ exp n := Iff.rfl

theorem cd_ballK_neg_one [PlacesK.FDQ K S] (P : HeightOneSpectrum S) :
    cd (ballK K (L := L) P (-1)) (ballK K P 0) = Places.deg K P := by
  let f : S →ₗ[K] L := (IsScalarTower.toAlgHom K S L).toLinearMap
  have hinj : Function.Injective f := IsFractionRing.injective S L
  have hle : ballK K (L := L) P (-1) ≤ ballK K P 0 := fun x hx =>
    (mem_ballK.1 hx).trans (exp_le_exp.2 (by norm_num))
  have hR : LinearMap.range f ≤ ballK K (L := L) P 0 := by
    rintro _ ⟨a, rfl⟩; exact P.valuation_le_one a
  rw [cd_split (LinearMap.range f) hle]
  have h1 : ballK K (L := L) P 0 ⊓ LinearMap.range f = (⊤ : Submodule K S).map f := by
    rw [inf_eq_right.2 hR, Submodule.map_top]
  have h2 : ballK K (L := L) P (-1) ⊓ LinearMap.range f = (P.asIdeal.restrictScalars K).map f := by
    ext y; constructor
    · rintro ⟨hy, ⟨a, rfl⟩⟩
      exact ⟨a, (P.valuation_lt_one_iff_mem a).1 (le_exp_neg_one_iff.1 hy), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨le_exp_neg_one_iff.2 ((P.valuation_lt_one_iff_mem a).2 ha), a, rfl⟩
  have h3 : ballK K (L := L) P 0 ≤ ballK K P (-1) ⊔ LinearMap.range f := by
    intro x hx
    obtain ⟨a, ha⟩ := P.exists_valuation_sub_lt_of_integer (mem_ballK.1 hx) 1
    have hmem : x - algebraMap S L a ∈ ballK K (L := L) P (-1) := by
      rw [mem_ballK, le_exp_neg_one_iff, Valuation.map_sub_swap]; simpa using ha
    exact Submodule.mem_sup.2 ⟨_, hmem, algebraMap S L a, ⟨a, rfl⟩, sub_add_cancel _ _⟩
  rw [h1, h2, sup_eq_left.2 hR, cd_eq_zero_iff.2 h3, add_zero, cd_map_of_injective f hinj]
  exact PlacesK.dq_asIdeal P

/-- The local index `dim_K ball P (n+1) / ball P n = deg P`. -/
theorem cd_ballK [PlacesK.FDQ K S] (P : HeightOneSpectrum S) (n : ℤ) :
    cd (ballK K (L := L) P n) (ballK K P (n + 1)) = Places.deg K P := by
  obtain ⟨c, hc⟩ := exists_valuation_eq_exp (K := L) P (-(n + 1))
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (exp_ne_zero hc.symm).elim
  let g : L →ₗ[K] L := LinearMap.mulLeft K c
  have e1 : ballK K (L := L) P n = (ballK K (L := L) P (-1)).comap g := by
    ext x
    simp only [Submodule.mem_comap, mem_ballK, g, LinearMap.mulLeft_apply, map_mul, hc,
      exp_mul_le_exp_iff]
    rw [show (-1 : ℤ) - -(n + 1) = n by ring]
  have e2 : (ballK K (L := L) P (n + 1)).map g = ballK K P 0 := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      show P.valuation L (c * x) ≤ exp 0
      rw [map_mul, hc, exp_mul_le_exp_iff, show (0 : ℤ) - -(n + 1) = n + 1 by ring]; exact hx
    · intro hy
      refine ⟨c⁻¹ * y, ?_, ?_⟩
      · show P.valuation L (c⁻¹ * y) ≤ exp (n + 1)
        rw [map_mul, map_inv₀, hc, ← exp_neg, exp_mul_le_exp_iff,
          show n + 1 - -(-(n + 1)) = (0 : ℤ) by ring]; exact hy
      · show c * (c⁻¹ * y) = y
        rw [mul_inv_cancel_left₀ hc0]
  rw [e1, cd_comap, e2, cd_ballK_neg_one]

end LocalIndexK

/-! ### The data of a function field over an arbitrary field -/

section FunctionFieldK

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable {K F}

theorem ord_eq_neg_logK (P : Places.Place K F) (f : F) : P.ord f = -log (ffv K F P f) := by
  rcases P with P | P <;> rfl

theorem ffv_eq_oneK {P : Places.Place K F} {f : F} (hf : f ≠ 0) (h : P.ord f = 0) :
    ffv K F P f = 1 := by
  have hv : ffv K F P f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  rw [ord_eq_neg_logK] at h
  rw [← exp_log hv, show log (ffv K F P f) = 0 by omega, exp_zero]

variable (K F)

/-- The abstract Riemann-Roch data of a function field over an arbitrary field `K`. -/
noncomputable def ffDataK : Data K F (Places.Place K F) where
  v := ffv K F
  deg := Places.Place.deg
  v_algebraMap P c hc := by
    have h0 : algebraMap K F c ≠ 0 := (_root_.map_ne_zero _).2 hc
    exact ffv_eq_oneK h0 (PlacesK.ord_eq_zero_of_mem_constField K F
      (IntermediateField.algebraMap_mem _ c) h0 P)
  finite_ne_one f hf := by
    refine (PlacesK.div f : Places.Divisor K F).support.finite_toSet.subset fun P hP => ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff, PlacesK.div_apply]
    exact fun h => hP (ffv_eq_oneK hf h)

variable {K F}

@[simp] theorem ffDataK_v (P : Places.Place K F) : (ffDataK K F).v P = ffv K F P := rfl

@[simp] theorem ffDataK_deg (P : Places.Place K F) : (ffDataK K F).deg P = P.deg := rfl

theorem ffDataK_div (f : F) : (ffDataK K F).div f = PlacesK.div f := by
  ext P
  rw [Data.div_apply, PlacesK.div_apply, ord_eq_neg_logK]; rfl

theorem ffDataK_degD (D : Places.Divisor K F) : (ffDataK K F).degD D = D.deg := rfl

theorem ffDataK_localIndex (P : Places.Place K F) (n : ℤ) :
    cd ((ffDataK K F).ball P n) ((ffDataK K F).ball P (n + 1)) = (ffDataK K F).deg P := by
  rcases P with P | P
  · have e : ∀ m : ℤ, (ffDataK K F).ball (Sum.inl P) m = ballK K P m :=
      fun m => Submodule.ext fun _ => Iff.rfl
    rw [e, e, cd_ballK]; rfl
  · have e : ∀ m : ℤ, (ffDataK K F).ball (Sum.inr P) m = ballK K P m :=
      fun m => Submodule.ext fun _ => Iff.rfl
    rw [e, e, cd_ballK]; rfl

theorem ffDataK_mem_constField (f : (ffDataK K F).LD 0) : (f : F) ∈ Places.constField K F :=
  PlacesK.mem_constField_of_ord_nonneg K F fun P => by
    have h := (ffDataK K F).mem_LD.1 f.2 P
    rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero] at h
    rcases P with P | P
    · exact Places.neg_log_nonneg_of_valuation_le_one P h
    · exact Places.neg_log_nonneg_of_valuation_le_one P h

theorem ffDataK_finite_L0 : FiniteDimensional K ((ffDataK K F).LD 0) := by
  let φ : (ffDataK K F).LD 0 →ₗ[K] Places.constField K F :=
    { toFun := fun f => ⟨f, ffDataK_mem_constField f⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective φ fun f g h => Subtype.ext (congrArg Subtype.val h :)

/-- The local axioms hold for function fields over any field. -/
theorem ffDataK_axioms0 : (ffDataK K F).AxiomsK0 where
  nonempty := ⟨Sum.inr (PlacesK.nonempty_infPlace K F).some⟩
  deg_pos := PlacesK.Place.deg_pos
  localIndex := ffDataK_localIndex
  deg_div f hf := by rw [ffDataK_div, ffDataK_degD]; exact PlacesK.deg_div hf
  finite_L0 := ffDataK_finite_L0

end FunctionFieldK

end RamanujanPetersson.RR


end

-- ===== S4.Def_RP_JacRRFam_B =====
section

/-!
# Riemann-Roch over an arbitrary constant field (S4-JacRRFam, part B)

Port of the second half of `RR_B` (S3-RR) from a finite `Fq` to an arbitrary field `K`, using the
`ℕ∞`-valued codimension `cd` and `Data.AxiomsK` of part A.  The definitions (`gamma`, `iota`,
`genus`, `Omega`, `wsmul`, `IsCanonical`) and the `General` lemmas of `RR_B` are reused unchanged.
Main results: `cd_adelesK` (`dim A/(A(D)+F) = iota D`), `finrank_OmegaK`, `exists_eq_wsmulK`,
`exists_isCanonicalK`, `riemannRochK` (`ℓ D - ℓ (W - D) = deg D + ℓ 0 - g`), `degD_canonicalK`,
`ell_eq_of_large_degDK` (`ℓ D = deg D + ℓ 0 - g` once `deg D > 2g - 2ℓ 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero

namespace RamanujanPetersson.RR

namespace Data

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F] {d : Data K F ι}

theorem LD_eq_bot_of_degD_negK (hd : d.AxiomsK) {D : ι →₀ ℤ} (hD : d.degD D < 0) : d.LD D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  have h := d.degD_nonneg ((d.mem_LD_iff_div hf0).1 hf)
  rw [degD_add, hd.deg_div f hf0] at h
  linarith

theorem ell_eq_zero_of_degD_negK (hd : d.AxiomsK) {D : ι →₀ ℤ} (hD : d.degD D < 0) : d.ell D = 0 := by
  rw [ell, LD_eq_bot_of_degD_negK hd hD, finrank_bot]

theorem exists_ne_zero_of_ell_posK {D : ι →₀ ℤ} (h : 0 < d.ell D) : ∃ f ∈ d.LD D, f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : d.LD D = ⊥ := (Submodule.eq_bot_iff _).2 hcon
  rw [ell, this, finrank_bot] at h
  exact lt_irrefl 0 h

/-- The defect of effective divisors is bounded by the Riemann-input constant. -/
theorem defect_le_of_nonnegK (hd : d.AxiomsK) {B : ι →₀ ℤ} (hBdeg : 0 < d.degD B) {c : ℤ}
    (hc : ∀ n : ℕ, (n : ℤ) * d.degD B - c ≤ d.ell (n • B)) {A : ι →₀ ℤ} (hA : 0 ≤ A) :
    d.degD A - d.ell A ≤ c := by
  set n : ℕ := (c + d.degD A).toNat + 1 with hn
  have h1 : (n : ℤ) ≥ c + d.degD A + 1 := by omega
  have h2 : (n : ℤ) * d.degD B ≥ n := by
    have : (1 : ℤ) ≤ d.degD B := hBdeg
    nlinarith
  have hle : n • B - A ≤ n • B := sub_le_self _ hA
  have h3 := (ell_sub_leK hd.1 hle).1
  rw [degD_sub] at h3
  have hcn := hc n
  have hpos : 0 < d.ell (n • B - A) := by
    rw [degD_nsmul] at h3
    omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_posK hpos
  have hdiv := (d.mem_LD_iff_div hz0).1 hz
  have hA2 : A + d.div z⁻¹ ≤ n • B := by
    rw [d.div_inv hz0, Finsupp.le_def]
    intro i
    have := Finsupp.le_def.1 hdiv i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_neg, Pi.add_apply, Pi.sub_apply,
      Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply] at this ⊢
    omega
  have h4 := (ell_sub_leK hd.1 hA2).1
  rw [d.ell_add_div (inv_ne_zero hz0), degD_add, hd.deg_div _ (inv_ne_zero hz0), degD_nsmul] at h4
  linarith

/-- Riemann's bound: `deg D - ℓ D` is bounded above. -/
theorem defect_leK (hd : d.AxiomsK) : ∃ c : ℤ, ∀ D : ι →₀ ℤ, d.degD D - d.ell D ≤ c := by
  obtain ⟨B, _, hBdeg, C, hC, c0, hc0⟩ := hd.riemannInput
  have hc : ∀ n : ℕ, (n : ℤ) * d.degD B - (c0 + d.degD C) ≤ d.ell (n • B) := fun n => by
    have h1 := (ell_sub_leK hd.1 (le_add_of_nonneg_right hC : n • B ≤ n • B + C)).1
    rw [degD_add] at h1
    have := hc0 n
    linarith
  refine ⟨c0 + d.degD C, fun D => ?_⟩
  have h1 := (ell_sub_leK hd.1 (le_sup_left : D ≤ D ⊔ 0)).1
  have h2 := defect_le_of_nonnegK hd hBdeg hc (le_sup_right : (0 : ι →₀ ℤ) ≤ D ⊔ 0)
  linarith

theorem bddAbove_defectK (hd : d.AxiomsK) :
    BddAbove (Set.range fun D : ι →₀ ℤ => d.degD D - d.ell D) := by
  obtain ⟨c, hc⟩ := defect_leK hd
  exact ⟨c, by rintro _ ⟨D, rfl⟩; exact hc D⟩

theorem defect_le_gammaK (hd : d.AxiomsK) (D : ι →₀ ℤ) : d.degD D - d.ell D ≤ d.gamma :=
  le_csSup (bddAbove_defectK hd) ⟨D, rfl⟩

theorem exists_gammaK (hd : d.AxiomsK) : ∃ D0 : ι →₀ ℤ, d.degD D0 - d.ell D0 = d.gamma :=
  Int.csSup_mem (Set.range_nonempty _) (bddAbove_defectK hd)

theorem defect_eq_gammaK (hd : d.AxiomsK) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) : d.degD D - d.ell D = d.gamma := by
  have h1 := (ell_sub_leK hd.1 h).1
  have h2 := defect_le_gammaK hd D
  linarith

theorem AD_le_AD_sup_FsK (hd : d.AxiomsK) {D0 D D' : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) (h' : D ≤ D') : d.AD D' ≤ d.AD D ⊔ d.Fs := by
  have e1 := defect_eq_gammaK hd h0 h
  have e2 := defect_eq_gammaK hd h0 (h.trans h')
  have hle := (ell_le_of_leK hd.1 h').1
  have hr := (ell_sub_leK hd.1 h').2
  have hexp : (d.degD D' - d.degD D).toNat - (d.ell D' - d.ell D) = 0 := by omega
  rw [hexp, Nat.cast_zero, cd_eq_zero_iff] at hr
  exact le_sup_left.trans hr

/-- `A = A(D) + F` once `D ≥ D0` (`D0` of maximal defect). -/
theorem adeles_eqK (hd : d.AxiomsK) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) : d.adeles = d.AD D ⊔ d.Fs := by
  apply le_antisymm
  · intro α hα
    obtain ⟨E, hE⟩ := d.exists_AD_of_mem_adeles hα
    exact AD_le_AD_sup_FsK hd h0 h (le_sup_left : D ≤ D ⊔ E) (d.AD_mono le_sup_right hE)
  · exact sup_le (d.AD_le_adeles D) d.Fs_le_adeles

theorem iota_eqK (hd : d.AxiomsK) (D : ι →₀ ℤ) : (d.iota D : ℤ) = d.ell D - d.degD D + d.gamma := by
  have := defect_le_gammaK hd D
  unfold iota; omega

theorem genus_eqK (hd : d.AxiomsK) : (d.genus : ℤ) = d.ell 0 + d.gamma := by
  rw [genus, iota_eqK hd, degD_zero, sub_zero]

/-- The index formula `[A : A(D) + F] = q ^ (ℓ D - deg D + γ)`. -/
theorem cd_adelesK (hd : d.AxiomsK) (D : ι →₀ ℤ) :
    cd (d.AD D ⊔ d.Fs) d.adeles = (d.iota D : ℕ∞) := by
  obtain ⟨D0, h0⟩ := exists_gammaK hd
  have hD : D ≤ D ⊔ D0 := le_sup_left
  rw [adeles_eqK hd h0 (le_sup_right : D0 ≤ D ⊔ D0), (ell_sub_leK hd.1 hD).2]
  congr 1
  have e2 := defect_eq_gammaK hd h0 (le_sup_right : D0 ≤ D ⊔ D0)
  have hle := (ell_le_of_leK hd.1 hD).1
  have h1 := (ell_sub_leK hd.1 hD).1
  have := iota_eqK hd D
  omega

/-- `A = A(D) + F` once `deg D > deg D0 + γ`. -/
theorem adeles_le_of_degDK (hd : d.AxiomsK) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (hD : d.degD D0 + d.gamma < d.degD D) : d.adeles ≤ d.AD D ⊔ d.Fs := by
  have hpos : 0 < d.ell (D - D0) := by
    have := defect_le_gammaK hd (D - D0); rw [degD_sub] at this; omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_posK hpos
  have hzD : D0 ≤ D + d.div z := by
    have := (d.mem_LD_iff_div hz0).1 hz
    rw [Finsupp.le_def] at this ⊢
    intro i
    have := this i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega
  intro α hα
  have hβ : (fun i => z⁻¹ * α i) ∈ d.AD (D + d.div z) ⊔ d.Fs :=
    (adeles_eqK hd h0 hzD).le (d.mul_mem_adeles z⁻¹ hα)
  have := d.mul_mem_AD_sup_Fs hz0 hβ
  rw [add_sub_cancel_right] at this
  convert this using 1
  funext i; simp [hz0]

theorem Omega_eq_bot_of_degDK (hd : d.AxiomsK) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (hD : d.degD D0 + d.gamma < d.degD D) : d.Omega D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro ω hω
  refine LinearMap.ext fun α => ?_
  exact d.mem_Omega.1 hω α (adeles_le_of_degDK hd h0 hD α.2)

/-! ### Dimension of `Ω(D)` -/

/-- `dim A / (A(D) + F) = iota D`: the quotient is finite-dimensional of dimension `iota D`. -/
theorem finrank_quot_adelesK (hd : d.AxiomsK) (D : ι →₀ ℤ) :
    Module.Finite K (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) ∧
    Module.finrank K (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) = d.iota D := by
  have hc := cd_adelesK hd D
  unfold cd at hc
  rw [Cardinal.toENat_eq_natCast] at hc
  refine ⟨Module.rank_lt_aleph0_iff.1 (hc ▸ Cardinal.natCast_lt_aleph0), ?_⟩
  exact Module.finrank_eq_of_rank_eq hc

theorem finite_quot_adelesK (hd : d.AxiomsK) (D : ι →₀ ℤ) :
    Module.Finite K (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) :=
  (finrank_quot_adelesK hd D).1

theorem finite_OmegaK (hd : d.AxiomsK) (D : ι →₀ ℤ) : Module.Finite K (d.Omega D) := by
  have := finite_quot_adelesK hd D
  exact Module.Finite.equiv
    (Submodule.dualQuotEquivDualAnnihilator ((d.AD D ⊔ d.Fs).comap d.adeles.subtype))

/-- `dim_K Ω(D) = iota D = ℓ D - deg D + γ`. -/
theorem finrank_OmegaK (hd : d.AxiomsK) (D : ι →₀ ℤ) : Module.finrank K (d.Omega D) = d.iota D := by
  have := finite_quot_adelesK hd D
  have h2 := (finrank_quot_adelesK hd D).2
  rw [← h2, ← Subspace.dual_finrank_eq]
  exact (LinearEquiv.finrank_eq
    (Submodule.dualQuotEquivDualAnnihilator ((d.AD D ⊔ d.Fs).comap d.adeles.subtype))).symm

/-! ### One-dimensionality over `F` -/

/-- Any two Weil differentials, the first nonzero, satisfy `ω₂ = x • ω₁` (Stichtenoth 1.5.9). -/
theorem exists_eq_wsmulK (hd : d.AxiomsK) {ω1 ω2 : Module.Dual K d.adeles} {A1 A2 : ι →₀ ℤ}
    (h1 : ω1 ∈ d.Omega A1) (h2 : ω2 ∈ d.Omega A2) (hω1 : ω1 ≠ 0) : ∃ x : F, ω2 = d.wsmul x ω1 := by
  by_cases hω2 : ω2 = 0
  · exact ⟨0, by rw [hω2, zero_wsmul]⟩
  obtain ⟨P⟩ := hd.nonempty
  have hP := hd.deg_pos P
  set n : ℕ := (3 * d.gamma - d.degD A1 - d.degD A2).toNat + 1 with hn
  set B : ι →₀ ℤ := n • Finsupp.single P 1 with hB
  have hdegB : d.degD B = n * d.deg P := by rw [hB, degD_nsmul, degD_single, one_mul]
  have hnP : (n : ℤ) ≤ n * d.deg P := by
    have : (1 : ℤ) ≤ d.deg P := by exact_mod_cast hP
    nlinarith
  have hn1 : (n : ℤ) ≥ 3 * d.gamma - d.degD A1 - d.degD A2 + 1 := by omega
  -- dimension of Ω(-B)
  have hneg : d.degD (-B) < 0 := by rw [degD_neg, hdegB]; omega
  have hiota : (Module.finrank K (d.Omega (-B)) : ℤ) = n * d.deg P + d.gamma := by
    rw [finrank_OmegaK hd, iota_eqK hd, ell_eq_zero_of_degD_negK hd hneg, degD_neg, hdegB]; ring
  have := finite_OmegaK hd (-B)
  -- the two subspaces
  have hU : ∀ {ω : Module.Dual K d.adeles} {A : ι →₀ ℤ}, ω ∈ d.Omega A →
      (d.LD (A + B)).map (d.wsmulL ω) ≤ d.Omega (-B) := by
    rintro ω A hω _ ⟨x, hx, rfl⟩
    refine d.wsmul_mem_Omega (D' := A) ?_ hω
    rwa [sub_neg_eq_add]
  have hdim : ∀ {ω : Module.Dual K d.adeles} {A : ι →₀ ℤ}, ω ≠ 0 →
      Module.finrank K ((d.LD (A + B)).map (d.wsmulL ω)) = d.ell (A + B) := fun hω =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (d.wsmulL_injective hω) _)).symm
  have hl : ∀ A : ι →₀ ℤ, d.degD A + n * d.deg P - d.gamma ≤ d.ell (A + B) := fun A => by
    have := defect_le_gammaK hd (A + B); rw [degD_add, hdegB] at this; linarith
  set U1 := (d.LD (A1 + B)).map (d.wsmulL ω1)
  set U2 := (d.LD (A2 + B)).map (d.wsmulL ω2)
  have hU1 : U1 ≤ d.Omega (-B) := hU h1
  have hU2 : U2 ≤ d.Omega (-B) := hU h2
  have : FiniteDimensional K U1 := Submodule.finiteDimensional_of_le hU1
  have : FiniteDimensional K U2 := Submodule.finiteDimensional_of_le hU2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U1 U2
  have hsup : Module.finrank K ↥(U1 ⊔ U2) ≤ Module.finrank K (d.Omega (-B)) :=
    Submodule.finrank_mono (sup_le hU1 hU2)
  rw [hdim hω1, hdim hω2] at hsum
  have hinf : U1 ⊓ U2 ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot, add_zero] at hsum
    have := hl A1
    have := hl A2
    have : (Module.finrank K ↥(U1 ⊔ U2) : ℤ) ≤ Module.finrank K (d.Omega (-B)) := by exact_mod_cast hsup
    have hs : (Module.finrank K ↥(U1 ⊔ U2) : ℤ) = d.ell (A1 + B) + d.ell (A2 + B) := by exact_mod_cast hsum
    nlinarith
  obtain ⟨η, hη, hη0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨⟨x1, -, hx1⟩, ⟨x2, -, hx2⟩⟩ := hη
  simp only [wsmulL_apply] at hx1 hx2
  have hx20 : x2 ≠ 0 := by
    rintro rfl; rw [zero_wsmul] at hx2; exact hη0 hx2.symm
  refine ⟨x1 * x2⁻¹, ?_⟩
  rw [← wsmul_wsmul, hx1, ← hx2, inv_wsmul_wsmul _ hx20]

/-- There is a nonzero Weil differential. -/
theorem exists_weilDiff_ne_zeroK (hd : d.AxiomsK) :
    ∃ (ω : Module.Dual K d.adeles) (A : ι →₀ ℤ), ω ∈ d.Omega A ∧ ω ≠ 0 := by
  obtain ⟨P⟩ := hd.nonempty
  have hP := hd.deg_pos P
  set n : ℕ := (-d.gamma).toNat + 1 with hn
  set B : ι →₀ ℤ := n • Finsupp.single P 1 with hB
  have hdegB : d.degD B = n * d.deg P := by rw [hB, degD_nsmul, degD_single, one_mul]
  have hnP : (n : ℤ) ≤ n * d.deg P := by
    have : (1 : ℤ) ≤ d.deg P := by exact_mod_cast hP
    nlinarith
  have hneg : d.degD (-B) < 0 := by rw [degD_neg, hdegB]; omega
  have hiota : (Module.finrank K (d.Omega (-B)) : ℤ) = n * d.deg P + d.gamma := by
    rw [finrank_OmegaK hd, iota_eqK hd, ell_eq_zero_of_degD_negK hd hneg, degD_neg, hdegB]; ring
  have hne : d.Omega (-B) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hiota
    omega
  obtain ⟨ω, hω, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨ω, -B, hω, hω0⟩

/-! ### The divisor of a Weil differential -/

/-- A nonzero Weil differential `ω` has a divisor `W`: `ω ∈ Ω(D) ↔ D ≤ W`. -/
theorem exists_divisorK (hd : d.AxiomsK) {ω : Module.Dual K d.adeles} (hω : ω ≠ 0) {A : ι →₀ ℤ}
    (hA : ω ∈ d.Omega A) : ∃ W : ι →₀ ℤ, ∀ D, ω ∈ d.Omega D ↔ D ≤ W := by
  obtain ⟨D0, h0⟩ := exists_gammaK hd
  have hb : ∀ D, ω ∈ d.Omega D → d.degD D ≤ d.degD D0 + d.gamma := fun D hD => by
    by_contra hlt
    push Not at hlt
    rw [Omega_eq_bot_of_degDK hd h0 hlt] at hD
    exact hω ((Submodule.mem_bot _).1 hD)
  obtain ⟨m, ⟨W, hW, rfl⟩, hm⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ D, ω ∈ d.Omega D ∧ d.degD D = m)
    ⟨d.degD D0 + d.gamma, by rintro z ⟨D, hD, rfl⟩; exact hb D hD⟩ ⟨_, A, hA, rfl⟩
  refine ⟨W, fun D => ⟨fun hD => ?_, fun hle => d.Omega_anti hle hW⟩⟩
  have hsup : ω ∈ d.Omega (D ⊔ W) := by rw [Omega_sup]; exact ⟨hD, hW⟩
  have h1 := hm _ ⟨_, hsup, rfl⟩
  have h2 : (D ⊔ W) - W = 0 := by
    apply d.eq_zero_of_degD_eq_zero hd.deg_pos (sub_nonneg.2 le_sup_right)
    have := d.degD_mono (le_sup_right : W ≤ D ⊔ W)
    rw [degD_sub]; linarith
  have : D ⊔ W = W := sub_eq_zero.1 h2
  exact le_sup_left.trans this.le

theorem exists_isCanonicalK (hd : d.AxiomsK) : ∃ W : ι →₀ ℤ, d.IsCanonical W := by
  obtain ⟨ω, A, hA, hω⟩ := exists_weilDiff_ne_zeroK hd
  obtain ⟨W, hW⟩ := exists_divisorK hd hω hA
  exact ⟨W, ω, hω, hW⟩

/-! ### The Riemann-Roch theorem -/

/-- `Ω(D) = L(W - D) • ω` for `ω` with divisor `W`. -/
theorem map_LD_eq_OmegaK (hd : d.AxiomsK) {ω : Module.Dual K d.adeles} (hω : ω ≠ 0) {W : ι →₀ ℤ}
    (hW : ∀ D, ω ∈ d.Omega D ↔ D ≤ W) (D : ι →₀ ℤ) :
    (d.LD (W - D)).map (d.wsmulL ω) = d.Omega D := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact d.wsmul_mem_Omega hx ((hW W).2 le_rfl)
  · intro η hη
    obtain ⟨x, rfl⟩ := exists_eq_wsmulK hd ((hW W).2 le_rfl) hη hω
    refine ⟨x, ?_, rfl⟩
    by_cases hx : x = 0
    · subst hx; exact zero_mem _
    rw [d.wsmul_mem_Omega_iff hx, hW] at hη
    rw [SetLike.mem_coe, d.mem_LD_iff_div hx, Finsupp.le_def]
    rw [Finsupp.le_def] at hη
    intro i; have := hη i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega

/-- `dim Ω(D) = ℓ(W - D)`. -/
theorem iota_eq_ellK (hd : d.AxiomsK) {W : ι →₀ ℤ} (hW : d.IsCanonical W) (D : ι →₀ ℤ) :
    d.iota D = d.ell (W - D) := by
  obtain ⟨ω, hω, hWω⟩ := hW
  rw [← finrank_OmegaK hd, ← map_LD_eq_OmegaK hd hω hWω D, ell]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (d.wsmulL_injective hω) _)).symm

/-- **Riemann-Roch**: `ℓ D - ℓ (W - D) = deg D + ℓ 0 - g` (`ℓ 0 = 1` for constant field `K`). -/
theorem riemannRochK (hd : d.AxiomsK) {W : ι →₀ ℤ} (hW : d.IsCanonical W) (D : ι →₀ ℤ) :
    (d.ell D : ℤ) - d.ell (W - D) = d.degD D + d.ell 0 - d.genus := by
  have h1 := iota_eq_ellK hd hW D
  have h2 := iota_eqK hd D
  have h3 := genus_eqK hd
  rw [h1] at h2
  linarith

/-- Riemann's inequality `ℓ D ≥ deg D + ℓ 0 - g`. -/
theorem riemann_inequalityK (hd : d.AxiomsK) (D : ι →₀ ℤ) :
    d.degD D + d.ell 0 - d.genus ≤ d.ell D := by
  have := defect_le_gammaK hd D
  have := genus_eqK hd
  linarith

/-- `ℓ W = g`. -/
theorem ell_canonicalK (hd : d.AxiomsK) {W : ι →₀ ℤ} (hW : d.IsCanonical W) : d.ell W = d.genus := by
  have := riemannRochK hd hW 0
  rw [sub_zero, degD_zero] at this
  omega

/-- `deg W = 2g - 2ℓ 0` (`= 2g - 2` for constant field `K`). -/
theorem degD_canonicalK (hd : d.AxiomsK) {W : ι →₀ ℤ} (hW : d.IsCanonical W) :
    d.degD W = 2 * d.genus - 2 * d.ell 0 := by
  have h1 := riemannRochK hd hW W
  have h2 := ell_canonicalK hd hW
  rw [sub_self] at h1
  rw [h2] at h1
  linarith

/-- `ℓ D = deg D + ℓ 0 - g` once `deg D > 2g - 2ℓ 0`. -/
theorem ell_eq_of_large_degDK (hd : d.AxiomsK) {D : ι →₀ ℤ}
    (hD : 2 * (d.genus : ℤ) - 2 * d.ell 0 < d.degD D) :
    (d.ell D : ℤ) = d.degD D + d.ell 0 - d.genus := by
  obtain ⟨W, hW⟩ := exists_isCanonicalK hd
  have h1 := riemannRochK hd hW D
  have h0 : d.ell (W - D) = 0 := by
    apply ell_eq_zero_of_degD_negK hd
    rw [degD_sub, degD_canonicalK hd hW]; linarith
  rw [h0, Nat.cast_zero, sub_zero] at h1
  exact h1

end Data

end RamanujanPetersson.RR


end

-- ===== S4.Def_RP_JacRRFam_H =====
section

/-!
# Riemann-Roch over an arbitrary field, part H: the Riemann input and Riemann-Roch for function fields

For a function field `F / K(x)` over an ARBITRARY field `K` (no finiteness, no perfectness),
`ffDataK K F` satisfies all axioms `AxiomsK` (`ffDataK_axioms`): the Riemann input uses the pole
divisor `B` of `x` and the pole divisor `C` of an integral basis (Fintype-free port of S3 `RR_C`).
Consequences: Riemann-Roch `riemannRochFK`, and for `constField K F = ⊥` (e.g. a geometrically
integral curve) `ℓ(D) = deg D + 1 - g` for `deg D ≥ 2g - 1` (`ellFK_eq_of_deg`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.RR

section RiemannInputK

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- The pole divisor of `x` (over `K`). -/
noncomputable def poleBK : Places.Divisor K F := (-(ffDataK K F).div (xF K F)) ⊔ 0

variable (K F) in
/-- The sum of the pole divisors of the integral basis (over `K`). -/
noncomputable def poleCK : Places.Divisor K F :=
  ∑ k, ((-(ffDataK K F).div (algebraMap (Places.Rfin K F) F (bas K F k))) ⊔ 0)

theorem xF_ne_zeroK : xF K F ≠ 0 := by
  rw [xF, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K[X] F)]; exact X_ne_zero

theorem aeval_xFK (q : K[X]) : aeval (xF K F) q = algebraMap K[X] F q := by
  have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K K[X] F) X q
  rw [aeval_X_left_apply, IsScalarTower.coe_toAlgHom'] at this
  exact this

theorem xF_inv_eqK : (xF K F)⁻¹ = algebraMap (Places.Rinf K F) F
    (algebraMap (Places.Oinf K) (Places.Rinf K F) (Places.piInf K)) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Places.Oinf K) (RatFunc K) F]
  show _ = algebraMap (RatFunc K) F (1 / RatFunc.X)
  rw [xF, IsScalarTower.algebraMap_apply K[X] (RatFunc K) F, RatFunc.algebraMap_X, one_div,
    map_inv₀]

theorem ffv_xF_inlK (P : HeightOneSpectrum (Places.Rfin K F)) :
    ffv K F (Sum.inl P) (xF K F) ≤ 1 := by
  show P.valuation F (algebraMap K[X] F X) ≤ 1
  rw [IsScalarTower.algebraMap_apply K[X] (Places.Rfin K F) F]
  exact P.valuation_le_one _

theorem one_le_ffv_xF_inrK (P : HeightOneSpectrum (Places.Rinf K F)) :
    1 ≤ ffv K F (Sum.inr P) (xF K F) := by
  have h : P.valuation F (xF K F)⁻¹ ≤ 1 := by rw [xF_inv_eqK]; exact P.valuation_le_one _
  have hv : P.valuation F (xF K F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zeroK
  rw [map_inv₀] at h
  show 1 ≤ P.valuation F (xF K F)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, P.valuation F (xF K F) = exp k := ⟨_, (exp_log hv).symm⟩
  rw [hk, ← exp_neg, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at h
  rw [hk, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]; omega

theorem poleBK_nonneg : 0 ≤ poleBK K F := le_sup_right

theorem poleCK_nonneg : 0 ≤ poleCK K F := Finset.sum_nonneg fun _ _ => le_sup_right

theorem poleBK_eq :
    poleBK K F = Finsupp.sumElim 0 (-(PlacesK.divS (Places.Rinf K F) (xF K F))) := by
  ext P
  have hv : ffv K F P (xF K F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zeroK
  rw [poleBK, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffDataK_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  rcases P with P | P
  · rw [Finsupp.sumElim_inl, Finsupp.coe_zero, Pi.zero_apply]
    exact sup_eq_right.2 ((log_nonpos_iff' hv).2 (ffv_xF_inlK P))
  · rw [Finsupp.sumElim_inr, Finsupp.neg_apply, PlacesK.divS_apply,
      sup_eq_left.2 ((log_nonneg_iff' hv).2 (one_le_ffv_xF_inrK P)), Places.ord, neg_neg]
    rfl

theorem degS_zeroK {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra K S] :
    Places.degS K (0 : HeightOneSpectrum S →₀ ℤ) = 0 := by
  simp [Places.degS]

theorem degD_poleBK :
    (ffDataK K F).degD (poleBK K F) =
      Fintype.card (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) := by
  rw [ffDataK_degD, poleBK_eq, PlacesK.Divisor.deg_sumElim, degS_zeroK, zero_add, ← zero_sub,
    PlacesK.degS_sub, degS_zeroK, zero_sub]
  have hsum := PlacesK.degS_fin_add_degS_inf (K := K) (xF_ne_zeroK (K := K) (F := F))
  have hxR : algebraMap K[X] (Places.Rfin K F) X ≠ 0 := fun h => xF_ne_zeroK (K := K) (F := F) (by
    rw [xF, IsScalarTower.algebraMap_apply K[X] (Places.Rfin K F) F, h, map_zero])
  have e : xF K F = algebraMap (Places.Rfin K F) F (algebraMap K[X] (Places.Rfin K F) X) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hfin : Places.degS K (PlacesK.divS (Places.Rfin K F) (xF K F)) =
      Fintype.card (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) := by
    rw [e, PlacesK.degS_fin hxR, ← PlacesK.norm_bridge_fin K F,
      Algebra.norm_algebraMap_of_basis (bas K F), RatFunc.intDegree_polynomial, natDegree_X_pow]
  omega

theorem ffv_bas_leK (k : Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) (P : Places.Place K F) :
    (ffDataK K F).v P (algebraMap (Places.Rfin K F) F (bas K F k)) ≤ exp (poleCK K F P) := by
  have hbk : algebraMap (Places.Rfin K F) F (bas K F k) ≠ 0 := fun h =>
    (bas K F).ne_zero k (Subtype.ext h)
  rw [(ffDataK K F).v_eq_exp hbk P, exp_le_exp, poleCK, Finsupp.finsetSum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ((-(ffDataK K F).div
    (algebraMap (Places.Rfin K F) F (bas K F k))) ⊔ 0) P)
    (fun k _ => by rw [Finsupp.sup_apply]; exact le_sup_right) (Finset.mem_univ k))
  rw [Finsupp.sup_apply, Finsupp.neg_apply]
  exact le_sup_left

theorem Phi_memK (m : ℕ) (p) :
    Phi K F m p ∈ (ffDataK K F).LD (m • poleBK K F + poleCK K F) := by
  rw [Data.mem_LD]
  intro P
  rw [Finsupp.add_apply, Finsupp.smul_apply, exp_add, exp_nsmul]
  show (ffDataK K F).v P (∑ k, aeval (xF K F) (p k : K[X]) *
    algebraMap (Places.Rfin K F) F (bas K F k)) ≤ _
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  have hB : 0 ≤ poleBK K F P := poleBK_nonneg (K := K) (F := F) P
  have he : 1 ≤ exp (poleBK K F P) := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]; exact hB
  have hx : (ffDataK K F).v P (xF K F) ≤ exp (poleBK K F P) := by
    rw [(ffDataK K F).v_eq_exp xF_ne_zeroK P, exp_le_exp, poleBK, Finsupp.sup_apply,
      Finsupp.neg_apply]
    exact le_sup_left
  exact mul_le_mul' ((ffDataK K F).v_aeval_le P he hx (p k).2) (ffv_bas_leK k P)

theorem Phi_injectiveK (m : ℕ) : Function.Injective (Phi K F m) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hker : LinearMap.ker (IsScalarTower.toAlgHom K[X] (Places.Rfin K F) F).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 fun a b h => Subtype.ext h
  have hli := Fintype.linearIndependent_iff.1 ((bas K F).linearIndependent.map' _ hker)
    (fun k => (p k : K[X])) (by
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
        Algebra.smul_def, ← aeval_xFK]
      exact hp)
  funext k
  exact Subtype.ext (hli k)

theorem finrank_domK (m : ℕ) :
    Module.finrank K (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F) → degreeLT K (m + 1)) =
      Fintype.card (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) * (m + 1) := by
  let e := (LinearEquiv.piCongrRight fun _ => degreeLTEquiv K (m + 1)).trans
    (LinearEquiv.curry K K (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) (Fin (m + 1))).symm
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]

theorem ell_geK (m : ℕ) :
    Fintype.card (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) * (m + 1) ≤
      (ffDataK K F).ell (m • poleBK K F + poleCK K F) := by
  have := Data.finite_LDK (ffDataK_axioms0 (K := K) (F := F)) (m • poleBK K F + poleCK K F)
  rw [← finrank_domK, Data.ell]
  exact LinearMap.finrank_le_finrank_of_injective (f := (Phi K F m).codRestrict _ (Phi_memK m))
    fun p q h => Phi_injectiveK m (congrArg Subtype.val h)

theorem ffDataK_riemannInput : ∃ B : Places.Divisor K F, 0 ≤ B ∧ 0 < (ffDataK K F).degD B ∧
    ∃ C : Places.Divisor K F, 0 ≤ C ∧
      ∃ c : ℤ, ∀ n : ℕ, (n : ℤ) * (ffDataK K F).degD B - c ≤ (ffDataK K F).ell (n • B + C) := by
  have := (bas K F).index_nonempty
  have hpos : 0 < Fintype.card (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) :=
    Fintype.card_pos
  refine ⟨poleBK K F, poleBK_nonneg, ?_, poleCK K F, poleCK_nonneg, 0, fun n => ?_⟩
  · rw [degD_poleBK]; exact_mod_cast hpos
  · rw [degD_poleBK]
    have h := ell_geK (K := K) (F := F) n
    have h' : ((Fintype.card (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) * (n + 1) : ℕ) : ℤ)
        ≤ (ffDataK K F).ell (n • poleBK K F + poleCK K F) := by exact_mod_cast h
    push_cast at h'
    nlinarith

/-- **The axioms of the abstract theory hold for function fields over any field.** -/
theorem ffDataK_axioms : (ffDataK K F).AxiomsK := ⟨ffDataK_axioms0, ffDataK_riemannInput⟩

end RiemannInputK

end RamanujanPetersson.RR


end

-- ===== S4.Def_RP_JacRRFam_I =====
section

/-!
# Riemann-Roch over an arbitrary field, part I: the classical statements for function fields

For a function field `F / K(x)` over an ARBITRARY field `K` (e.g. `K = k(V)`, non-perfect and infinite):
`L(D)`, `ℓ(D) = dim_K L(D)`, the genus, canonical divisors; Riemann-Roch
`ℓ(D) - ℓ(W - D) = deg D + ℓ(0) - g`; and when the full constant field is `K` (`constField K F = ⊥`,
e.g. a geometrically integral curve over `K`): `ℓ(D) = deg D + 1 - g` for `deg D ≥ 2g - 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.RR

section ConcreteK

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- The Riemann-Roch space `L(D)` of a function field over `K`. -/
noncomputable abbrev LFK (D : Places.Divisor K F) : Submodule K F := (ffDataK K F).LD D

variable (K F) in
/-- `ℓ(D) = dim_K L(D)`. -/
noncomputable abbrev ellFK (D : Places.Divisor K F) : ℕ := (ffDataK K F).ell D

variable (K F) in
/-- The genus of `F` over `K`: `g = dim_K A / (A(0) + F)`. -/
noncomputable abbrev genusFK : ℕ := (ffDataK K F).genus

variable (K F) in
/-- `W` is a canonical divisor of `F / K` (the divisor of a nonzero Weil differential). -/
abbrev IsCanonicalFK (W : Places.Divisor K F) : Prop := (ffDataK K F).IsCanonical W

theorem mem_LFK {D : Places.Divisor K F} {f : F} (hf : f ≠ 0) :
    f ∈ LFK K F D ↔ 0 ≤ PlacesK.div f + D := by
  rw [(ffDataK K F).mem_LD_iff_div hf, ffDataK_div]

theorem finiteDimensional_LFK (D : Places.Divisor K F) : FiniteDimensional K (LFK K F D) :=
  Data.finite_LDK ffDataK_axioms0 D

/-- `L(0)` is the full constant field. -/
theorem LFK_zero_eq :
    LFK K F 0 = Subalgebra.toSubmodule (Places.constField K F).toSubalgebra := by
  ext f
  rw [Data.mem_LD, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
  constructor
  · intro h
    exact PlacesK.mem_constField_of_ord_nonneg K F fun P => by
      have h1 := h P
      rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero] at h1
      rcases P with P | P
      · exact Places.neg_log_nonneg_of_valuation_le_one P h1
      · exact Places.neg_log_nonneg_of_valuation_le_one P h1
  · intro hf P
    rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero]
    rcases P with P | P
    · exact Places.valuation_le_one_of_neg_log_nonneg P
        (PlacesK.ord_nonneg_of_mem_constField K F hf (Sum.inl P))
    · exact Places.valuation_le_one_of_neg_log_nonneg P
        (PlacesK.ord_nonneg_of_mem_constField K F hf (Sum.inr P))

/-- `ℓ(0) = [k : K]` for the full constant field `k`. -/
theorem ellFK_zero : ellFK K F 0 = Module.finrank K (Places.constField K F) := by
  rw [ellFK, Data.ell, show (ffDataK K F).LD 0 = _ from LFK_zero_eq]
  rfl

theorem ellFK_zero_of_bot (h : Places.constField K F = ⊥) : ellFK K F 0 = 1 := by
  rw [ellFK_zero, h, IntermediateField.finrank_bot]

theorem genusFK_eq_iota : genusFK K F = (ffDataK K F).iota 0 := rfl

theorem exists_isCanonicalFK : ∃ W : Places.Divisor K F, IsCanonicalFK K F W :=
  Data.exists_isCanonicalK ffDataK_axioms

/-- **Riemann-Roch** over any field `K`: `ℓ(D) - ℓ(W - D) = deg D + ℓ(0) - g`. -/
theorem riemannRochFK {W : Places.Divisor K F} (hW : IsCanonicalFK K F W) (D : Places.Divisor K F) :
    (ellFK K F D : ℤ) - ellFK K F (W - D) = D.deg + ellFK K F 0 - genusFK K F :=
  Data.riemannRochK ffDataK_axioms hW D

theorem riemann_inequalityFK (D : Places.Divisor K F) :
    D.deg + ellFK K F 0 - genusFK K F ≤ ellFK K F D :=
  Data.riemann_inequalityK ffDataK_axioms D

/-- `ℓ(D) = deg D + ℓ(0) - g` once `deg D > 2g - 2ℓ(0)` (any constant field). -/
theorem ellFK_eq_of_large_deg {D : Places.Divisor K F}
    (hD : 2 * (genusFK K F : ℤ) - 2 * ellFK K F 0 < D.deg) :
    (ellFK K F D : ℤ) = D.deg + ellFK K F 0 - genusFK K F :=
  Data.ell_eq_of_large_degDK ffDataK_axioms hD

/-! #### Full constant field `K` (`ℓ(0) = 1`), e.g. a geometrically integral curve over `K` -/

section FullConstantFieldK

variable (hk : Places.constField K F = ⊥)
include hk

/-- **Riemann-Roch** over `K`: `ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/
theorem riemannRochFK' {W : Places.Divisor K F} (hW : IsCanonicalFK K F W)
    (D : Places.Divisor K F) :
    (ellFK K F D : ℤ) - ellFK K F (W - D) = D.deg + 1 - genusFK K F := by
  have := riemannRochFK hW D
  rw [ellFK_zero_of_bot hk] at this
  exact_mod_cast this

/-- Riemann's inequality `ℓ(D) ≥ deg D + 1 - g`. -/
theorem riemann_inequalityFK' (D : Places.Divisor K F) :
    D.deg + 1 - genusFK K F ≤ ellFK K F D := by
  have := riemann_inequalityFK (K := K) (F := F) D
  rw [ellFK_zero_of_bot hk] at this
  exact_mod_cast this

/-- `deg W = 2g - 2`. -/
theorem degFK_canonical {W : Places.Divisor K F} (hW : IsCanonicalFK K F W) :
    W.deg = 2 * (genusFK K F : ℤ) - 2 := by
  have := Data.degD_canonicalK ffDataK_axioms hW
  rw [ffDataK_degD] at this
  rw [this]
  have h1 := ellFK_zero_of_bot hk
  simp only [ellFK] at h1
  rw [h1]; push_cast; ring

/-- **`ℓ(D) = deg D + 1 - g` for `deg D ≥ 2g - 1`**, over an arbitrary field `K`. -/
theorem ellFK_eq_of_deg {D : Places.Divisor K F} (hD : 2 * (genusFK K F : ℤ) - 1 ≤ D.deg) :
    (ellFK K F D : ℤ) = D.deg + 1 - genusFK K F := by
  have h1 := ellFK_zero_of_bot hk
  simp only [ellFK] at h1
  have hD' : 2 * ((ffDataK K F).genus : ℤ) - 1 ≤ D.deg := hD
  have := Data.ell_eq_of_large_degDK ffDataK_axioms (D := D) (by
    rw [ffDataK_degD, h1]; push_cast; omega)
  rw [this, h1, ffDataK_degD]; push_cast; ring

end FullConstantFieldK

end ConcreteK

/-! ### The pole-divisor family and constant field extensions (port of S3 `RR_D` to any `K`) -/

theorem mem_range_iff_valuation_le_oneK {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*}
    [Field L] [Algebra S L] [IsFractionRing S L] (f : L) :
    f ∈ (algebraMap S L).range ↔ ∀ P : HeightOneSpectrum S, P.valuation L f ≤ 1 := by
  refine ⟨?_, HeightOneSpectrum.mem_integers_of_valuation_le_one L f⟩
  rintro ⟨r, rfl⟩ P
  exact P.valuation_le_one r

section PoleFamilyK

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem degD_poleBK_pos : 0 < (poleBK K F).deg := by
  have := (bas K F).index_nonempty
  have hpos : 0 < Fintype.card (Module.Free.ChooseBasisIndex K[X] (Places.Rfin K F)) :=
    Fintype.card_pos
  rw [← ffDataK_degD, degD_poleBK]; exact_mod_cast hpos

end PoleFamilyK

section ConstantFieldExtensionK

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]
variable (L : Type*) [Field L] [Algebra K L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra K F'] [IsScalarTower K F F'] [IsScalarTower K L F']

variable {K L}
variable {ι : Type*} [Fintype ι]

variable {F F'}
variable {c : Module.Basis ι K L}

end ConstantFieldExtensionK

end RamanujanPetersson.RR


end

-- ===== S4.Def_RP_JacLaw_RRk =====
section

/-!
# S4-JacLaw, file O4c: the Riemann-Roch dictionary for the chart ring `B = Rfin K F`

* `IsInf H`: `H` vanishes at the finite places. `Linf H := L(H) ∩ B` as a `K`-subspace of `B`;
  `finrank_Linf` (`= ℓ(H)`, since `L(H) ⊆ B`), `finrank_Linf_eq` (`= deg H + 1 - g` for `deg H ≥ 2g - 1`).
* `mul_mem_Linf`, `poleDiv f = (-div f) ⊔ 0`, `mem_Linf_poleDiv`.
* `ExactPole s Pinf N`: `ord_P s = -N` at `Pinf` and `0` at the other infinite places. Then
  `s ∈ Linf (N • ptInf Pinf)`, `L(H) ∩ s B = s L(H - N Pinf)` (`mem_Linf_sub_of_mul`) and `dim_K B/(s) = N`
  (`finrank_quot_of_exactPole`, when `deg Pinf = 1`).
* `deg_eq_one`: over an algebraically closed `K` every place has degree one; `constField_eq_bot'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section RRk

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- `H` vanishes at the finite places. -/
def IsInf (H : Places.Divisor K F) : Prop := ∀ P : HeightOneSpectrum (Places.Rfin K F), H (Sum.inl P) = 0

theorem IsInf.add {H H' : Places.Divisor K F} (h : IsInf H) (h' : IsInf H') : IsInf (H + H') := fun P => by
  simp [h P, h' P]

theorem IsInf.sub {H H' : Places.Divisor K F} (h : IsInf H) (h' : IsInf H') : IsInf (H - H') := fun P => by
  simp [h P, h' P]

theorem IsInf.nsmul {H : Places.Divisor K F} (h : IsInf H) (n : ℕ) : IsInf (n • H) := fun P => by
  simp [h P]

/-- The divisor `1 · P` of an infinite place. -/
noncomputable def ptInf (P : HeightOneSpectrum (Places.Rinf K F)) : Places.Divisor K F :=
  Finsupp.single (Sum.inr P) 1

variable (K F) in
/-- The inclusion `B → F` as a `K`-algebra map. -/
noncomputable def incB : Places.Rfin K F →ₐ[K] F := IsScalarTower.toAlgHom K (Places.Rfin K F) F

theorem incB_apply (b : Places.Rfin K F) : incB K F b = algebraMap (Places.Rfin K F) F b := rfl

theorem incB_injective : Function.Injective (incB K F) := fun a b h => Subtype.ext h

variable (K F) in
/-- `L(H) ∩ B` as a `K`-subspace of `B`. -/
noncomputable def Linf (H : Places.Divisor K F) : Submodule K (Places.Rfin K F) :=
  (LFK K F H).comap (incB K F).toLinearMap

theorem mem_Linf {H : Places.Divisor K F} {b : Places.Rfin K F} : b ∈ Linf K F H ↔ incB K F b ∈ LFK K F H :=
  Iff.rfl

theorem ord_incB_nonneg (P : HeightOneSpectrum (Places.Rfin K F)) (b : Places.Rfin K F) :
    0 ≤ Places.ord P (incB K F b) := by
  by_cases hb : b = 0
  · subst hb; simp [Places.ord]
  · rw [incB_apply, PlacesK.ord_algebraMap P hb]; exact Nat.cast_nonneg _

theorem exists_incB_eq {H : Places.Divisor K F} (hH : IsInf H) {f : F} (hf : f ∈ LFK K F H) :
    ∃ b, incB K F b = f := by
  have : f ∈ (algebraMap (Places.Rfin K F) F).range := by
    rw [mem_range_iff_valuation_le_oneK]
    intro P
    have h := (Data.mem_LD (ffDataK K F)).mp hf (Sum.inl P)
    rw [hH P, exp_zero] at h
    exact h
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

theorem finrank_Linf {H : Places.Divisor K F} (hH : IsInf H) : finrank K (Linf K F H) = ellFK K F H := by
  let φ : Linf K F H →ₗ[K] LFK K F H :=
    ((incB K F).toLinearMap.domRestrict (Linf K F H)).codRestrict (LFK K F H) fun b => b.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => ?_, fun f => ?_⟩
    · have h' := congrArg Subtype.val h
      exact Subtype.ext (incB_injective h')
    obtain ⟨b, hb⟩ := exists_incB_eq hH f.2
    exact ⟨⟨b, show incB K F b ∈ LFK K F H from hb ▸ f.2⟩, Subtype.ext hb⟩
  exact (LinearEquiv.ofBijective φ hφ).finrank_eq

theorem finrank_Linf_eq (hk : Places.constField K F = ⊥) {H : Places.Divisor K F} (hH : IsInf H)
    (hd : 2 * (genusFK K F : ℤ) - 1 ≤ H.deg) :
    (finrank K (Linf K F H) : ℤ) = H.deg + 1 - genusFK K F := by
  rw [finrank_Linf hH]; exact ellFK_eq_of_deg hk hd

theorem mul_mem_Linf {D₁ D₂ : Places.Divisor K F} {s y : Places.Rfin K F} (hs : s ∈ Linf K F D₁)
    (hy : y ∈ Linf K F D₂) : s * y ∈ Linf K F (D₁ + D₂) := by
  by_cases hs0 : s = 0
  · simp [hs0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have hy' : incB K F y ≠ 0 := fun h => hy0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hs'] at hs
  rw [mem_Linf, mem_LFK hy'] at hy
  rw [mem_Linf, map_mul, mem_LFK (mul_ne_zero hs' hy'), PlacesK.div_mul hs' hy']
  have := add_nonneg hs hy
  rwa [add_add_add_comm] at this

/-- The pole divisor `(-div f) ⊔ 0`. -/
noncomputable def poleDiv (f : F) : Places.Divisor K F := (-PlacesK.div f) ⊔ 0

theorem isInf_poleDiv (b : Places.Rfin K F) : IsInf (poleDiv (K := K) (incB K F b)) := fun P => by
  have := ord_incB_nonneg P b
  simp only [poleDiv, Finsupp.sup_apply, Finsupp.neg_apply, PlacesK.div_apply, Places.Place.ord_inl,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_right.mpr (by omega)

theorem mem_Linf_poleDiv (b : Places.Rfin K F) : b ∈ Linf K F (poleDiv (K := K) (incB K F b)) := by
  by_cases hb : b = 0
  · simp [hb]
  have hb' : incB K F b ≠ 0 := fun h => hb (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hb', Finsupp.le_def]
  intro P
  simp only [poleDiv, Finsupp.coe_add, Pi.add_apply, Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.coe_zero,
    Pi.zero_apply]
  omega

theorem deg_nonneg_of_nonneg {D : Places.Divisor K F} (hD : 0 ≤ D) : 0 ≤ D.deg := by
  unfold Places.Divisor.deg
  exact Finsupp.sum_nonneg fun P _ => mul_nonneg (hD P) (Nat.cast_nonneg _)

theorem deg_poleDiv_nonneg (f : F) : 0 ≤ (poleDiv (K := K) f).deg :=
  deg_nonneg_of_nonneg le_sup_right

variable {s : Places.Rfin K F} {Pinf : HeightOneSpectrum (Places.Rinf K F)} {N : ℕ}

end RRk

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K]

theorem deg_eq_one {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra K S] [PlacesK.FDQ K S]
    (P : HeightOneSpectrum S) : Places.deg K P = 1 := by
  haveI := PlacesK.moduleFinite_residue (K := K) P
  haveI := P.isPrime
  have hs : Function.Surjective (algebraMap K (S ⧸ P.asIdeal)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)).2
  have hb : Function.Bijective (Algebra.linearMap K (S ⧸ P.asIdeal)) :=
    ⟨(algebraMap K (S ⧸ P.asIdeal)).injective, hs⟩
  rw [Places.deg, ← (LinearEquiv.ofBijective _ hb).finrank_eq, finrank_self]

variable [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem constField_eq_bot' : Places.constField K F = ⊥ := by
  obtain ⟨P⟩ := PlacesK.nonempty_infPlace K F
  exact PlacesK.constField_eq_bot_of_deg_one K F (P := Sum.inr P) (deg_eq_one P)

end AlgClosed

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Exact =====
section

/-!
# S4-JacLaw, file O6a: exact poles from hyperplane conditions

* The places at infinity are finitely many (each contains `1/x`): `Finite` instance.
* `Linf_mono`.
* `exactPole_of_not_mem`: a nonzero `s ∈ L(N P∞) ∩ B` outside every hyperplane `L(N P∞ - P')`
  (`P'` at infinity) has an exact pole of order `N` at `P∞` and no other zero or pole at infinity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section Exact

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- The image of `1/x` in `Rinf`. -/
noncomputable abbrev piR : Places.Rinf K F :=
  algebraMap (Places.Oinf K) (Places.Rinf K F) (Places.piInf K)

theorem piR_ne_zero : piR K F ≠ 0 := by
  intro h
  have h2 : algebraMap (Places.Oinf K) F (Places.piInf K) = 0 := congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply (Places.Oinf K) (RatFunc K) F] at h2
  have h3 : ((Places.piInf K : Places.Oinf K) : RatFunc K) = 0 :=
    (FaithfulSMul.algebraMap_injective (RatFunc K) F) (h2.trans (map_zero _).symm)
  exact Places.piInf_ne_zero K (Subtype.ext h3)

/-- Every place over `x = ∞` contains `1/x`. -/
theorem piR_mem (P : HeightOneSpectrum (Places.Rinf K F)) : piR K F ∈ P.asIdeal := by
  have := P.isMaximal
  have h1 : (P.asIdeal.comap (algebraMap (Places.Oinf K) (Places.Rinf K F))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
  have h2 := IsLocalRing.eq_maximalIdeal h1
  have h3 := IsLocalRing.eq_maximalIdeal (Places.span_piInf_isMaximal K)
  have h4 : Places.piInf K ∈ P.asIdeal.comap (algebraMap (Places.Oinf K) (Places.Rinf K F)) := by
    rw [h2, ← h3]; exact Ideal.mem_span_singleton_self _
  exact h4

instance finite_infPlaces : Finite (HeightOneSpectrum (Places.Rinf K F)) := by
  have hfin : {P : HeightOneSpectrum (Places.Rinf K F) | P.asIdeal ∣ Ideal.span {piR K F}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact piR_ne_zero)
  refine Set.finite_univ_iff.mp (hfin.subset fun P _ => ?_)
  exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (piR_mem P))

theorem Linf_mono {H H' : Places.Divisor K F} (h : H ≤ H') : Linf K F H ≤ Linf K F H' := by
  intro b hb
  by_cases hb0 : b = 0
  · rw [hb0]; exact Submodule.zero_mem _
  have hb' : incB K F b ≠ 0 := fun h => hb0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hb'] at hb ⊢
  exact hb.trans (add_le_add le_rfl h)

variable {s : Places.Rfin K F} {Pinf : HeightOneSpectrum (Places.Rinf K F)} {N : ℕ}

end Exact

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_RRkH =====
section

/-!
# S4-JacLaw, file X2: exact pole divisors `Hn` at infinity (generalising `N • P∞`)

* `ExactPoleH s Hn`: `ord_P s = -Hn(P)` at every infinite place `P`.
* `mem_Linf_of_exactPoleH`, `mem_Linf_sub_of_mulH` (`L(H) ∩ s B = s L(H - Hn)`),
  `finrank_quot_of_exactPoleH` (`dim_K B/(s) = deg Hn`, no degree hypothesis on the places),
  `exactPoleH_of_not_mem` (exact poles from hyperplane conditions).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section RRkH

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- `s` has pole divisor exactly `Hn` at infinity (and no zeros there). -/
def ExactPoleH (s : Places.Rfin K F) (Hn : Places.Divisor K F) : Prop :=
  ∀ P : HeightOneSpectrum (Places.Rinf K F), Places.ord P (incB K F s) = -Hn (Sum.inr P)

variable {s : Places.Rfin K F} {Hn : Places.Divisor K F}

theorem mem_Linf_of_exactPoleH (hHn : IsInf Hn) (hs : ExactPoleH s Hn) : s ∈ Linf K F Hn := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def]
  rintro (P | P)
  · have := ord_incB_nonneg P s
    simp [hHn P, this]
  · have := hs P
    simp [this]

theorem mem_Linf_sub_of_mulH (hs0 : s ≠ 0) (hs : ExactPoleH s Hn) (hHn : IsInf Hn) {H : Places.Divisor K F}
    (hH : IsInf H) {y : Places.Rfin K F} (hz : s * y ∈ Linf K F H) : y ∈ Linf K F (H - Hn) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have hy' : incB K F y ≠ 0 := fun h => hy0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, map_mul, mem_LFK (mul_ne_zero hs' hy'), PlacesK.div_mul hs' hy', Finsupp.le_def] at hz
  rw [mem_Linf, mem_LFK hy', Finsupp.le_def]
  rintro (P | P)
  · have := ord_incB_nonneg P y
    simp [hH P, hHn P, this]
  · have h1 := hz (Sum.inr P)
    have h2 := hs P
    simp only [Finsupp.coe_add, Pi.add_apply, PlacesK.div_apply, Places.Place.ord_inr, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, PlacesK.div_apply,
      Places.Place.ord_inr, Finsupp.coe_zero, Pi.zero_apply]
    omega

/-- `dim_K B/(s) = deg Hn` (product formula). -/
theorem finrank_quot_of_exactPoleH (hs0 : s ≠ 0) (hHn : IsInf Hn) (hs : ExactPoleH s Hn) :
    (finrank K (Places.Rfin K F ⧸ Ideal.span {s}) : ℤ) = Hn.deg := by
  have h1 := PlacesK.finrank_quot_span (K := K) hs0
  have h2 := PlacesK.degS_divS_algebraMap (K := K) (L := F) hs0
  have hs' : algebraMap (Places.Rfin K F) F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have e : Hn + PlacesK.div (algebraMap (Places.Rfin K F) F s) =
      (PlacesK.divS (Places.Rfin K F) (algebraMap (Places.Rfin K F) F s)).sumElim 0 := by
    ext (P | P)
    · simp [PlacesK.div, hHn P]
    · have this : Places.ord P (s : F) = -Hn (Sum.inr P) := hs P
      simp [PlacesK.div]
      omega
  have h3 := congrArg Places.Divisor.deg e
  rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hs', PlacesK.Divisor.deg_sumElim] at h3
  have h4 : Places.degS K (0 : HeightOneSpectrum (Places.Rinf K F) →₀ ℤ) = 0 := by
    unfold Places.degS; simp
  rw [h4, h2, ← h1] at h3
  omega

/-- **Exact pole divisor from hyperplane conditions.** -/
theorem exactPoleH_of_not_mem (hs0 : s ≠ 0) (hs : s ∈ Linf K F Hn)
    (hP : ∀ P' : HeightOneSpectrum (Places.Rinf K F), s ∉ Linf K F (Hn - ptInf P')) : ExactPoleH s Hn := by
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  intro P
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def] at hs
  have h1 := hs (Sum.inr P)
  by_contra hne
  apply hP P
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def]
  rintro (Q | Q)
  · have h2 := hs (Sum.inl Q)
    simpa [ptInf] using h2
  · have h2 := hs (Sum.inr Q)
    by_cases hQ : Q = P
    · subst hQ
      simp [ptInf] at h1 ⊢
      omega
    · simp [ptInf, hQ] at h2 ⊢
      exact h2

end RRkH

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_IsogDegA_Fib1 =====
section

/-!
# S4-IsogDegA, file Fib1: generic fibre count, part 1 (finite dimensionality, fibres, upper bound)
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.IsogDegA

section FinDim

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

omit [IsDomain R] [IsDomain B] [IsFractionRing R K] in
include R B in
/-- If `B` is a finite `R`-algebra (domains), then `Frac B` is finite dimensional over `Frac R`. -/
theorem finiteDimensional_of_finite : FiniteDimensional K L := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  set S : Set L := (algebraMap B L) '' (s : Set B) with hSdef
  have hint : ∀ x ∈ S, IsIntegral K x := by
    rintro _ ⟨b, -, rfl⟩
    have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
    exact (hb.map (IsScalarTower.toAlgHom R B L)).tower_top
  have hfin : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hB : ∀ c : B, algebraMap B L c ∈ IntermediateField.adjoin K S := by
    intro c
    have hc : c ∈ Submodule.span R (s : Set B) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K S ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R K L]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
  have htop : IntermediateField.adjoin K S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfin
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end FinDim

section Fibre

variable (k : Type*) [Field k]
variable {R : Type*} (B : Type*) [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]

/-- The `k`-points of `Spec B` lying over the `k`-point `χ` of `Spec R`. -/
abbrev fiber (χ : R →ₐ[k] k) : Type _ :=
  {ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ}

variable {k B}

theorem fiber_apply_algebraMap {χ : R →ₐ[k] k} (ψ : fiber k B χ) (r : R) :
    ψ.1 (algebraMap R B r) = χ r := by
  have h := congrArg (fun φ : R →ₐ[k] k => φ r) ψ.2
  simpa using h

theorem fiber_aeval {χ : R →ₐ[k] k} (ψ : fiber k B χ) (β : B) (g : R[X]) :
    ψ.1 (aeval β g) = eval₂ (χ : R →+* k) (ψ.1 β) g := by
  rw [aeval_def]
  refine (Polynomial.hom_eval₂ g (algebraMap R B) (ψ.1 : B →+* k) β).trans ?_
  congr 1
  ext r
  exact fiber_apply_algebraMap ψ r

/-- Two points of the fibre agreeing at `β` agree, provided every generator of `B` over `R` has a
`q`-power that is (up to a unit at `χ`) a polynomial in `β`. -/
theorem fiber_ext {χ : R →ₐ[k] k} (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (ψ₁ ψ₂ : fiber k B χ) (hβ : ψ₁.1 β = ψ₂.1 β) : ψ₁ = ψ₂ := by
  have hgen' : ∀ b ∈ s, ψ₁.1 b = ψ₂.1 b := by
    intro b hb
    obtain ⟨n, c, h, hc, hbh⟩ := hgen b hb
    have e1 := congrArg ψ₁.1 hbh
    have e2 := congrArg ψ₂.1 hbh
    rw [map_mul, map_pow, fiber_apply_algebraMap, fiber_aeval] at e1 e2
    rw [hβ] at e1
    have h3 : ψ₁.1 b ^ q ^ n = ψ₂.1 b ^ q ^ n := mul_left_cancel₀ hc (e1.trans e2.symm)
    apply iterateFrobenius_inj k q n
    simpa [iterateFrobenius_def] using h3
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  have hx : x ∈ Submodule.span R s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen' y hy
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy =>
    rw [Algebra.smul_def, map_mul, map_mul, fiber_apply_algebraMap, fiber_apply_algebraMap, hy]

/-- Upper bound: the fibre injects into the roots of `f0` mod `χ`. -/
theorem card_fiber_le {χ : R →ₐ[k] k} (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (f0 : R[X]) (hf0 : f0.Monic) (hβ0 : aeval β f0 = 0) :
    Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) ≤ f0.natDegree := by
  classical
  set p : k[X] := f0.map (χ : R →+* k) with hpdef
  have hp : p ≠ 0 := (hf0.map _).ne_zero
  let F : fiber k B χ → p.roots.toFinset := fun ψ => ⟨ψ.1 β, by
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot, hpdef, eval_map, ← fiber_aeval, hβ0,
      map_zero]⟩
  have hF : Function.Injective F := fun ψ₁ ψ₂ h =>
    fiber_ext s hs β q hgen ψ₁ ψ₂ (congrArg Subtype.val h)
  refine ⟨Finite.of_injective F hF, ?_⟩
  calc Nat.card (fiber k B χ) ≤ Nat.card p.roots.toFinset := Nat.card_le_card_of_injective F hF
    _ = p.roots.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ = f0.natDegree := hf0.natDegree_map _

end Fibre

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IsogDegA_Fib2 =====
section

/-!
# S4-IsogDegA, file Fib2: generic fibre count, part 2 (lower bound via going-up, exact count)
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.IsogDegA

section Lower

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {R B : Type*} [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Algebra.IsIntegral R B]

/-- Lower bound, pointwise: every root `α` of `f0 mod χ` is the value at `β` of a point of the
fibre over `χ`, provided `f0` divides every polynomial relation of `β`. -/
theorem exists_fiber_of_root (χ : R →ₐ[k] k) (β : B) (f0 : R[X])
    (hdvd : ∀ g : R[X], aeval β g = 0 → f0 ∣ g) (α : k)
    (hα : eval₂ (χ : R →+* k) α f0 = 0) : ∃ ψ : fiber k B χ, ψ.1 β = α := by
  classical
  set ev : R[X] →+* k := eval₂RingHom (χ : R →+* k) α with hev
  have hevC : ∀ c : k, ev (C (algebraMap k R c)) = c := fun c => by
    simp [hev]
  have hsurj : Function.Surjective ev := fun c => ⟨_, hevC c⟩
  have hPmax : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hsurj
  let _ : Algebra R[X] B := (aeval β).toRingHom.toAlgebra
  have halg : ∀ g : R[X], algebraMap R[X] B g = aeval β g := fun _ => rfl
  have hcomp : (algebraMap R[X] B).comp (C : R →+* R[X]) = algebraMap R B := by
    ext r; simp [halg]
  have hint : Algebra.IsIntegral R[X] B := by
    refine ⟨fun x => ?_⟩
    have h0 : ((algebraMap R[X] B).comp (C : R →+* R[X])).IsIntegral := by
      rw [hcomp]; exact fun y => Algebra.IsIntegral.isIntegral (R := R) y
    exact RingHom.IsIntegral.tower_top (f := (C : R →+* R[X])) (g := algebraMap R[X] B) h0 x
  have hker : RingHom.ker (algebraMap R[X] B) ≤ RingHom.ker ev := by
    intro g hg
    rw [RingHom.mem_ker, halg] at hg
    obtain ⟨h, rfl⟩ := hdvd g hg
    rw [RingHom.mem_ker, map_mul]
    simp [hev, hα]
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker ev) hker
  -- key: modulo `Q`, `aeval β g` is the constant `ev g`
  have hkey : ∀ g : R[X], Ideal.Quotient.mk Q (aeval β g) =
      algebraMap k (B ⧸ Q) (ev g) := by
    intro g
    have hmem : g - C (algebraMap k R (ev g)) ∈ RingHom.ker ev := by
      rw [RingHom.mem_ker, map_sub, hevC, sub_self]
    rw [← hQ, Ideal.mem_comap, halg, map_sub] at hmem
    rw [Ideal.Quotient.eq.mpr hmem, aeval_C, ← IsScalarTower.algebraMap_apply]
    rfl
  have hR : ∀ r : R, Ideal.Quotient.mk Q (algebraMap R B r) = algebraMap k (B ⧸ Q) (χ r) := by
    intro r
    have := hkey (C r)
    rwa [aeval_C, show ev (C r) = χ r by simp [hev]] at this
  -- `B ⧸ Q` is integral, hence equal to `k`
  have hintk : Algebra.IsIntegral k (B ⧸ Q) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    refine ⟨p.map (χ : R →+* k), hpm.map _, ?_⟩
    rw [eval₂_map]
    have hc : (algebraMap k (B ⧸ Q)).comp (χ : R →+* k) =
        (Ideal.Quotient.mk Q).comp (algebraMap R B) := by
      ext r; exact (hR r).symm
    rw [hc, ← hom_eval₂, hp, map_zero]
  have hbij : Function.Bijective (algebraMap k (B ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] B ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ Q)) hbij
  let ψ : B →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k Q)
  have hψ : ∀ b : B, e (ψ b) = Ideal.Quotient.mk Q b := fun b => by
    simp [ψ]
  have hψg : ∀ g : R[X], ψ (aeval β g) = ev g := by
    intro g
    apply e.injective
    rw [hψ, hkey]
    rfl
  refine ⟨⟨ψ, ?_⟩, ?_⟩
  · ext r
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    have := hψg (C r)
    rwa [aeval_C, show ev (C r) = χ r by simp [hev]] at this
  · have := hψg X
    rwa [aeval_X, show ev X = α by simp [hev]] at this

/-- Exact count: if moreover `f0 mod χ` is separable, the fibre has exactly `deg f0` points. -/
theorem card_fiber_eq (χ : R →ₐ[k] k) (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (f0 : R[X]) (hf0 : f0.Monic) (hβ0 : aeval β f0 = 0)
    (hdvd : ∀ g : R[X], aeval β g = 0 → f0 ∣ g) (hsep : (f0.map (χ : R →+* k)).Separable) :
    Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) = f0.natDegree := by
  classical
  obtain ⟨hfin, hle⟩ := card_fiber_le s hs β q hgen f0 hf0 hβ0
  refine ⟨hfin, le_antisymm hle ?_⟩
  set p : k[X] := f0.map (χ : R →+* k) with hpdef
  have hp : p ≠ 0 := (hf0.map _).ne_zero
  have hroot : ∀ α ∈ p.roots.toFinset, ∃ ψ : fiber k B χ, ψ.1 β = α := by
    intro α hα
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot, hpdef, eval_map] at hα
    exact exists_fiber_of_root χ β f0 hdvd α hα
  choose G hG using hroot
  let G' : p.roots.toFinset → fiber k B χ := fun α => G α.1 α.2
  have hG' : Function.Injective G' := by
    intro a b hab
    apply Subtype.ext
    rw [← hG a.1 a.2, ← hG b.1 b.2]
    exact congrArg (fun ψ : fiber k B χ => ψ.1 β) hab
  calc f0.natDegree = p.natDegree := (hf0.natDegree_map _).symm
    _ = Multiset.card p.roots := IsAlgClosed.card_roots_eq_natDegree.symm
    _ = p.roots.toFinset.card := (Multiset.toFinset_card_of_nodup (nodup_roots hsep)).symm
    _ = Nat.card p.roots.toFinset := (Nat.card_eq_finsetCard _).symm
    _ ≤ Nat.card (fiber k B χ) := Nat.card_le_card_of_injective G' hG'

end Lower

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IsogDegA_Fib3 =====
section

/-!
# S4-IsogDegA, file Fib3: generic fibre count, part 3 (choice of a generic primitive element)
-/

set_option autoImplicit false

open Polynomial IntermediateField

namespace RamanujanPetersson.IsogDegA

section Adjoin

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem adjoin_simple_mul_eq {e : K} (he : e ≠ 0) (θ : L) :
    K⟮algebraMap K L e * θ⟯ = K⟮θ⟯ := by
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact mul_mem (IntermediateField.algebraMap_mem _ e) (mem_adjoin_simple_self K θ)
  · rw [adjoin_simple_le_iff]
    have h : algebraMap K L e⁻¹ * (algebraMap K L e * θ) ∈ K⟮algebraMap K L e * θ⟯ :=
      mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_simple_self K _)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, one_mul] at h

theorem minpoly_mul_eq {e : K} (he : e ≠ 0) {θ : L} (hθ : IsIntegral K θ) :
    minpoly K (algebraMap K L e * θ) = (minpoly K θ).scaleRoots e := by
  have hθ' : IsIntegral K (algebraMap K L e * θ) := isIntegral_algebraMap.mul hθ
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hθ')
    ((monic_scaleRoots_iff e).2 (minpoly.monic hθ)) ?_ ?_).symm
  · exact minpoly.dvd K _ (scaleRoots_aeval_eq_zero (minpoly.aeval K θ))
  · refine le_of_eq ?_
    rw [natDegree_scaleRoots, ← adjoin.finrank hθ, ← adjoin.finrank hθ', adjoin_simple_mul_eq he]

theorem exists_adjoin_eq_separableClosure [FiniteDimensional K L] :
    ∃ θ : L, K⟮θ⟯ = separableClosure K L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K (separableClosure K L)
  exact ⟨α.1, by rw [← lift_adjoin_simple, hα, lift_top]⟩

end Adjoin

section Lift

variable {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

theorem exists_monic_lift_minpoly {θ : L} (hθ : IsIntegral K θ) :
    ∃ d : R, d ≠ 0 ∧ ∃ f0 : R[X], f0.Monic ∧
      f0.map (algebraMap R K) = minpoly K (algebraMap R L d * θ) := by
  classical
  have hp : (minpoly K θ).Monic := minpoly.monic hθ
  obtain ⟨f0, hf1, -, hf2⟩ := lifts_and_natDegree_eq_and_monic
    (IsLocalization.scaleRoots_commonDenom_mem_lifts (nonZeroDivisors R) (minpoly K θ)
      (by rw [hp.leadingCoeff]; exact one_mem _)) ((monic_scaleRoots_iff _).2 hp)
  set D := IsLocalization.commonDenom (nonZeroDivisors R) (minpoly K θ).support (minpoly K θ).coeff
  have hD : algebraMap R K D ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors D.2
  refine ⟨D, nonZeroDivisors.ne_zero D.2, f0, hf2, ?_⟩
  rw [hf1, IsScalarTower.algebraMap_apply R K L, minpoly_mul_eq hD hθ]

omit [IsDomain R] in
/-- A monic lift of a minimal polynomial divides every polynomial relation. -/
theorem dvd_of_aeval_eq_zero {B : Type*} [CommRing B] [Algebra R B] [Algebra B L]
    [IsScalarTower R B L] (β : B) (f0 : R[X]) (hf0 : f0.Monic)
    (hmap : f0.map (algebraMap R K) = minpoly K (algebraMap B L β)) (g : R[X])
    (hg : aeval β g = 0) : f0 ∣ g := by
  have h1 : minpoly K (algebraMap B L β) ∣ g.map (algebraMap R K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, hg, map_zero]
  have h2 : (g %ₘ f0).map (algebraMap R K) = 0 := by
    rw [map_modByMonic _ hf0, (modByMonic_eq_zero_iff_dvd (hf0.map _)).2 (hmap ▸ h1)]
  have h3 : g %ₘ f0 = 0 :=
    map_injective _ (IsFractionRing.injective R K) (by rw [h2, Polynomial.map_zero])
  exact (modByMonic_eq_zero_iff_dvd hf0).1 h3

/-- Separability of `f0` over `Frac R` spreads out: it holds modulo every `χ` with `χ a ≠ 0`. -/
theorem exists_sep_witness (k : Type*) [Field k] (f0 : R[X])
    (hsep : (f0.map (algebraMap R K)).Separable) :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →+* k, χ a ≠ 0 → (f0.map χ).Separable := by
  classical
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨bu, hbu, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) u
  obtain ⟨bv, hbv, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) v
  set U := IsLocalization.integerNormalization (nonZeroDivisors R) u
  set V := IsLocalization.integerNormalization (nonZeroDivisors R) v
  have hu' : U.map (algebraMap R K) = C (algebraMap R K bu) * u := by
    rw [hu, ← smul_eq_C_mul, algebraMap_smul]
  have hv' : V.map (algebraMap R K) = C (algebraMap R K bv) * v := by
    rw [hv, ← smul_eq_C_mul, algebraMap_smul]
  have key : (C (bu * bv) : R[X]) = C bv * U * f0 + C bu * V * derivative f0 := by
    apply map_injective (algebraMap R K) (IsFractionRing.injective R K)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu', hv',
      ← derivative_map, map_mul]
    linear_combination (-(C (algebraMap R K bu) * C (algebraMap R K bv))) * huv
  refine ⟨bu * bv, mul_ne_zero (nonZeroDivisors.ne_zero hbu) (nonZeroDivisors.ne_zero hbv), ?_⟩
  intro χ hχ
  have hk := congrArg (Polynomial.map χ) key
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hk
  have hinv : C (χ (bu * bv))⁻¹ * C (χ (bu * bv)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hχ, C_1]
  rw [Separable, derivative_map]
  refine ⟨C (χ (bu * bv))⁻¹ * (C (χ bv) * U.map χ), C (χ (bu * bv))⁻¹ * (C (χ bu) * V.map χ), ?_⟩
  linear_combination (-C (χ (bu * bv))⁻¹) * hk + hinv

end Lift

section Generic

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

variable (R B K L) in
/-- A generic element: `β ∈ B` generating the separable closure, with a monic lift over `R` of its
minimal polynomial. -/
theorem exists_generic_element :
    ∃ β : B, ∃ f0 : R[X], f0.Monic ∧ f0.map (algebraMap R K) = minpoly K (algebraMap B L β) ∧
      K⟮algebraMap B L β⟯ = separableClosure K L := by
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  obtain ⟨θ0, hθ0⟩ := exists_adjoin_eq_separableClosure (K := K) (L := L)
  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := B) θ0
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hne := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self c)
    (Algebra.IsIntegral.isIntegral (R := R) c)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hr
  obtain ⟨c', hc'⟩ := hr
  have hcL : algebraMap B L c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  have hrK : algebraMap R K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hr0)
  have hθ : algebraMap B L (b * c') = algebraMap K L (algebraMap R K r) * θ0 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R B L, ← hc', ← hbc,
      map_mul, map_mul]
    first | (field_simp; ring) | field_simp
  have hθint : IsIntegral K (algebraMap B L (b * c')) :=
    ((Algebra.IsIntegral.isIntegral (R := R) (b * c')).map
      (IsScalarTower.toAlgHom R B L)).tower_top
  obtain ⟨d, hd, f0, hf0, hmap⟩ := exists_monic_lift_minpoly (R := R) hθint
  have hdK : algebraMap R K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hd)
  refine ⟨algebraMap R B d * (b * c'), f0, hf0, ?_, ?_⟩
  · rw [map_mul, ← IsScalarTower.algebraMap_apply]; exact hmap
  · rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K L,
      adjoin_simple_mul_eq hdK, hθ, adjoin_simple_mul_eq hrK, hθ0]

end Generic

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IsogDegA_Fib4 =====
section

/-!
# S4-IsogDegA, file Fib4: the generic fibre has `finSepDegree` points (O1 headline)

`B` finite over `R` (domains, `k`-algebras, `k` algebraically closed), `K = Frac R`, `L = Frac B`.
Over a dense open set of `k`-points `χ` of `Spec R` (those with `χ a ≠ 0`), the fibre of
`Spec B → Spec R` has exactly `[L : K]_s` points.
-/

set_option autoImplicit false

open Polynomial IntermediateField

namespace RamanujanPetersson.IsogDegA

section Headline

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

/-- Every element of `B` has a `q`-power which, up to a nonzero constant, is a polynomial in a
generic element. -/
theorem exists_pow_eq_aeval (q : ℕ) [ExpChar K q] (β : B)
    (hβ : K⟮algebraMap B L β⟯ = separableClosure K L) (b : B) :
    ∃ n : ℕ, ∃ c : R, ∃ h : R[X], c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h := by
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  have : ExpChar (separableClosure K L) q :=
    expChar_of_injective_algebraMap (algebraMap K _).injective q
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (separableClosure K L) q (algebraMap B L b)
  obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
  have hθint : IsIntegral K (algebraMap B L β) :=
    ((Algebra.IsIntegral.isIntegral (R := R) β).map (IsScalarTower.toAlgHom R B L)).tower_top
  have hmem : algebraMap B L b ^ q ^ n ∈ Algebra.adjoin K {algebraMap B L β} := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic, hβ, ← hy]
    exact y.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨hK, hhK⟩ := (AlgHom.mem_range _).1 hmem
  obtain ⟨c, hc, hH⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) hK
  refine ⟨n, c, IsLocalization.integerNormalization (nonZeroDivisors R) hK,
    nonZeroDivisors.ne_zero hc, ?_⟩
  apply IsFractionRing.injective B L
  calc algebraMap B L (algebraMap R B c * b ^ q ^ n)
      = algebraMap R L c * algebraMap B L b ^ q ^ n := by
        rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    _ = aeval (algebraMap B L β)
          ((IsLocalization.integerNormalization (nonZeroDivisors R) hK).map (algebraMap R K)) := by
        rw [hH, ← algebraMap_smul K c hK, smul_eq_C_mul, aeval_mul, aeval_C, hhK,
          ← IsScalarTower.algebraMap_apply]
    _ = _ := by rw [aeval_map_algebraMap, aeval_algebraMap_apply]

variable (k : Type*) [Field k] [IsAlgClosed k] [Algebra k R] [Algebra k B] [IsScalarTower k R B]

variable (K L) in
/-- **O1 headline.** There is `a ≠ 0` in `R` such that over every `k`-point `χ` with `χ a ≠ 0` the
fibre has exactly `Field.finSepDegree K L` points. -/
theorem exists_card_fiber_eq_finSepDegree :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →ₐ[k] k, χ a ≠ 0 →
      Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) = Field.finSepDegree K L := by
  classical
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  obtain ⟨q, hq⟩ := ExpChar.exists k
  have : ExpChar K q := expChar_of_injective_ringHom
    (f := (algebraMap R K).comp (algebraMap k R)) (RingHom.injective _) q
  obtain ⟨β, f0, hf0, hmap, hadj⟩ := exists_generic_element R B K L
  have hθint : IsIntegral K (algebraMap B L β) :=
    ((Algebra.IsIntegral.isIntegral (R := R) β).map (IsScalarTower.toAlgHom R B L)).tower_top
  have hsep : (f0.map (algebraMap R K)).Separable := by
    rw [hmap]
    have h : algebraMap B L β ∈ separableClosure K L := hadj ▸ mem_adjoin_simple_self K _
    exact h
  obtain ⟨a1, ha1, hsepχ⟩ := exists_sep_witness (K := K) k f0 hsep
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  have hg := fun b : B => exists_pow_eq_aeval (R := R) (K := K) (L := L) q β hadj b
  choose n c h hc hch using hg
  refine ⟨a1 * ∏ b ∈ s, c b, mul_ne_zero ha1 (Finset.prod_ne_zero_iff.2 fun b _ => hc b), ?_⟩
  intro χ hχ
  rw [map_mul, map_prod] at hχ
  have hχ1 : χ a1 ≠ 0 := left_ne_zero_of_mul hχ
  have hχ2 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hχ)
  have hβ0 : aeval β f0 = 0 := by
    have h0 : aeval (algebraMap B L β) (f0.map (algebraMap R K)) = 0 := by
      rw [hmap]; exact minpoly.aeval K _
    rw [aeval_map_algebraMap, aeval_algebraMap_apply] at h0
    exact IsFractionRing.injective B L (h0.trans (map_zero _).symm)
  have hdeg : f0.natDegree = Field.finSepDegree K L := by
    rw [← hf0.natDegree_map (algebraMap R K), hmap, ← adjoin.finrank hθint, hadj,
      Field.finSepDegree_eq K L]
    rfl
  rw [← hdeg]
  exact card_fiber_eq χ (s : Set B) hs β q (fun b hb => ⟨n b, c b, h b, hχ2 b hb, hch b⟩) f0 hf0
    hβ0 (dvd_of_aeval_eq_zero (K := K) (L := L) β f0 hf0 hmap) (hsepχ χ hχ1)

end Headline

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_JacLaw_GenFib =====
section

/-!
# S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets

`xB = x ∈ B` (the chart coordinate), `n = rank_{K[X]} B = [F : K(x)]`.
* `finrank_quot_poly`: `dim_K B/(q(x)) = deg q · n`.
* `exactPoleH_poly`: `q(x)` has exact pole divisor `poleDiv q(x)` at infinity (no zeros there).
* `exists_fib_card`: for all but finitely many `c` the fibre `x = c` has exactly `n` points (IsogDegA).
* `exists_fib_data`: for a finset `Λ` of good values, `s = ∏_{c∈Λ} (x - c)` has exact pole divisor of degree
  `|Λ| n` and exactly `|Λ| n` zeros, namely the points with `x ∈ Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section Fib

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- The chart coordinate `x ∈ B`. -/
noncomputable abbrev xB : Places.Rfin K F := algebraMap K[X] (Places.Rfin K F) X

theorem algebraMap_poly_injective : Function.Injective (algebraMap K[X] (Places.Rfin K F)) := by
  intro p q h
  apply FaithfulSMul.algebraMap_injective K[X] F
  rw [IsScalarTower.algebraMap_apply K[X] (Places.Rfin K F) F, h, ← IsScalarTower.algebraMap_apply]

/-- `dim_K B/(q(x)) = deg q · n`. -/
theorem finrank_quot_poly {q : K[X]} (hq : q ≠ 0) :
    finrank K (Places.Rfin K F ⧸ Ideal.span {algebraMap K[X] (Places.Rfin K F) q}) =
      q.natDegree * finrank K[X] (Places.Rfin K F) := by
  have hf : algebraMap K[X] (Places.Rfin K F) q ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_poly_injective).2 hq
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis K[X] (Places.Rfin K F)) hf,
    Algebra.norm_algebraMap, natDegree_pow, mul_comm]

theorem incB_poly (q : K[X]) :
    incB K F (algebraMap K[X] (Places.Rfin K F) q) =
      algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) q) := by
  rw [incB_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K[X] (RatFunc K) F]

theorem apply_poly (φ : Places.Rfin K F →ₐ[K] K) (q : K[X]) :
    φ (algebraMap K[X] (Places.Rfin K F) q) = q.eval (φ (xB K F)) := by
  have e : φ.comp (IsScalarTower.toAlgHom K K[X] (Places.Rfin K F)) = Polynomial.aeval (φ (xB K F)) :=
    Polynomial.algHom_ext (by simp)
  have := congrArg (fun ψ : K[X] →ₐ[K] K => ψ q) e
  simpa [coe_aeval_eq_eval] using this

section AlgClosed

variable [IsAlgClosed K]

theorem fib_iff (c : K) (φ : Places.Rfin K F →ₐ[K] K) :
    φ.comp (IsScalarTower.toAlgHom K K[X] (Places.Rfin K F)) = Polynomial.aeval c ↔ φ (xB K F) = c := by
  constructor
  · intro h
    have := congrArg (fun ψ : K[X] →ₐ[K] K => ψ X) h
    simpa using this
  · intro h
    exact Polynomial.algHom_ext (by simpa using h)

end AlgClosed

end Fib

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacSymA_A =====
section

/-!
# S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`

For a commutative `k`-algebra `B` (the coordinate ring of an affine chart `X = Spec B` of a curve), the coordinate
ring of `X^g` is the tensor power `XPow k B g = ⨂[k] _ : Fin g, B`. The symmetric group `S_g = Perm (Fin g)` acts by
permuting the tensor factors, and the affine chart of `Sym^g X` is `Spec (SymRing k B g)` with
`SymRing k B g = (⨂ B)^(S_g)`. A `g`-tuple of `k`-points of `B` is the same as a `k`-point of `XPow k B g`.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

variable (k : Type*) [CommRing k] (B : Type*) [CommRing B] [Algebra k B] (g : ℕ)

/-- The coordinate ring of `X^g`: the `g`-fold tensor power of `B` over `k`. -/
abbrev XPow : Type _ := PiTensorProduct k (fun _ : Fin g => B)

variable {k B g}

/-- The algebra map of `X^g` that permutes the factors: `b_1 ⊗ ... ⊗ b_g ↦ b_(σ⁻¹ 1) ⊗ ... ⊗ b_(σ⁻¹ g)`. -/
noncomputable def permHom (σ : Equiv.Perm (Fin g)) : XPow k B g →ₐ[k] XPow k B g :=
  PiTensorProduct.liftAlgHom ((PiTensorProduct.tprod k).domDomCongr σ.symm)
    (by simp [MultilinearMap.domDomCongr_apply, PiTensorProduct.one_def]; rfl)
    (fun x y => by
      simp only [MultilinearMap.domDomCongr_apply, PiTensorProduct.tprod_mul_tprod]; rfl)

@[simp] theorem permHom_tprod (σ : Equiv.Perm (Fin g)) (b : Fin g → B) :
    permHom σ (PiTensorProduct.tprod k b) = PiTensorProduct.tprod k (fun i => b (σ.symm i)) := by
  simp [permHom, MultilinearMap.domDomCongr_apply]

theorem algHom_ext_tprod {f h : XPow k B g →ₐ[k] XPow k B g}
    (H : ∀ b : Fin g → B, f (PiTensorProduct.tprod k b) = h (PiTensorProduct.tprod k b)) : f = h :=
  AlgHom.toLinearMap_injective (PiTensorProduct.ext (MultilinearMap.ext H))

theorem permHom_one : permHom (1 : Equiv.Perm (Fin g)) = AlgHom.id k (XPow k B g) :=
  algHom_ext_tprod (fun b => by rw [permHom_tprod]; rfl)

theorem permHom_mul (σ τ : Equiv.Perm (Fin g)) :
    permHom (σ * τ) = (permHom σ).comp (permHom τ : XPow k B g →ₐ[k] XPow k B g) :=
  algHom_ext_tprod (fun b => by simp [Equiv.Perm.mul_def])

variable (k B g)

variable {k B g}

/-! ### `k`-points of `X^g` are `g`-tuples of `k`-points of `X` -/

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacDivisors_Q =====
section

/-!
# S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
For `V G : Over (Spec k)` (`k` algebraically closed), `G` a group object and `f : V ⇀ G` a partial map over `k`:
* `mem_domain_of_slice`: if `a ∈ dom f` is a `k`-point and the difference map `Φ(v, w) = f(v) f(w)⁻¹` is defined at
  `(x, a)`, then `f` extends to `x` (`v ↦ Φ(v, a) · f(a)` near `x`).
* `mem_domain_of_isClosed`: if `Φ` is defined at `Δ x` and `x` is closed, then `f` extends to `x`.
* `domain_eq_top` (E10): if `V` and `V ×_k V` are integral, locally Noetherian with factorial stalks, `V` is of finite type
  and `G` is separated, locally of finite type and satisfies the existence part of the valuative criterion (e.g. proper),
  then every rational map `V ⤏ G` over `k` is defined everywhere.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Limits Order Topology MonoidalCategory MonObj CartesianMonoidalCategory

universe u

section
variable {k : Type u} [Field k] {V G : Over (Spec (.of k))}

/-- The slice `v ↦ (v, a)` through a `k`-point `a`. -/
noncomputable abbrev slice (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) : V ⟶ V ⊗ V := lift (𝟙 V) (toUnit V ≫ a)

variable [GrpObj G]

end

end RamanujanPetersson.JacDivisors


end



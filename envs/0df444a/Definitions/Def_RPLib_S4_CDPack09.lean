-- Prove2me | Definitions.Def_RPLib_S4_CDPack09
-- name    : RPLib_S4_CDPack09
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:03:13.364285+00:00
-- url     : https://prove2.me/theorems/af83828e-a83e-43fa-9c2d-b76f632df378
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 9 of 71
-- statement:
--   Part 9 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResFrob`: S4-PD (4), E4B part 3b: Frobenius elements in decomposition groups and boundary residue degrees
--   * `Def_RP_CP4a_Res`: S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants
--   * `Def_RP_CP4a_Trans`: S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CP4aLift
import Definitions.Def_RPLib_S4_KummerConst
import Definitions.Def_RPLib_S4_KummerInf

/-!
# Curve-duality library package, part 9 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResFrob`: S4-PD (4), E4B part 3b: Frobenius elements in decomposition groups and boundary residue degrees
* `Def_RP_CP4a_Res`: S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants
* `Def_RP_CP4a_Trans`: S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResFrob =====
section

/-!
# S4-PD (4), E4B part 3b: Frobenius elements in decomposition groups and boundary residue degrees

* `isUnit_of_pow_eq_self`, `card_le_of_pow_eq`: elementary facts on `d ^ n = d`.
* `exists_frob_mem` (abstract, profinite `H` with invariants `A'`): some `h ∈ H` acts as `x ↦ x^(p^k)` modulo `P`.
* `exists_frob_level`: at the pro-chart, for a level `L` on whose ring `y^(p^k) ≡ y` modulo `P`.
* `mem_fix_sup`, `mem_fix_constLevel`: such an `h` fixes `L ⊔ K(𝔽_{p^k})`.
* `card_quot_sup_le`: the residue field of `L ⊔ K(𝔽_{p^k})` under `P` has at most `p^k` elements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a

noncomputable section

theorem isUnit_of_pow_eq_self {B : Type*} [CommRing B] [IsDomain B] {d : B} {n : ℕ} (hn : 2 ≤ n)
    (hd : d ^ n = d) (h0 : d ≠ 0) : IsUnit d := by
  have h1 : d ^ (n - 1) = 1 :=
    mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel (by omega), hd, one_mul])
  have h2 : d * d ^ (n - 2) = 1 := by rw [← pow_succ', show n - 2 + 1 = n - 1 by omega, h1]
  exact ⟨⟨d, d ^ (n - 2), h2, by rw [mul_comm]; exact h2⟩, rfl⟩

/-- A field all of whose elements satisfy `z ^ n = z` (`1 < n`) is finite with at most `n` elements. -/
theorem card_le_of_pow_eq {k : Type*} [Field k] {n : ℕ} (hn : 1 < n) (h : ∀ z : k, z ^ n = z) :
    Finite k ∧ Nat.card k ≤ n := by
  classical
  have hX : (X ^ n - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hn
  have hmem : ∀ z : k, z ∈ (X ^ n - X : k[X]).roots.toFinset := fun z => by
    rw [Multiset.mem_toFinset, mem_roots hX]
    simp [h z]
  haveI hfin : Finite k := Finite.of_injective
    (fun z : k => (⟨z, hmem z⟩ : (X ^ n - X : k[X]).roots.toFinset)) (fun a b hab => congrArg Subtype.val hab)
  letI : Fintype k := Fintype.ofFinite k
  refine ⟨hfin, ?_⟩
  calc Nat.card k = (Finset.univ : Finset k).card := by rw [Nat.card_eq_fintype_card, Finset.card_univ]
    _ ≤ (X ^ n - X : k[X]).roots.toFinset.card := Finset.card_le_card fun z _ => hmem z
    _ ≤ Multiset.card (X ^ n - X : k[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ n - X : k[X]).natDegree := card_roots' _
    _ = n := FiniteField.X_pow_card_sub_X_natDegree_eq k hn

section AbsFrob

variable {G B A' : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CommRing A'] [Algebra A' B] [SMulCommClass H A' B] [Algebra.IsInvariant A' B H]
  [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

/-- **Frobenius in the decomposition group**: if `B/P` is perfect of characteristic `p` and `x ↦ x^(p^k)` is the
identity on `A'` modulo `P`, some `h ∈ H` acts as `x ↦ x^(p^k)` modulo `P`. -/
theorem exists_frob_mem (P : Ideal B) [P.IsPrime] (p k : ℕ) [ExpChar (B ⧸ P) p] [PerfectRing (B ⧸ P) p]
    (hk : ∀ a : A', algebraMap A' B a ^ (p ^ k) - algebraMap A' B a ∈ P) :
    ∃ h : H, ∀ b : B, (h : G) • b - b ^ (p ^ k) ∈ P := by
  let σ0 : (B ⧸ P) ≃+* (B ⧸ P) := iterateFrobeniusEquiv (B ⧸ P) p k
  have hσ0 : ∀ b : B, σ0 (Ideal.Quotient.mk P b) = Ideal.Quotient.mk P (b ^ (p ^ k)) := fun b => by
    show iterateFrobenius (B ⧸ P) p k _ = _
    rw [iterateFrobenius_def, map_pow]
  let σ : (B ⧸ P) ≃ₐ[A' ⧸ P.under A'] (B ⧸ P) := AlgEquiv.ofRingEquiv (f := σ0) (fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change σ0 (Ideal.Quotient.mk P (algebraMap A' B a)) = Ideal.Quotient.mk P (algebraMap A' B a)
    rw [hσ0]
    exact Ideal.Quotient.eq.2 (hk a))
  obtain ⟨⟨h2, hh2⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H) (P.under A') P σ
  refine ⟨h2, fun b => ?_⟩
  have h3 : Ideal.Quotient.mk P (h2 • b) = σ (Ideal.Quotient.mk P b) := by
    rw [← hσ]
    rfl
  exact Ideal.Quotient.eq.1 (h3.trans (hσ0 b))

end AbsFrob

section AbsFrobFix

variable {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B] [TopologicalSpace G]
  (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul H B]

/-- `exists_frob_mem` with `A' = B^H`. -/
theorem exists_frob_mem_fix {R0 : Type*} [CommRing R0] [Algebra R0 B] [SMulCommClass G R0 B]
    (P : Ideal B) [P.IsPrime] (p k : ℕ) [ExpChar (B ⧸ P) p] [PerfectRing (B ⧸ P) p]
    (hk : ∀ b : B, (∀ h ∈ H, h • b = b) → b ^ (p ^ k) - b ∈ P) :
    ∃ h ∈ H, ∀ b : B, h • b - b ^ (p ^ k) ∈ P := by
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra R0 B H) B H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨h, hh⟩ := exists_frob_mem (A' := FixedPoints.subalgebra R0 B H) H P p k
    (fun a => hk (a : B) fun σ hσ => (a.2 : ∀ g : H, g • (a : B) = a) ⟨σ, hσ⟩)
  exact ⟨h, h.2, hh⟩

end AbsFrobFix

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- The profinite step at the pro-chart: a Frobenius-type element of `Gal(K_U/L)` at `P`. -/
theorem exists_fix_frob {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] (P : Ideal (proChart A K R0)) [P.IsPrime] (p k : ℕ)
    [ExpChar (proChart A K R0 ⧸ P) p] [PerfectRing (proChart A K R0 ⧸ P) p]
    (hk : ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ P.comap (inclU R0 hLU)) :
    ∃ h ∈ (IntermediateField.restrict hLU).fixingSubgroup, ∀ b : proChart A K R0, h • b - b ^ (p ^ k) ∈ P := by
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
  refine exists_frob_mem_fix (R0 := R0) (IntermediateField.restrict hLU).fixingSubgroup P p k fun b hb => ?_
  obtain ⟨y, rfl⟩ := exists_inclU_eq hLU b fun σ hσ => congrArg Subtype.val (hb σ hσ)
  have h := hk y
  rw [Ideal.mem_comap, map_sub, map_pow] at h
  exact h

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
/-- `exists_fix_frob` with its perfectness hypotheses discharged (`R0` with finite quotients). -/
theorem exists_frob_level [Ring.HasFiniteQuotients R0] {L : IntermediateField K (AlgebraicClosure K)}
    (hLU : L ≤ maxUnram A K) [FiniteDimensional K L] (P : Ideal (proChart A K R0)) [P.IsPrime]
    (hP0 : P.under R0 ≠ ⊥) (k : ℕ)
    (hk : ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ P.comap (inclU R0 hLU)) :
    ∃ h ∈ (IntermediateField.restrict hLU).fixingSubgroup, ∀ b : proChart A K R0, h • b - b ^ (p ^ k) ∈ P := by
  haveI hm0 : (P.under R0).IsMaximal := Ring.HasFiniteQuotients.maximalOfPrime hP0
  haveI : Finite (R0 ⧸ P.under R0) := Ring.HasFiniteQuotients.finiteQuotient hP0
  haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R0) P hm0
  letI : Field (R0 ⧸ P.under R0) := Ideal.Quotient.field _
  letI : Field (proChart A K R0 ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.IsIntegral (R0 ⧸ P.under R0) (proChart A K R0 ⧸ P) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver (p := P.under R0) (P := P)
  haveI : Algebra.IsAlgebraic (R0 ⧸ P.under R0) (proChart A K R0 ⧸ P) := Algebra.IsIntegral.isAlgebraic
  haveI : PerfectField (proChart A K R0 ⧸ P) := Algebra.IsAlgebraic.perfectField (R0 ⧸ P.under R0)
  haveI : CharP (maxUnram A K) p := charP_of_injective_algebraMap (algebraMap K (maxUnram A K)).injective p
  haveI : CharP (proChart A K R0 ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
    have h0 : ((p : ℕ) : proChart A K R0) = 0 := by
      apply Subtype.ext
      simpa using CharP.cast_eq_zero (maxUnram A K) p
    rw [← map_natCast (Ideal.Quotient.mk P), h0, map_zero])
  haveI : ExpChar (proChart A K R0 ⧸ P) p := ExpChar.prime hp.out
  exact exists_fix_frob hLU P p k hk

/-! ## Fixed levels of one element -/

variable (A) in
/-- The elements of `K_U ⊆ K̄` fixed by `h`, as an intermediate field of `K̄ / K`. -/
def fixF (h : Pi1 A K) : IntermediateField K (AlgebraicClosure K) :=
  (IntermediateField.fixedField (Subgroup.zpowers h)).map (maxUnram A K).val

theorem mem_fixF {h : Pi1 A K} {x : maxUnram A K} (hx : h x = x) : (x : AlgebraicClosure K) ∈ fixF A h := by
  refine (IntermediateField.mem_map _).2 ⟨x, (IntermediateField.mem_fixedField_iff _ _).2 fun g hg => ?_, rfl⟩
  have hs : h ∈ MulAction.stabilizer (Pi1 A K) x := hx
  exact (Subgroup.zpowers_le.2 hs) hg

theorem fix_of_mem_fixF {h : Pi1 A K} {x : maxUnram A K} (hx : (x : AlgebraicClosure K) ∈ fixF A h) : h x = x := by
  obtain ⟨z, hz, hzx⟩ := (IntermediateField.mem_map _).1 hx
  have hzx' : z = x := Subtype.ext hzx
  subst hzx'
  exact (IntermediateField.mem_fixedField_iff _ _).1 hz h (Subgroup.mem_zpowers h)

theorem le_fixF {X : IntermediateField K (AlgebraicClosure K)} (hXU : X ≤ maxUnram A K) {h : Pi1 A K}
    (hX : h ∈ (IntermediateField.restrict hXU).fixingSubgroup) : X ≤ fixF A h := fun y hy =>
  mem_fixF ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hX ⟨y, hXU hy⟩
    ((IntermediateField.mem_restrict hXU _).2 hy))

theorem mem_fix_of_le {X : IntermediateField K (AlgebraicClosure K)} (hXU : X ≤ maxUnram A K) {h : Pi1 A K}
    (hX : X ≤ fixF A h) : h ∈ (IntermediateField.restrict hXU).fixingSubgroup :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
    fix_of_mem_fixF (hX ((IntermediateField.mem_restrict hXU _).1 hx))

/-- An element of `π₁(U)` fixing two levels fixes their compositum. -/
theorem mem_fix_sup {L C : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    (hCU : C ≤ maxUnram A K) {h : Pi1 A K} (hL : h ∈ (IntermediateField.restrict hLU).fixingSubgroup)
    (hC : h ∈ (IntermediateField.restrict hCU).fixingSubgroup) :
    h ∈ (IntermediateField.restrict (sup_le hLU hCU)).fixingSubgroup :=
  mem_fix_of_le _ (sup_le (le_fixF hLU hL) (le_fixF hCU hC))

/-- A Frobenius-type `h` (`h • b ≡ b^(p^k)` modulo a prime `P`) fixes the constant level `K(𝔽_{p^k})`. -/
theorem mem_fix_constLevel {k : ℕ} (hk : 0 < k) (hCU : constLevel K p k ≤ maxUnram A K)
    {P : Ideal (proChart A K R0)} [P.IsPrime] {h : Pi1 A K}
    (hP : ∀ b : proChart A K R0, h • b - b ^ (p ^ k) ∈ P) :
    h ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
  haveI : CharP (maxUnram A K) p := charP_of_injective_algebraMap (algebraMap K (maxUnram A K)).injective p
  have hn : 1 < p ^ k := one_lt_pow_p hk
  refine mem_fix_of_le hCU (IntermediateField.adjoin_le_iff.2 fun y hy => ?_)
  have hyC : y ∈ constLevel K p k := IntermediateField.subset_adjoin _ _ hy
  let x : maxUnram A K := ⟨y, hCU hyC⟩
  have hy0 : y ^ (p ^ k) = y := by
    have h1 := ((mem_rootSet).1 hy).2
    simp only [map_sub, map_pow, aeval_X] at h1
    exact sub_eq_zero.1 h1
  have hx : x ^ (p ^ k) = x := Subtype.ext hy0
  have hint : IsIntegral R0 x := ⟨X ^ (p ^ k) - X,
    monic_X_pow_sub (degree_X_le.trans_lt (by exact_mod_cast hn)), by simp [hx]⟩
  let b : proChart A K R0 := ⟨x, hint⟩
  have hb : b ^ (p ^ k) = b := Subtype.ext hx
  have hd : h • b - b ∈ P := by simpa [hb] using hP b
  refine mem_fixF (x := x) ?_
  by_contra hne
  have hdd : (h x - x) ^ (p ^ k) = h x - x := by
    rw [sub_pow_char_pow, ← map_pow, hx]
  have hd0 : h • b - b ≠ 0 := fun h0 => hne (sub_eq_zero.1 (congrArg Subtype.val h0))
  have hpow : (h • b - b) ^ (p ^ k) = h • b - b := Subtype.ext hdd
  exact (Ideal.IsPrime.ne_top inferInstance)
    (Ideal.eq_top_of_isUnit_mem _ hd (isUnit_of_pow_eq_self (by omega) hpow hd0))

/-- On a level fixed by `h`, `h • b ≡ b^n` gives `y^n ≡ y` modulo `P`. -/
theorem pow_sub_mem_of_fix {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {P : Ideal (proChart A K R0)} {h : Pi1 A K} {n : ℕ} (hP : ∀ b : proChart A K R0, h • b - b ^ n ∈ P)
    (hL : h ∈ (IntermediateField.restrict hLU).fixingSubgroup) (y : integralClosure R0 L) :
    y ^ n - y ∈ P.comap (inclU R0 hLU) := by
  have hfix : h • inclU R0 hLU y = inclU R0 hLU y := Subtype.ext
    ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hL _ ((IntermediateField.mem_restrict hLU _).2 (y : L).2))
  have h1 := hP (inclU R0 hLU y)
  rw [hfix] at h1
  rw [Ideal.mem_comap, map_sub, map_pow]
  have h2 := P.neg_mem h1
  rwa [neg_sub] at h2

/-- **Boundary residue degrees at `L ⊔ K(𝔽_{p^k})`**: if `y^(p^k) ≡ y` on the ring of `L` modulo `P`, the residue
field of `L ⊔ K(𝔽_{p^k})` under `P` has at most `p^k` elements. -/
theorem card_quot_sup_le [Ring.HasFiniteQuotients R0] [Nontrivial R0]
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [FiniteDimensional K L]
    {k : ℕ} (hk : 0 < k) (hCU : constLevel K p k ≤ maxUnram A K) (P : Ideal (proChart A K R0)) [P.IsPrime]
    (hP : P ≠ ⊥) (hres : ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ P.comap (inclU R0 hLU)) :
    Nat.card (integralClosure R0 ↥(L ⊔ constLevel K p k) ⧸ P.comap (inclU R0 (sup_le hLU hCU))) ≤ p ^ k := by
  have hP0 : P.under R0 ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨h, hhL, hfr⟩ := exists_frob_level hLU P hP0 k hres
  have hL' := mem_fix_sup hLU hCU hhL (mem_fix_constLevel hk hCU hfr)
  set w := P.comap (inclU R0 (sup_le hLU hCU)) with hw
  have hwu : w.comap (algebraMap R0 (integralClosure R0 ↥(L ⊔ constLevel K p k))) = P.under R0 := by
    ext r
    show inclU R0 (sup_le hLU hCU) (algebraMap R0 _ r) ∈ P ↔ algebraMap R0 (proChart A K R0) r ∈ P
    rw [AlgHom.commutes]
  haveI : w.IsPrime := Ideal.comap_isPrime _ _
  haveI : w.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R0) w
    (by rw [hwu]; exact Ring.HasFiniteQuotients.maximalOfPrime hP0)
  letI : Field (integralClosure R0 ↥(L ⊔ constLevel K p k) ⧸ w) := Ideal.Quotient.field w
  refine (card_le_of_pow_eq (one_lt_pow_p hk) fun z => ?_).2
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_pow]
  exact Ideal.Quotient.eq.2 (pow_sub_mem_of_fix (sup_le hLU hCU) hfr hL' y)

end Chart

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_CP4a_Res =====
section

/-!
# S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants

For a nonzero prime `Q` of the pro-chart `B = proChart A K R0` with finite residue ring `R0 ⧸ (Q ∩ R0)` of order a
power of `q = p^e`, and assuming `K_U` contains primitive `(q^a - 1)`-th roots of unity for every `a ≥ 1`:

* `constSub`: the constants of `K_U` that lie in `B` form a subring;
* `const_eq_of_sub_mem`: two constants congruent mod a proper ideal are equal;
* `exists_const_sub_mem`: every element of `B` is congruent mod `Q` to a constant;
* `resEquiv`: so `constSub ≃+* B ⧸ Q`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

theorem isConst_pow_mul {L : Type} [Monoid L] {x : L} {Q n : ℕ} (h : x ^ Q ^ n = x) (k : ℕ) :
    x ^ Q ^ (n * k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

section Field

variable {L : Type} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p] (e : ℕ)

theorem isConst_common {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) :
    ∃ n, 0 < n ∧ x ^ p ^ (e * n) = x ∧ y ^ p ^ (e * n) = y := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨m, hm, hy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · rw [pow_mul]; exact isConst_pow_mul hx m
  · rw [pow_mul, mul_comm n m]; exact isConst_pow_mul hy n

theorem IsConst.add' {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) : IsConst (p ^ e) (x + y) := by
  obtain ⟨n, hn, h1, h2⟩ := isConst_common e hx hy
  exact ⟨n, hn, by rw [← pow_mul, add_pow_char_pow, h1, h2]⟩

theorem IsConst.sub' {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) : IsConst (p ^ e) (x - y) := by
  obtain ⟨n, hn, h1, h2⟩ := isConst_common e hx hy
  exact ⟨n, hn, by rw [← pow_mul, sub_pow_char_pow, h1, h2]⟩

theorem IsConst.mul' {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) : IsConst (p ^ e) (x * y) := by
  obtain ⟨n, hn, h1, h2⟩ := isConst_common e hx hy
  exact ⟨n, hn, by rw [← pow_mul, mul_pow, h1, h2]⟩

theorem isConst_one : IsConst (p ^ e) (1 : L) := ⟨1, one_pos, one_pow _⟩

theorem isConst_zero : IsConst (p ^ e) (0 : L) :=
  ⟨1, one_pos, zero_pow (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))⟩

end Field

section Res

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  (p e : ℕ) [hp : Fact p.Prime] [CharP K p]

theorem charP_maxUnram : CharP (maxUnram A K) p :=
  charP_of_injective_algebraMap (algebraMap K (maxUnram A K)).injective p

/-- The constants of `K_U` lying in the pro-chart. -/
def constSub : Subring (proChart A K R0) :=
  haveI := charP_maxUnram A K p
  { carrier := {x | IsConst (p ^ e) (x : maxUnram A K)}
    mul_mem' := fun {x y} hx hy => IsConst.mul' e hx hy
    one_mem' := isConst_one e
    add_mem' := fun {x y} hx hy => IsConst.add' e hx hy
    zero_mem' := isConst_zero e
    neg_mem' := fun {x} hx => by
      have h := IsConst.sub' e (isConst_zero e) hx
      simpa using h }

variable {A K R0 p e}

theorem mem_constSub {x : proChart A K R0} : x ∈ constSub A K R0 p e ↔ IsConst (p ^ e) (x : maxUnram A K) :=
  Iff.rfl

/-- Constants are integral over any chart. -/
theorem isIntegral_of_isConst (he : 0 < e) {y : maxUnram A K} (hy : IsConst (p ^ e) y) : IsIntegral R0 y := by
  obtain ⟨n, hn, hyn⟩ := hy
  have hn1 : 1 < p ^ (e * n) := one_lt_pow_p (p := p) (Nat.mul_pos he hn)
  have hyp : y ^ (p ^ (e * n)) = y := by rw [pow_mul]; exact hyn
  by_cases h0 : y = 0
  · rw [h0]; exact isIntegral_zero
  · refine IsIntegral.of_pow (by omega : 0 < p ^ (e * n) - 1) ?_
    rw [pow_pred_eq_one hn1.le hyp h0]
    exact isIntegral_one

/-- A constant as an element of the pro-chart. -/
def mkConst (he : 0 < e) (y : maxUnram A K) (hy : IsConst (p ^ e) y) : proChart A K R0 :=
  ⟨y, isIntegral_of_isConst he hy⟩

theorem mkConst_mem (he : 0 < e) (y : maxUnram A K) (hy : IsConst (p ^ e) y) :
    mkConst (R0 := R0) he y hy ∈ constSub A K R0 p e := hy

/-- Two constants congruent modulo a proper ideal of the pro-chart are equal. -/
theorem const_eq_of_sub_mem (he : 0 < e) {Q : Ideal (proChart A K R0)} (hQ : Q ≠ ⊤) {c c' : proChart A K R0}
    (hc : c ∈ constSub A K R0 p e) (hc' : c' ∈ constSub A K R0 p e) (h : c - c' ∈ Q) : c = c' := by
  haveI := charP_maxUnram A K p
  have hd : c - c' ∈ constSub A K R0 p e := sub_mem hc hc'
  by_contra hne
  obtain ⟨n, hn, hdn⟩ := hd
  have hn1 : 1 < p ^ (e * n) := one_lt_pow_p (p := p) (Nat.mul_pos he hn)
  have hdp : ((c - c' : proChart A K R0) : maxUnram A K) ^ (p ^ (e * n)) = (c - c' : proChart A K R0) := by
    rw [pow_mul]; exact hdn
  have hd0 : ((c - c' : proChart A K R0) : maxUnram A K) ≠ 0 := fun h0 =>
    hne (sub_eq_zero.1 (Subtype.val_injective (by simpa using h0)))
  have h1 : (c - c') ^ (p ^ (e * n) - 1) ∈ Q := Ideal.pow_mem_of_mem Q h _ (by omega)
  have h1' : (c - c') ^ (p ^ (e * n) - 1) = 1 := by
    apply Subtype.val_injective
    change ((c - c' : proChart A K R0) : maxUnram A K) ^ (p ^ (e * n) - 1) = 1
    rw [pow_pred_eq_one hn1.le hdp hd0]
  rw [h1'] at h1
  exact hQ ((Ideal.eq_top_iff_one Q).2 h1)

/-- In a field integral over a finite field of order `Q ^ d` (`d ≠ 0`), every element satisfies `y ^ Q ^ a = y`
for some `a ≥ 1`. -/
theorem exists_pow_eq_self_of_integral {k L : Type} [Field k] [Field L] [Algebra k L] [Finite k]
    [Algebra.IsIntegral k L] {Q d : ℕ} (hcard : Nat.card k = Q ^ d) (hd0 : d ≠ 0) (y : L) :
    ∃ a, 0 < a ∧ y ^ Q ^ a = y := by
  classical
  let E := IntermediateField.adjoin k {y}
  haveI : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : Finite E := Module.finite_of_finite k
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype k := Fintype.ofFinite k
  have hcE : Fintype.card E = Q ^ (d * Module.finrank k E) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := E), ← Nat.card_eq_fintype_card, hcard, pow_mul]
  have hr : 0 < Module.finrank k E := Module.finrank_pos
  refine ⟨d * Module.finrank k E, Nat.mul_pos (Nat.pos_of_ne_zero hd0) hr, ?_⟩
  have hpow := FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self k y⟩ : E)
  rw [hcE] at hpow
  exact congrArg Subtype.val hpow

/-- Every element of the residue field of a prime `Q` with finite residue ring below of order a power of `q`
satisfies `x̄ ^ (q ^ a) = x̄` for some `a ≥ 1`. -/
theorem exists_pow_sub_mem {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    [Finite (R0 ⧸ Q.under R0)] (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) (x : proChart A K R0) :
    ∃ a, 0 < a ∧ x ^ (p ^ e) ^ a - x ∈ Q := by
  have hPmax : (Q.under R0).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R0 ⧸ Q.under R0))
  have hQmax : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q hPmax
  letI := Ideal.Quotient.field (Q.under R0)
  letI := Ideal.Quotient.field Q
  obtain ⟨d, hd⟩ := hcard
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 : Nat.card (R0 ⧸ Q.under R0) = 1 := by rw [hd, pow_zero]
    exact (Finite.one_lt_card (α := R0 ⧸ Q.under R0)).ne' h1
  obtain ⟨a, ha, hpow⟩ := exists_pow_eq_self_of_integral (k := R0 ⧸ Q.under R0) hd hd0 (Ideal.Quotient.mk Q x)
  refine ⟨a, ha, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq] at hpow
  exact hpow

/-- Every element of the pro-chart is congruent to a constant modulo a prime `Q` as above. -/
theorem exists_const_sub_mem (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    [Finite (R0 ⧸ Q.under R0)] (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) (x : proChart A K R0) :
    ∃ c ∈ constSub A K R0 p e, x - c ∈ Q := by
  classical
  obtain ⟨a, ha, hxa⟩ := exists_pow_sub_mem hcard x
  obtain ⟨ζ, hζp⟩ := hζ a ha
  have hk1 : 1 < (p ^ e) ^ a := by rw [← pow_mul]; exact one_lt_pow_p (p := p) (Nat.mul_pos he ha)
  set k := (p ^ e) ^ a - 1 with hk
  have hkpos : 0 < k := by omega
  have hζc : IsConst (p ^ e) ζ := by
    refine ⟨a, ha, ?_⟩
    have h1 : ζ ^ k = 1 := hζp.pow_eq_one
    calc ζ ^ (p ^ e) ^ a = ζ ^ (k + 1) := by rw [hk, Nat.sub_add_cancel hk1.le]
      _ = ζ := by rw [pow_succ, h1, one_mul]
  let ζB : proChart A K R0 := mkConst he ζ hζc
  have hζB : IsPrimitiveRoot ζB k :=
    IsPrimitiveRoot.of_map_of_injective (f := (integralClosure R0 (maxUnram A K)).val) hζp Subtype.val_injective
  have hprod := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod hkpos hζB)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
  have hsplit : x ^ (p ^ e) ^ a - x = x * (x ^ k - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', hk, Nat.sub_add_cancel hk1.le]
  rw [hsplit] at hxa
  rcases (Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› hxa) with h0 | h1
  · exact ⟨0, zero_mem _, by simpa using h0⟩
  · rw [hprod] at h1
    obtain ⟨μ, hμ, hμQ⟩ := Ideal.IsPrime.prod_mem_iff.1 h1
    refine ⟨μ, ?_, hμQ⟩
    have hμk : μ ^ k = 1 := (mem_nthRootsFinset hkpos _).1 hμ
    refine ⟨a, ha, ?_⟩
    have : (μ : maxUnram A K) ^ k = 1 := by
      rw [← Subalgebra.coe_pow, hμk]; rfl
    calc (μ : maxUnram A K) ^ (p ^ e) ^ a = (μ : maxUnram A K) ^ (k + 1) := by rw [hk, Nat.sub_add_cancel hk1.le]
      _ = μ := by rw [pow_succ, this, one_mul]

variable (A K R0 p e)

/-- The residue isomorphism `constants ≃+* B ⧸ Q` at a boundary prime. -/
def resEquiv (he : 0 < e) (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    (Q : Ideal (proChart A K R0)) [Q.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) :
    constSub A K R0 p e ≃+* proChart A K R0 ⧸ Q :=
  RingEquiv.ofBijective ((Ideal.Quotient.mk Q).comp (constSub A K R0 p e).subtype)
    ⟨fun c c' h => Subtype.ext (const_eq_of_sub_mem he (Ideal.IsPrime.ne_top ‹_›) c.2 c'.2
        (Ideal.Quotient.eq.1 h)),
     fun y => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨c, hc, hxc⟩ := exists_const_sub_mem he hζ hcard x
      exact ⟨⟨c, hc⟩, (Ideal.Quotient.eq.2 hxc).symm⟩⟩

theorem resEquiv_apply (he : 0 < e) (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    (Q : Ideal (proChart A K R0)) [Q.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) (c : constSub A K R0 p e) :
    resEquiv A K R0 p e he hζ Q hcard c = Ideal.Quotient.mk Q (c : proChart A K R0) := rfl

end Res

end

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_CP4a_Trans =====
section

/-!
# S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues

* `isInvariant_proChart`: `(proChart A K R0)^{π₁(U)} = R0` (`R0` integrally closed with fraction field `K`).
* `exists_smul_of_under_eq'`: `π₁(U)` is transitive on the primes of the pro-chart over a prime of `R0` (profinite).
* `exists_stab_of_algEquiv`: the stabilizer of `Q` surjects onto `Aut((B ⧸ Q)/(R0 ⧸ Q ∩ R0))`.
* `exists_pi1geo_smul`: two primes `Q, Q'` (finite residue rings of `q`-power order) on which every `r ∈ R0` has the
  same constant residue are conjugate under `π₁^geo`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

section Trans

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

theorem isInvariant_proChart [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K] :
    Algebra.IsInvariant R0 (proChart A K R0) (Pi1 A K) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Pi1 A K, σ (b : maxUnram A K) = b := fun σ => congrArg Subtype.val (hb σ)
  obtain ⟨k, hk⟩ := (InfiniteGalois.mem_bot_iff_fixed (k := K) (K := maxUnram A K) (b : maxUnram A K)).2 hfix
  have hint : IsIntegral R0 k := by
    have hb' : IsIntegral R0 (b : maxUnram A K) := b.2
    rw [← hk] at hb'
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R0 K (maxUnram A K))
      (algebraMap K (maxUnram A K)).injective).1 hb'
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨a, Subtype.ext ?_⟩
  show algebraMap R0 (maxUnram A K) a = b
  rw [IsScalarTower.algebraMap_apply R0 K (maxUnram A K), ha]
  exact hk

theorem exists_smul_of_under_eq' [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
    (P Q : Ideal (proChart A K R0)) [P.IsPrime] [Q.IsPrime] (h : P.under R0 = Q.under R0) :
    ∃ g : Pi1 A K, Q = g • P := by
  letI : TopologicalSpace (proChart A K R0) := ⊥
  haveI : DiscreteTopology (proChart A K R0) := ⟨rfl⟩
  haveI : ContinuousSMul (Pi1 A K) (proChart A K R0) := by
    refine (continuousSMul_iff_stabilizer_isOpen).2 fun x => ?_
    refine Subgroup.isOpen_mono (H₁ := fixElt A K (x : maxUnram A K)) (fun σ hσ => ?_) (fixElt_isOpen A K _)
    exact Subtype.ext hσ
  haveI := isInvariant_proChart (A := A) (K := K) (R0 := R0)
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite P Q h

theorem exists_stab_of_algEquiv [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
    (Q : Ideal (proChart A K R0)) [Q.IsPrime]
    (σ' : (proChart A K R0 ⧸ Q) ≃ₐ[R0 ⧸ Q.under R0] (proChart A K R0 ⧸ Q)) :
    ∃ δ : Pi1 A K, δ • Q = Q ∧ ∀ b, Ideal.Quotient.mk Q (δ • b) = σ' (Ideal.Quotient.mk Q b) := by
  letI : TopologicalSpace (proChart A K R0) := ⊥
  haveI : DiscreteTopology (proChart A K R0) := ⟨rfl⟩
  haveI : ContinuousSMul (Pi1 A K) (proChart A K R0) := by
    refine (continuousSMul_iff_stabilizer_isOpen).2 fun x => ?_
    refine Subgroup.isOpen_mono (H₁ := fixElt A K (x : maxUnram A K)) (fun σ hσ => ?_) (fixElt_isOpen A K _)
    exact Subtype.ext hσ
  haveI := isInvariant_proChart (A := A) (K := K) (R0 := R0)
  obtain ⟨⟨δ, hδ⟩, hδσ⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Pi1 A K) (Q.under R0) Q σ'
  refine ⟨δ, hδ, fun b => ?_⟩
  rw [← hδσ]
  rfl

theorem mul_inv_smul_of_smul_eq {G α : Type*} [Group G] [MulAction G α] {σ δ : G} {x : α} (h : δ • x = x) :
    (σ * δ⁻¹) • x = σ • x := by
  rw [mul_smul, inv_smul_eq_iff.2 h.symm]

variable {p e : ℕ} [hp : Fact p.Prime] [CharP K p]

variable (R0 p e) in
/-- `σ ∈ π₁(U)` permutes the constants of the pro-chart. -/
def constSmul (σ : Pi1 A K) : constSub A K R0 p e ≃+* constSub A K R0 p e where
  toFun c := ⟨σ • (c : proChart A K R0), (mem_constSub.1 c.2).map σ⟩
  invFun c := ⟨σ⁻¹ • (c : proChart A K R0), (mem_constSub.1 c.2).map σ⁻¹⟩
  left_inv c := Subtype.ext (inv_smul_smul σ (c : proChart A K R0))
  right_inv c := Subtype.ext (smul_inv_smul σ (c : proChart A K R0))
  map_mul' x y := Subtype.ext (smul_mul' σ (x : proChart A K R0) y)
  map_add' x y := Subtype.ext (smul_add σ (x : proChart A K R0) y)

set_option synthInstance.maxHeartbeats 200000 in
/-- **Geometric transitivity**: boundary-type primes with the same constant residues on `R0` are `π₁^geo`-conjugate. -/
theorem exists_pi1geo_smul [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K] (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    {Q Q' : Ideal (proChart A K R0)} [Q.IsPrime] [Q'.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
    (hres : ∀ r : R0, ∀ c ∈ constSub A K R0 p e,
      algebraMap R0 (proChart A K R0) r - c ∈ Q → algebraMap R0 (proChart A K R0) r - c ∈ Q') :
    ∃ g ∈ pi1geo A K (p ^ e), Q' = g • Q := by
  have hres' : ∀ r : R0, ∀ c ∈ constSub A K R0 p e,
      algebraMap R0 (proChart A K R0) r - c ∈ Q' → algebraMap R0 (proChart A K R0) r - c ∈ Q := by
    intro r c hc h'
    obtain ⟨c0, hc0, h0⟩ := exists_const_sub_mem he hζ hcard (algebraMap R0 (proChart A K R0) r)
    have h0' := hres r c0 hc0 h0
    have hcc : c0 = c := const_eq_of_sub_mem he (Ideal.IsPrime.ne_top ‹_›) hc0 hc (by
      have h2 := Q'.sub_mem h' h0'
      rwa [sub_sub_sub_cancel_left] at h2)
    rw [← hcc]
    exact h0
  have hunder : Q.under R0 = Q'.under R0 := by
    ext r
    simp only [Ideal.under, Ideal.mem_comap]
    constructor
    · intro h
      simpa using hres r 0 (zero_mem _) (by simpa using h)
    · intro h
      simpa using hres' r 0 (zero_mem _) (by simpa using h)
  obtain ⟨σ, hσ⟩ := exists_smul_of_under_eq' Q Q' hunder
  have hσc : ∀ r : R0, ∀ c ∈ constSub A K R0 p e, algebraMap R0 (proChart A K R0) r - c ∈ Q →
      algebraMap R0 (proChart A K R0) r - σ • c ∈ Q := by
    intro r c hc h
    have h1 : algebraMap R0 (proChart A K R0) r - σ • c ∈ Q' := by
      rw [hσ]
      have h2 := Ideal.smul_mem_pointwise_smul σ _ Q h
      rwa [smul_sub, smul_algebraMap] at h2
    exact hres' r _ ((constSmul R0 p e σ ⟨c, hc⟩).2) h1
  let e0 := resEquiv A K R0 p e he hζ Q hcard
  let eR : (proChart A K R0 ⧸ Q) ≃+* (proChart A K R0 ⧸ Q) := e0.symm.trans ((constSmul R0 p e σ).trans e0)
  have heR : ∀ c : constSub A K R0 p e, eR (Ideal.Quotient.mk Q (c : proChart A K R0)) =
      Ideal.Quotient.mk Q (σ • (c : proChart A K R0)) := by
    intro c
    show e0 (constSmul R0 p e σ (e0.symm (e0 c))) = _
    rw [e0.symm_apply_apply]
    rfl
  have hcomm : ∀ y : R0 ⧸ Q.under R0, eR (algebraMap _ _ y) = algebraMap _ _ y := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc, hrc⟩ := exists_const_sub_mem he hζ hcard (algebraMap R0 (proChart A K R0) r)
    change eR (Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r)) =
      Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r)
    rw [Ideal.Quotient.eq.2 hrc, heR ⟨c, hc⟩]
    exact (Ideal.Quotient.eq.2 ((Ideal.Quotient.eq.1 (Ideal.Quotient.eq.2 (hσc r c hc hrc))))).symm.trans
      (Ideal.Quotient.eq.2 hrc)
  obtain ⟨δ, hδQ, hδ⟩ := exists_stab_of_algEquiv Q (AlgEquiv.ofRingEquiv (f := eR) hcomm)
  have hδc : ∀ c ∈ constSub A K R0 p e, δ • c = σ • c := by
    intro c hc
    have h1 : Ideal.Quotient.mk Q (δ • c) = Ideal.Quotient.mk Q (σ • c) := by
      rw [hδ]
      exact heR ⟨c, hc⟩
    exact const_eq_of_sub_mem he (Ideal.IsPrime.ne_top ‹_›) ((mem_constSub.1 hc).map δ)
      ((mem_constSub.1 hc).map σ) (Ideal.Quotient.eq.1 h1)
  refine ⟨σ * δ⁻¹, ?_, ?_⟩
  · rw [mem_pi1geo]
    intro y hy
    have h := hδc (mkConst he (σ⁻¹ • y) (hy.map σ⁻¹)) (mkConst_mem he _ _)
    have hv : δ • (σ⁻¹ • y) = y := (congrArg Subtype.val h).trans (smul_inv_smul σ y)
    show (σ * δ⁻¹) • y = y
    rw [mul_smul, inv_smul_eq_iff.2 hv.symm, smul_inv_smul]
  · exact hσ.trans (mul_inv_smul_of_smul_eq hδQ).symm

end Trans

end

end RamanujanPetersson.CP4a

end



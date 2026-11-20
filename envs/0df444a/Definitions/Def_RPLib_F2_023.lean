-- Prove2me | Definitions.Def_RPLib_F2_023
-- name    : RPLib_F2_023
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T10:55:01.076177+00:00
-- url     : https://prove2.me/theorems/9a493d32-25d5-4cd2-b96c-0890dc12d629
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 023 of 70
-- statement:
--   File 023 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Cone_LevProd`: S4-PD (4), E4B part 1: the product formula at a finite level
--   * `S4.Def_RP_TameInertia_Onto`: Tame inertia, part Onto: the tame character reaches every `N`-th root of unity (S4-PD item (2), T8)
--   * `S4.Def_RP_TameInertia_Main`: Tame inertia, part Main: `Hom(I_x, ℤ/N) = ℤ/N(-1)` (S4-PD item (2))
--   * `S4.Def_RP_Cone_LocKum`: S4-PD (4), E4L part 1: local Kummer theory at a finite level, for subgroups of an inertia group
--   * `S4.Def_RP_Cone_LocKumJ`: S4-PD (4), E4L part 2: tame inertia for a subgroup of finite exponent-index in `I(Q)`
--   * `S4.Def_RP_Cone_LocRam`: S4-PD (4), E4L part 3: the ramification converse at a finite level
--   * `S4.Def_RP_Cone_LocNorm`: S4-PD (4), E4L part 4: the normalised tame generator at a finite level
--   * `S4.Def_RP_Cone_ResRad`: S4-PD (4), E4B part 5a: radicands in constant levels, and normalisation along constant extensions
--   * `S4.Def_RP_Cone_ResFrob`: S4-PD (4), E4B part 3b: Frobenius elements in decomposition groups and boundary residue degrees
--   * `S4.Def_RP_Cone_ResOrb`: S4-PD (4), E4B part 3(iii): boundary primes over one place of a level are geometrically conjugate
--   * `S4.Def_RP_Cone_ResCard`: S4-PD (4), E4B part 3a: residue field cardinalities at a level
--   * `S4.Def_RP_Cone_ResMax`: S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels
--   * `S4.Def_RP_Cone_ResCos`: S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)
--   * `S4.Def_RP_TameInertia_Coef`: Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_022

/-!
# Ramanujan-Petersson curve library (flat edition), file 023 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Cone_LevProd`: S4-PD (4), E4B part 1: the product formula at a finite level
* `S4.Def_RP_TameInertia_Onto`: Tame inertia, part Onto: the tame character reaches every `N`-th root of unity (S4-PD item (2), T8)
* `S4.Def_RP_TameInertia_Main`: Tame inertia, part Main: `Hom(I_x, ℤ/N) = ℤ/N(-1)` (S4-PD item (2))
* `S4.Def_RP_Cone_LocKum`: S4-PD (4), E4L part 1: local Kummer theory at a finite level, for subgroups of an inertia group
* `S4.Def_RP_Cone_LocKumJ`: S4-PD (4), E4L part 2: tame inertia for a subgroup of finite exponent-index in `I(Q)`
* `S4.Def_RP_Cone_LocRam`: S4-PD (4), E4L part 3: the ramification converse at a finite level
* `S4.Def_RP_Cone_LocNorm`: S4-PD (4), E4L part 4: the normalised tame generator at a finite level
* `S4.Def_RP_Cone_ResRad`: S4-PD (4), E4B part 5a: radicands in constant levels, and normalisation along constant extensions
* `S4.Def_RP_Cone_ResFrob`: S4-PD (4), E4B part 3b: Frobenius elements in decomposition groups and boundary residue degrees
* `S4.Def_RP_Cone_ResOrb`: S4-PD (4), E4B part 3(iii): boundary primes over one place of a level are geometrically conjugate
* `S4.Def_RP_Cone_ResCard`: S4-PD (4), E4B part 3a: residue field cardinalities at a level
* `S4.Def_RP_Cone_ResMax`: S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels
* `S4.Def_RP_Cone_ResCos`: S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)
* `S4.Def_RP_TameInertia_Coef`: Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)
-/

set_option autoImplicit false

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

end Level

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Onto =====
section

/-!
# Tame inertia, part Onto: the tame character reaches every `N`-th root of unity (S4-PD item (2), T8)

At a boundary prime `Q` of the pro-chart (a pole `a ∈ A` at `x = Q ∩ R0`), take the pole element `f` of order
`N n + 1` (`exists_pole_mod`), the Abhyankar polynomial `abhy p N f` (roots in `K_U`), a finite Galois level `L ≤ K_U`
containing its roots and `ζ`, the small root `w` of `X^(p+1) - f X + 1` and `z^N = w`. The count
`exists_inertia_smul_eq` at `P = Q ∩ B_L` and the inertia lift `exists_inertia_lift` give
`exists_inertia_zeta_mul`: some `Z ∈ K_U` with `Z^N` fixed by every element of `Pi1` stabilising `Q` (in particular
by `I(Q)`, `stab_of_mem_inertia`) and `g ∈ I(Q)` with `g Z = ζ Z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain WithZero

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer Swan

noncomputable section

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **T8.** At a boundary prime with a pole, some `Z ∈ K_U` has `Z^N` fixed by the stabiliser of `Q` (so by the
inertia group `I(Q)`) and an inertia element `g` with `g Z = ζ Z`, for any `N`-th root of unity `ζ ∈ K_U` (`N` a unit). -/
theorem exists_inertia_zeta_mul {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N : ℕ} (hN0 : 0 < N)
    (hN : IsUnit (N : A)) {ζ : maxUnram A K} (hζ : ζ ^ N = 1)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a)) :
    ∃ Z : maxUnram A K, Z ≠ 0 ∧ (∀ σ : Pi1 A K, (∀ b : proChart A K R0, σ • b ∈ Q ↔ b ∈ Q) → σ (Z ^ N) = Z ^ N) ∧
      ∃ g ∈ Q.inertia (Pi1 A K), g Z = ζ * Z := by
  classical
  haveI := hQ.1
  have : Nontrivial A := (algebraMap A K).domain_nontrivial
  have hp : 0 < p := (Fact.out : p.Prime).pos
  -- the pole element `f` of order `N n + 1`
  obtain ⟨f, n, -, hfv⟩ := exists_pole_mod x (N - 1) ha
  have hNN : N - 1 + 1 = N := Nat.sub_add_cancel hN0
  rw [hNN] at hfv
  have hcN : Nat.Coprime (N * n + 1) N := by
    have h := coprime_pole_order (N - 1) n
    rwa [hNN] at h
  -- the level `L`
  obtain ⟨s, hsdef⟩ : ∃ s : Finset (AlgebraicClosure K), s = insert (ζ : AlgebraicClosure K)
      (((abhy p N f).map (algebraMap A K)).aroots (AlgebraicClosure K)).toFinset := ⟨_, rfl⟩
  have hroot : ∀ y : AlgebraicClosure K, aeval y (abhy p N f) = 0 → y ∈ s := by
    intro y hy
    rw [hsdef, Finset.mem_insert, Multiset.mem_toFinset]
    refine Or.inr (mem_aroots.2 ⟨((abhy_monic hp hN0 f).map (algebraMap A K)).ne_zero, ?_⟩)
    rw [aeval_map_algebraMap]
    exact hy
  obtain ⟨L, hL, hsL⟩ := exists_unramSet_of_finite A K s (by
    intro y hy
    rw [hsdef, Finset.mem_insert, Multiset.mem_toFinset] at hy
    rcases hy with rfl | hy
    · exact ζ.2
    · have h := (mem_aroots.1 hy).2
      rw [aeval_map_algebraMap] at h
      exact mem_maxUnram_abhy hp hN f h)
  have hsL' : ∀ y ∈ s, y ∈ L := fun y hy => hsL (IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 hy))
  haveI : FiniteDimensional K L := hL.1
  haveI : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  haveI : IsFractionRing (integralClosure R0 L) L := integralClosure.isFractionRing_of_finite_extension (A := R0) K L
  haveI : IsDedekindDomain (integralClosure R0 L) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := L)
  haveI : Module.Finite R0 (integralClosure R0 L) := IsIntegralClosure.finite R0 K L (integralClosure R0 L)
  haveI : IsGaloisGroup (L ≃ₐ[K] L) R0 (integralClosure R0 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R0 (integralClosure R0 L) K L
  haveI : Module.IsTorsionFree R0 (integralClosure R0 L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_integralClosure_injective R0 L)
  haveI : Ring.HasFiniteQuotients (integralClosure R0 L) := Ring.HasFiniteQuotients.of_module_finite R0 _
  -- the prime `P` of `B_L` under `Q`
  obtain ⟨P0, hP0def⟩ : ∃ P0 : Ideal (integralClosure R0 L), P0 = Q.comap (inclU R0 hLU) := ⟨_, rfl⟩
  have hPp : P0.IsPrime := by rw [hP0def]; exact Ideal.IsPrime.comap _
  have hP0 : P0 ≠ ⊥ := by
    haveI : Nontrivial R0 := (algebraMap R0 K).domain_nontrivial
    obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    have h1 : Q.comap (algebraMap R0 (proChart A K R0)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hy0 hyQ (Algebra.IsIntegral.isIntegral y)
    obtain ⟨r, hrQ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    refine (Submodule.ne_bot_iff _).2 ⟨algebraMap R0 (integralClosure R0 L) r, ?_, ?_⟩
    · rw [hP0def, Ideal.mem_comap, AlgHom.commutes]
      exact hrQ
    · intro h
      exact hr0 (algebraMap_integralClosure_injective R0 L (h.trans (map_zero _).symm))
  let P : HeightOneSpectrum (integralClosure R0 L) := ⟨P0, hPp, hP0⟩
  haveI : Finite (integralClosure R0 L ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have hP : P.asIdeal = Q.comap (inclU R0 hLU) := hP0def
  have hxP : P.under R0 = x := by
    refine HeightOneSpectrum.ext ?_
    ext r
    show algebraMap R0 (integralClosure R0 L) r ∈ P0 ↔ r ∈ x.asIdeal
    rw [hP0def, Ideal.mem_comap, AlgHom.commutes, hx, Ideal.mem_comap]
  -- valuations of `f`
  have hf0 : algebraMap A K f ≠ 0 := by
    intro h
    rw [h, map_zero] at hfv
    exact exp_ne_zero hfv.symm
  have hav : adicAdd (P.under R0) (algebraMap A K f) = ((-((N * n + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hxP, adicAdd_apply, negLogV_of_ne x hf0, hfv, log_exp]
  have hF : 1 < P.valuation L (algebraMap K L (algebraMap A K f)) :=
    one_lt_valuation_level hLU x hx P hP (by
      rw [hfv, ← exp_zero, exp_lt_exp]
      exact_mod_cast Nat.succ_pos _)
  -- the trinomial splits in `L`
  have hudL : udField A K (abhy p N f) ≤ L := by
    show IntermediateField.adjoin K _ ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    refine hsL' y (hroot y ?_)
    have h := (mem_rootSet.1 hy).2
    rwa [aeval_map_algebraMap] at h
  have hs1 : (((abhy p 1 f).map (algebraMap A K)).map (algebraMap K L)).Splits := by
    refine IntermediateField.splits_of_splits (IsAlgClosed.splits _) fun y hy => ?_
    exact hudL (udField_abhy_one_le hp hN0 f (IntermediateField.subset_adjoin K _ hy))
  have hs : (trin p (algebraMap K L (algebraMap A K f))).Splits := by
    rw [← map_abhy_one]
    exact hs1
  -- the small root `w` and `z^N = w`
  obtain ⟨w, ⟨hw, hwv⟩, -⟩ := trin_existsUnique_small (P.valuation L) hp hF hs
  have hw' := (trin_isRoot_iff p _ w).1 hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w : AlgebraicClosure K) hN0
  have hzr : aeval z (abhy p N f) = 0 := by
    have h := congrArg L.val hw'
    rw [map_add, map_sub, map_mul, map_pow, map_one, map_zero, AlgHom.commutes] at h
    rw [aeval_abhy, hz, IsScalarTower.algebraMap_apply A K (AlgebraicClosure K)]
    exact h
  let zL : L := ⟨z, hsL' z (hroot z hzr)⟩
  have hzN : zL ^ N = w := L.val.injective (by rw [map_pow]; exact hz)
  let ζL : L := ⟨(ζ : AlgebraicClosure K), hsL' _ (by rw [hsdef]; exact Finset.mem_insert_self _ _)⟩
  have hζN : ζL ^ N = 1 := L.val.injective (by
    have h := congrArg (maxUnram A K).val hζ
    rw [map_pow, map_one] at h
    rw [map_pow, map_one]
    exact h)
  -- the count at level `L` and the lift
  obtain ⟨τ, hτI, hτz⟩ := exists_inertia_smul_eq (R := R0) (G := L ≃ₐ[K] L) (fun _ _ => rfl) P hp hN0 hcN hav
    hF hs (fun σ => σ.commutes _) hw hwv hzN hζN
  have hτ' : τ ∈ (Q.comap (inclU R0 hLU)).inertia (L ≃ₐ[K] L) := by
    rw [← hP]
    exact hτI
  obtain ⟨g, hgI, hg⟩ := exists_inertia_lift hLU hτ'
  have hzL0 : zL ≠ 0 := fun h => hw0 (by rw [← hzN, h, zero_pow hN0.ne'])
  refine ⟨IntermediateField.inclusion hLU zL, (map_ne_zero_iff _ (IntermediateField.inclusion hLU).injective).2 hzL0,
    fun σ hσ => ?_, g, hgI, ?_⟩
  · rw [← map_pow (IntermediateField.inclusion hLU) zL N, hzN]
    exact fix_of_stab_small hLU P hP hp hF hs hw hwv hσ
  · have hτz' : τ zL = ζL * zL := hτz
    rw [hg, hτz', map_mul]
    rfl

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Main =====
section

/-!
# Tame inertia, part Main: `Hom(I_x, ℤ/N) = ℤ/N(-1)` (S4-PD item (2))

At a boundary prime `Q` of the pro-chart (a pole at `x = Q ∩ R0`), with `N` a unit and `ζ` a primitive `N`-th root of
unity fixed by inertia: the Kummer character `θ = kchar ζ Z` of the radical `Z` of `exists_inertia_zeta_mul` is a
locally constant homomorphism `I(Q) → ℤ/N` taking the value `1`, every locally constant homomorphism
`χ : I(Q) → ℤ/N` is `k θ` for a unique `k`, and `θ` is twisted by the cyclotomic character: for `φ ∈ Pi1` stabilising
`Q` with `φ ζ = ζ ^ w`, `θ σ = w θ (φ⁻¹ σ φ)` (`exists_tame_char`). So `Hom(I(Q), ℤ/N) ≅ ℤ/N(-1)` as a module over the
decomposition group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- **Tame inertia (item (2)).** The tame character `θ : I(Q) → ℤ/N` is a locally constant homomorphism with
`θ σ₀ = 1` for some `σ₀`, every locally constant homomorphism `I(Q) → ℤ/N` is a unique multiple of `θ`, and for
`φ` stabilising `Q` with `φ ζ = ζ ^ w` one has `θ σ = w * θ (φ⁻¹ σ φ)` (the twist by `ℤ/N(-1)`). -/
theorem exists_tame_char {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N : ℕ} [NeZero N]
    (hNA : IsUnit (N : A)) (hNR : IsUnit (N : R0)) {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
    (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : IsDedekindDomain.HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a)) :
    ∃ θ : Q.inertia (Pi1 A K) → ZMod N, IsLocallyConstant θ ∧ (∀ σ τ, θ (σ * τ) = θ σ + θ τ) ∧
      (∃ σ₀, θ σ₀ = 1) ∧ (∀ χ : Q.inertia (Pi1 A K) → ZMod N, IsLocallyConstant χ →
        (∀ σ τ, χ (σ * τ) = χ σ + χ τ) → ∃! k : ZMod N, ∀ σ, χ σ = k * θ σ) ∧
      ∀ φ : Pi1 A K, ∀ hφ : (∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q), ∀ w : ZMod N, φ ζ = epow ζ w →
        ∀ σ (hσ : σ ∈ Q.inertia (Pi1 A K)), θ ⟨σ, hσ⟩ = w * θ ⟨φ⁻¹ * σ * φ, inertia_conj hφ hσ⟩ := by
  haveI := hQ.1
  obtain ⟨Z, hZ0, hZD, g, hgI, hgZ⟩ :=
    exists_inertia_zeta_mul (p := p) hQ (NeZero.pos N) hNA hζ.pow_eq_one x hx ha
  have hZI : ∀ σ ∈ Q.inertia (Pi1 A K), σ (Z ^ N) = Z ^ N := fun σ hσ => hZD σ (stab_of_mem_inertia hσ)
  let α : (maxUnram A K)ˣ := Units.mk0 Z hZ0
  have hα : α ∈ rad (Q.inertia (Pi1 A K)) N := fun σ hσ => hZI σ hσ
  have h1 : kchar hζ (Γ := Q.inertia (Pi1 A K)) α ⟨g, hgI⟩ = 1 := by
    rw [kchar_eq_iff hζ hα, epow_one_eq hζ]
    exact hgZ
  refine ⟨kchar hζ (Γ := Q.inertia (Pi1 A K)) α, isLocallyConstant_kchar hζ α, kchar_mul hζ hζI hα,
    ⟨⟨g, hgI⟩, h1⟩, fun χ hχc hχ => ?_, fun φ hφ w hw σ hσ => ?_⟩
  · obtain ⟨k, hk⟩ := exists_eq_mul_of_surj (fun χ' hc' h' => exists_ne_eq_of_family hQ hNR hζ hζI χ' hc' h')
      (isLocallyConstant_kchar hζ α) (kchar_mul hζ hζI hα) h1 hχc hχ
    refine ⟨k, hk, fun k' hk' => ?_⟩
    have h2 := (hk' ⟨g, hgI⟩).symm.trans (hk ⟨g, hgI⟩)
    rwa [h1, mul_one, mul_one] at h2
  · -- the twist: `kchar (φ α) = kchar α` since `φ Z / Z` is an `N`-th root of unity, then `kchar_conj`
    have hφΓ : ∀ τ ∈ Q.inertia (Pi1 A K), φ⁻¹ * τ * φ ∈ Q.inertia (Pi1 A K) := fun τ hτ => inertia_conj hφ hτ
    have hφα : Units.map (φ : maxUnram A K →* maxUnram A K) α ∈ rad (Q.inertia (Pi1 A K)) N := by
      intro τ hτ
      show τ ((φ Z) ^ N) = (φ Z) ^ N
      rw [← map_pow, hZD φ hφ]
      exact hZI τ hτ
    have hφZ0 : φ Z ≠ 0 := (map_ne_zero_iff _ φ.injective).2 hZ0
    have hβ1 : (φ Z / Z) ^ N = 1 := by
      rw [div_pow, ← map_pow, hZD φ hφ, div_self (pow_ne_zero _ hZ0)]
    let β : (maxUnram A K)ˣ := Units.mk0 (φ Z / Z) (div_ne_zero hφZ0 hZ0)
    have hβfix : β ∈ fixUnits (Q.inertia (Pi1 A K)) := by
      intro τ hτ
      show τ (φ Z / Z) = φ Z / Z
      rw [← epow_dlog hζ hβ1]
      exact map_epow (hζI τ hτ) _
    have hβα : Units.map (φ : maxUnram A K →* maxUnram A K) α = β * α := by
      apply Units.ext
      show φ Z = φ Z / Z * Z
      rw [div_mul_cancel₀ _ hZ0]
    have key := kchar_conj hζ φ hφΓ hw hα hφα ⟨σ, hσ⟩
    rw [hβα, kchar_mul_left hζ (fixUnits_le_rad _ N hβfix) hα, kchar_of_fix hζ hβfix, zero_add] at key
    exact key

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_LocKum =====
section

/-!
# S4-PD (4), E4L part 1: local Kummer theory at a finite level, for subgroups of an inertia group

Let `Q` be a prime of the pro-chart, `M ≤ K_U` a finite level with the prime `v = Q ∩ B_M` (`B_M = integralClosure R0 M`),
and `Γ' ≤ I(Q)` a subgroup fixing `M` pointwise (e.g. `Γ' = I(Q) ⊓ H` for the open subgroup `H` fixing a cover level).

* `fix_of_val_dvd_lev`: `γ ^ N = a ∈ M` with `N ∣ v(a)` ⇒ every `σ ∈ I(Q)` fixing `M` fixes `γ` (local Kummer lemma at `M`).
* `kchar_eq_of_val_lev`: Kummer characters on `Γ'` of radicals `α, β` with `α ^ N, β ^ N ∈ M` agree as soon as
  `v(α ^ N) ≡ v(β ^ N) mod N`.
* `exists_ne_eq_of_family_le` (T3 for `Γ'`): among `N + 1` locally constant characters `Γ' → ℤ/N` two coincide, so
  `#Hom_cont(Γ', ℤ/N) ≤ N`; with an onto character `exists_eq_mul_of_surj` makes `Hom_cont(Γ', ℤ/N)` cyclic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- Local Kummer lemma at a finite level `M`: if `γ ^ N = a ∈ M` and `N ∣ v(a)` at `v = Q ∩ B_M`, every inertia
element fixing `M` fixes `γ`. -/
theorem fix_of_val_dvd_lev {Q : Ideal (proChart A K R0)} [Q.IsPrime] {N : ℕ} (hN : IsUnit (N : R0))
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    {σ : Pi1 A K} (hσ : σ ∈ Q.inertia (Pi1 A K))
    (hσM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → σ x = x)
    {γ : maxUnram A K} {a : M} (ha0 : a ≠ 0) (hγ : γ ^ N = IntermediateField.inclusion hMU a)
    (hdvd : (N : ℤ) ∣ WithZero.log (v.valuation M a)) : σ γ = γ := by
  obtain ⟨c, b, s', hc0, hb, hs', hcbs⟩ := exists_pow_mul_of_dvd v ha0 hdvd
  have hNp : IsUnit (N : proChart A K R0) := by
    simpa using hN.map (algebraMap R0 (proChart A K R0))
  have hγ' : γ ^ N * ((inclU R0 hMU s' : proChart A K R0) : maxUnram A K) =
      (IntermediateField.inclusion hMU c) ^ N * ((inclU R0 hMU b : proChart A K R0) : maxUnram A K) := by
    have h1 := congrArg (IntermediateField.inclusion hMU) hcbs
    simp only [map_mul, map_pow] at h1
    have e2 : ∀ y : integralClosure R0 M, IntermediateField.inclusion hMU (algebraMap _ M y) =
        ((inclU R0 hMU y : proChart A K R0) : maxUnram A K) := fun y => rfl
    rw [e2, e2] at h1
    rw [hγ]
    exact h1
  have hbQ : inclU R0 hMU b ∉ Q := fun h => hb (by rw [hv]; exact h)
  have hsQ : inclU R0 hMU s' ∉ Q := fun h => hs' (by rw [hv]; exact h)
  exact fix_of_inertia_local A K R0 hNp hσ ((map_ne_zero (IntermediateField.inclusion hMU)).2 hc0) hbQ hsQ
    (hσM _ c.2) (hσM _ (b : M).2) (hσM _ (s' : M).2) hγ'

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- Kummer characters on `Γ' ≤ I(Q)` (fixing the level `M`) of radicals with `N`-th powers in `M` are determined by
the valuations of the radicands mod `N`. -/
theorem kchar_eq_of_val_lev {Q : Ideal (proChart A K R0)} [Q.IsPrime] {N : ℕ} [NeZero N] (hN : IsUnit (N : R0))
    {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N) {Γ' : Subgroup (Pi1 A K)} (hΓ' : Γ' ≤ Q.inertia (Pi1 A K))
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    (hΓM : ∀ σ ∈ Γ', ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → σ x = x)
    {α β : (maxUnram A K)ˣ} (hα : α ∈ rad Γ' N) (hβ : β ∈ rad Γ' N) {a b : M} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU a)
    (hb : (β : maxUnram A K) ^ N = IntermediateField.inclusion hMU b)
    (hab : ((WithZero.log (v.valuation M a) : ℤ) : ZMod N) = ((WithZero.log (v.valuation M b) : ℤ) : ZMod N)) :
    kchar hζ (Γ := Γ') α = kchar hζ (Γ := Γ') β := by
  funext σ
  have hdvd : (N : ℤ) ∣ WithZero.log (v.valuation M (a / b)) := by
    rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 ha0) ((Valuation.ne_zero_iff _).2 hb0)]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).1 hab.symm
  have hγ : ((α : maxUnram A K) / (β : maxUnram A K)) ^ N = IntermediateField.inclusion hMU (a / b) := by
    rw [div_pow, ha, hb, map_div₀]
  have hfix := fix_of_val_dvd_lev hN hMU v hv (hΓ' σ.2) (hΓM σ σ.2) (div_ne_zero ha0 hb0) hγ hdvd
  have hi := kchar_spec hζ hα σ
  have hj := kchar_spec hζ hβ σ
  have hα0 : ((α : (maxUnram A K)ˣ) : maxUnram A K) ≠ 0 := α.ne_zero
  have hβ0 : ((β : (maxUnram A K)ˣ) : maxUnram A K) ≠ 0 := β.ne_zero
  have hb0' := epow_ne_zero hζ (kchar hζ (Γ := Γ') β σ)
  rw [map_div₀, hi, hj, div_eq_div_iff (mul_ne_zero hb0' hβ0) hβ0] at hfix
  apply epow_injective hζ
  have h5 : (epow ζ (kchar hζ (Γ := Γ') α σ) - epow ζ (kchar hζ (Γ := Γ') β σ)) *
      (((α : (maxUnram A K)ˣ) : maxUnram A K) * ((β : (maxUnram A K)ˣ) : maxUnram A K)) = 0 := by
    linear_combination hfix
  rcases mul_eq_zero.1 h5 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (mul_ne_zero hα0 hβ0)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- T3 for a subgroup `Γ' ≤ I(Q)`: among `N + 1` locally constant characters `Γ' → ℤ/N` two coincide. -/
theorem exists_ne_eq_of_family_le {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q) {N : ℕ} [NeZero N]
    (hN : IsUnit (N : R0)) {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N) {Γ' : Subgroup (Pi1 A K)}
    (hΓ' : Γ' ≤ Q.inertia (Pi1 A K)) (hζΓ : ∀ σ ∈ Γ', σ ζ = ζ)
    (χ : Fin (N + 1) → Γ' → ZMod N) (hχc : ∀ i, IsLocallyConstant (χ i))
    (hχ : ∀ i σ τ, χ i (σ * τ) = χ i σ + χ i τ) : ∃ i j, i ≠ j ∧ χ i = χ j := by
  classical
  haveI := hQ.1
  choose α hαr hαχ using fun i => exists_kchar_eq hζ hζΓ (χ i) (hχc i) (hχ i)
  obtain ⟨s, hs⟩ : ∃ s : Finset (AlgebraicClosure K), s = Finset.univ.image
      (fun i => ((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K)) := ⟨_, rfl⟩
  have hsmem : ∀ i, ((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K) ∈
      (s : Set (AlgebraicClosure K)) := fun i => by
    rw [hs, Finset.coe_image]
    exact ⟨i, by simp, rfl⟩
  obtain ⟨L, hL, hML⟩ := exists_unramSet_of_finite A K s (by
    intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact SetLike.coe_mem _)
  obtain ⟨M, hMdef⟩ : ∃ M : IntermediateField K (AlgebraicClosure K),
      M = IntermediateField.adjoin K (s : Set (AlgebraicClosure K)) := ⟨_, rfl⟩
  rw [← hMdef] at hML
  haveI : FiniteDimensional K L := hL.1
  haveI : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  have hMU : M ≤ maxUnram A K := hML.trans hLU
  haveI : FiniteDimensional K M := FiniteDimensional.of_injective
    (IntermediateField.inclusion hML).toLinearMap (IntermediateField.inclusion hML).injective
  haveI : Algebra.IsSeparable K M :=
    Algebra.IsSeparable.of_algHom (F := K) (E' := L) (IntermediateField.inclusion hML)
  haveI : IsFractionRing (integralClosure R0 M) M :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K M
  haveI : IsDedekindDomain (integralClosure R0 M) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := M)
  -- `M` is fixed by `Γ'`
  have hfixM : ∀ σ ∈ Γ', ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → σ x = x := by
    intro σ hσ x hx
    rw [hMdef] at hx
    refine fixed_of_mem_adjoin (Γ := Γ') ?_ hx σ hσ
    intro y hy
    rw [hs, Finset.coe_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact ⟨_, rfl, fun τ hτ => hαr i τ hτ⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Ideal (integralClosure R0 M), P = Q.comap (inclU R0 hMU) := ⟨_, rfl⟩
  have hPp : P.IsPrime := by rw [hPdef]; exact Ideal.IsPrime.comap _
  have hP0 : P ≠ ⊥ := by
    haveI : Nontrivial R0 := (algebraMap R0 K).domain_nontrivial
    obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    have h1 : Q.comap (algebraMap R0 (proChart A K R0)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hx0 hxQ (Algebra.IsIntegral.isIntegral x)
    obtain ⟨r, hrQ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    refine (Submodule.ne_bot_iff _).2 ⟨algebraMap R0 (integralClosure R0 M) r, ?_, ?_⟩
    · rw [hPdef, Ideal.mem_comap, AlgHom.commutes]
      exact hrQ
    · intro h
      have h3 : algebraMap R0 M r = 0 := by
        rw [IsScalarTower.algebraMap_apply R0 (integralClosure R0 M) M, h, map_zero]
      rw [IsScalarTower.algebraMap_apply R0 K M] at h3
      have h4 : algebraMap R0 K r = 0 := (map_eq_zero_iff _ (algebraMap K M).injective).1 h3
      exact hr0 (IsFractionRing.injective R0 K (h4.trans (map_zero _).symm))
  let v : HeightOneSpectrum (integralClosure R0 M) := ⟨P, hPp, hP0⟩
  let aM : Fin (N + 1) → M := fun i =>
    ⟨((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K), by
      rw [hMdef]; exact IntermediateField.subset_adjoin K _ (hsmem i)⟩
  have haM0 : ∀ i, aM i ≠ 0 := by
    intro i h
    have h1 : ((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K) = 0 :=
      congrArg Subtype.val h
    have h2 : (((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) = 0 := Subtype.ext h1
    exact pow_ne_zero _ (α i).ne_zero h2
  have haM : ∀ i, ((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N = IntermediateField.inclusion hMU (aM i) :=
    fun i => Subtype.ext rfl
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => ((WithZero.log (v.valuation M (aM i)) : ℤ) : ZMod N)) (by rw [ZMod.card, Fintype.card_fin]; omega)
  refine ⟨i, j, hij, ?_⟩
  funext σ
  rw [← hαχ i σ, ← hαχ j σ]
  exact congrFun (kchar_eq_of_val_lev hN hζ hΓ' hMU v hPdef hfixM (hαr i) (hαr j) (haM0 i) (haM0 j)
    (haM i) (haM j) hfij) σ

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_LocKumJ =====
section

/-!
# S4-PD (4), E4L part 2: tame inertia for a subgroup of finite exponent-index in `I(Q)`

* `exists_div_char`: an additive character `r : G → ℤ/(N d)` whose image contains `p^k d` (`p` prime to `N d`) yields,
  by dividing by the generator `e ∣ d` of its image, an additive character `f ∘ r : G → ℤ/N` taking the value `1`.
* `tame_inertia_le`: for `J ≤ I(Q)` with `σ ^ (p^k d) ∈ J` for all `σ ∈ I(Q)` (e.g. `J = I(Q) ⊓ ker π` for a finite
  quotient `π` of order `p^k d`), there are a locally constant character `θ_J : J → ℤ/N` and `τ₀ ∈ J` with
  `θ_J τ₀ = 1`, `θ_J` invariant under conjugation by `I(Q)`, and every locally constant character `J → ℤ/N` a multiple
  of `θ_J` (so `Hom_cont(J, ℤ/N) ≅ ℤ/N` by evaluation at `τ₀`). Uses `tame_inertia` at level `N d` and the pigeonhole
  bound `exists_ne_eq_of_family_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

section Div

/-- Dividing an additive character `r : G → ℤ/(N d)` by the generator of its image. -/
theorem exists_div_char {G : Type} [Group G] {N d p k : ℕ} [NeZero N] [NeZero d] (hp0 : 0 < p)
    (hp : Nat.Coprime p (N * d)) (r : G → ZMod (N * d)) (hr : ∀ σ τ, r (σ * τ) = r σ + r τ) {g : G}
    (hg : r g = ((p ^ k * d : ℕ) : ZMod (N * d))) :
    ∃ f : ZMod (N * d) → ZMod N, (∀ σ τ, f (r (σ * τ)) = f (r σ) + f (r τ)) ∧ ∃ τ, f (r τ) = 1 := by
  classical
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne d)⟩
  have h1 : r 1 = 0 := by
    have h := hr 1 1
    rw [mul_one] at h
    linear_combination -h
  have hinv : ∀ σ, r σ⁻¹ = -r σ := fun σ => by
    have h := hr σ⁻¹ σ
    rw [inv_mul_cancel, h1] at h
    linear_combination -h
  have hpow : ∀ σ (n : ℕ), r (σ ^ n) = (n : ZMod (N * d)) * r σ := by
    intro σ n
    induction n with
    | zero => rw [pow_zero, h1, Nat.cast_zero, zero_mul]
    | succ n ih => rw [pow_succ, hr, ih, Nat.cast_succ]; ring
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ σ, r σ = (n : ZMod (N * d)) :=
    ⟨p ^ k * d, Nat.mul_pos (pow_pos hp0 k) (NeZero.pos d), g, hg⟩
  obtain ⟨he0, τ₀, hτ₀⟩ := Nat.find_spec hex
  have hdvd : ∀ n : ℕ, (∃ σ, r σ = (n : ZMod (N * d))) → Nat.find hex ∣ n := by
    rintro n ⟨σ, hσ⟩
    have hlt : n % Nat.find hex < Nat.find hex := Nat.mod_lt _ he0
    by_contra hne
    have hpos : 0 < n % Nat.find hex := Nat.pos_of_ne_zero fun h => hne (Nat.dvd_of_mod_eq_zero h)
    refine Nat.find_min hex hlt ⟨hpos, σ * (τ₀ ^ (n / Nat.find hex))⁻¹, ?_⟩
    have key : (n : ZMod (N * d)) = ((n % Nat.find hex : ℕ) : ZMod (N * d)) +
        ((Nat.find hex : ℕ) : ZMod (N * d)) * ((n / Nat.find hex : ℕ) : ZMod (N * d)) := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [hr, hinv, hpow, hσ, hτ₀, key]
    ring
  set e := Nat.find hex with he_def
  have he_Nd : e ∣ N * d := hdvd (N * d) ⟨1, by rw [h1, ZMod.natCast_self]⟩
  have he_D : e ∣ p ^ k * d := hdvd _ ⟨g, hg⟩
  have hcop : Nat.Coprime e (p ^ k) := Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left he_Nd hp.symm)
  obtain ⟨c, hc⟩ : e ∣ d := hcop.dvd_of_dvd_mul_left he_D
  refine ⟨fun y => ((y.val / e : ℕ) : ZMod N), fun σ τ => ?_, τ₀, ?_⟩
  · obtain ⟨a, ha⟩ := hdvd (r σ).val ⟨σ, (ZMod.natCast_zmod_val _).symm⟩
    obtain ⟨b, hb⟩ := hdvd (r τ).val ⟨τ, (ZMod.natCast_zmod_val _).symm⟩
    have hNd : N * d = e * (N * c) := by rw [hc]; ring
    show (((r (σ * τ)).val / e : ℕ) : ZMod N) = (((r σ).val / e : ℕ) : ZMod N) + (((r τ).val / e : ℕ) : ZMod N)
    rw [hr, ZMod.val_add, ha, hb, ← mul_add, hNd, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ he0,
      Nat.mul_div_cancel_left _ he0, Nat.mul_div_cancel_left _ he0]
    conv_rhs => rw [← Nat.cast_add, ← Nat.mod_add_div (a + b) (N * c)]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul, add_zero]
  · show (((r τ₀).val / e : ℕ) : ZMod N) = 1
    by_cases hN1 : N = 1
    · subst hN1
      have h := (ZMod.natCast_eq_natCast_iff' ((r τ₀).val / e) 1 1).2 (by simp [Nat.mod_one])
      rwa [Nat.cast_one] at h
    · have hdlt : d < N * d := by
        have h2 : 2 ≤ N := by have := NeZero.pos N; omega
        have := NeZero.pos d
        nlinarith
      have hlt : e < N * d := lt_of_le_of_lt (Nat.le_of_dvd (NeZero.pos d) ⟨c, hc⟩) hdlt
      rw [hτ₀, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.div_self he0, Nat.cast_one]

end Div

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

omit [IsDomain A] [IsFractionRing A K] in
/-- A unit `n` of `A` (`K` of characteristic `p`) is prime to `p`. -/
theorem coprime_of_isUnit {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hn : IsUnit (n : A)) : Nat.Coprime p n := by
  refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => ?_
  have h1 : IsUnit (n : K) := by simpa using hn.map (algebraMap A K)
  rw [(CharP.cast_eq_zero_iff K p n).2 h] at h1
  exact not_isUnit_zero h1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Tame inertia for `J ≤ I(Q)`** with `σ ^ (p^k d) ∈ J` for `σ ∈ I(Q)`: `Hom_cont(J, ℤ/N)` is cyclic of order `N`,
generated by an `I(Q)`-conjugation invariant `θ_J` with `θ_J τ₀ = 1`. -/
theorem tame_inertia_le {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K)) (k : ℕ)
    (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J) :
    ∃ θ : J → ZMod N, ∃ τ₀ : J, IsLocallyConstant θ ∧ (∀ σ τ, θ (σ * τ) = θ σ + θ τ) ∧ θ τ₀ = 1 ∧
      (∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
        θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
      ∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ τ, χ (σ * τ) = χ σ + χ τ) →
        ∃ c : ZMod N, ∀ σ, χ σ = c * θ σ := by
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne d)⟩
  obtain ⟨θ', hθc, hθm, ⟨σ₀, hθ1⟩, -, -⟩ := exists_tame_char (p := p) hQ hNA hNR hζ hζI x hx ha
  let ι : J → Q.inertia (Pi1 A K) := fun σ => ⟨σ, hJ σ.2⟩
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  let r : J → ZMod (N * d) := fun σ => θ' (ι σ)
  have hr : ∀ σ τ, r (σ * τ) = r σ + r τ := fun σ τ => hθm (ι σ) (ι τ)
  have h1 : θ' 1 = 0 := by
    have h := hθm 1 1
    rw [mul_one] at h
    linear_combination -h
  have hpow : ∀ n : ℕ, θ' (σ₀ ^ n) = (n : ZMod (N * d)) := by
    intro n
    induction n with
    | zero => rw [pow_zero, h1, Nat.cast_zero]
    | succ n ih => rw [pow_succ, hθm, ih, hθ1, Nat.cast_succ]
  let g : J := ⟨(σ₀ : Pi1 A K) ^ (p ^ k * d), hd _ σ₀.2⟩
  have hg : r g = ((p ^ k * d : ℕ) : ZMod (N * d)) := by
    rw [← hpow]
    show θ' (ι g) = _
    congr 1
  have hp : Nat.Coprime p (N * d) := coprime_of_isUnit (K := K) hNA
  obtain ⟨f, hf, τ₀, hτ₀⟩ := exists_div_char (Fact.out : p.Prime).pos hp r hr hg
  let θ : J → ZMod N := fun σ => f (r σ)
  have hθm' : ∀ σ τ, θ (σ * τ) = θ σ + θ τ := hf
  have hθc' : IsLocallyConstant θ := (hθc.comp_continuous hιc).comp f
  have hconj : ∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
      θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩ := by
    intro g hg σ hσ hσ'
    show f (θ' (ι ⟨g⁻¹ * σ * g, hσ'⟩)) = f (θ' (ι ⟨σ, hσ⟩))
    congr 1
    have e : ι ⟨g⁻¹ * σ * g, hσ'⟩ = (⟨g, hg⟩ : Q.inertia (Pi1 A K))⁻¹ * ι ⟨σ, hσ⟩ * ⟨g, hg⟩ := rfl
    have hinv : θ' (⟨g, hg⟩ : Q.inertia (Pi1 A K))⁻¹ = -θ' ⟨g, hg⟩ := by
      have h := hθm (⟨g, hg⟩ : Q.inertia (Pi1 A K))⁻¹ ⟨g, hg⟩
      rw [inv_mul_cancel, h1] at h
      linear_combination -h
    rw [e, hθm, hθm, hinv]
    ring
  have hN : IsUnit (N : R0) := by
    rw [Nat.cast_mul] at hNR
    exact isUnit_of_mul_isUnit_left hNR
  have hζN : IsPrimitiveRoot (ζ ^ d) N := IsPrimitiveRoot.pow (NeZero.pos _) hζ (mul_comm N d)
  have hζJ : ∀ σ ∈ J, σ (ζ ^ d) = ζ ^ d := fun σ hσ => by rw [map_pow, hζI σ (hJ hσ)]
  exact ⟨θ, τ₀, hθc', hθm', hτ₀, hconj, fun χ hχc hχ => exists_eq_mul_of_surj
    (fun χ' hc' h' => exists_ne_eq_of_family_le hQ hN hζN hJ hζJ χ' hc' h') hθc' hθm' hτ₀ hχc hχ⟩

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_LocRam =====
section

/-!
# S4-PD (4), E4L part 3: the ramification converse at a finite level

* `log_val_eq_card_mul`: for a finite Galois level `L` over `K` and a subextension `F ≤ L`, the valuation of `x ∈ F` at
  a prime `w` of `B_L = integralClosure R0 L` is `#(I_w ∩ Gal(L/F))` times its valuation at `w ∩ B_F` (Hilbert
  ramification theory, `Ideal.card_inertia_eq_ramificationIdxIn`, for the subgroup `Gal(L/F)` over `B_F`).
* `dvd_val_of_fix_lev` (R): `γ ∈ K_U`, `γ ^ N = a ∈ M` for a finite level `M ≤ K_U`, and every inertia element at `Q`
  fixing `M` fixes `γ`: then `N ∣ v(a)` at `v = Q ∩ B_M` (converse of `fix_of_val_dvd_lev`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Valuations of elements of `F ≤ L` at a prime `w` of `B_L` are `#(I_w ∩ Gal(L/F))` times those at `w ∩ B_F`. -/
theorem log_val_eq_card_mul [Ring.HasFiniteQuotients R0] {L F : IntermediateField K (AlgebraicClosure K)}
    [FiniteDimensional K L] [IsGalois K L] (hFL : F ≤ L)
    [IsDedekindDomain (integralClosure R0 F)] [IsFractionRing (integralClosure R0 F) F]
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    (w : HeightOneSpectrum (integralClosure R0 L)) (vF : HeightOneSpectrum (integralClosure R0 F))
    (hvF : vF.asIdeal = w.asIdeal.comap (incl R0 K hFL)) (x : F) :
    WithZero.log (w.valuation L (IntermediateField.inclusion hFL x)) =
      (Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hFL).fixingSubgroup) : ℤ) *
        WithZero.log (vF.valuation F x) := by
  classical
  have : FiniteDimensional K F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFL).toLinearMap
      (IntermediateField.inclusion hFL).injective
  have : Algebra.IsSeparable K F :=
    Algebra.IsSeparable.of_algHom (F := K) (E := F) (E' := L) (f := IntermediateField.inclusion hFL)
  have : Module.Finite R0 (integralClosure R0 L) := IsIntegralClosure.finite R0 K L (integralClosure R0 L)
  have : Module.Finite R0 (integralClosure R0 F) := IsIntegralClosure.finite R0 K F (integralClosure R0 F)
  have hGal : IsGaloisGroup (L ≃ₐ[K] L) R0 (integralClosure R0 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R0 (integralClosure R0 L) K L
  letI : Algebra (integralClosure R0 F) (integralClosure R0 L) := (incl R0 K hFL).toRingHom.toAlgebra
  letI : SMul (integralClosure R0 F) (integralClosure R0 L) := Algebra.toSMul
  letI : Algebra F L := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : Algebra (integralClosure R0 F) L :=
    ((algebraMap F L).comp (algebraMap (integralClosure R0 F) F)).toAlgebra
  have : @IsScalarTower (integralClosure R0 F) F L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : @IsScalarTower (integralClosure R0 F) (integralClosure R0 L) L Algebra.toSMul Algebra.toSMul
      Algebra.toSMul := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R0 (integralClosure R0 F) (integralClosure R0 L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext (Subtype.ext rfl))
  have : Module.IsTorsionFree (integralClosure R0 F) (integralClosure R0 L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : integralClosure R0 L => ((z : L) : AlgebraicClosure K)) h))
  have : Module.Finite (integralClosure R0 F) (integralClosure R0 L) :=
    Module.Finite.of_restrictScalars_finite R0 _ _
  have : Module.Flat (integralClosure R0 F) (integralClosure R0 L) := inferInstance
  have : Ring.HasFiniteQuotients (integralClosure R0 F) := Ring.HasFiniteQuotients.of_module_finite R0 _
  have : Finite (integralClosure R0 F ⧸ vF.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient vF.ne_bot
  have : w.asIdeal.LiesOver vF.asIdeal := ⟨hvF.trans (Ideal.ext fun _ => Iff.rfl)⟩
  set H := (IntermediateField.restrict hFL).fixingSubgroup
  have hfixH : ∀ h : H, ∀ c : integralClosure R0 F,
      (h : L ≃ₐ[K] L) • algebraMap (integralClosure R0 F) (integralClosure R0 L) c =
        algebraMap (integralClosure R0 F) (integralClosure R0 L) c := by
    intro h c
    apply Subtype.ext
    show (h : L ≃ₐ[K] L) (IntermediateField.inclusion hFL (c : F)) = IntermediateField.inclusion hFL (c : F)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 _
      ((IntermediateField.mem_restrict hFL _).2 (c : F).2)
  have : IsGaloisGroup H (integralClosure R0 F) (integralClosure R0 L) := by
    refine ⟨⟨fun {h1 h2} heq => Subtype.ext (hGal.faithful.eq_of_smul_eq_smul fun b => heq b)⟩,
      ⟨fun h c b => ?_⟩, ⟨fun b hb => ?_⟩⟩
    · rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
      congr 1
      exact hfixH h c
    · have hbF : (b : L) ∈ IntermediateField.restrict hFL := by
        rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.restrict hFL),
          IntermediateField.mem_fixedField_iff]
        intro f hf
        exact congrArg (fun z : integralClosure R0 L => (z : L)) (hb ⟨f, hf⟩)
      rw [IntermediateField.mem_restrict] at hbF
      have hint : IsIntegral R0 (⟨((b : L) : AlgebraicClosure K), hbF⟩ : F) := by
        rw [← isIntegral_algHom_iff ((IntermediateField.inclusion hFL).restrictScalars R0)
          (IntermediateField.inclusion hFL).injective]
        exact b.2
      exact ⟨⟨⟨_, hbF⟩, hint⟩, Subtype.ext (Subtype.ext rfl)⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := H) vF.asIdeal w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx vF.asIdeal w.asIdeal H] at hcard
  have he' : vF.asIdeal.ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx (integralClosure R0 F) :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ vF.ne_bot
  have hval := HeightOneSpectrum.valuation_liesOver L vF w x
  have hc : Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ H) = Nat.card ↥(w.asIdeal.inertia H) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ H ≤ H)).toEquiv, Subgroup.inf_subgroupOf_right]
    rfl
  rw [hc, hcard, ← he']
  change WithZero.log (w.valuation L (algebraMap F L x)) = _
  rw [← hval, WithZero.log_pow, nsmul_eq_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Ramification converse (R).** If `γ ^ N = a ∈ M` (finite level `M ≤ K_U`) and every element of `I(Q)` fixing `M`
fixes `γ`, then `N ∣ v(a)` at `v = Q ∩ B_M`. -/
theorem dvd_val_of_fix_lev [Ring.HasFiniteQuotients R0] {Q : Ideal (proChart A K R0)} [Q.IsPrime] {N : ℕ}
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) [FiniteDimensional K M]
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    {γ : maxUnram A K} {a : M} (hγ : γ ^ N = IntermediateField.inclusion hMU a)
    (hfix : ∀ σ ∈ Q.inertia (Pi1 A K), (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → σ x = x) →
      σ γ = γ) :
    (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  classical
  by_cases ha0 : a = 0
  · simp [ha0]
  -- a finite Galois level `L ⊇ M(γ)` inside `K_U`
  obtain ⟨t, ht⟩ : M.FG := by
    have : Module.Finite K M.toSubalgebra.toSubmodule := inferInstanceAs (Module.Finite K M)
    exact IntermediateField.fg_of_fg_toSubalgebra M (Subalgebra.fg_of_fg_toSubmodule Submodule.FG.of_finite)
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K (insert (γ : AlgebraicClosure K) t) (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact γ.2
    · exact hMU (by rw [← ht]; exact IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 hx)))
  have : FiniteDimensional K L := hL.1
  have : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  have hγL : (γ : AlgebraicClosure K) ∈ L :=
    hle (IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 (Finset.mem_insert_self _ _)))
  have hML : M ≤ L := by
    rw [← ht, IntermediateField.adjoin_le_iff]
    intro x hx
    exact hle (IntermediateField.subset_adjoin K _
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))))
  have : IsFractionRing (integralClosure R0 L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K L
  have : IsDedekindDomain (integralClosure R0 L) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := L)
  have hcomp : ∀ y : integralClosure R0 M, inclU R0 hLU (incl R0 K hML y) = inclU R0 hMU y :=
    fun y => Subtype.ext (Subtype.ext rfl)
  obtain ⟨y0, hy0v, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  -- the prime `w = Q ∩ B_L`
  let w : HeightOneSpectrum (integralClosure R0 L) := ⟨Q.comap (inclU R0 hLU), Ideal.IsPrime.comap _, by
    refine (Submodule.ne_bot_iff _).2 ⟨incl R0 K hML y0, ?_, ?_⟩
    · rw [Ideal.mem_comap, hcomp, ← Ideal.mem_comap, ← hv]
      exact hy0v
    · intro h
      exact hy00 (Subtype.ext (Subtype.ext
        (congrArg (fun z : integralClosure R0 L => ((z : L) : AlgebraicClosure K)) h)))⟩
  have hvw : v.asIdeal = w.asIdeal.comap (incl R0 K hML) := by
    ext y
    show y ∈ v.asIdeal ↔ inclU R0 hLU (incl R0 K hML y) ∈ Q
    rw [hcomp, hv, Ideal.mem_comap]
  -- the fixed field `F` of `I_w ∩ Gal(L/M)`: it contains `M` and `γ`
  obtain ⟨F, hFL, hmemF⟩ : ∃ F : IntermediateField K (AlgebraicClosure K), ∃ _ : F ≤ L,
      ∀ y : L, (y : AlgebraicClosure K) ∈ F ↔
        ∀ τ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup, τ y = y := by
    refine ⟨(IntermediateField.fixedField (w.asIdeal.inertia (L ≃ₐ[K] L) ⊓
      (IntermediateField.restrict hML).fixingSubgroup)).map L.val, ?_, fun y => ?_⟩
    · intro x hx
      obtain ⟨y, -, rfl⟩ := (IntermediateField.mem_map _).1 hx
      exact y.2
    · rw [IntermediateField.mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        have hxy' : x = y := Subtype.ext hxy
        subst hxy'
        exact (IntermediateField.mem_fixedField_iff _ _).1 hx
      · intro h
        exact ⟨y, (IntermediateField.mem_fixedField_iff _ _).2 h, rfl⟩
  have hMF : M ≤ F := fun x hx => (hmemF ⟨x, hML hx⟩).2 fun τ hτ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 _
      ((IntermediateField.mem_restrict hML _).2 hx)
  have hγF : (γ : AlgebraicClosure K) ∈ F := by
    refine (hmemF ⟨γ, hγL⟩).2 fun τ hτ => ?_
    obtain ⟨g, hgI, hg⟩ := exists_inertia_lift (R0 := R0) hLU (Q := Q) (Subgroup.mem_inf.1 hτ).1
    have hgM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x := by
      intro x hx
      have h1 := hg ⟨x, hML hx⟩
      have h2 : τ ⟨x, hML hx⟩ = ⟨x, hML hx⟩ :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 _
          ((IntermediateField.mem_restrict hML _).2 hx)
      rw [h2] at h1
      exact h1
    have h4 : IntermediateField.inclusion hLU (τ ⟨γ, hγL⟩) = IntermediateField.inclusion hLU ⟨γ, hγL⟩ :=
      (hg ⟨γ, hγL⟩).symm.trans (hfix g hgI hgM)
    exact (IntermediateField.inclusion hLU).injective h4
  have hIeq : w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup =
      w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hFL).fixingSubgroup := by
    apply le_antisymm
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1,
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_⟩
      exact (hmemF y).1 ((IntermediateField.mem_restrict hFL _).1 hy) τ hτ
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1,
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 y
        ((IntermediateField.mem_restrict hFL _).2 (hMF ((IntermediateField.mem_restrict hML _).1 hy)))
  -- instances at `F` and the prime `vF = w ∩ B_F`
  have : FiniteDimensional K F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFL).toLinearMap
      (IntermediateField.inclusion hFL).injective
  have : Algebra.IsSeparable K F :=
    Algebra.IsSeparable.of_algHom (F := K) (E := F) (E' := L) (f := IntermediateField.inclusion hFL)
  have : IsFractionRing (integralClosure R0 F) F :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K F
  have : IsDedekindDomain (integralClosure R0 F) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := F)
  let vF : HeightOneSpectrum (integralClosure R0 F) := ⟨w.asIdeal.comap (incl R0 K hFL), Ideal.IsPrime.comap _, by
    refine (Submodule.ne_bot_iff _).2 ⟨incl R0 K hMF y0, ?_, ?_⟩
    · have h5 : incl R0 K hFL (incl R0 K hMF y0) = incl R0 K hML y0 := Subtype.ext (Subtype.ext rfl)
      rw [Ideal.mem_comap, h5, ← Ideal.mem_comap, ← hvw]
      exact hy0v
    · intro h
      exact hy00 (Subtype.ext (Subtype.ext
        (congrArg (fun z : integralClosure R0 F => ((z : F) : AlgebraicClosure K)) h)))⟩
  have hA := log_val_eq_card_mul (R0 := R0) hML w v hvw a
  have hB := log_val_eq_card_mul (R0 := R0) hFL w vF rfl ⟨γ, hγF⟩
  rw [← hIeq] at hB
  have hpow : IntermediateField.inclusion hML a = (IntermediateField.inclusion hFL ⟨γ, hγF⟩) ^ N := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    have h : ((γ ^ N : maxUnram A K) : AlgebraicClosure K) =
        ((IntermediateField.inclusion hMU a : maxUnram A K) : AlgebraicClosure K) := congrArg Subtype.val hγ
    rw [SubmonoidClass.coe_pow] at h
    exact h.symm
  rw [hpow, map_pow, WithZero.log_pow, nsmul_eq_mul, hB] at hA
  have he : (Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  refine ⟨WithZero.log (vF.valuation F ⟨γ, hγF⟩), ?_⟩
  apply mul_left_cancel₀ he
  linear_combination hA.symm

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_LocNorm =====
section

/-!
# S4-PD (4), E4L part 4: the normalised tame generator at a finite level

* `zmod_exists_mul_of_nsmul`, `zmod_exists_unit_mul`: in `ℤ/N`, `ord(c) • g = 0` makes `g` a multiple of `c`, and
  elements of the same additive order differ by a unit.
* `exists_norm_tau` (N): for a boundary prime `Q`, a finite level `M ≤ K_U` with the prime `v = Q ∩ B_M`, and
  `J = I(Q) ∩ Fix(M)` (of finite exponent-index in `I(Q)`), there are `τ ∈ J` and a locally constant character
  `θ : J → ℤ/N` with `θ τ = 1`, invariant under `I(Q)`-conjugation, such that every locally constant character
  `χ : J → ℤ/N` is `χ(τ) • θ`, and `τ` is normalised by valuations: `kchar(α)(τ) = v(α ^ N) mod N` whenever
  `α ^ N ∈ M`. Uses `tame_inertia_le`, the valuation criterion `kchar_eq_of_val_lev` and the ramification converse
  `dvd_val_of_fix_lev`, through the cyclic subgroup of `ℤ/N` of valuations of level-`M` radicands.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

section ZModAux

/-- In `ℤ/N`, an element killed by the additive order of `c` is a multiple of `c`. -/
theorem zmod_exists_mul_of_nsmul {N : ℕ} [NeZero N] (c g : ZMod N) (h : addOrderOf c • g = 0) :
    ∃ x : ZMod N, g = x * c := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hord : addOrderOf c = N / N.gcd c.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact ZMod.addOrderOf_coe _ (NeZero.ne N)
  rw [hord, nsmul_eq_mul, ← ZMod.natCast_zmod_val g, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
  have hq : 0 < N / N.gcd c.val := Nat.div_pos (Nat.gcd_le_left _ hN) (Nat.gcd_pos_of_pos_left _ hN)
  have hdvd : N.gcd c.val ∣ g.val := by
    refine (Nat.mul_dvd_mul_iff_left hq).1 ?_
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N c.val)]
    exact h
  obtain ⟨t, ht⟩ := hdvd
  have hb : ((N.gcd c.val : ℕ) : ZMod N) = c * (N.gcdB c.val : ZMod N) := by
    have h1 := congrArg (fun z : ℤ => (z : ZMod N)) (Nat.gcd_eq_gcd_ab N c.val)
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
      ZMod.natCast_zmod_val] at h1
    exact h1
  refine ⟨(N.gcdB c.val : ZMod N) * t, ?_⟩
  rw [← ZMod.natCast_zmod_val g, ht, Nat.cast_mul, hb]
  ring

/-- In `ℤ/N`, elements killing each other's additive orders differ by a unit. -/
theorem zmod_exists_unit_mul {N : ℕ} [NeZero N] {c g : ZMod N} (h1 : addOrderOf c • g = 0)
    (h2 : addOrderOf g • c = 0) : ∃ u : (ZMod N)ˣ, g = u * c := by
  obtain ⟨x, hx⟩ := zmod_exists_mul_of_nsmul c g h1
  obtain ⟨y, hy⟩ := zmod_exists_mul_of_nsmul g c h2
  have hmN : addOrderOf c ∣ N :=
    addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
  have : NeZero (addOrderOf c) := ⟨(addOrderOf_pos c).ne'⟩
  have hz : ∀ z : ZMod N, z * c = 0 ↔ ZMod.castHom hmN (ZMod (addOrderOf c)) z = 0 := by
    intro z
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff, addOrderOf_dvd_iff_nsmul_eq_zero,
      nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hxy : ZMod.castHom hmN (ZMod (addOrderOf c)) x * ZMod.castHom hmN (ZMod (addOrderOf c)) y = 1 := by
    have h3 : (x * y - 1) * c = 0 := by linear_combination -hy - y * hx
    have h4 := (hz _).1 h3
    rw [map_sub, map_mul, map_one, sub_eq_zero] at h4
    exact h4
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hmN ⟨_, _, hxy, by rw [mul_comm]; exact hxy⟩
  refine ⟨u, ?_⟩
  have hu' : ZMod.castHom hmN (ZMod (addOrderOf c)) (u : ZMod N) = ZMod.castHom hmN (ZMod (addOrderOf c)) x :=
    congrArg Units.val hu
  have h5 : ((u : ZMod N) - x) * c = 0 := (hz _).2 (by rw [map_sub, hu', sub_self])
  linear_combination hx - h5

end ZModAux

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- (N) The normalised tame generator of `J = I(Q) ∩ Fix(M)`: `θ τ = 1`, every locally constant character is
`χ(τ) • θ`, and `kchar(α)(τ) = v(α ^ N) mod N` for every radical `α` with `α ^ N ∈ M`. -/
theorem exists_norm_tau {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) [FiniteDimensional K M]
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    {J : Subgroup (Pi1 A K)}
    (hJ : ∀ σ, σ ∈ J ↔ σ ∈ Q.inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y)
    (k : ℕ) (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J)
    {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N) (hζNJ : ∀ σ ∈ J, σ ζN = ζN) :
    ∃ τ : J, ∃ θ : J → ZMod N, IsLocallyConstant θ ∧ (∀ σ σ', θ (σ * σ') = θ σ + θ σ') ∧ θ τ = 1 ∧
      (∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
        θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
      (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∀ σ, χ σ = χ τ * θ σ) ∧
      ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
        kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) := by
  classical
  have := hQ.1
  have hN : IsUnit (N : R0) := by
    have h := hNR
    rw [Nat.cast_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hJle : J ≤ Q.inertia (Pi1 A K) := fun σ hσ => ((hJ σ).1 hσ).1
  have hJM : ∀ σ ∈ J, ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y :=
    fun σ hσ => ((hJ σ).1 hσ).2
  obtain ⟨θ, τ₀, hθc, hθm, hθ1, hθconj, hθall⟩ := tame_inertia_le hQ hNA hNR hζ hζI x hx ha hJle k hd
  -- radicals of the level `M`
  have hrad : ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
      α ∈ rad J N := by
    intro α b h σ hσ
    rw [h]
    exact hJM σ hσ _ b.2
  have hne : ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
      b ≠ 0 := by
    intro α b h hb
    rw [hb, map_zero] at h
    exact pow_ne_zero _ α.ne_zero h
  have hpowγ : ∀ (α : (maxUnram A K)ˣ) (b : M), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b →
      ∀ n : ℕ, ((α ^ n : (maxUnram A K)ˣ) : maxUnram A K) ^ N = IntermediateField.inclusion hMU (b ^ n) := by
    intro α b h n
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, h, map_pow]
  have hνpow : ∀ (b : M) (n : ℕ), ((WithZero.log (v.valuation M (b ^ n)) : ℤ) : ZMod N) =
      n • ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) := by
    intro b n
    rw [map_pow, WithZero.log_pow, nsmul_eq_mul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hkpow : ∀ α : (maxUnram A K)ˣ, α ∈ rad J N → ∀ (n : ℕ) (σ : J),
      kchar hζN (Γ := J) (α ^ n) σ = n • kchar hζN (Γ := J) α σ := by
    intro α hα n σ
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact kchar_of_fix hζN (fixUnits J).one_mem σ
    | succ n ih => rw [pow_succ, kchar_mul_left hζN ((rad J N).pow_mem hα n) hα σ, ih, succ_nsmul]
  have hθ0 : θ 1 = 0 := by
    have h := hθm 1 1
    rw [mul_one] at h
    linear_combination -h
  have hθpow : ∀ n : ℕ, θ (τ₀ ^ n) = (n : ZMod N) := by
    intro n
    induction n with
    | zero => rw [pow_zero, hθ0, Nat.cast_zero]
    | succ n ih => rw [pow_succ, hθm, ih, hθ1, Nat.cast_succ]
  -- the subgroup `S ≤ ℤ/N` of valuations of level-`M` radicands, and a generator `g = v(b₀)`
  obtain ⟨S, hS⟩ : ∃ S : AddSubgroup (ZMod N), ∀ s, s ∈ S ↔ ∃ (α : (maxUnram A K)ˣ) (b : M),
      (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b ∧
        ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) = s := by
    refine ⟨{
      carrier := {s | ∃ (α : (maxUnram A K)ˣ) (b : M),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU b ∧
          ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) = s}
      add_mem' := by
        rintro _ _ ⟨α, b, hα, rfl⟩ ⟨β, c, hβ, rfl⟩
        refine ⟨α * β, b * c, by rw [Units.val_mul, mul_pow, hα, hβ, map_mul], ?_⟩
        rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 (hne α b hα))
          ((Valuation.ne_zero_iff _).2 (hne β c hβ)), Int.cast_add]
      zero_mem' := ⟨1, 1, by rw [Units.val_one, one_pow, map_one], by
        rw [map_one, WithZero.log_one, Int.cast_zero]⟩
      neg_mem' := by
        rintro _ ⟨α, b, hα, rfl⟩
        refine ⟨α⁻¹, b⁻¹, by rw [Units.val_inv_eq_inv_val, inv_pow, hα, map_inv₀], ?_⟩
        rw [map_inv₀, WithZero.log_inv, Int.cast_neg] }, fun s => Iff.rfl⟩
  obtain ⟨⟨g, hgS⟩, hgen⟩ := IsAddCyclic.exists_generator (α := S)
  obtain ⟨α₀, b₀, hb₀, hg₀⟩ := (hS g).1 hgS
  have hα₀ := hrad α₀ b₀ hb₀
  obtain ⟨c, hc⟩ := hθall (kchar hζN (Γ := J) α₀) (isLocallyConstant_kchar hζN α₀) (kchar_mul hζN hζNJ hα₀)
  -- `ord(c) • g = 0`, by the ramification converse
  have h1 : addOrderOf c • g = 0 := by
    have hfixU : α₀ ^ addOrderOf c ∈ fixUnits J := by
      refine (kchar_eq_zero_iff hζN ((rad J N).pow_mem hα₀ _)).1 fun σ => ?_
      rw [hkpow α₀ hα₀, hc, ← smul_mul_assoc, addOrderOf_nsmul_eq_zero, zero_mul]
    have hdvd := dvd_val_of_fix_lev hMU v hv (hpowγ α₀ b₀ hb₀ (addOrderOf c))
      (fun σ hσ hσM => hfixU σ ((hJ σ).2 ⟨hσ, hσM⟩))
    rw [← hg₀, ← hνpow]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hdvd
  -- `ord(g) • c = 0`, by the valuation criterion
  have h2 : addOrderOf g • c = 0 := by
    have hval : ((WithZero.log (v.valuation M (b₀ ^ addOrderOf g)) : ℤ) : ZMod N) =
        ((WithZero.log (v.valuation M (1 : M)) : ℤ) : ZMod N) := by
      rw [hνpow, hg₀, addOrderOf_nsmul_eq_zero, map_one, WithZero.log_one, Int.cast_zero]
    have hk := congrFun (kchar_eq_of_val_lev hN hζN hJle hMU v hv hJM ((rad J N).pow_mem hα₀ _)
      (rad J N).one_mem (pow_ne_zero _ (hne α₀ b₀ hb₀)) one_ne_zero (hpowγ α₀ b₀ hb₀ _)
      (by rw [Units.val_one, one_pow, map_one]) hval) τ₀
    rw [hkpow α₀ hα₀, hc, hθ1, mul_one, kchar_of_fix hζN (fixUnits J).one_mem] at hk
    exact hk
  obtain ⟨u, hu⟩ := zmod_exists_unit_mul h1 h2
  let τ : J := τ₀ ^ (u : ZMod N).val
  have hθτ : θ τ = u := by
    show θ (τ₀ ^ (u : ZMod N).val) = u
    rw [hθpow, ZMod.natCast_zmod_val]
  let θ' : J → ZMod N := fun σ => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ σ
  have hθ'm : ∀ σ σ', θ' (σ * σ') = θ' σ + θ' σ' := fun σ σ' => by
    show _ * θ (σ * σ') = _ * θ σ + _ * θ σ'
    rw [hθm, mul_add]
  refine ⟨τ, θ', hθc.comp (fun t : ZMod N => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * t), hθ'm, ?_, ?_, ?_, ?_⟩
  · show ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ τ = 1
    rw [hθτ, Units.inv_mul]
  · intro g' hg' σ hσ hσ'
    show ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ _ = ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ _
    rw [hθconj g' hg' σ hσ hσ']
  · intro χ hχc hχm σ
    obtain ⟨c', hc'⟩ := hθall χ hχc hχm
    have hu1 : (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv u
    show χ σ = χ τ * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * θ σ)
    rw [hc' σ, hc' τ, hθτ]
    linear_combination (-(c' * θ σ)) * hu1
  · intro α b h
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.1 (hgen ⟨_, (hS _).2 ⟨α, b, h, rfl⟩⟩)
    have hz' : z • g = ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) := congrArg Subtype.val hz
    obtain ⟨m, hmg⟩ : ∃ m : ℕ, m • g = ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) :=
      ⟨(z : ZMod N).val, by rw [← hz', nsmul_eq_mul, zsmul_eq_mul, ZMod.natCast_zmod_val]⟩
    have hval : ((WithZero.log (v.valuation M b) : ℤ) : ZMod N) =
        ((WithZero.log (v.valuation M (b₀ ^ m)) : ℤ) : ZMod N) := by
      rw [hνpow, hg₀, hmg]
    have hk := congrFun (kchar_eq_of_val_lev hN hζN hJle hMU v hv hJM (hrad α b h) ((rad J N).pow_mem hα₀ m)
      (hne α b h) (pow_ne_zero _ (hne α₀ b₀ hb₀)) h (hpowγ α₀ b₀ hb₀ m) hval) τ
    rw [hk, hkpow α₀ hα₀, hc, hθτ, ← hmg, hu, mul_comm c]

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResRad =====
section

/-!
# S4-PD (4), E4B part 5a: radicands in constant levels, and normalisation along constant extensions

* `exists_sup_constLevel_of_fixed`: an element of `K_U` fixed by `π₁^geo ∩ Gal(K_U/M)` lies in
  `M ⊔ K(𝔽_{p^(e k)})` for some `k > 0` (infinite Galois correspondence on `K_U / K`).
* `log_val_eq_of_inertia_fix`: if `M ≤ M'` are finite levels and every inertia element at `Q` fixing `M` fixes `M'`
  (e.g. `M'` a constant extension of `M`), valuations of elements of `M` agree at `Q ∩ B_M` and `Q ∩ B_M'`.
* `kchar_norm_of_le`: a tame generator normalised by the radicands of `M` is normalised by those of `M'`, once every
  valuation class of an `M'`-radicand is one of an `M`-radicand.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer TameInertia IsDedekindDomain

noncomputable section

section Rad

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- An element of `K_U` fixed by `π₁^geo ∩ Gal(K_U/M)` lies in `M ⊔ K(𝔽_{q^k})` for some `k > 0`. -/
theorem exists_sup_constLevel_of_fixed {e : ℕ} (he : 0 < e)
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) {x : maxUnram A K}
    (hx : ∀ σ ∈ pi1geo A K (p ^ e), σ ∈ (IntermediateField.restrict hMU).fixingSubgroup → σ x = x) :
    ∃ k, 0 < k ∧ (x : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) := by
  classical
  have hmem : x ∈ IntermediateField.fixedField
      (constFieldU A K (p ^ e) ⊔ IntermediateField.restrict hMU).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.fixingSubgroup_sup, fixingSubgroup_constFieldU] at hσ
    exact hx σ (Subgroup.mem_inf.1 hσ).1 (Subgroup.mem_inf.1 hσ).2
  have hsup : constFieldU A K (p ^ e) ⊔ IntermediateField.restrict hMU =
      IntermediateField.adjoin K ({y | IsConst (p ^ e) y} ∪
        (IntermediateField.restrict hMU : Set (maxUnram A K))) := by
    rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
    rfl
  rw [InfiniteGalois.fixedField_fixingSubgroup, hsup] at hmem
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hmem
  have hc : ∀ y ∈ T, ∃ n, 0 < n ∧ ((y : AlgebraicClosure K) ∈ M ∨ y ^ (p ^ e) ^ n = y) := by
    intro y hy
    rcases hT hy with hyc | hyM
    · obtain ⟨n, hn, hyn⟩ := hyc
      exact ⟨n, hn, Or.inr hyn⟩
    · exact ⟨1, one_pos, Or.inl ((IntermediateField.mem_restrict hMU _).1 hyM)⟩
  choose! n hn hpow using hc
  refine ⟨∏ y ∈ T, n y, Finset.prod_pos fun y hy => hn y hy, ?_⟩
  have hk : 0 < e * ∏ y ∈ T, n y := Nat.mul_pos he (Finset.prod_pos fun y hy => hn y hy)
  have hle : (IntermediateField.adjoin K (T : Set (maxUnram A K))).map (maxUnram A K).val ≤
      M ⊔ constLevel K p (e * ∏ y ∈ T, n y) := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rcases hpow y hy with hyM | hyc
    · exact le_sup_left (a := M) hyM
    · refine le_sup_right (a := M) (mem_constLevel hk ?_)
      obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem n hy
      have h1 := pow_pow_mul_eq hyc j
      rw [← hj, ← pow_mul] at h1
      show ((y : AlgebraicClosure K)) ^ p ^ (e * ∏ y ∈ T, n y) = y
      rw [← SubmonoidClass.coe_pow, h1]
  exact hle ⟨x, hxT, rfl⟩

end Rad

section Val

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Valuations agree along an extension of finite levels `M ≤ M'` in which inertia at `Q` fixing `M` fixes `M'`. -/
theorem log_val_eq_of_inertia_fix [Ring.HasFiniteQuotients R0] {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    {M M' : IntermediateField K (AlgebraicClosure K)} (hMM : M ≤ M') (hMU : M ≤ maxUnram A K)
    (hMU' : M' ≤ maxUnram A K) [FiniteDimensional K M']
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    [IsDedekindDomain (integralClosure R0 M')] [IsFractionRing (integralClosure R0 M') M']
    (v : HeightOneSpectrum (integralClosure R0 M)) (hv : v.asIdeal = Q.comap (inclU R0 hMU))
    (v' : HeightOneSpectrum (integralClosure R0 M')) (hv' : v'.asIdeal = Q.comap (inclU R0 hMU'))
    (hfix : ∀ σ ∈ Q.inertia (Pi1 A K), (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → σ x = x) →
      ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M' → σ x = x)
    (b : M) :
    WithZero.log (v'.valuation M' (IntermediateField.inclusion hMM b)) = WithZero.log (v.valuation M b) := by
  classical
  obtain ⟨t, ht⟩ : M'.FG := by
    have : Module.Finite K M'.toSubalgebra.toSubmodule := inferInstanceAs (Module.Finite K M')
    exact IntermediateField.fg_of_fg_toSubalgebra M' (Subalgebra.fg_of_fg_toSubmodule Submodule.FG.of_finite)
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K t (fun x hx =>
    hMU' (by rw [← ht]; exact IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 hx)))
  have : FiniteDimensional K L := hL.1
  have : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  have hM'L : M' ≤ L := by
    rw [← ht]
    exact hle
  have hML : M ≤ L := hMM.trans hM'L
  have : IsFractionRing (integralClosure R0 L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K L
  have : IsDedekindDomain (integralClosure R0 L) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := L)
  have hcomp : ∀ y : integralClosure R0 M, inclU R0 hLU (incl R0 K hML y) = inclU R0 hMU y :=
    fun y => Subtype.ext (Subtype.ext rfl)
  have hcomp' : ∀ y : integralClosure R0 M', inclU R0 hLU (incl R0 K hM'L y) = inclU R0 hMU' y :=
    fun y => Subtype.ext (Subtype.ext rfl)
  obtain ⟨y0, hy0v, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let w : HeightOneSpectrum (integralClosure R0 L) := ⟨Q.comap (inclU R0 hLU), Ideal.IsPrime.comap _, by
    refine (Submodule.ne_bot_iff _).2 ⟨incl R0 K hML y0, ?_, ?_⟩
    · rw [Ideal.mem_comap, hcomp, ← Ideal.mem_comap, ← hv]
      exact hy0v
    · intro h
      exact hy00 (Subtype.ext (Subtype.ext
        (congrArg (fun z : integralClosure R0 L => ((z : L) : AlgebraicClosure K)) h)))⟩
  have hvw : v.asIdeal = w.asIdeal.comap (incl R0 K hML) := by
    ext y
    show y ∈ v.asIdeal ↔ inclU R0 hLU (incl R0 K hML y) ∈ Q
    rw [hcomp, hv, Ideal.mem_comap]
  have hv'w : v'.asIdeal = w.asIdeal.comap (incl R0 K hM'L) := by
    ext y
    show y ∈ v'.asIdeal ↔ inclU R0 hLU (incl R0 K hM'L y) ∈ Q
    rw [hcomp', hv', Ideal.mem_comap]
  have hIeq : w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hML).fixingSubgroup =
      w.asIdeal.inertia (L ≃ₐ[K] L) ⊓ (IntermediateField.restrict hM'L).fixingSubgroup := by
    apply le_antisymm
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1, ?_⟩
      obtain ⟨g, hgI, hg⟩ := TameInertia.exists_inertia_lift (R0 := R0) hLU (Q := Q) (Subgroup.mem_inf.1 hτ).1
      have hgM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x := by
        intro x hx
        have h1 := hg ⟨x, hML hx⟩
        have h2 : τ ⟨x, hML hx⟩ = ⟨x, hML hx⟩ :=
          (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 _
            ((IntermediateField.mem_restrict hML _).2 hx)
        rw [h2] at h1
        exact h1
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h3 := hfix g hgI hgM (IntermediateField.inclusion hLU y) ((IntermediateField.mem_restrict hM'L _).1 hy)
      rw [hg y] at h3
      exact (IntermediateField.inclusion hLU).injective h3
    · intro τ hτ
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hτ).1, ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 hτ).2 y
        ((IntermediateField.mem_restrict hM'L _).2 (hMM ((IntermediateField.mem_restrict hML _).1 hy)))
  have h1 := log_val_eq_card_mul (R0 := R0) hML w v hvw b
  have h2 := log_val_eq_card_mul (R0 := R0) hM'L w v' hv'w (IntermediateField.inclusion hMM b)
  have hpos : (0 : ℤ) < (Nat.card ↥(w.asIdeal.inertia (L ≃ₐ[K] L) ⊓
      (IntermediateField.restrict hM'L).fixingSubgroup) : ℤ) := by
    exact_mod_cast Nat.card_pos
  rw [hIeq] at h1
  have h12 : IntermediateField.inclusion hM'L (IntermediateField.inclusion hMM b) =
      IntermediateField.inclusion hML b := rfl
  rw [h12, h1] at h2
  exact (mul_left_cancel₀ hpos.ne' h2).symm

set_option synthInstance.maxHeartbeats 400000 in
/-- Normalisation propagates from `M` to `M' ⊇ M` when the valuation classes of `M'`-radicands come from `M`. -/
theorem kchar_norm_of_le {Q : Ideal (proChart A K R0)} [Q.IsPrime] {N : ℕ} [NeZero N] (hN : IsUnit (N : R0))
    {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N) {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K))
    {M M' : IntermediateField K (AlgebraicClosure K)} (hMM : M ≤ M') (hMU : M ≤ maxUnram A K)
    (hMU' : M' ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M]
    [IsDedekindDomain (integralClosure R0 M')] [IsFractionRing (integralClosure R0 M') M']
    (v : HeightOneSpectrum (integralClosure R0 M)) (v' : HeightOneSpectrum (integralClosure R0 M'))
    (hv' : v'.asIdeal = Q.comap (inclU R0 hMU'))
    (hJM' : ∀ σ ∈ J, ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M' → σ x = x)
    (hval : ∀ b : M, WithZero.log (v'.valuation M' (IntermediateField.inclusion hMM b)) =
      WithZero.log (v.valuation M b))
    (hS : ∀ (α : (maxUnram A K)ˣ) (b : M'), (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU' b →
      ∃ (β : (maxUnram A K)ˣ) (c : M), (β : maxUnram A K) ^ N = IntermediateField.inclusion hMU c ∧
        ((WithZero.log (v.valuation M c) : ℤ) : ZMod N) = ((WithZero.log (v'.valuation M' b) : ℤ) : ZMod N))
    {τ : J} (hτ : ∀ (β : (maxUnram A K)ˣ) (c : M), (β : maxUnram A K) ^ N = IntermediateField.inclusion hMU c →
      kchar hζN (Γ := J) β τ = ((WithZero.log (v.valuation M c) : ℤ) : ZMod N))
    (α : (maxUnram A K)ˣ) (b : M') (hα : (α : maxUnram A K) ^ N = IntermediateField.inclusion hMU' b) :
    kchar hζN (Γ := J) α τ = ((WithZero.log (v'.valuation M' b) : ℤ) : ZMod N) := by
  obtain ⟨β, c, hβ, hc⟩ := hS α b hα
  have hrad : ∀ (γ : (maxUnram A K)ˣ) (a : M'), (γ : maxUnram A K) ^ N = IntermediateField.inclusion hMU' a →
      γ ∈ rad J N := by
    intro γ a h σ hσ
    rw [h]
    exact hJM' σ hσ _ a.2
  have hne : ∀ (γ : (maxUnram A K)ˣ) (a : M'), (γ : maxUnram A K) ^ N = IntermediateField.inclusion hMU' a →
      a ≠ 0 := by
    intro γ a h ha
    rw [ha, map_zero] at h
    exact pow_ne_zero _ γ.ne_zero h
  have hβ' : (β : maxUnram A K) ^ N = IntermediateField.inclusion hMU' (IntermediateField.inclusion hMM c) := hβ
  have heq := kchar_eq_of_val_lev hN hζN hJ hMU' v' hv' hJM' (hrad α b hα) (hrad β _ hβ')
    (hne α b hα) (hne β _ hβ') hα hβ' (by rw [hval, hc])
  rw [heq, hτ β c hβ, hc]

end Val

end

end Residue
end RamanujanPetersson


end

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

end Chart

end

end Residue
end RamanujanPetersson


end

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

-- ===== S4.Def_RP_Cone_ResCard =====
section

/-!
# S4-PD (4), E4B part 3a: residue field cardinalities at a level

* `card_quot_eq_pow`: a finite residue field of a ring receiving a finite field `k1` has `#k1 ^ k` elements.
* `pow_card_pow_sub_mem`: `b ^ (#(B/y) ^ j) ≡ b` modulo a maximal ideal `y` with finite residue field.
* `card_quot_levelField`: if a field `M ⊇ R` contains a primitive `(q^m - 1)`-th root of unity (so `𝔽_{q^m} ⊆ M`),
  every finite residue field of the integral closure of `R` in `M` has `q^(m*k)` elements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Residue

open CP4a

noncomputable section

/-- A finite quotient field of a ring receiving a finite field `k1` has `#k1 ^ k` elements. -/
theorem card_quot_eq_pow {B k1 : Type} [CommRing B] [Field k1] [Fintype k1] (φ : k1 →+* B) (y : Ideal B)
    [y.IsMaximal] [Finite (B ⧸ y)] : ∃ k : ℕ, Nat.card (B ⧸ y) = Fintype.card k1 ^ k := by
  letI : Field (B ⧸ y) := Ideal.Quotient.field y
  letI : Algebra k1 (B ⧸ y) := ((Ideal.Quotient.mk y).comp φ).toAlgebra
  letI : Fintype (B ⧸ y) := Fintype.ofFinite _
  exact ⟨Module.finrank k1 (B ⧸ y), by rw [Nat.card_eq_fintype_card]; exact Module.card_eq_pow_finrank⟩

/-- `b ^ (#(B/y) ^ j) ≡ b` modulo a maximal ideal `y` with finite residue field. -/
theorem pow_card_pow_sub_mem {B : Type} [CommRing B] (y : Ideal B) [y.IsMaximal] [Finite (B ⧸ y)] (j : ℕ)
    (b : B) : b ^ (Nat.card (B ⧸ y) ^ j) - b ∈ y := by
  letI : Field (B ⧸ y) := Ideal.Quotient.field y
  letI : Fintype (B ⧸ y) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq, map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]

variable {Fq : Type} [Field Fq] [Fintype Fq]

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResMax =====
section

/-!
# S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels

* `exists_stable`: finitely many families of subsets of `ℤ/N`, monotone along divisibility, are all constant on the
  multiples of one index `k₀`.
* `radVal` (valuation classes of the radicands of a level at `Q ∩ B_L`), `radVal_mono` (they grow along extensions in
  which inertia fixing the smaller level fixes the larger one).
* `exists_stable_tau`: for boundary primes `Q t` (`t` in a finite type) there are `k₀ > 0` and generators `τ t`
  normalised at every constant level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k` (from one normalisation per level).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial

noncomputable section

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- Constant levels grow with divisibility. -/
theorem constLevel_le_of_dvd {k k' : ℕ} (hk' : 0 < k') (h : k ∣ k') : constLevel K p k ≤ constLevel K p k' := by
  refine IntermediateField.adjoin_le_iff.2 fun y hy => ?_
  have hy' : y ^ p ^ k = y := by
    rw [mem_rootSet] at hy
    simpa [sub_eq_zero] using hy.2
  obtain ⟨j, rfl⟩ := h
  exact mem_constLevel hk' (pow_pow_mul_eq hy' j)

end Chart

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResCos =====
section

/-!
# S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)

`π : G →* Gf`, `Γ ≤ G`, subgroups `I s`. The cover points are `CosT = Σ s, π(Γ) ⧸ π(Γ ∩ I s)` (left cosets), with lifts
`cosX t ∈ Γ` of the coset representatives (`cosX = 1` on the trivial coset).

* `cos_rep`: every `p ∈ π(Γ)` lies in exactly one coset `π(x_t) π(Γ ∩ I s)` over `s` (the `hrep` field of `ResDat`).
* `cos_cover`, `cos_disj`: for an action of `G` with `I s ≤ Stab(P s)`, every `γ • P s` (`γ ∈ Γ`) is `g • (x_t • P s)` with
  `g ∈ Γ ∩ ker π`, and such a `t` is unique when `Γ`-conjugate base points coincide and `Γ`-stabilisers lie in `I s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

section Cos

variable {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- The subgroup `π(Γ ∩ I s)` of `π(Γ)`. -/
abbrev cosD (s : S) : Subgroup (Γ.map π) := ((Γ ⊓ I s).map π).subgroupOf (Γ.map π)

variable {π Γ I}

variable [Finite S] [Finite Gf]

end Cos

section Act

variable {G Gf : Type} [Group G] [Group Gf] {π : G →* Gf} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}
  {X : Type} [MulAction G X] {P : S → X}

end Act

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Coef =====
section

/-!
# Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)

Abstract step: let `θ : Γ → ℤ/N` with `θ σ₀ = 1` be such that every locally constant homomorphism `Γ → ℤ/N` is a
multiple of `θ`. Then for every abelian group `M` killed by `N`, every locally constant homomorphism `χ : Γ → M` is
`σ ↦ (θ σ).val • χ σ₀` (`eq_val_nsmul_of_gen`), and conversely `σ ↦ (θ σ).val • m` is a locally constant homomorphism
for every `m` with value `m` at `σ₀`. So `Hom(Γ, M) ≅ M` by evaluation at `σ₀`. The proof separates points of `M` by
characters `M → ℚ/ℤ` (`CharacterModule`) and identifies the `N`-torsion of `ℚ/ℤ` with `ℤ/N` (`toQCircle`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Circ

variable (N : ℕ) [NeZero N]

end Circ

section Gen

variable {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] {N : ℕ} [NeZero N] {θ : Γ → ZMod N}
  {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0)

include hM in
theorem one_val_nsmul (m : M) : (1 : ZMod N).val • m = m := by
  rw [ZMod.val_one_eq_one_mod, nsmul_mod_eq hM, one_nsmul]

end Gen

end

end TameInertia
end RamanujanPetersson


end



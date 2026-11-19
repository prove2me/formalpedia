-- Prove2me | Definitions.Def_RPLib_S4_CDPack45
-- name    : RPLib_S4_CDPack45
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:12:56.612231+00:00
-- url     : https://prove2.me/theorems/81336518-da86-4aea-842c-37eb5256d799
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 45 of 71
-- statement:
--   Part 45 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ThetaCube_SmDed`: S4-ThetaCube, file SmDed (D-B0, part 1): a Dedekind domain of finite type over an algebraically closed field is smooth
--   * `Def_RP_IntersectA_Top`: S4-IntersectA, file Top: general position by a dimension count (topology only)
--   * `Def_RP_IsogDegA_Trans`: S4-IsogDegA, file Trans: translations by `k`-points of a group scheme over `k`
--   * `Def_RP_IntersectA_Gen`: S4-IntersectA, file Gen: translates in general position (L31 existence)
--   * `Def_RP_IntersectA_Fam`: S4-IntersectA, file Fam: the family of translated intersections over `A^g`
--   * `Def_RP_IntersectA_Cons`: S4-IntersectA, file Cons: generic flatness of a finite morphism
--   * `Def_RP_IntersectB_Alg`: S4-IntersectB, file Alg: the exact-sequence lemma behind additivity (L33, part 3)
--   * `Def_RP_IntersectB_Gen`: S4-IntersectB, file Gen: the generator `u`, the multiplier `s`, the weak NZD criterion (L33, part 3b)
--   * `Def_RP_IntersectB_Ass`: S4-IntersectB, file Ass: associated points of an ideal sheaf (L33, part 4)
--   * `Def_RP_JacDivisors_F`: S4-JacDivisors F (O8: finite free resolutions)
--   * `Def_RP_IntersectC_Rank`: S4-IntersectC, file Rank: ranks multiply in a finite flat tower over a field (L35 core)
--   * `Def_RP_IsogDegB_Unram`: S4-IsogDegB, algebra part (lemma L27 of S4_COREB_ROUTE.md §3)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_JacDivisorsE

/-!
# Curve-duality library package, part 45 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ThetaCube_SmDed`: S4-ThetaCube, file SmDed (D-B0, part 1): a Dedekind domain of finite type over an algebraically closed field is smooth
* `Def_RP_IntersectA_Top`: S4-IntersectA, file Top: general position by a dimension count (topology only)
* `Def_RP_IsogDegA_Trans`: S4-IsogDegA, file Trans: translations by `k`-points of a group scheme over `k`
* `Def_RP_IntersectA_Gen`: S4-IntersectA, file Gen: translates in general position (L31 existence)
* `Def_RP_IntersectA_Fam`: S4-IntersectA, file Fam: the family of translated intersections over `A^g`
* `Def_RP_IntersectA_Cons`: S4-IntersectA, file Cons: generic flatness of a finite morphism
* `Def_RP_IntersectB_Alg`: S4-IntersectB, file Alg: the exact-sequence lemma behind additivity (L33, part 3)
* `Def_RP_IntersectB_Gen`: S4-IntersectB, file Gen: the generator `u`, the multiplier `s`, the weak NZD criterion (L33, part 3b)
* `Def_RP_IntersectB_Ass`: S4-IntersectB, file Ass: associated points of an ideal sheaf (L33, part 4)
* `Def_RP_JacDivisors_F`: S4-JacDivisors F (O8: finite free resolutions)
* `Def_RP_IntersectC_Rank`: S4-IntersectC, file Rank: ranks multiply in a finite flat tower over a field (L35 core)
* `Def_RP_IsogDegB_Unram`: S4-IsogDegB, algebra part (lemma L27 of S4_COREB_ROUTE.md §3)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaCube_SmDed =====
section

/-!
# S4-ThetaCube, file SmDed (D-B0, part 1): a Dedekind domain of finite type over an algebraically closed field is smooth

Let `B` be a Dedekind domain (not a field) of finite type over an algebraically closed field `K`.
* `exists_unif`: at a nonzero prime `q`, some `x : B` generates the maximal ideal of `B_q`.
* `aeval_injective`: such an `x` is transcendental over `K`.
* `isSmoothAt_of_isMaximal`: `K[X] → B`, `X ↦ x`, is flat (torsion free over a PID), finitely presented and
  unramified at `q` (Mathlib `isUnramifiedAt_iff_map_eq`), hence etale at `q`
  (Mathlib `IsEtaleAt.of_isUnramifiedAt_of_flat`); so `B` is smooth over `K` at `q`.
* `smooth_of_dedekind`: `Algebra.Smooth K B` (the smooth locus is open and contains every closed point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaCube

open Polynomial IsLocalRing

section SmoothDedekind

variable {K : Type*} [Field K] [IsAlgClosed K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra K B]
  [Algebra.FiniteType K B]

/-- A uniformizer at a nonzero prime of a Dedekind domain can be chosen in `B`. -/
theorem exists_unif (q : Ideal B) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ x : B, maximalIdeal (Localization.AtPrime q) = Ideal.span {algebraMap B _ x} := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq (Localization.AtPrime q)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective q.primeCompl ϖ
  refine ⟨x, ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ, ← hxs,
    ← IsLocalization.mk'_spec (Localization.AtPrime q) x s,
    Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ s)]

theorem mem_of_unif (q : Ideal B) [q.IsPrime] {x : B}
    (hx : maximalIdeal (Localization.AtPrime q) = Ideal.span {algebraMap B _ x}) : x ∈ q := by
  have h : algebraMap B (Localization.AtPrime q) x ∈ maximalIdeal (Localization.AtPrime q) := by
    rw [hx]
    exact Ideal.subset_span rfl
  rw [← Localization.AtPrime.under_maximalIdeal (I := q)]
  exact h

theorem ne_zero_of_unif (q : Ideal B) [q.IsPrime] (hq : q ≠ ⊥) {x : B}
    (hx : maximalIdeal (Localization.AtPrime q) = Ideal.span {algebraMap B _ x}) : x ≠ 0 := by
  rintro rfl
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq (Localization.AtPrime q)
  exact IsDiscreteValuationRing.not_a_field _ (by rw [hx, map_zero, Ideal.span_singleton_eq_bot.mpr rfl])

omit [IsDedekindDomain B] [Algebra.FiniteType K B] in
/-- A nonzero element of a proper prime is transcendental over the algebraically closed field `K`. -/
theorem aeval_injective [IsDomain B] (q : Ideal B) [q.IsPrime] {x : B} (hxq : x ∈ q) (hx0 : x ≠ 0) :
    Function.Injective (aeval x : K[X] →ₐ[K] B) := by
  by_contra h
  have halg : IsAlgebraic K x := by
    by_contra h'
    exact h (transcendental_iff_injective.mp h')
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one K x
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [← hc, map_zero])
  apply Ideal.IsPrime.ne_top ‹q.IsPrime›
  apply Ideal.eq_top_of_isUnit_mem q hxq
  rw [← hc]
  exact (IsUnit.mk0 c hc0).map (algebraMap K B)

omit [IsDedekindDomain B] in
/-- Nullstellensatz: every element is congruent to a constant modulo a maximal ideal. -/
theorem exists_sub_mem (q : Ideal B) [q.IsMaximal] (b : B) : ∃ c : K, b - algebraMap K B c ∈ q := by
  letI := Ideal.Quotient.field q
  have : Module.Finite K (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ q)
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ q)).2 (Ideal.Quotient.mk q b)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, Ideal.Quotient.mk_algebraMap, sub_self]

/-- A field extension whose algebra map is surjective is separable. -/
theorem isSeparable_of_surjective {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : Function.Surjective (algebraMap F E)) : Algebra.IsSeparable F E :=
  ⟨fun y => by
    obtain ⟨a, rfl⟩ := h y
    exact isSeparable_algebraMap a⟩

/-- **Smoothness at closed points.** -/
theorem isSmoothAt_of_isMaximal (hB : ¬ IsField B) (q : Ideal B) [hqm : q.IsMaximal] :
    Algebra.IsSmoothAt K q := by
  have hq : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hqm hB
  obtain ⟨x, hx⟩ := exists_unif q hq
  have hxq : x ∈ q := mem_of_unif q hx
  have hx0 : x ≠ 0 := ne_zero_of_unif q hq hx
  letI : Algebra K[X] B := (aeval x).toRingHom.toAlgebra
  haveI : IsScalarTower K K[X] B := IsScalarTower.of_algebraMap_eq fun c => (aeval_C x c).symm
  haveI : Algebra.FiniteType K[X] B := Algebra.FiniteType.of_restrictScalars_finiteType K K[X] B
  haveI : Algebra.FinitePresentation K[X] B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Module.Flat K[X] B := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot,
      Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
    exact aeval_injective q hxq hx0
  have hxX : algebraMap K[X] B X = x := aeval_X x
  letI : Algebra (Localization.AtPrime (q.under K[X])) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under K[X]) q
  haveI : Algebra.IsUnramifiedAt K[X] q := by
    rw [Algebra.isUnramifiedAt_iff_map_eq K[X] (q.under K[X]) q]
    refine ⟨?_, le_antisymm ?_ ?_⟩
    · apply isSeparable_of_surjective
      intro y
      obtain ⟨b, rfl⟩ := Ideal.algebraMap_residueField_surjective q y
      obtain ⟨c, hc⟩ := exists_sub_mem (K := K) q b
      refine ⟨algebraMap K[X] (q.under K[X]).ResidueField (C c), ?_⟩
      rw [← IsScalarTower.algebraMap_apply K[X] (q.under K[X]).ResidueField q.ResidueField,
        IsScalarTower.algebraMap_apply K[X] B q.ResidueField,
        show algebraMap K[X] B (C c) = algebraMap K B c from aeval_C x c,
        ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField, ← neg_sub]
      exact q.neg_mem hc
    · calc Ideal.map (algebraMap K[X] (Localization.AtPrime q)) (q.under K[X])
          = Ideal.map (algebraMap B (Localization.AtPrime q))
              (Ideal.map (algebraMap K[X] B) (q.under K[X])) := by
            rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
        _ ≤ Ideal.map (algebraMap B (Localization.AtPrime q)) q :=
            Ideal.map_mono (Ideal.map_comap_le (f := algebraMap K[X] B) (K := q))
        _ = maximalIdeal (Localization.AtPrime q) := Localization.AtPrime.map_eq_maximalIdeal
    · rw [hx, Ideal.span_le, Set.singleton_subset_iff]
      have hX : (X : K[X]) ∈ Ideal.comap (algebraMap K[X] B) q := by
        rw [Ideal.mem_comap, hxX]
        exact hxq
      have h1 : algebraMap B (Localization.AtPrime q) x = algebraMap K[X] (Localization.AtPrime q) X := by
        rw [IsScalarTower.algebraMap_apply K[X] B (Localization.AtPrime q), hxX]
      rw [SetLike.mem_coe, h1]
      exact Ideal.mem_map_of_mem _ hX
  haveI : Algebra.IsEtaleAt K[X] q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q
  haveI : IsScalarTower K K[X] (Localization.AtPrime q) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K B (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply K[X] B (Localization.AtPrime q), ← IsScalarTower.algebraMap_apply K K[X] B]
  exact Algebra.FormallySmooth.comp K K[X] (Localization.AtPrime q)

/-- `B` is formally smooth over `K`: the smooth locus is open and contains every closed point. -/
theorem formallySmooth_of_dedekind (hB : ¬ IsField B) : Algebra.FormallySmooth K B := by
  haveI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [← Algebra.smoothLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun P => ?_
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  have hMs : (⟨M, hM.isPrime⟩ : PrimeSpectrum B) ∈ Algebra.smoothLocus K B := isSmoothAt_of_isMaximal hB M
  exact ((PrimeSpectrum.le_iff_specializes P ⟨M, hM.isPrime⟩).mp hle).mem_open Algebra.isOpen_smoothLocus hMs

/-- **D-B0 (ring part).** A Dedekind domain of finite type over an algebraically closed field is smooth. -/
theorem smooth_of_dedekind (hB : ¬ IsField B) : Algebra.Smooth K B :=
  haveI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  ⟨formallySmooth_of_dedekind hB, inferInstance⟩

end SmoothDedekind

end RamanujanPetersson.ThetaCube

end

-- ===== S4.Def_RP_IntersectA_Top =====
section

/-!
# S4-IntersectA, file Top: general position by a dimension count (topology only)

`X` a Noetherian scheme (points ordered by specialization, `x ≤ y ↔ y ⤳ x`, so `Order.height x` is the
dimension of `closure {x}`). If `height x ≤ g` everywhere and, for each `i < g`, the closed sets `H i a`
(`a : α`) can be chosen to avoid any finite set of points, then some choice makes `⋂ i < g, H i (a i)`
a finite set of closed points. This is the dimension half of L31 (S4_COREB_ROUTE.md section 3).
-/

set_option autoImplicit false

universe u

open Topology TopologicalSpace AlgebraicGeometry

namespace RamanujanPetersson.IntersectA

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- A closed set is a finite union of closures of its own points (its generic points of components). -/
theorem exists_finset_closure (F : Set X) (hF : IsClosed F) :
    ∃ S : Finset X, (∀ η ∈ S, η ∈ F) ∧ F = ⋃ η ∈ S, closure {η} := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨∅, by simp, by rw [Set.eq_empty_of_isEmpty F]; simp⟩
  obtain ⟨T, hTf, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  choose! gp hgp using fun t (ht : t ∈ T) => QuasiSober.sober (hTi t ht) (hTc t ht)
  refine ⟨(hTf.image gp).toFinset, ?_, ?_⟩
  · intro η hη
    rw [Set.Finite.mem_toFinset] at hη
    obtain ⟨t, ht, rfl⟩ := hη
    exact ⟨t, ht, (hgp t ht).mem⟩
  · ext x
    simp only [Set.mem_sUnion, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨gp t, ⟨t, ht, rfl⟩, by rw [(hgp t ht).def]; exact hx⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, hx⟩
      exact ⟨t, ht, by rwa [(hgp t ht).def] at hx⟩

/-- Cutting by a closed set `H` that misses the finitely many generic points strictly lowers them. -/
theorem step (S : Finset X) (H : Set X) (hH : IsClosed H) (hS : ∀ η ∈ S, η ∉ H) :
    ∃ S' : Finset X, (⋃ η ∈ S, closure {η}) ∩ H ⊆ ⋃ ξ ∈ S', closure {ξ} ∧
      ∀ ξ ∈ S', ∃ η ∈ S, ξ < η := by
  have hF : IsClosed ((⋃ η ∈ S, closure {η}) ∩ H) :=
    (isClosed_biUnion_finset fun η _ => isClosed_closure).inter hH
  obtain ⟨S', hS'F, hS'eq⟩ := exists_finset_closure _ hF
  refine ⟨S', hS'eq.le, fun ξ hξ => ?_⟩
  obtain ⟨hξ1, hξH⟩ := hS'F ξ hξ
  simp only [Set.mem_iUnion, exists_prop] at hξ1
  obtain ⟨η, hη, hξη⟩ := hξ1
  refine ⟨η, hη, lt_iff_le_not_ge.2 ⟨specializes_iff_mem_closure.mpr hξη, fun h => ?_⟩⟩
  exact hS η hη (Specializes.mem_closed h hH hξH)

/-- The height bookkeeping of one cut: `height + j ≤ g` becomes `height + (j + 1) ≤ g`. -/
theorem height_step (S : Finset X) (H : Set X) (hH : IsClosed H) (hS : ∀ η ∈ S, η ∉ H) (j g : ℕ)
    (hht : ∀ η ∈ S, Order.height η + j ≤ g) :
    ∃ S' : Finset X, (⋃ η ∈ S, closure {η}) ∩ H ⊆ ⋃ ξ ∈ S', closure {ξ} ∧
      ∀ ξ ∈ S', Order.height ξ + ((j + 1 : ℕ) : ℕ∞) ≤ g := by
  obtain ⟨S', h1, h2⟩ := step S H hH hS
  refine ⟨S', h1, fun ξ hξ => ?_⟩
  obtain ⟨η, hη, hlt⟩ := h2 ξ hξ
  have hηfin : Order.height η < ⊤ :=
    lt_of_le_of_lt le_self_add (lt_of_le_of_lt (hht η hη) (ENat.natCast_lt_top g))
  have hξfin : Order.height ξ < ⊤ := lt_of_le_of_lt (Order.height_mono hlt.le) hηfin
  have h3 : Order.height ξ + 1 ≤ Order.height η :=
    Order.add_one_le_of_lt (Order.height_strictMono hlt hξfin)
  calc Order.height ξ + ((j + 1 : ℕ) : ℕ∞) = Order.height ξ + 1 + j := by push_cast; ring
    _ ≤ Order.height η + j := by gcongr
    _ ≤ g := hht η hη

omit [NoetherianSpace X] in
/-- A point of height `0` is closed. -/
theorem isClosed_singleton_of_height_eq_zero (x : X) (hx : Order.height x = 0) :
    IsClosed ({x} : Set X) := by
  rw [Order.height_eq_zero] at hx
  refine isClosed_of_closure_subset fun y hy => ?_
  have h1 : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have h2 : y ⤳ x := hx (show y ≤ x from h1)
  exact Set.mem_singleton_iff.mpr (h1.antisymm h2).eq.symm

/-- The inductive construction: after `j` cuts the intersection lies in `⋃ closure {η}` with
`height η + j ≤ g`. -/
theorem gp_aux {α : Type*} (g : ℕ) (H : ℕ → α → Set X) (hHc : ∀ i a, IsClosed (H i a))
    (hH : ∀ i (S : Finset X), ∃ a, ∀ η ∈ S, η ∉ H i a)
    (S0 : Finset X) (hS0 : ∀ η ∈ S0, Order.height η ≤ g) :
    ∀ j ≤ g, ∃ a : ℕ → α, ∃ S : Finset X,
      (⋃ η ∈ S0, closure {η}) ∩ (⋂ i < j, H i (a i)) ⊆ ⋃ η ∈ S, closure {η} ∧
        ∀ η ∈ S, Order.height η + (j : ℕ∞) ≤ g := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨a0, -⟩ := hH 0 ∅
    exact ⟨fun _ => a0, S0, Set.inter_subset_left, fun η hη => by simpa using hS0 η hη⟩
  | succ j ih =>
    intro hj
    obtain ⟨a, S, hsub, hht⟩ := ih (Nat.le_of_succ_le hj)
    obtain ⟨b, hb⟩ := hH j S
    obtain ⟨S', hsub', hht'⟩ := height_step S (H j b) (hHc j b) hb j g hht
    refine ⟨Function.update a j b, S', ?_, hht'⟩
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hx
    obtain ⟨hx0, hxi⟩ := hx
    refine hsub' ⟨hsub ⟨hx0, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter]
      intro i hi
      have := hxi i (Nat.lt_succ_of_lt hi)
      rwa [Function.update_of_ne (Nat.ne_of_lt hi)] at this
    · have := hxi j (Nat.lt_succ_self j)
      rwa [Function.update_self] at this

/-- **General position (topological form).** If `dim X ≤ g` and each `H i ·` can avoid any finite set,
some choice of parameters makes `⋂ i < g, H i (a i)` a finite set of closed points. -/
theorem exists_finite_inter {α : Type*} (g : ℕ) (hdim : ∀ x : X, Order.height x ≤ g)
    (H : ℕ → α → Set X) (hHc : ∀ i a, IsClosed (H i a))
    (hH : ∀ i (S : Finset X), ∃ a, ∀ η ∈ S, η ∉ H i a) :
    ∃ a : ℕ → α, (⋂ i < g, H i (a i)).Finite ∧
      ∀ x ∈ ⋂ i < g, H i (a i), IsClosed ({x} : Set X) := by
  obtain ⟨S0, -, hS0⟩ := exists_finset_closure (Set.univ : Set X) isClosed_univ
  obtain ⟨a, S, hsub, hht⟩ := gp_aux g H hHc hH S0 (fun η _ => hdim η) g le_rfl
  have hcl : ∀ η ∈ S, closure {η} = ({η} : Set X) := fun η hη => by
    have h0 : Order.height η = 0 := by
      have h1 := hht η hη
      by_contra h
      have h3 : (1 : ℕ∞) + g ≤ Order.height η + g := by
        gcongr
        exact Order.one_le_iff_ne_zero.mpr h
      have h2 := h3.trans h1
      norm_cast at h2
      omega
    exact (isClosed_singleton_of_height_eq_zero η h0).closure_eq
  have key : (⋂ i < g, H i (a i)) ⊆ (S : Set X) := by
    intro x hx
    have hx' := hsub ⟨by rw [← hS0]; trivial, hx⟩
    simp only [Set.mem_iUnion, exists_prop] at hx'
    obtain ⟨η, hη, hxη⟩ := hx'
    rw [hcl η hη, Set.mem_singleton_iff] at hxη
    rw [hxη]
    exact hη
  refine ⟨a, S.finite_toSet.subset key, fun x hx => ?_⟩
  exact closure_eq_iff_isClosed.mp (hcl x (key hx))

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IsogDegA_Trans =====
section

/-!
# S4-IsogDegA, file Trans: translations by `k`-points of a group scheme over `k`

`A : Over (Spec k)` with `[GrpObj A]`. For a `k`-point `a : 𝟙_ ⟶ A`, `transl A a = 𝟙 A * (toUnit A ≫ a)`
is right translation by `a`, an automorphism of `A` over `k`. A homomorphism `φ` intertwines
`transl a` and `transl (a ≫ φ)`. With `k` algebraically closed and `A` locally of finite type,
`pt c = c.left (closed point)` identifies `k`-points with closed points, and translations act
transitively on closed points.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IsogDegA

section Group

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Right translation by the `k`-point `a`. -/
noncomputable def transl (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ⟶ A :=
  𝟙 A * (toUnit A ≫ a)

theorem comp_transl {X : Over (Spec (.of k))} (f : X ⟶ A) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    f ≫ transl A a = f * (toUnit X ≫ a) := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem transl_one : transl A 1 = 𝟙 A := by
  rw [transl, comp_one, _root_.mul_one]

theorem transl_comp_transl (a b : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    transl A a ≫ transl A b = transl A (a * b) := by
  rw [comp_transl, transl, transl, comp_mul, _root_.mul_assoc]

/-- Translation as an automorphism. -/
noncomputable def translIso (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ≅ A where
  hom := transl A a
  inv := transl A a⁻¹
  hom_inv_id := by rw [transl_comp_transl, mul_inv_cancel, transl_one]
  inv_hom_id := by rw [transl_comp_transl, inv_mul_cancel, transl_one]

theorem point_comp_transl (c a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    c ≫ transl A a = c * a := by
  rw [comp_transl, toUnit_unit, Category.id_comp]

/-- A homomorphism intertwines translations. -/
theorem transl_comp_hom (φ : A ⟶ A) [IsMonHom φ] (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    transl A a ≫ φ = φ ≫ transl A (a ≫ φ) := by
  rw [comp_transl, transl, mul_comp, Category.id_comp, Category.assoc]

end Group

section Points

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

variable (k) in
/-- The unique point of `Spec k`. -/
noncomputable def pt0 : Spec (.of k) := IsLocalRing.closedPoint k

/-- The point of `A` hit by the `k`-point `c`. -/
noncomputable def pt (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A.left :=
  c.left (pt0 k)

theorem pt_comp {B : Over (Spec (.of k))} (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) (f : A ⟶ B) :
    pt B (c ≫ f) = f.left (pt A c) := by
  simp only [pt, Over.comp_left, Scheme.Hom.comp_apply]

theorem transl_pt [GrpObj A] (c a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    (transl A a).left (pt A c) = pt A (c * a) := by
  rw [← pt_comp, point_comp_transl, pt]

variable [IsAlgClosed k] [LocallyOfFiniteType A.hom]

/-- `k`-points are the closed points. -/
noncomputable def ptEquiv : (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃ closedPoints A.left :=
  (Equiv.mk (fun c ↦ ⟨c.left, Over.w c⟩) (fun p ↦ Over.homMk p.1 p.2) (fun _ ↦ rfl)
    (fun _ ↦ rfl)).trans (pointEquivClosedPoint A.hom)

theorem ptEquiv_apply (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : (ptEquiv A c).1 = pt A c := rfl

theorem pt_injective : Function.Injective (pt A) := fun _ _ h ↦
  (ptEquiv A).injective (Subtype.ext h)

theorem isClosed_pt (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsClosed {pt A c} :=
  (ptEquiv A c).2

theorem exists_pt_eq (z : A.left) (hz : IsClosed {z}) : ∃ c, pt A c = z :=
  ⟨(ptEquiv A).symm ⟨z, hz⟩, by rw [← ptEquiv_apply, Equiv.apply_symm_apply]⟩

/-- Translations act transitively on closed points. -/
theorem exists_transl_eq [GrpObj A] (z₁ z₂ : A.left) (h₁ : IsClosed {z₁}) (h₂ : IsClosed {z₂}) :
    ∃ a, (transl A a).left z₁ = z₂ := by
  obtain ⟨c₁, rfl⟩ := exists_pt_eq A z₁ h₁
  obtain ⟨c₂, rfl⟩ := exists_pt_eq A z₂ h₂
  exact ⟨c₁⁻¹ * c₂, by rw [transl_pt, mul_inv_cancel_left]⟩

end Points

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IntersectA_Gen =====
section

/-!
# S4-IntersectA, file Gen: translates in general position (L31 existence)

`A : Over (Spec k)` a group scheme, `k` algebraically closed, `A` locally of finite type.
Left translations `ltransl A w` move `k`-points by `w * _`. For a point `y` and a proper closed `D`,
the right translation parameters `a` with `(transl A a).left y ∈ D` have their points in a proper
closed set (`exists_open_good`); with `A` irreducible, finitely many points can be moved off `D` by one
`a` (`exists_good`). Combined with the dimension count of file Top: for `g` closed subschemes `D i`
with proper supports on `A` of dimension `≤ g`, some translates meet in a finite set of closed points
(`exists_finite_support`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory TopologicalSpace

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

/-- Finitely many nonempty opens of an irreducible space meet. -/
theorem nonempty_biInter_finset {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] {I : Type*}
    (S : Finset I) (U : I → Set X) (ho : ∀ i ∈ S, IsOpen (U i)) (hn : ∀ i ∈ S, (U i).Nonempty) :
    (⋂ i ∈ S, U i).Nonempty := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at ho hn
    rw [Finset.set_biInter_insert]
    exact nonempty_preirreducible_inter ho.1 (isOpen_biInter_finset ho.2) hn.1 (ih ho.2 hn.2)

section Left

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Left translation by the `k`-point `w`. -/
noncomputable def ltransl (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ⟶ A :=
  (toUnit A ≫ w) * 𝟙 A

theorem comp_ltransl {X : Over (Spec (.of k))} (f : X ⟶ A) (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    f ≫ ltransl A w = (toUnit X ≫ w) * f := by
  rw [ltransl, comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem ltransl_one : ltransl A 1 = 𝟙 A := by
  rw [ltransl, comp_one, _root_.one_mul]

theorem ltransl_comp_ltransl (w v : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ltransl A w ≫ ltransl A v = ltransl A (v * w) := by
  rw [comp_ltransl, ltransl, ltransl, comp_mul, _root_.mul_assoc]

theorem isIso_ltransl_left (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsIso (ltransl A w).left :=
  ⟨⟨(ltransl A w⁻¹).left, by
    rw [← Over.comp_left, ltransl_comp_ltransl, _root_.inv_mul_cancel, ltransl_one, Over.id_left], by
    rw [← Over.comp_left, ltransl_comp_ltransl, _root_.mul_inv_cancel, ltransl_one, Over.id_left]⟩⟩

theorem point_comp_ltransl (c w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : c ≫ ltransl A w = w * c := by
  rw [comp_ltransl, toUnit_unit, Category.id_comp]

theorem ltransl_pt (c w : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    (ltransl A w).left (pt A c) = pt A (w * c) := by
  rw [← pt_comp, point_comp_ltransl]

/-- The intersection of the translates `D i` by `a i` (all `g` divisors translated). -/
noncomputable def Zid {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) : A.left.IdealSheafData :=
  ⨆ i, (D i).comap (transl A (a i)).left

theorem coe_support_Zid {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ((Zid A D a).support : Set A.left) = ⋂ i, (transl A (a i)).left ⁻¹' (D i).support := by
  ext x
  simp [Zid]

end Left

section Generic

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [LocallyOfFiniteType A.hom]

omit [GrpObj A] in
/-- A nonempty locally closed set contains a `k`-point (Jacobson). -/
theorem exists_pt_mem (F : Set A.left) (hF : IsLocallyClosed F) (hne : F.Nonempty) :
    ∃ w, pt A w ∈ F := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨z, hzF, hz⟩ := nonempty_inter_closedPoints hne hF
  obtain ⟨w, rfl⟩ := exists_pt_eq A z hz
  exact ⟨w, hzF⟩

/-- The translation parameters moving `y` into a proper closed `D` lie in a proper closed set. -/
theorem exists_open_good (y : A.left) (D : Set A.left) (hD : IsClosed D) (hne : D ≠ Set.univ) :
    ∃ U : Set A.left, IsOpen U ∧ U.Nonempty ∧ ∀ a, pt A a ∈ U → (transl A a).left y ∉ D := by
  let B : Set A.left := ⋂ (w) (_ : pt A w ∈ closure {y}), (ltransl A w).left ⁻¹' D
  have hB : IsClosed B :=
    isClosed_iInter fun w => isClosed_iInter fun _ => hD.preimage (ltransl A w).left.continuous
  refine ⟨Bᶜ, hB.isOpen_compl, ?_, ?_⟩
  · obtain ⟨w₀, hw₀⟩ := exists_pt_mem A (closure {y}) isClosed_closure.isLocallyClosed
      ⟨y, subset_closure rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y ∉ D := by
      by_contra h
      push_neg at h
      exact hne (Set.eq_univ_of_forall h)
    have := isIso_ltransl_left A w₀
    obtain ⟨x, rfl⟩ := (ltransl A w₀).left.surjective y
    exact ⟨x, fun hx => hy (Set.mem_iInter₂.1 hx w₀ hw₀)⟩
  · intro a ha hbad
    apply ha
    refine Set.mem_iInter₂.2 fun w hw => ?_
    show (ltransl A w).left (pt A a) ∈ D
    rw [ltransl_pt, ← transl_pt]
    have h1 := map_mem_closure (t := D) (transl A a).left.continuous hw
      (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hbad)
    rwa [hD.closure_eq] at h1

/-- One translation moves finitely many points off a proper closed set. -/
theorem exists_good [IrreducibleSpace A.left] (S : Finset A.left) (D : Set A.left) (hD : IsClosed D)
    (hne : D ≠ Set.univ) : ∃ a, ∀ y ∈ S, (transl A a).left y ∉ D := by
  choose U hUo hUn hU using fun y => exists_open_good A y D hD hne
  obtain ⟨a, ha⟩ := exists_pt_mem A (⋂ y ∈ S, U y)
    (isOpen_biInter_finset fun y _ => hUo y).isLocallyClosed
    (nonempty_biInter_finset S U (fun y _ => hUo y) fun y _ => hUn y)
  exact ⟨a, fun y hy => hU y a (Set.mem_iInter₂.1 ha y hy)⟩

/-- L31 (existence): some translates of `g` proper closed subschemes meet in finitely many closed
points, on a Noetherian irreducible `A` of dimension `≤ g`. -/
theorem exists_finite_support [NoetherianSpace A.left] [IrreducibleSpace A.left] (g : ℕ)
    (hdim : ∀ x : A.left, Order.height x ≤ g) (D : Fin g → A.left.IdealSheafData)
    (hD : ∀ i, (D i).support ≠ ⊤) :
    ∃ a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A),
      ((Zid A D a).support : Set A.left).Finite ∧
        ∀ x ∈ ((Zid A D a).support : Set A.left), IsClosed ({x} : Set A.left) := by
  classical
  let H : ℕ → (𝟙_ (Over (Spec (.of k))) ⟶ A) → Set A.left := fun i a =>
    if h : i < g then (transl A a).left ⁻¹' (D ⟨i, h⟩).support else ∅
  have hHc : ∀ i a, IsClosed (H i a) := by
    intro i a
    by_cases h : i < g
    · simp only [H, dif_pos h]
      exact (D ⟨i, h⟩).support.isClosed.preimage (transl A a).left.continuous
    · simp only [H, dif_neg h]
      exact isClosed_empty
  have hH : ∀ i (S : Finset A.left), ∃ a, ∀ y ∈ S, y ∉ H i a := by
    intro i S
    by_cases h : i < g
    · have hne : ((D ⟨i, h⟩).support : Set A.left) ≠ Set.univ := fun he =>
        hD ⟨i, h⟩ (TopologicalSpace.Closeds.ext (by rw [he]; rfl))
      obtain ⟨a, ha⟩ := exists_good A S _ (D ⟨i, h⟩).support.isClosed hne
      exact ⟨a, fun y hy => by simp only [H, dif_pos h]; exact ha y hy⟩
    · exact ⟨1, fun y _ => by simp only [H, dif_neg h]; exact Set.notMem_empty y⟩
  obtain ⟨a, hfin, hcl⟩ := exists_finite_inter g hdim H hHc hH
  have hsub : ((Zid A D (fun i => a i)).support : Set A.left) ⊆ ⋂ i < g, H i (a i) := by
    intro x hx
    rw [coe_support_Zid, Set.mem_iInter] at hx
    refine Set.mem_iInter₂.2 fun i hi => ?_
    simp only [H, dif_pos hi]
    exact hx ⟨i, hi⟩
  exact ⟨fun i => a i, hfin.subset hsub, fun x hx => hcl x (hsub hx)⟩

end Generic

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IntersectA_Fam =====
section

/-!
# S4-IntersectA, file Fam: the family of translated intersections over `A^g`

`Pw A n = A ⊗ ⋯ ⊗ A` (`n` factors) in `Over (Spec k)`, with projections `proj A n i` and the point
`ptOf A n a` with coordinates `a`. Over `P = Pw A g` the family `famI A D` on `A ⊗ P` is cut out by
the pullbacks of the `D i` along `μᵢ(x, c) = x * cᵢ`. Its fibre over a `k`-point `c` of `P` is the
intersection `Zid A D (c ≫ proj A g ·)` of the translates (`comap_famI`, `isPullback_fibre`).
`len A J` is the length of a closed subscheme `J` of `A`: the rank of `J → Spec k`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

section Pow

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- `Pw A n = A^n` as an iterated tensor power. -/
noncomputable def Pw : ℕ → Over (Spec (.of k))
  | 0 => 𝟙_ _
  | n + 1 => Pw n ⊗ A

/-- The coordinate projections of `A^n`. -/
noncomputable def proj : (n : ℕ) → Fin n → (Pw A n ⟶ A)
  | 0, i => i.elim0
  | n + 1, i => if h : (i : ℕ) < n then fst (Pw A n) A ≫ proj n ⟨i, h⟩ else snd (Pw A n) A

/-- The `k`-point of `A^n` with coordinates `a`. -/
noncomputable def ptOf : (n : ℕ) → (Fin n → (𝟙_ (Over (Spec (.of k))) ⟶ A)) →
    (𝟙_ (Over (Spec (.of k))) ⟶ Pw A n)
  | 0, _ => 𝟙 _
  | n + 1, a => lift (ptOf n (Fin.init a)) (a (Fin.last n))

theorem proj_last (n : ℕ) : proj A (n + 1) (Fin.last n) = snd (Pw A n) A := by
  simp [proj]; rfl

theorem proj_castSucc (n : ℕ) (j : Fin n) :
    proj A (n + 1) j.castSucc = fst (Pw A n) A ≫ proj A n j := by
  simp [proj]; rfl

theorem ptOf_succ_fst (n : ℕ) (a : Fin (n + 1) → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ptOf A (n + 1) a ≫ fst (Pw A n) A = ptOf A n (Fin.init a) :=
  lift_fst _ _

theorem ptOf_succ_snd (n : ℕ) (a : Fin (n + 1) → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ptOf A (n + 1) a ≫ snd (Pw A n) A = a (Fin.last n) :=
  lift_snd _ _

theorem ptOf_proj (n : ℕ) (a : Fin n → (𝟙_ (Over (Spec (.of k))) ⟶ A)) (i : Fin n) :
    ptOf A n a ≫ proj A n i = a i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => rw [proj_last]; exact ptOf_succ_snd A n a
    | cast j =>
      rw [proj_castSucc]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ proj A n j) (ptOf_succ_fst A n a))).trans (ih _ j)

theorem ptOf_comp_proj (n : ℕ) (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A n) :
    ptOf A n (fun i => c ≫ proj A n i) = c := by
  induction n with
  | zero => exact toUnit_unique _ _
  | succ n ih =>
    refine CartesianMonoidalCategory.hom_ext (X := Pw A n) (Y := A) _ _ ?_ ?_
    · have h : Fin.init (fun i => c ≫ proj A (n + 1) i) =
          fun j => (c ≫ fst (Pw A n) A) ≫ proj A n j := by
        funext j
        simp only [Fin.init, proj_castSucc]
        exact (Category.assoc _ _ _).symm
      exact (ptOf_succ_fst A n _).trans (by rw [h, ih]; rfl)
    · exact (ptOf_succ_snd A n _).trans (congrArg (c ≫ ·) (proj_last A n))

end Pow

section Family

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- `mu A g i : A ⊗ A^g ⟶ A`, `(x, c) ↦ x * cᵢ`. -/
noncomputable def mu (g : ℕ) (i : Fin g) : A ⊗ Pw A g ⟶ A :=
  fst A (Pw A g) * (snd A (Pw A g) ≫ proj A g i)

/-- The family of translated intersections on `A × A^g`. -/
noncomputable def famI {g : ℕ} (D : Fin g → A.left.IdealSheafData) :
    (A ⊗ Pw A g).left.IdealSheafData :=
  ⨆ i, (D i).comap (mu A g i).left

/-- The section `x ↦ (x, c)` over a `k`-point `c` of `A^g`. -/
noncomputable def sec {g : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) : A ⟶ A ⊗ Pw A g :=
  lift (𝟙 A) (toUnit A ≫ c)

theorem sec_mu {g : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) (i : Fin g) :
    sec A c ≫ mu A g i = transl A (c ≫ proj A g i) := by
  simp only [mu, sec, transl, comp_mul, lift_fst, lift_snd_assoc, Category.assoc]

theorem comap_famI {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) :
    (famI A D).comap (sec A c).left = Zid A D (fun i => c ≫ proj A g i) := by
  rw [famI, Zid, (Scheme.IdealSheafData.map_gc (sec A c).left).l_iSup]
  refine iSup_congr fun i => ?_
  try dsimp only
  rw [← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, sec_mu]

omit [GrpObj A] in
/-- The section over `c` is the base change of the point `c` along `A ⊗ A^g → A^g`. -/
theorem isPullback_sec {g : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) :
    IsPullback (sec A c).left A.hom (snd A (Pw A g)).left c.left := by
  have h1 : (sec A c).left ≫ (fst A (Pw A g)).left = 𝟙 _ := by
    rw [← Over.comp_left, sec, lift_fst, Over.id_left]
  have h2 : c.left ≫ (Pw A g).hom = 𝟙 (Spec (.of k)) := Over.w c
  have t : IsPullback (fst A (Pw A g)).left (snd A (Pw A g)).left A.hom (Pw A g).hom :=
    IsPullback.of_hasPullback A.hom (Pw A g).hom
  refine IsPullback.of_right (h₁₁ := (sec A c).left) ?_ ?_ t
  · rw [h1, h2]
    exact IsPullback.id_horiz A.hom
  · rw [← Over.comp_left, sec, lift_snd, Over.comp_left]; rfl

/-- The family over `A^g`: the subscheme `famI` mapped to the parameter space. -/
noncomputable def famP {g : ℕ} (D : Fin g → A.left.IdealSheafData) :
    (famI A D).subscheme ⟶ (Pw A g).left :=
  (famI A D).subschemeι ≫ (snd A (Pw A g)).left

/-- The fibre of the family over `c` is the subscheme `(famI A D).comap (sec A c)` over `Spec k`. -/
theorem isPullback_fibre {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) :
    IsPullback (((famI A D).comapIso (sec A c).left).hom ≫ pullback.snd _ _)
      (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) (famP A D) c.left := by
  have s : IsPullback ((famI A D).comap (sec A c).left).subschemeι
      (((famI A D).comapIso (sec A c).left).hom ≫ pullback.snd _ _) (sec A c).left
      (famI A D).subschemeι :=
    IsPullback.of_iso_pullback ⟨by
      rw [Category.assoc, ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]⟩ _
      (Scheme.IdealSheafData.comapIso_hom_fst _ _) rfl
  exact s.flip.paste_vert (isPullback_sec A c)

end Family

/-- The length of a closed subscheme `J` of `A`: the rank of `J → Spec k` at the point. -/
noncomputable def len {k : Type u} [Field k] (A : Over (Spec (.of k))) (J : A.left.IdealSheafData) : ℕ :=
  Scheme.Hom.finrank (J.subschemeι ≫ A.hom) (pt0 k)

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IntersectA_Cons =====
section

/-!
# S4-IntersectA, file Cons: generic flatness of a finite morphism

`GoodNbhd p`: an open `j : T ⟶ Y` (nonempty) over which `p : Z ⟶ Y` becomes finite flat of constant rank.
`exists_free_away`: a finite algebra `S` over a Noetherian domain `R` becomes free after inverting one
`r ≠ 0`. Hence `goodNbhd_SpecMap` (finite `Spec S → Spec R`), `goodNbhd_of_isFinite` (finite `q` over an
integral locally Noetherian base) and `goodNbhd_of_isProper` (proper `p` with one finite fibre, by
Zariski's main theorem `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace RamanujanPetersson.IntersectA

theorem exists_free_away {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ r : R, r ≠ 0 ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] S) := by
  haveI : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) S) (FractionRing R)
  refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
  exact Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r)
    (Localization.Away r) (LocalizedModule.mkLinearMap (Submonoid.powers r) S)).equiv.symm

/-- A nonempty open `j : T ⟶ Y` over which `p` is finite flat of constant rank `n`. -/
def GoodNbhd {Z Y : Scheme.{u}} (p : Z ⟶ Y) : Prop :=
  ∃ (T W : Scheme.{u}) (j : T ⟶ Y) (i : W ⟶ Z) (q : W ⟶ T), IsOpenImmersion j ∧ Nonempty T ∧
    IsPullback i q p j ∧ Flat q ∧ IsFinite q ∧ ∃ n : ℕ, ∀ t, q.finrank t = n

theorem GoodNbhd.of_isPullback {Z Y Z' Y' : Scheme.{u}} {p : Z ⟶ Y} {p' : Z' ⟶ Y'} {i' : Z' ⟶ Z}
    {j' : Y' ⟶ Y} [IsOpenImmersion j'] (h : IsPullback i' p' p j') (hp : GoodNbhd p') :
    GoodNbhd p := by
  obtain ⟨T, W, j, i, q, hj, hT, hsq, hfl, hfin, n, hn⟩ := hp
  haveI := hj
  exact ⟨T, W, j ≫ j', i ≫ i', q, inferInstance, hT, hsq.paste_horiz h, hfl, hfin, n, hn⟩

theorem goodNbhd_SpecMap {R S : CommRingCat.{u}} [IsDomain R] [IsNoetherianRing R] (φ : R ⟶ S)
    (hφ : φ.hom.Finite) : GoodNbhd (Spec.map φ) := by
  letI : Algebra R S := φ.hom.toAlgebra
  haveI : Module.Finite R S := hφ
  obtain ⟨r, hr, hfree⟩ := exists_free_away (R := R) (S := S)
  haveI : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have hsq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) S)).flip
  have e : (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom :
      CommRingCat.of (Localization.Away r) ⟶ CommRingCat.of (Localization.Away r ⊗[R] S)) =
      CommRingCat.ofHom (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S)) := rfl
  rw [e] at hsq
  refine ⟨_, _, _, _, _, inferInstance, inferInstance, hsq, ?_, ?_,
    Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] S), fun t => ?_⟩
  · exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · refine (Scheme.Hom.finrank_SpecMap_algebraMap (Localization.Away r)
      (Localization.Away r ⊗[R] S) t).trans ?_
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact Pi.natCast_apply _ t

/-- Finite over an affine integral locally Noetherian base. -/
theorem goodNbhd_of_isAffine {W T : Scheme.{u}} (q : W ⟶ T) [IsFinite q] [IsAffine T]
    [IsIntegral T] [IsLocallyNoetherian T] : GoodNbhd q := by
  haveI : IsAffine W := isAffine_of_isAffineHom q
  haveI : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  have hsq : IsPullback W.isoSpec.inv (Spec.map q.appTop) q T.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [Iso.inv_comp_eq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  exact GoodNbhd.of_isPullback hsq (goodNbhd_SpecMap q.appTop q.finite_appTop)

/-- Finite over an integral locally Noetherian base. -/
theorem goodNbhd_of_isFinite {W T : Scheme.{u}} (q : W ⟶ T) [IsFinite q] [IsIntegral T]
    [IsLocallyNoetherian T] : GoodNbhd q := by
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  obtain ⟨R, u, hu, y, -⟩ := T.exists_Spec_apply_eq t
  haveI := hu
  haveI : Nonempty (Spec R) := ⟨y⟩
  haveI : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion u
  haveI : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion u
  exact GoodNbhd.of_isPullback (IsPullback.of_hasPullback q u)
    (goodNbhd_of_isAffine (pullback.snd q u))

/-- Proper with one finite fibre, over an integral locally Noetherian base (generic flatness). -/
theorem goodNbhd_of_isProper {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p] [IsIntegral Y]
    [IsLocallyNoetherian Y] (y : Y) (hy : (p ⁻¹' {y}).Finite) : GoodNbhd p := by
  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton p y hy
  haveI := hV
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  exact GoodNbhd.of_isPullback (isPullback_morphismRestrict p V).flip
    (goodNbhd_of_isFinite (p ∣_ V))

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IntersectB_Alg =====
section

/-!
# S4-IntersectB, file Alg: the exact-sequence lemma behind additivity (L33, part 3)

`finrank_quot_mul`: for ideals `I, I', J` of a `k`-algebra `R`, an element `u ∈ I'` and `s ∈ R`
with `s • I' ⊆ (u)`, `s` a unit modulo `X := I * I' ⊔ J`, and `u` a non-zero-divisor modulo `J`
after inverting `s`, the quotient dimensions add:
`dim R/X = dim R/(I ⊔ J) + dim R/(I' ⊔ J)` (short exact sequence `0 → R/(I⊔J) --u--> R/X → R/(I'⊔J) → 0`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.IntersectB

section Alg

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

theorem mem_of_isUnit_mul_mem {X : Ideal R} {s x : R} (hs : IsUnit (Ideal.Quotient.mk X s))
    (h : s * x ∈ X) : x ∈ X := by
  obtain ⟨t, ht⟩ := hs.exists_left_inv
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  calc Ideal.Quotient.mk X x
      = (Ideal.Quotient.mk X t * Ideal.Quotient.mk X s) * Ideal.Quotient.mk X x := by
        rw [ht, one_mul]
    _ = Ideal.Quotient.mk X t * Ideal.Quotient.mk X (s * x) := by rw [map_mul, mul_assoc]
    _ = 0 := by rw [h, mul_zero]

theorem isUnit_mk_of_le {X Y : Ideal R} (hXY : X ≤ Y) {s : R}
    (hs : IsUnit (Ideal.Quotient.mk X s)) : IsUnit (Ideal.Quotient.mk Y s) := by
  have := hs.map (Ideal.Quotient.factor hXY)
  simpa using this

theorem exists_mul_of_mem_mul {I I' : Ideal R} {u s : R}
    (hsu : ∀ y ∈ I', s * y ∈ Ideal.span {u}) {y : R} (hy : y ∈ I * I') :
    ∃ i ∈ I, s * y = u * i := by
  refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) ?_
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hsu b hb)
    exact ⟨a * c, I.mul_mem_right c ha, by linear_combination (-a) * hc⟩
  · rintro y₁ y₂ ⟨i₁, hi₁, e₁⟩ ⟨i₂, hi₂, e₂⟩
    exact ⟨i₁ + i₂, I.add_mem hi₁ hi₂, by rw [mul_add, e₁, e₂, mul_add]⟩

/-- B3 core: additivity of quotient dimensions along `0 → R/(I⊔J) --u--> R/X → R/(I'⊔J) → 0`. -/
theorem finrank_quot_mul (I I' J : Ideal R) (u s : R) (hu : u ∈ I')
    (hsu : ∀ y ∈ I', s * y ∈ Ideal.span {u})
    (hs : IsUnit (Ideal.Quotient.mk (I * I' ⊔ J) s))
    (hnzd : ∀ x, u * x ∈ J → ∃ n : ℕ, s ^ n * x ∈ J)
    [Module.Finite k (R ⧸ (I * I' ⊔ J))] :
    Module.finrank k (R ⧸ (I * I' ⊔ J)) =
      Module.finrank k (R ⧸ (I ⊔ J)) + Module.finrank k (R ⧸ (I' ⊔ J)) := by
  have hXY : I * I' ⊔ J ≤ I ⊔ J := sup_le_sup_right Ideal.mul_le_left J
  have hXZ : I * I' ⊔ J ≤ I' ⊔ J := sup_le_sup_right Ideal.mul_le_right J
  let ψ : R →ₗ[k] R ⧸ (I * I' ⊔ J) :=
    (Ideal.Quotient.mkₐ k (I * I' ⊔ J)).toLinearMap ∘ₗ LinearMap.mulLeft k u
  have hψ (r : R) : ψ r = Ideal.Quotient.mk (I * I' ⊔ J) (u * r) := rfl
  have hker : LinearMap.ker ψ = (I ⊔ J).restrictScalars k := by
    ext r
    rw [LinearMap.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem, Submodule.restrictScalars_mem]
    constructor
    · intro h
      obtain ⟨y, hy, j, hj, hyj⟩ := Submodule.mem_sup.mp h
      obtain ⟨i, hi, hi'⟩ := exists_mul_of_mem_mul hsu hy
      have h1 : u * (s * r - i) ∈ J := by
        have e : u * (s * r - i) = s * j := by linear_combination hi' - s * hyj
        rw [e]; exact J.mul_mem_left s hj
      obtain ⟨n, hn⟩ := hnzd _ h1
      have h2 : s ^ (n + 1) * r ∈ I ⊔ J := by
        have e : s ^ (n + 1) * r = s ^ n * (s * r - i) + s ^ n * i := by ring
        rw [e]
        exact add_mem (Submodule.mem_sup_right hn) (Submodule.mem_sup_left (I.mul_mem_left _ hi))
      refine mem_of_isUnit_mul_mem ?_ h2
      have := (isUnit_mk_of_le hXY hs).pow (n + 1)
      rwa [← map_pow] at this
    · intro h
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp h
      rw [mul_add]
      exact add_mem (Submodule.mem_sup_left (show u * i ∈ I * I' by
        rw [mul_comm u i]; exact Ideal.mul_mem_mul hi hu))
        (Submodule.mem_sup_right (J.mul_mem_left u hj))
  let π : (R ⧸ (I * I' ⊔ J)) →ₗ[k] R ⧸ (I' ⊔ J) := (Ideal.Quotient.factorₐ k hXZ).toLinearMap
  have hπmk (r : R) : π (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk (I' ⊔ J) r := rfl
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hXZ
  have hkr : LinearMap.ker π = LinearMap.range ψ := by
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearMap.mem_ker, hπmk, Ideal.Quotient.eq_zero_iff_mem, LinearMap.mem_range]
    simp only [hψ]
    constructor
    · intro h
      have h1 : r ∈ Ideal.span {u} ⊔ (I * I' ⊔ J) := by
        apply mem_of_isUnit_mul_mem (isUnit_mk_of_le le_sup_right hs)
        obtain ⟨y, hy, j, hj, rfl⟩ := Submodule.mem_sup.mp h
        rw [mul_add]
        exact add_mem (Submodule.mem_sup_left (hsu y hy))
          (Submodule.mem_sup_right (Submodule.mem_sup_right (J.mul_mem_left s hj)))
      obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.mp h1
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      refine ⟨c, ?_⟩
      rw [Ideal.Quotient.eq]
      have e : u * c - (c * u + x) = -x := by ring
      rw [e]
      exact Submodule.neg_mem _ hx
    · rintro ⟨y, hy⟩
      rw [Ideal.Quotient.eq] at hy
      have e : r = u * y - (u * y - r) := by ring
      rw [e]
      exact sub_mem (Submodule.mem_sup_left (I'.mul_mem_right y hu)) (hXZ hy)
  have e1 := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hkr] at e1
  have e2 : Module.finrank k (LinearMap.range ψ) = Module.finrank k (R ⧸ (I ⊔ J)) := by
    rw [← (LinearMap.quotKerEquivRange ψ).finrank_eq, hker]
    exact (Submodule.Quotient.restrictScalarsEquiv k (I ⊔ J)).finrank_eq
  omega

end Alg

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Gen =====
section

/-!
# S4-IntersectB, file Gen: the generator `u`, the multiplier `s`, the weak NZD criterion (L33, part 3b)

* `LocPrinAt I' m`: `I'` is principal near the maximal ideal `m`, phrased without localisation.
* `exists_gen_quot`: if `R/X` is finite over an infinite field `k` and `I'` is principal near every maximal ideal
  containing `X`, there are `u ∈ I'` and `s` with `s • I' ⊆ (u)` and `s` a unit modulo `X`.
* `weak_nzd`: if every associated prime of `R/J` containing `u` contains `s`, then `u x ∈ J → s^n x ∈ J`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IntersectB

open Ideal

section Gen

variable {R : Type*} [CommRing R]

/-- `I'` is principal near `m`: some `v ∈ I'` and `t ∉ m` with `t • I' ⊆ (v)`. -/
def LocPrinAt (I' m : Ideal R) : Prop :=
  ∃ v ∈ I', ∃ t ∉ m, ∀ y ∈ I', t * y ∈ span ({v} : Set R)

theorem mem_mul_of_mul_mem {m I' : Ideal R} (hm : m.IsMaximal) {t u : R} (ht : t ∉ m)
    (hu : u ∈ I') (h : t * u ∈ m * I') : u ∈ m * I' := by
  obtain ⟨y, i, hi, e⟩ := hm.exists_inv ht
  have : u = y * (t * u) + i * u := by
    calc u = (y * t + i) * u := by rw [e, one_mul]
      _ = y * (t * u) + i * u := by ring
  rw [this]
  exact add_mem (mul_mem_left _ _ h) (mul_mem_mul hi hu)

theorem colon_of_notMem [IsDomain R] {I' m : Ideal R} (hm : m.IsMaximal) (h : LocPrinAt I' m)
    {u : R} (hu : u ∈ I') (hum : u ∉ m * I') :
    ∃ a ∉ m, ∀ y ∈ I', a * y ∈ span ({u} : Set R) := by
  obtain ⟨v, hv, t, ht, htv⟩ := h
  obtain ⟨a, ha⟩ := mem_span_singleton'.1 (htv u hu)
  refine ⟨a, fun ham => hum (mem_mul_of_mul_mem hm ht hu ?_), fun y hy => ?_⟩
  · rw [← ha]; exact mul_mem_mul ham hv
  · obtain ⟨b, hb⟩ := mem_span_singleton'.1 (htv y hy)
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ m.zero_mem)
    have key : t * (a * y) = t * (b * u) := by
      calc t * (a * y) = a * (t * y) := by ring
        _ = a * (b * v) := by rw [hb]
        _ = b * (a * v) := by ring
        _ = b * (t * u) := by rw [ha]
        _ = t * (b * u) := by ring
    rw [mul_left_cancel₀ ht0 key]
    exact mul_mem_left _ _ (mem_span_singleton_self u)

theorem mul_ne_self [IsDomain R] {I' m : Ideal R} (hm : m.IsMaximal) (h : LocPrinAt I' m)
    (hI : I' ≠ ⊥) : m * I' ≠ I' := by
  intro hEq
  obtain ⟨v, hv, t, ht, htv⟩ := h
  have key : ∀ x ∈ m * I', t * x ∈ m * span ({v} : Set R) := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha y hy => ?_) (fun x y hx hy => ?_)
    · rw [show t * (a * y) = a * (t * y) by ring]; exact mul_mem_mul ha (htv y hy)
    · rw [mul_add]; exact add_mem hx hy
  have h1 := key v (hEq.symm ▸ hv)
  rw [mul_comm m, mem_span_singleton_mul] at h1
  obtain ⟨z, hz, hzv⟩ := h1
  have ht0 : t - z ∉ m := fun h' => ht (by simpa using add_mem h' hz)
  have hv0 : v = 0 := by
    have : v * (t - z) = 0 := by rw [mul_sub, hzv]; ring
    exact (mul_eq_zero.1 this).resolve_right (fun h0 => ht0 (h0 ▸ m.zero_mem))
  apply hI
  rw [eq_bot_iff]
  intro y hy
  have := htv y hy
  rw [hv0, span_singleton_eq_bot.2 rfl, mem_bot] at this
  exact mem_bot.2 ((mul_eq_zero.1 this).resolve_left (fun h0 => ht (h0 ▸ m.zero_mem)))

theorem exists_gen (k : Type*) [Field k] [Infinite k] [Algebra k R] [IsDomain R] (I' : Ideal R)
    (S : Set (Ideal R)) (hS : S.Finite) (hmax : ∀ m ∈ S, m.IsMaximal)
    (hloc : ∀ m ∈ S, LocPrinAt I' m) :
    ∃ u ∈ I', ∃ s, (∀ m ∈ S, s ∉ m) ∧ ∀ y ∈ I', s * y ∈ span ({u} : Set R) := by
  by_cases hI : I' = ⊥
  · refine ⟨0, zero_mem _, 1, fun m hm h1 => (hmax m hm).ne_top ((eq_top_iff_one m).2 h1),
      fun y hy => ?_⟩
    rw [hI, mem_bot] at hy; simp [hy]
  have : Finite S := hS.to_subtype
  let M := I'.restrictScalars k
  let p : S → Submodule k M := fun m => ((m.1 * I').restrictScalars k).comap M.subtype
  have hp : ∀ m, p m ≠ ⊤ := by
    intro m htop
    apply mul_ne_self (hmax m.1 m.2) (hloc m.1 m.2) hI
    refine le_antisymm mul_le_right (fun y hy => ?_)
    have : (⟨y, hy⟩ : M) ∈ p m := htop ▸ Submodule.mem_top
    exact this
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let Q : Ideal R := (span ({(x : R)} : Set R)).colon (I' : Set R)
  have hcol : ∀ m ∈ S, ∃ a ∉ m, a ∈ Q := by
    intro m hm
    obtain ⟨a, ham, ha⟩ := colon_of_notMem (hmax m hm) (hloc m hm) x.2 (hx ⟨m, hm⟩)
    exact ⟨a, ham, Submodule.mem_colon.2 (fun y hy => ha y hy)⟩
  have hnot : ¬ ((Q : Set R) ⊆ ⋃ i ∈ S, (((fun m : Ideal R => m) i : Ideal R) : Set R)) := by
    intro hsub
    obtain ⟨m, hm, hle⟩ := (subset_union_prime_finite hS (f := fun m : Ideal R => m) ⊤ ⊤
      (fun m hm _ _ => (hmax m hm).isPrime)).1 hsub
    obtain ⟨a, ham, ha⟩ := hcol m hm
    exact ham (hle ha)
  obtain ⟨s, hs, hsS⟩ := Set.not_subset.1 hnot
  exact ⟨x, x.2, s, fun m hm hsm => hsS (Set.mem_biUnion hm hsm),
    fun y hy => Submodule.mem_colon.1 hs y hy⟩

theorem isUnit_mk_of_forall {X : Ideal R} {s : R}
    (h : ∀ m : Ideal R, m.IsMaximal → X ≤ m → s ∉ m) : IsUnit (Ideal.Quotient.mk X s) := by
  by_contra hs
  obtain ⟨M, hM, hsM⟩ :=
    exists_max_ideal_of_mem_nonunits (show Ideal.Quotient.mk X s ∈ nonunits _ from hs)
  refine h (M.comap (Ideal.Quotient.mk X))
    (comap_isMaximal_of_surjective _ Quotient.mk_surjective) (fun x hx => ?_) hsM
  rw [mem_comap, Quotient.eq_zero_iff_mem.2 hx]; exact M.zero_mem

theorem finite_maximal_of_finite (k : Type*) [Field k] [Algebra k R] (X : Ideal R)
    [Module.Finite k (R ⧸ X)] : {m : Ideal R | m.IsMaximal ∧ X ≤ m}.Finite := by
  have : IsArtinianRing (R ⧸ X) := IsArtinianRing.of_finite k (R ⧸ X)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (R := R ⧸ X)).image
    (Ideal.comap (Ideal.Quotient.mk X))).subset ?_
  rintro m ⟨hm, hXm⟩
  have := hm
  exact ⟨m.map (Ideal.Quotient.mk X), IsMaximal.map_of_surjective_of_ker_le Quotient.mk_surjective
    (by rw [mk_ker]; exact hXm), comap_map_mk hXm⟩

/-- O3b: the generator and the multiplier for `finrank_quot_mul`. -/
theorem exists_gen_quot (k : Type*) [Field k] [Infinite k] [Algebra k R] [IsDomain R]
    (I' X : Ideal R) [Module.Finite k (R ⧸ X)]
    (hloc : ∀ m : Ideal R, m.IsMaximal → X ≤ m → LocPrinAt I' m) :
    ∃ u ∈ I', ∃ s, IsUnit (Ideal.Quotient.mk X s) ∧ ∀ y ∈ I', s * y ∈ span ({u} : Set R) := by
  obtain ⟨u, hu, s, hs, hsu⟩ := exists_gen k I' _ (finite_maximal_of_finite k X)
    (fun m hm => hm.1) (fun m hm => hloc m hm.1 hm.2)
  exact ⟨u, hu, s, isUnit_mk_of_forall (fun m hm hXm => hs m ⟨hm, hXm⟩), hsu⟩

/-- O4 (algebra): the weak non-zero-divisor condition from associated primes. -/
theorem weak_nzd [IsNoetherianRing R] (J : Ideal R) (u s : R)
    (H : ∀ p ∈ associatedPrimes R (R ⧸ J), u ∈ p → s ∈ p) :
    ∀ x, u * x ∈ J → ∃ n : ℕ, s ^ n * x ∈ J := by
  intro x hux
  have hsm : ∀ r y : R, r • Ideal.Quotient.mk J y = Ideal.Quotient.mk J (r * y) := fun _ _ => rfl
  let N : Submodule R (R ⧸ J) := Submodule.span R {Ideal.Quotient.mk J x}
  have : Module.Finite R N := Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _)
  have hu : u ∈ Module.annihilator R N := by
    rw [Module.mem_annihilator]
    rintro ⟨n, hn⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hn
    apply Subtype.ext
    change u • a • Ideal.Quotient.mk J x = 0
    rw [smul_comm, hsm u x, Quotient.eq_zero_iff_mem.2 hux, smul_zero]
  have hsrad : s ∈ (Module.annihilator R N).radical := by
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro p hp
    have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R N hp
    exact H p (associatedPrimes.subset_of_injective (f := N.subtype) N.injective_subtype hass)
      (hp.1.2 hu)
  obtain ⟨n, hn⟩ := hsrad
  have := congrArg Subtype.val
    (Module.mem_annihilator.1 hn ⟨_, Submodule.mem_span_singleton_self (Ideal.Quotient.mk J x)⟩)
  change s ^ n • Ideal.Quotient.mk J x = 0 at this
  exact ⟨n, Quotient.eq_zero_iff_mem.1 (by rw [← hsm]; exact this)⟩

end Gen

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Ass =====
section

/-!
# S4-IntersectB, file Ass: associated points of an ideal sheaf (L33, part 4)

* `IsAssPt C V x hx`: the prime of `x` in the affine chart `V` is associated to `Γ(V) ⧸ C(V)`.
* `assSet C`: the points that are associated in some affine chart.
* `isAssPt_basicOpen`: being associated does not change when passing to a basic open.
* `assSet_finite`: on a quasi-compact locally Noetherian scheme `assSet C` is finite.
* `not_le_of_ass`: if no associated point lies in `supp I`, then `I(V)` lies in no associated prime of `Γ(V)/C(V)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IntersectB

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

section AssAlg

/-- Associated primes of `R ⧸ J` and of `R' ⧸ J R'` for a localisation `R'` of `R`. -/
theorem ass_localization {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S R'] (J : Ideal R) (P : Ideal R') :
    P.comap (algebraMap R R') ∈ associatedPrimes R (R ⧸ J) ↔
      P ∈ associatedPrimes R' (R' ⧸ J.map (algebraMap R R')) := by
  have h := Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    (S := S) (R' := R') (f := J.toLocalizedQuotient' R' S (Algebra.linearMap R R'))
  have hJ : J.localized' R' S (Algebra.linearMap R R') = J.map (algebraMap R R') := by
    rw [Submodule.localized'_eq_span]; rfl
  rw [hJ] at h
  exact Set.ext_iff.1 h P

end AssAlg

section Ass

variable {X : Scheme} (C : X.IdealSheafData)

/-- `x ∈ V` is an associated point of `C` in the affine chart `V`. -/
def IsAssPt (V : X.affineOpens) (x : X) (hx : x ∈ (V : X.Opens)) : Prop :=
  (V.2.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, V) (Γ(X, V) ⧸ C.ideal V)

/-- The associated points of `C` (in some affine chart). -/
def assSet : Set X := {x | ∃ (V : X.affineOpens) (hx : x ∈ (V : X.Opens)), IsAssPt C V x hx}

theorem isAssPt_congr {U U' : X.affineOpens} (h : U = U') (x : X) (hx : x ∈ (U : X.Opens))
    (hx' : x ∈ (U' : X.Opens)) : IsAssPt C U x hx ↔ IsAssPt C U' x hx' := by
  subst h; rfl

theorem primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U))
    (h : hU.fromSpec P ∈ U) : hU.primeIdealOf ⟨hU.fromSpec P, h⟩ = P := by
  have e : (⟨hU.fromSpec P, h⟩ : U) = hU.isoSpec.inv P := by
    apply Subtype.ext
    rfl
  rw [e]
  dsimp only [IsAffineOpen.primeIdealOf]
  change (hU.isoSpec.inv ≫ hU.isoSpec.hom) P = P
  rw [Iso.inv_hom_id]
  rfl

theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec P ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨P, rfl⟩

variable [IsLocallyNoetherian X]

theorem isAssPt_basicOpen (V : X.affineOpens) (f : Γ(X, V)) (x : X) (hx : x ∈ X.basicOpen f) :
    IsAssPt C V x (X.basicOpen_le f hx) ↔ IsAssPt C (X.affineBasicOpen f) x hx := by
  have hle : (X.affineBasicOpen f : X.Opens) ≤ V := X.basicOpen_le f
  let ρ := X.presheaf.map (homOfLE hle).op
  let _ := ρ.hom.toAlgebra
  have hloc : IsLocalization.Away f Γ(X, (X.affineBasicOpen f : X.Opens)) :=
    V.2.isLocalization_of_eq_basicOpen f (homOfLE hle) rfl
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have h0 := IsAffineOpen.comap_primeIdealOf_appLE (f := 𝟙 X) (x := x) V.1 V.2
    (X.affineBasicOpen f : X.Opens) (X.affineBasicOpen f).2 (fun y hy => hle hy) hx
  have hP : ((X.affineBasicOpen f).2.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap _ _) =
      (V.2.primeIdealOf ⟨x, X.basicOpen_le f hx⟩).asIdeal := by
    have h1 := congrArg PrimeSpectrum.asIdeal h0
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at h1
    exact h1
  unfold IsAssPt
  rw [← hP, ass_localization (Submonoid.powers f) (C.ideal V)]
  have hm := C.map_ideal' (U := X.affineBasicOpen f) (V := V) (homOfLE hle).op
  exact Iff.of_eq (by rw [← hm]; rfl)

theorem finite_isAssPt_chart (W : X.affineOpens) :
    {x | ∃ hx : x ∈ (W : X.Opens), IsAssPt C W x hx}.Finite := by
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  have hA := associatedPrimes.finite Γ(X, W) (Γ(X, W) ⧸ C.ideal W)
  have hB : {P : PrimeSpectrum Γ(X, W) |
      P.asIdeal ∈ associatedPrimes Γ(X, W) (Γ(X, W) ⧸ C.ideal W)}.Finite :=
    hA.preimage (fun P _ Q _ h => PrimeSpectrum.ext h)
  refine (hB.image (fun P => W.2.fromSpec P)).subset ?_
  rintro x ⟨hx, hass⟩
  exact ⟨_, hass, W.2.fromSpec_primeIdealOf ⟨x, hx⟩⟩

theorem assSet_finite [CompactSpace X] : (assSet C).Finite := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => V.1.isOpen) (fun x _ => by
      have hx : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]; trivial
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine (t.finite_toSet.biUnion (fun W _ => finite_isAssPt_chart C W)).subset ?_
  rintro x ⟨V, hxV, hass⟩
  obtain ⟨W, hWt, hxW⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.2 W.2 x ⟨hxV, hxW⟩
  have hxg : x ∈ X.basicOpen g := hfg ▸ hxf
  exact Set.mem_biUnion hWt ⟨hxW, (isAssPt_basicOpen C W g x hxg).2
    ((isAssPt_congr C (Subtype.ext hfg) x hxf hxg).1 ((isAssPt_basicOpen C V f x hxf).1 hass))⟩

omit [IsLocallyNoetherian X] in
/-- If no associated point of `C` lies in `supp I`, then `I(V)` lies in no associated prime of
`Γ(V) ⧸ C(V)`. -/
theorem not_le_of_ass (I : X.IdealSheafData) (h : ∀ x ∈ assSet C, x ∉ I.support)
    (V : X.affineOpens) (p : Ideal Γ(X, V))
    (hp : p ∈ associatedPrimes Γ(X, V) (Γ(X, V) ⧸ C.ideal V)) : ¬ I.ideal V ≤ p := by
  intro hle
  have hpr : p.IsPrime := IsAssociatedPrime.isPrime hp
  let P : PrimeSpectrum Γ(X, V) := ⟨p, hpr⟩
  have hmem := fromSpec_mem V.2 P
  apply h (V.2.fromSpec P) ⟨V, hmem, by
    unfold IsAssPt; rw [primeIdealOf_fromSpec V.2 P hmem]; exact hp⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  exact (Set.ext_iff.1 (V.2.fromSpec_preimage_zeroLocus (I.ideal V : Set Γ(X, V))) P).2
    ((PrimeSpectrum.mem_zeroLocus _ _).2 hle)

end Ass

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_JacDivisors_F =====
section

/-!
# S4-JacDivisors F (O8: finite free resolutions)
* `HasFFR A n M`: `M` has a resolution of length `n` by finite free `A`-modules.
* `hasFFR_of_hasPDLT`: over a Noetherian local ring, a finite module of finite projective
  dimension has a finite free resolution.
* `hasFFR_of_isLocalizedModule`: finite free resolutions localize.
* `isStablyFree_of_hasFFR`: a projective module with a finite free resolution is stably free.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal
open scoped TensorProduct

universe u

/-- `HasFFR A n M`: a resolution `0 → F_n → ⋯ → F_0 → M → 0` by finite free modules. -/
def HasFFR (A : Type u) [CommRing A] : ℕ → (M : Type u) → [AddCommGroup M] → [Module A M] → Prop
  | 0 => fun M => Module.Finite A M ∧ Module.Free A M
  | n + 1 => fun M => ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module A F),
      Module.Finite A F ∧ Module.Free A F ∧ ∃ f : F →ₗ[A] M, Function.Surjective f ∧
        HasFFR A n (LinearMap.ker f)

section Basic

variable {A : Type u} [CommRing A]

theorem hasFFR_zero_iff {M : Type u} [AddCommGroup M] [Module A M] :
    HasFFR A 0 M ↔ Module.Finite A M ∧ Module.Free A M := Iff.rfl

theorem hasFFR_succ_iff {n : ℕ} {M : Type u} [AddCommGroup M] [Module A M] :
    HasFFR A (n + 1) M ↔ ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module A F),
      Module.Finite A F ∧ Module.Free A F ∧ ∃ f : F →ₗ[A] M, Function.Surjective f ∧
        HasFFR A n (LinearMap.ker f) := Iff.rfl

theorem HasFFR.finite : ∀ {n : ℕ} {M : Type u} [AddCommGroup M] [Module A M],
    HasFFR A n M → Module.Finite A M
  | 0, _, _, _, h => h.1
  | _ + 1, _, _, _, h => by
    obtain ⟨F, _, _, _, _, f, hf, -⟩ := hasFFR_succ_iff.mp h
    exact Module.Finite.of_surjective f hf

theorem HasFFR.of_equiv : ∀ {n : ℕ} {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N], HasFFR A n M → (M ≃ₗ[A] N) → HasFFR A n N
  | 0, _, _, _, _, _, _, h, e => by
    obtain ⟨_, _⟩ := hasFFR_zero_iff.mp h
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  | _ + 1, _, _, _, _, _, _, h, e => by
    obtain ⟨F, _, _, _, _, f, hf, hK⟩ := hasFFR_succ_iff.mp h
    refine hasFFR_succ_iff.mpr ⟨F, _, _, inferInstance, inferInstance, e.toLinearMap ∘ₗ f,
      e.surjective.comp hf, ?_⟩
    exact HasFFR.of_equiv hK (LinearEquiv.ofEq _ _ (LinearEquiv.ker_comp e f).symm)

end Basic

/-- Over a Noetherian local ring, a finite module with `pd < n + 1` has a free resolution of
length `n` by finite free modules. -/
theorem hasFFR_of_hasPDLT {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∀ (n : ℕ) (M : ModuleCat.{u} R), Module.Finite R M → HasProjectiveDimensionLT M (n + 1) →
      HasFFR R n M := by
  intro n
  induction n with
  | zero =>
    intro M _ hM
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    exact ⟨inferInstance, this⟩
  | succ n ih =>
    intro M _ hM
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have : Projective (ModuleCat.of R (Fin k → R)) :=
      ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
    have hK := (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
    exact hasFFR_succ_iff.mpr ⟨Fin k → R, _, _, inferInstance, inferInstance, f, hf,
      ih (ModuleCat.of R (LinearMap.ker f)) inferInstance hK⟩

/-- Finite free resolutions localize. -/
theorem hasFFR_of_isLocalizedModule {R : Type u} [CommRing R] (S : Submonoid R) (A : Type u)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M], HasFFR R n M →
      ∀ (M' : Type u) [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
        (g : M →ₗ[R] M') [IsLocalizedModule S g], HasFFR A n M' := by
  intro n
  induction n with
  | zero =>
    intro M _ _ hM M' _ _ _ _ g _
    obtain ⟨_, _⟩ := hasFFR_zero_iff.mp hM
    exact ⟨Module.Finite.of_isLocalizedModule S g, Module.free_of_isLocalizedModule S g⟩
  | succ n ih =>
    intro M _ _ hM M' _ _ _ _ g _
    obtain ⟨F, _, _, _, _, f, hf, hK⟩ := hasFFR_succ_iff.mp hM
    let gF : F →ₗ[R] A ⊗[R] F := TensorProduct.mk R A F 1
    have : IsLocalizedModule S gF :=
      (isLocalizedModule_iff_isBaseChange S A gF).mpr (TensorProduct.isBaseChange R F A)
    let f' : A ⊗[R] F →ₗ[A] M' :=
      (IsLocalizedModule.map S gF g f).extendScalarsOfIsLocalization S A
    have hf' : Function.Surjective f' := IsLocalizedModule.map_surjective S gF g f hf
    let e : (LinearMap.ker f).localized' A S gF ≃ₗ[A] LinearMap.ker f' :=
      LinearEquiv.ofEq _ _ (LinearMap.localized'_ker_eq_ker_localizedMap A S gF g f)
    let h : LinearMap.ker f →ₗ[R] LinearMap.ker f' :=
      (e.restrictScalars R).toLinearMap ∘ₗ (LinearMap.ker f).toLocalized' A S gF
    have : IsLocalizedModule S h := IsLocalizedModule.of_linearEquiv S _ _
    exact hasFFR_succ_iff.mpr ⟨A ⊗[R] F, _, _, Module.Finite.of_isLocalizedModule S gF,
      Module.free_of_isLocalizedModule S gF, f', hf',
      ih (LinearMap.ker f) hK (LinearMap.ker f') h⟩

/-- A projective module with a finite free resolution is stably free. -/
theorem isStablyFree_of_hasFFR {A : Type u} [CommRing A] :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module A M] [Module.Projective A M],
      HasFFR A n M → Module.IsStablyFree A M := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ hM
    obtain ⟨_, _⟩ := hasFFR_zero_iff.mp hM
    infer_instance
  | succ n ih =>
    intro M _ _ _ hM
    obtain ⟨F, _, _, _, _, f, hf, hK⟩ := hasFFR_succ_iff.mp hM
    obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
    have hfs (m : M) : f (s m) = m := LinearMap.congr_fun hs m
    let K := LinearMap.ker f
    let r : F →ₗ[A] K := (LinearMap.id - s ∘ₗ f).codRestrict K (fun y =>
      LinearMap.mem_ker.mpr (by simp [hfs]))
    have hr : r ∘ₗ K.subtype = LinearMap.id := by
      ext k
      simp [r, LinearMap.mem_ker.mp k.2]
    have : Module.Projective A K := Module.Projective.of_split K.subtype r hr
    have : Module.IsStablyFree A K := ih K hK
    have : Module.Finite A K := hK.finite
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A K
    let φ : M × K →ₗ[A] F := LinearMap.coprod s K.subtype
    have hφ : Function.Bijective φ := by
      refine ⟨(injective_iff_map_eq_zero φ).mpr fun ⟨m, k⟩ h => ?_, fun y => ⟨(f y, r y), ?_⟩⟩
      · have h' : s m + (k : F) = 0 := h
        have hm : m = 0 := by
          have := congrArg f h'
          rwa [map_add, hfs, LinearMap.mem_ker.mp k.2, add_zero, map_zero] at this
        subst hm
        have hk : (k : F) = 0 := by simpa using h'
        exact Prod.ext rfl (Subtype.ext hk)
      · simp [φ, r]
    let e : (M × K) ≃ₗ[A] F := LinearEquiv.ofBijective φ hφ
    have : Module.Free A (M × (K × N)) := Module.Free.of_equiv
      ((e.symm.prodCongr (LinearEquiv.refl A N)).trans (LinearEquiv.prodAssoc A M K N))
    exact Module.IsStablyFree.of_free_prod A M (K × N)

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_IntersectC_Rank =====
section

/-!
# S4-IntersectC, file Rank: ranks multiply in a finite flat tower over a field (L35 core)

* `finrank_eq_mul_of_flat`: `R` finite over a field `K`, `M` finite flat over `R` of rank `d` at every prime
  ⇒ `finrank K M = d * finrank K R` (semilocal freeness, `Module.free_of_flat_of_finrank_eq`).
* `finrank_comp_SpecMap`: the scheme form, for `g : W ⟶ Spec R` finite flat of rank `d` everywhere.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits TensorProduct

namespace RamanujanPetersson.IntersectC

/-- Ranks multiply: `finrank K M = d * finrank K R` for `M` finite flat of constant rank `d` over `R`. -/
theorem finrank_eq_mul_of_flat (K R M : Type u) [Field K] [CommRing R] [Algebra K R]
    [Module.Finite K R] [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
    [Module.Finite R M] [Module.Flat R M] (d : ℕ)
    (hd : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = d) :
    Module.finrank K M = d * Module.finrank K R := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton M := Module.subsingleton R M
    simp [Module.finrank_zero_of_subsingleton]
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  have : Finite (MaximalSpectrum R) := inferInstance
  have hrk : ∀ P : MaximalSpectrum R, Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) = d := by
    intro P
    haveI : P.1.IsMaximal := P.2
    letI : Field (R ⧸ P.1) := Ideal.Quotient.field P.1
    calc Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M)
        = Module.finrank P.1.ResidueField
            (P.1.ResidueField ⊗[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] M)) :=
          (Module.finrank_baseChange).symm
      _ = Module.finrank P.1.ResidueField (P.1.ResidueField ⊗[R] M) :=
          (AlgebraTensorModule.cancelBaseChange R (R ⧸ P.1) P.1.ResidueField
            P.1.ResidueField M).finrank_eq
      _ = Module.rankAtStalk M ⟨P.1, P.2.isPrime⟩ := Ideal.finrank_fiber_eq_rankAtStalk P.1
      _ = d := hd _
  haveI : Module.Free R M := Module.free_of_flat_of_finrank_eq R M d hrk
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have h1 : Module.finrank R M = d := by
    rw [← hd ⟨m, hm.isPrime⟩, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← Module.finrank_mul_finrank K R M, h1, mul_comm]

/-- The scheme form: a finite flat `g : W ⟶ Spec R` of rank `d` everywhere, `R` finite over `K`. -/
theorem finrank_comp_SpecMap {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    [Module.Finite K R] {W : Scheme.{u}} (g : W ⟶ Spec (.of R)) [Flat g] [IsFinite g] (d : ℕ)
    (hd : ∀ x, g.finrank x = d) (s : Spec (.of K)) :
    (g ≫ Spec.map (CommRingCat.ofHom (algebraMap K R))).finrank s = d * Module.finrank K R := by
  haveI : IsAffine W := isAffine_of_isAffineHom g
  let r : CommRingCat.of R ⟶ Γ(W, ⊤) := Spec.preimage (W.isoSpec.inv ≫ g)
  have hr : Spec.map r = W.isoSpec.inv ≫ g := Spec.map_preimage _
  letI : Algebra R Γ(W, ⊤) := r.hom.toAlgebra
  letI : Algebra K Γ(W, ⊤) := (r.hom.comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R Γ(W, ⊤) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hg' : g = W.isoSpec.hom ≫ Spec.map r := by rw [hr, Iso.hom_inv_id_assoc]
  haveI : IsFinite (Spec.map r) := by rw [hr]; infer_instance
  haveI : Flat (Spec.map r) := by rw [hr]; infer_instance
  have hfin : r.hom.Finite := (IsFinite.SpecMap_iff r).mp inferInstance
  have hflat : r.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  haveI : Module.Finite R Γ(W, ⊤) := hfin
  haveI : Module.Flat R Γ(W, ⊤) := hflat
  haveI : Module.Finite K Γ(W, ⊤) := Module.Finite.trans R _
  have hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk Γ(W, ⊤) p = d := by
    intro p
    have h1 := Scheme.Hom.finrank_SpecMap_algebraMap R Γ(W, ⊤) p
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap R Γ(W, ⊤))) = W.isoSpec.inv ≫ g := hr
    rw [h2, Scheme.Hom.finrank_comp_left_of_isIso] at h1
    rw [← h1]
    exact hd _
  have key := finrank_eq_mul_of_flat K R Γ(W, ⊤) d hrank
  have hcomp : g ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) =
      W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(W, ⊤))) := by
    rw [hg', Category.assoc, ← Spec.map_comp]
    rfl
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap K Γ(W, ⊤)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Γ(W, ⊤)))) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]; infer_instance
  rw [hcomp, Scheme.Hom.finrank_comp_left_of_isIso]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap K Γ(W, ⊤) s).trans ?_
  rw [Module.rankAtStalk_eq_finrank_of_free, key]
  rfl

end RamanujanPetersson.IntersectC

end

-- ===== S4.Def_RP_IsogDegB_Unram =====
section

/-!
# S4-IsogDegB, algebra part (lemma L27 of S4_COREB_ROUTE.md §3)

`S → R` a local homomorphism of local rings. If `𝔪_R = 𝔪_S R + 𝔪_R²` (the cotangent map is surjective)
and `R = im S + 𝔪_R`, then `Ω[R⁄S] = 0` (Nakayama), so `R` is formally unramified over `S`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IsogDegB

open IsLocalRing

section Unram

variable {S R : Type*} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R] [Algebra S R]
  [IsLocalHom (algebraMap S R)]

theorem algebraMap_mem_maximalIdeal {s : S} (hs : s ∈ maximalIdeal S) :
    algebraMap S R s ∈ maximalIdeal R :=
  (mem_maximalIdeal _).2 fun hu ↦ (mem_maximalIdeal _).1 hs (isUnit_of_map_unit _ _ hu)

/-- `d x ∈ 𝔪 • Ω` for `x ∈ 𝔪_S R ⊔ 𝔪_R ^ 2`. -/
theorem D_mem_smul_of_mem {x : R}
    (hx : x ∈ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    KaehlerDifferential.D S R x ∈ (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine Submodule.add_mem _ ?_ ?_
  · have key : y ∈ maximalIdeal R ∧
        KaehlerDifferential.D S R y ∈ (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]) := by
      refine Submodule.span_induction (p := fun y _ ↦ y ∈ maximalIdeal R ∧
        KaehlerDifferential.D S R y ∈ (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]))
        ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨s, hs, rfl⟩
        refine ⟨algebraMap_mem_maximalIdeal hs, ?_⟩
        rw [(KaehlerDifferential.D S R).map_algebraMap]
        exact Submodule.zero_mem _
      · simp
      · intro a b _ _ ha hb
        rw [map_add]
        exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      · intro a b _ hb
        refine ⟨Ideal.mul_mem_left _ a hb.1, ?_⟩
        rw [smul_eq_mul, Derivation.leibniz]
        exact Submodule.add_mem _ (Submodule.smul_mem _ a hb.2)
          (Submodule.smul_mem_smul hb.1 Submodule.mem_top)
    exact key.2
  · rw [pow_two] at hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro u hu v hv
      rw [Derivation.leibniz]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul hu Submodule.mem_top)
        (Submodule.smul_mem_smul hv Submodule.mem_top)
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- Nakayama: surjective cotangent map + residue fields generated by `S` give `Ω[R⁄S] = 0`. -/
theorem subsingleton_kaehler [Module.Finite R Ω[R⁄S]]
    (hres : ∀ r : R, ∃ s : S, r - algebraMap S R s ∈ maximalIdeal R)
    (hle : maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    Subsingleton Ω[R⁄S] := by
  have hspan : Submodule.span R (Set.range (KaehlerDifferential.D S R)) ≤
      (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    obtain ⟨s, hs⟩ := hres r
    have h := D_mem_smul_of_mem (S := S) (hle hs)
    rwa [map_sub, (KaehlerDifferential.D S R).map_algebraMap, sub_zero] at h
  rw [KaehlerDifferential.span_range_derivation] at hspan
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
    (Module.Finite.fg_top) hspan (maximalIdeal_le_jacobson _)
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : x ∈ (⊤ : Submodule R Ω[R⁄S]) := Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hx

theorem formallyUnramified_of_le [Module.Finite R Ω[R⁄S]]
    (hres : ∀ r : R, ∃ s : S, r - algebraMap S R s ∈ maximalIdeal R)
    (hle : maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    Algebra.FormallyUnramified S R :=
  ⟨subsingleton_kaehler hres hle⟩

end Unram

end RamanujanPetersson.IsogDegB

end



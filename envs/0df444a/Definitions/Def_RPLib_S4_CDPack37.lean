-- Prove2me | Definitions.Def_RPLib_S4_CDPack37
-- name    : RPLib_S4_CDPack37
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:15:43.291882+00:00
-- url     : https://prove2.me/theorems/d9fb5d12-aaca-453a-828d-dbc1023778b9
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 37 of 71
-- statement:
--   Part 37 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacSymB_Chart`: S4-JacSymB, file F1: the affine charts of a curve (L12)
--   * `Def_RP_JacSymB_ChartDed`: S4-JacSymB, file F3: the chart rings are finitely generated; the singleton charts are Dedekind (L12)
--   * `Def_RP_JacSymB_ValAlg`: S4-JacSymB, file H2a: a valuation-ring lemma for the valuative criterion (L12)
--   * `Def_RP_JacAlg_Defs`: Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)
--   * `Def_RP_DegPoly`: Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)
--   * `Def_RP_DegPoly_Data`: Degree polynomiality, part 2: (D2) in `DegreeData` form (unit S4-DegPoly, L37)
--   * `Def_RP_JacDivisors_H`: S4-JacDivisors H (O11: Weil divisors on integral locally Noetherian schemes)
--   * `Def_RP_JacDivisors_I`: S4-JacDivisors I (O12 bridges: orders of sections at codimension-one points, affine charts)
--   * `Def_RP_JacDivisors_J`: S4-JacDivisors J (O12b: algebraic Hartogs at points with factorial stalks)
--   * `Def_RP_JacDivisors_K`: S4-JacDivisors K (O12a: Weil divisors are locally principal at factorial points)
--   * `Def_RP_IsogDegA_FF`: S4-IsogDegA, file FF: the function-field map of a dominant morphism and the degree (O2, O5)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib

/-!
# Curve-duality library package, part 37 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacSymB_Chart`: S4-JacSymB, file F1: the affine charts of a curve (L12)
* `Def_RP_JacSymB_ChartDed`: S4-JacSymB, file F3: the chart rings are finitely generated; the singleton charts are Dedekind (L12)
* `Def_RP_JacSymB_ValAlg`: S4-JacSymB, file H2a: a valuation-ring lemma for the valuative criterion (L12)
* `Def_RP_JacAlg_Defs`: Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)
* `Def_RP_DegPoly`: Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)
* `Def_RP_DegPoly_Data`: Degree polynomiality, part 2: (D2) in `DegreeData` form (unit S4-DegPoly, L37)
* `Def_RP_JacDivisors_H`: S4-JacDivisors H (O11: Weil divisors on integral locally Noetherian schemes)
* `Def_RP_JacDivisors_I`: S4-JacDivisors I (O12 bridges: orders of sections at codimension-one points, affine charts)
* `Def_RP_JacDivisors_J`: S4-JacDivisors J (O12b: algebraic Hartogs at points with factorial stalks)
* `Def_RP_JacDivisors_K`: S4-JacDivisors K (O12a: Weil divisors are locally principal at factorial points)
* `Def_RP_IsogDegA_FF`: S4-IsogDegA, file FF: the function-field map of a dominant morphism and the degree (O2, O5)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacSymB_Chart =====
section

/-!
# S4-JacSymB, file F1: the affine charts of a curve (L12)

Curve data: a field `F` over `k` with a transcendental `x`. For a finite set `A ⊆ k` the chart ring `B_A` is the integral
closure in `F` of `P_A = k[1/(x - c) : c ∈ A]` (functions regular away from the poles of `x - c`, `c ∈ A`, i.e. on the
preimage of `ℙ¹ ∖ A`). For `c0 ∈ A ⊆ A'` the element `w = ∏_{d ∈ A' \ A} (x - d)/(x - c0)` lies in `P_A`, is a unit of
`P_A'`, and every element of `B_A'` becomes an element of `B_A` after multiplying by a power of `w`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Chart

open Polynomial

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F}

/-- The coordinate `1 / (x - c)`. -/
noncomputable def uc (x : F) (c : k) : F := (x - algebraMap k F c)⁻¹

theorem sub_ne_zero_of_tr {x : F} (hx : Transcendental k x) (c : k) : x - algebraMap k F c ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact hx (by rw [h]; exact isAlgebraic_algebraMap c)

theorem sub_mul_uc {x : F} (hx : Transcendental k x) (c d : k) :
    (x - algebraMap k F d) * uc x c = 1 + algebraMap k F (c - d) * uc x c := by
  have h := sub_ne_zero_of_tr hx c
  rw [uc, map_sub]
  field_simp
  ring

/-- `P_A = k[1/(x - c) : c ∈ A]`. -/
noncomputable def polyA (x : F) (A : Finset k) : Subalgebra k F := Algebra.adjoin k (uc x '' (A : Set k))

theorem uc_mem_polyA (x : F) {A : Finset k} {c : k} (hc : c ∈ A) : uc x c ∈ polyA x A :=
  Algebra.subset_adjoin ⟨c, hc, rfl⟩

theorem polyA_mono (x : F) {A A' : Finset k} (h : A ⊆ A') : polyA x A ≤ polyA x A' :=
  Algebra.adjoin_mono (Set.image_mono (Finset.coe_subset.mpr h))

/-- The chart ring `B_A`: the integral closure of `P_A` in `F`. -/
noncomputable def chartRing (x : F) (A : Finset k) : Subalgebra k F :=
  (integralClosure (polyA x A) F).restrictScalars k

theorem mem_chartRing {x : F} {A : Finset k} {y : F} : y ∈ chartRing x A ↔ IsIntegral (polyA x A) y := Iff.rfl

theorem isIntegral_of_subalgebra_le {R R' : Subalgebra k F} (h : R ≤ R') {y : F} (hy : IsIntegral R y) :
    IsIntegral R' y := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [eval₂_map]
  exact hpy

theorem polyA_le_chartRing (x : F) (A : Finset k) : polyA x A ≤ chartRing x A := fun y hy =>
  mem_chartRing.mpr (isIntegral_algebraMap (R := polyA x A) (x := ⟨y, hy⟩))

theorem chartRing_mono (x : F) {A A' : Finset k} (h : A ⊆ A') : chartRing x A ≤ chartRing x A' := fun _ hy =>
  mem_chartRing.mpr (isIntegral_of_subalgebra_le (polyA_mono x h) (mem_chartRing.mp hy))

/-- `w = ∏_{d ∈ D} (x - d)/(x - c0)`. -/
noncomputable def wt (x : F) (c0 : k) (D : Finset k) : F := ∏ d ∈ D, (x - algebraMap k F d) * uc x c0

theorem wt_mem (hx : Transcendental k x) {A : Finset k} {c0 : k} (hc0 : c0 ∈ A) (D : Finset k) :
    wt x c0 D ∈ polyA x A := by
  refine Subalgebra.prod_mem _ fun d _ => ?_
  rw [sub_mul_uc hx]
  exact Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (uc_mem_polyA x hc0))

theorem wt_ne_zero {x : F} (hx : Transcendental k x) (c0 : k) (D : Finset k) : wt x c0 D ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun d _ =>
    mul_ne_zero (sub_ne_zero_of_tr hx d) (inv_ne_zero (sub_ne_zero_of_tr hx c0))

theorem wt_inv_mem (hx : Transcendental k x) {A' D : Finset k} (hD : D ⊆ A') (c0 : k) :
    (wt x c0 D)⁻¹ ∈ polyA x A' := by
  rw [wt, ← Finset.prod_inv_distrib]
  refine Subalgebra.prod_mem _ fun d hd => ?_
  have h1 : ((x - algebraMap k F d) * uc x c0)⁻¹ = (x - algebraMap k F c0) * uc x d := by
    rw [uc, uc, mul_inv, inv_inv, mul_comm]
  rw [h1, sub_mul_uc hx]
  exact Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (uc_mem_polyA x (hD hd)))

theorem uc_mul_wt_mem (hx : Transcendental k x) {A D : Finset k} {c0 d : k} (hc0 : c0 ∈ A) (hd : d ∈ D) :
    uc x d * wt x c0 D ∈ polyA x A := by
  classical
  rw [wt, ← Finset.mul_prod_erase D _ hd, ← mul_assoc, ← mul_assoc]
  have h1 : uc x d * (x - algebraMap k F d) = 1 := inv_mul_cancel₀ (sub_ne_zero_of_tr hx d)
  rw [h1, one_mul]
  exact Subalgebra.mul_mem _ (uc_mem_polyA x hc0) (wt_mem hx hc0 _)

theorem pow_mul_mem_of_le {R : Subalgebra k F} {w y : F} (hw : w ∈ R) {m n : ℕ} (hmn : m ≤ n)
    (h : w ^ m * y ∈ R) : w ^ n * y ∈ R := by
  rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem hw _) h

theorem exists_pow_mul_mem_polyA [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} {c0 : k} (hc0 : c0 ∈ A)
    {y : F} (hy : y ∈ polyA x A') : ∃ n : ℕ, wt x c0 (A' \ A) ^ n * y ∈ polyA x A := by
  have hw := wt_mem hx hc0 (A' \ A)
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    by_cases hcA : c ∈ A
    · exact ⟨0, by rw [pow_zero, one_mul]; exact uc_mem_polyA x hcA⟩
    · refine ⟨1, ?_⟩
      rw [pow_one, mul_comm]
      exact uc_mul_wt_mem hx hc0 (Finset.mem_sdiff.mpr ⟨hc, hcA⟩)
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (pow_mul_mem_of_le hw (Nat.le_add_right m n) hm)
      (pow_mul_mem_of_le hw (Nat.le_add_left n m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact Subalgebra.mul_mem _ hm hn

/-- Clearing denominators in an integral equation: if `R'` lies in `R[1/w]`, then a multiple `w^n b` of an element `b`
integral over `R'` is integral over `R`. -/
theorem exists_pow_mul_isIntegral {R R' : Subalgebra k F} {w : F} (hw : w ∈ R)
    (h : ∀ y ∈ R', ∃ n : ℕ, w ^ n * y ∈ R) {b : F} (hb : IsIntegral R' b) :
    ∃ n : ℕ, IsIntegral R (w ^ n * b) := by
  obtain ⟨p, hp, hpb⟩ := hb
  set q : F[X] := p.map (algebraMap R' F) with hqdef
  have hq : q.Monic := hp.map _
  have hqb : q.eval b = 0 := by rw [hqdef, eval_map]; exact hpb
  have hcoeff : ∀ i, q.coeff i ∈ R' := fun i => by
    rw [hqdef, coeff_map]
    exact (p.coeff i).2
  choose m hm using fun i => h _ (hcoeff i)
  set N := ∑ i ∈ Finset.range (q.natDegree + 1), m i
  have hN : ∀ i ≤ q.natDegree, w ^ N * q.coeff i ∈ R := fun i hi =>
    pow_mul_mem_of_le hw (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) (hm i)
  have hc : ∀ i, q.coeff i * (w ^ N) ^ (q.natDegree - i) ∈ R := by
    intro i
    rcases lt_trichotomy i q.natDegree with hi | hi | hi
    · obtain ⟨j, hj⟩ : ∃ j, q.natDegree - i = j + 1 := ⟨q.natDegree - i - 1, by omega⟩
      have e : q.coeff i * (w ^ N) ^ (j + 1) = (w ^ N) ^ j * (w ^ N * q.coeff i) := by ring
      rw [hj, e]
      exact R.mul_mem (R.pow_mem (R.pow_mem hw _) _) (hN i hi.le)
    · rw [hi, hq.coeff_natDegree, Nat.sub_self, pow_zero, one_mul]
      exact R.one_mem
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact R.zero_mem
  have hlift : q.scaleRoots (w ^ N) ∈ Polynomial.lifts (algebraMap R F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    exact ⟨⟨_, hc i⟩, rfl⟩
  obtain ⟨p', hp'1, -, hp'2⟩ :=
    lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff _).mpr hq)
  refine ⟨N, p', hp'2, ?_⟩
  rw [← eval_map, hp'1, scaleRoots_eval_mul, hqb, mul_zero]

theorem exists_pow_mul_mem_chartRing [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} {c0 : k} (hc0 : c0 ∈ A)
    {y : F} (hy : y ∈ chartRing x A') : ∃ n : ℕ, wt x c0 (A' \ A) ^ n * y ∈ chartRing x A :=
  exists_pow_mul_isIntegral (wt_mem hx hc0 _) (fun _ hz => exists_pow_mul_mem_polyA hx hc0 hz) (mem_chartRing.mp hy)

theorem wt_mem_chartRing (hx : Transcendental k x) {A : Finset k} {c0 : k} (hc0 : c0 ∈ A) (D : Finset k) :
    wt x c0 D ∈ chartRing x A :=
  polyA_le_chartRing x A (wt_mem hx hc0 D)

theorem wt_inv_mem_chartRing (hx : Transcendental k x) {A' D : Finset k} (hD : D ⊆ A') (c0 : k) :
    (wt x c0 D)⁻¹ ∈ chartRing x A' :=
  polyA_le_chartRing x A' (wt_inv_mem hx hD c0)

end Chart

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymB_ChartDed =====
section

/-!
# S4-JacSymB, file F3: the chart rings are finitely generated; the singleton charts are Dedekind (L12)

Curve data as in file F1, plus: `F / k⟮x⟯` finite separable. Then `B_{c} = ` integral closure of `k[1/(x - c)] ≅ k[X]`
in `F` is a Dedekind domain, finite over `k[1/(x-c)]`, and not a field; every chart ring `B_A` is a finitely generated
`k`-algebra (`B_A = B_{c0}[1/w]`).
-/

set_option autoImplicit false

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace RamanujanPetersson.JacSym

section ChartDed

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F}

theorem transcendental_uc (hx : Transcendental k x) (c : k) : Transcendental k (uc x c) := by
  intro h
  apply hx
  have h1 : IsAlgebraic k (x - algebraMap k F c) := IsAlgebraic.inv_iff.mp h
  simpa using h1.add (isAlgebraic_algebraMap (R := k) (A := F) c)

theorem polyA_singleton (x : F) (c : k) : polyA x {c} = Algebra.adjoin k {uc x c} := by
  rw [polyA, Finset.coe_singleton, Set.image_singleton]

theorem adjoin_uc_eq (hx : Transcendental k x) (c : k) : k⟮uc x c⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (sub_mem (IntermediateField.mem_adjoin_simple_self k x) (IntermediateField.algebraMap_mem _ c))
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h : (uc x c)⁻¹ + algebraMap k F c = x := by rw [uc, inv_inv, sub_add_cancel]
    exact (congrArg (· ∈ k⟮uc x c⟯) h).mp
      (add_mem (inv_mem (IntermediateField.mem_adjoin_simple_self k (uc x c))) (IntermediateField.algebraMap_mem _ c))

theorem isPrincipalIdealRing_adjoin_uc (hx : Transcendental k x) (c : k) :
    IsPrincipalIdealRing (Algebra.adjoin k {uc x c}) :=
  IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental k (uc x c) (transcendental_uc hx c)).toRingEquiv.toRingHom
    (Polynomial.algEquivOfTranscendental k (uc x c) (transcendental_uc hx c)).surjective

theorem not_isField_adjoin_uc (hx : Transcendental k x) (c : k) : ¬IsField (Algebra.adjoin k {uc x c}) := fun h =>
  Polynomial.not_isField k
    (MulEquiv.isField h (Polynomial.algEquivOfTranscendental k (uc x c) (transcendental_uc hx c)).toMulEquiv)

theorem not_isField_chartRing_single (hx : Transcendental k x) (c : k) : ¬IsField (chartRing x {c}) := by
  have key : ∀ P : Subalgebra k F, P = Algebra.adjoin k {uc x c} →
      ¬IsField ((integralClosure P F).restrictScalars k) := by
    intro P hP h
    subst hP
    have hinj : Function.Injective
        (algebraMap (Algebra.adjoin k {uc x c}) (integralClosure (Algebra.adjoin k {uc x c}) F)) := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa using this
    exact not_isField_adjoin_uc hx c ((Algebra.IsIntegral.isField_iff_isField hinj).mpr h)
  exact key _ (polyA_singleton x c)

variable [FiniteDimensional k⟮x⟯ F] [Algebra.IsSeparable k⟮x⟯ F]

theorem finite_integralClosure_uc (hx : Transcendental k x) (c : k) :
    Module.Finite (Algebra.adjoin k {uc x c}) (integralClosure (Algebra.adjoin k {uc x c}) F) := by
  have hK : k⟮uc x c⟯ = k⟮x⟯ := adjoin_uc_eq hx c
  have : FiniteDimensional k⟮uc x c⟯ F := hK ▸ inferInstance
  have : Algebra.IsSeparable k⟮uc x c⟯ F := hK ▸ inferInstance
  have := isPrincipalIdealRing_adjoin_uc hx c
  exact IsIntegralClosure.finite (Algebra.adjoin k {uc x c}) k⟮uc x c⟯ F _

theorem isDedekindDomain_chartRing_single (hx : Transcendental k x) (c : k) : IsDedekindDomain (chartRing x {c}) := by
  have hK : k⟮uc x c⟯ = k⟮x⟯ := adjoin_uc_eq hx c
  have : FiniteDimensional k⟮uc x c⟯ F := hK ▸ inferInstance
  have : Algebra.IsSeparable k⟮uc x c⟯ F := hK ▸ inferInstance
  have := isPrincipalIdealRing_adjoin_uc hx c
  have key : ∀ P : Subalgebra k F, P = Algebra.adjoin k {uc x c} →
      IsDedekindDomain ((integralClosure P F).restrictScalars k) := by
    intro P hP
    subst hP
    exact integralClosure.isDedekindDomain (Algebra.adjoin k {uc x c}) k⟮uc x c⟯ F
  exact key _ (polyA_singleton x c)

theorem fg_chartRing_single (hx : Transcendental k x) (c : k) : (chartRing x {c}).FG := by
  classical
  have key : ∀ P : Subalgebra k F, P = Algebra.adjoin k {uc x c} → ((integralClosure P F).restrictScalars k).FG := by
    intro P hP
    subst hP
    have hfin := finite_integralClosure_uc hx c
    have hfg : (integralClosure (Algebra.adjoin k {uc x c}) F).FG :=
      Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.mp hfin)
    obtain ⟨t, ht⟩ := hfg
    refine ⟨insert (uc x c) t, ?_⟩
    rw [Finset.coe_insert, Set.insert_eq, Algebra.adjoin_union_eq_adjoin_adjoin, ht]
  exact key _ (polyA_singleton x c)

theorem fg_chartRing [DecidableEq k] (hx : Transcendental k x) {A : Finset k} {c0 : k} (hc0 : c0 ∈ A) :
    (chartRing x A).FG := by
  classical
  obtain ⟨t, ht⟩ := fg_chartRing_single hx c0
  refine ⟨insert (wt x c0 (A \ {c0}))⁻¹ t, le_antisymm ?_ ?_⟩
  · rw [Algebra.adjoin_le_iff]
    intro y hy
    rw [Finset.coe_insert] at hy
    rcases hy with rfl | hy
    · exact wt_inv_mem_chartRing hx Finset.sdiff_subset c0
    · refine chartRing_mono x (Finset.singleton_subset_iff.mpr hc0) ?_
      rw [← ht]
      exact Algebra.subset_adjoin hy
  · intro y hy
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (A := {c0}) hx (Finset.mem_singleton_self c0) hy
    have hy' : y = ((wt x c0 (A \ {c0}))⁻¹) ^ n * (wt x c0 (A \ {c0}) ^ n * y) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (wt_ne_zero hx c0 _), one_pow, one_mul]
    rw [hy']
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) _) ?_
    · rw [Finset.coe_insert]
      exact Set.mem_insert _ _
    · rw [← ht] at hn
      refine Algebra.adjoin_mono ?_ hn
      rw [Finset.coe_insert]
      exact Set.subset_insert _ _

theorem finiteType_chartRing (hx : Transcendental k x) {A : Finset k} (hA : A.Nonempty) :
    Algebra.FiniteType k (chartRing x A) := by
  classical
  obtain ⟨c0, hc0⟩ := hA
  exact (Subalgebra.fg_iff_finiteType _).mp (fg_chartRing hx hc0)

end ChartDed

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymB_ValAlg =====
section

/-!
# S4-JacSymB, file H2a: a valuation-ring lemma for the valuative criterion (L12)

`O` a valuation ring with fraction field `K`, `μ : k →+* O` with `k` an infinite field. For a nonzero `p : K[X]` there is
`t : k` such that, with `λ = μ t ∈ O ⊆ K`, `p(λ) ≠ 0` and every coefficient of the Taylor shift `p(X + λ)` is an
`O`-multiple of `p(λ)`. Proof: scale `p` so its largest coefficient (for the valuation) is `1`; then it lies in `O[X]`
with nonzero reduction mod the maximal ideal, and an infinite field `k ⊆ O/𝔪` contains a non-root `t`, so `p(μ t)` is a
unit of `O` after scaling.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section ValAlg

open Polynomial

theorem exists_taylor_integral {k O K : Type*} [Field k] [Infinite k] [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (μ : k →+* O) (p : K[X]) (hp : p ≠ 0) :
    ∃ t : k, p.eval (algebraMap O K (μ t)) ≠ 0 ∧
      ∀ j, ∃ o : O, algebraMap O K o * p.eval (algebraMap O K (μ t)) = (taylor (algebraMap O K (μ t)) p).coeff j := by
  classical
  set v := ValuationRing.valuation O K
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image p.support (fun j => v (p.coeff j))
    (Finset.nonempty_of_ne_empty (by simpa using hp))
  set a := p.coeff j0 with ha_def
  have ha : a ≠ 0 := mem_support_iff.mp hj0
  have hle : ∀ j, v (a⁻¹ * p.coeff j) ≤ 1 := by
    intro j
    by_cases hj : j ∈ p.support
    · rw [map_mul, map_inv₀]
      have hva : v a ≠ 0 := by simpa using ha
      calc (v a)⁻¹ * v (p.coeff j) ≤ (v a)⁻¹ * v a := by gcongr; exact hmax j hj
        _ = 1 := inv_mul_cancel₀ hva
    · rw [notMem_support_iff.mp hj, mul_zero, map_zero]; exact zero_le
  have hlift : C a⁻¹ * p ∈ lifts (algebraMap O K) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    rw [coeff_C_mul]
    obtain ⟨o, ho⟩ := (ValuationRing.mem_integer_iff O K _).mp ((Valuation.mem_integer_iff _ _).mpr (hle j))
    exact ⟨o, ho⟩
  obtain ⟨q0, hq0⟩ := (mem_lifts _).mp hlift
  have hq0j : q0.coeff j0 = 1 := by
    apply IsFractionRing.injective O K
    rw [map_one, ← coeff_map, hq0, coeff_C_mul, ← ha_def, inv_mul_cancel₀ ha]
  have hp_eq : p = C a * q0.map (algebraMap O K) := by
    rw [hq0, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  set ρ : O →+* IsLocalRing.ResidueField O := IsLocalRing.residue O
  have hqbar : q0.map ρ ≠ 0 := by
    intro h
    have := congrArg (fun r => r.coeff j0) h
    simp only [coeff_map, hq0j, map_one, coeff_zero] at this
    exact one_ne_zero this
  obtain ⟨t, ht⟩ : ∃ t : k, (q0.map ρ).eval (ρ (μ t)) ≠ 0 := by
    by_contra! H
    apply hqbar
    apply eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range (ρ.comp μ)) ?_ (Set.infinite_range_of_injective (ρ.comp μ).injective)
    rintro _ ⟨t, rfl⟩
    exact H t
  rw [eval_map, eval₂_hom, IsLocalRing.residue_ne_zero_iff_isUnit] at ht
  obtain ⟨u, hu⟩ := ht
  refine ⟨t, ?_, fun j => ⟨(taylor (μ t) q0).coeff j * ↑u⁻¹, ?_⟩⟩
  · rw [hp_eq, eval_mul, eval_C, eval_map, eval₂_hom, ← hu]
    exact mul_ne_zero ha ((IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero u.ne_zero)))
  · rw [hp_eq, taylor_mul, taylor_C, coeff_C_mul, ← map_taylor, coeff_map, eval_mul, eval_C, eval_map, eval₂_hom, ← hu,
      map_mul]
    have h1 : algebraMap O K (↑u⁻¹ : O) * algebraMap O K (↑u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (algebraMap O K ((taylor (μ t) q0).coeff j) * a) * h1

end ValAlg

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacAlg_Defs =====
section

/-!
# Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)

`A` is an abelian group (in the application `Pic⁰(X̄) = J(F̄_q)`), `π` an additive endomorphism of `A`
(the arithmetic Frobenius) and `deg F` the degree of the endomorphism `F(π_J)` of the Jacobian, for
`F ∈ ℤ[X]`. The fields are (D1)-(D3) of `S4_COREB_ROUTE.md` (reduction F1):
* (D1) `deg` is multiplicative with `deg 1 = 1`;
* (D2) `deg (n • F + G)` is a polynomial in `n ∈ ℤ` of degree `≤ 2g`, and `deg n = n ^ (2g)`;
* (D3) `deg F = 0` iff `Ker F(π)` is infinite, and `deg F = #Ker F(π)` when `p ∤ F(0)`.
Every geometric Core B unit delivers exactly this structure.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

/-- Degree data on `ℤ[π]` (S4_COREB_ROUTE.md, F1). -/
structure DegreeData {A : Type*} [AddCommGroup A] (π : Module.End ℤ A) (g p : ℕ) where
  /-- `deg F` = degree of the isogeny `F(π)` (`0` if `F(π)` is not an isogeny). -/
  deg : ℤ[X] → ℕ
  deg_one : deg 1 = 1
  deg_mul : ∀ F G : ℤ[X], deg (F * G) = deg F * deg G
  deg_natCast : ∀ n : ℕ, deg (n : ℤ[X]) = n ^ (2 * g)
  deg_poly : ∀ F G : ℤ[X], ∃ P : ℚ[X], P.natDegree ≤ 2 * g ∧
    ∀ n : ℤ, (deg (n • F + G) : ℚ) = P.eval (n : ℚ)
  deg_eq_zero_iff : ∀ F : ℤ[X], deg F = 0 ↔ (LinearMap.ker (aeval π F) : Set A).Infinite
  deg_eq_card_ker : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
    deg F = Nat.card (LinearMap.ker (aeval π F))

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

theorem deg_neg_one : D.deg (-1) = 1 := by
  have h := D.deg_mul (-1) (-1)
  rw [neg_one_mul, neg_neg, D.deg_one] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

theorem deg_neg (F : ℤ[X]) : D.deg (-F) = D.deg F := by
  rw [← neg_one_mul, D.deg_mul, D.deg_neg_one, one_mul]

theorem deg_intCast (n : ℤ) : D.deg (n : ℤ[X]) = n.natAbs ^ (2 * g) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast, D.deg_natCast, Int.natAbs_natCast]
  · rw [Int.cast_neg, Int.cast_natCast, D.deg_neg, D.deg_natCast, Int.natAbs_neg,
      Int.natAbs_natCast]

theorem deg_zsmul (n : ℤ) (F : ℤ[X]) : D.deg (n • F) = n.natAbs ^ (2 * g) * D.deg F := by
  rw [zsmul_eq_mul, D.deg_mul, D.deg_intCast]

theorem deg_C_mul (c : ℤ) (F : ℤ[X]) : D.deg (C c * F) = c.natAbs ^ (2 * g) * D.deg F := by
  rw [show (C c : ℤ[X]) = (c : ℤ[X]) from by simpa using C_eq_intCast (R := ℤ) c,
    D.deg_mul, D.deg_intCast]

theorem deg_pow (F : ℤ[X]) (k : ℕ) : D.deg (F ^ k) = D.deg F ^ k := by
  induction k with
  | zero => simp [D.deg_one]
  | succ k ih => rw [pow_succ, D.deg_mul, ih, pow_succ]

/-- The polynomial of (D2) for the pencil `n • F + G`. -/
noncomputable def polyOf (F G : ℤ[X]) : ℚ[X] := Classical.choose (D.deg_poly F G)

theorem polyOf_natDegree_le (F G : ℤ[X]) : (D.polyOf F G).natDegree ≤ 2 * g :=
  (Classical.choose_spec (D.deg_poly F G)).1

theorem polyOf_eval (F G : ℤ[X]) (n : ℤ) :
    (D.polyOf F G).eval (n : ℚ) = (D.deg (n • F + G) : ℚ) :=
  ((Classical.choose_spec (D.deg_poly F G)).2 n).symm

/-- A polynomial over `ℚ` is determined by its values at the integers. -/
theorem eq_of_eval_intCast_eq {P Q : ℚ[X]} (h : ∀ n : ℤ, P.eval (n : ℚ) = Q.eval (n : ℚ)) :
    P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Int.cast_injective (α := ℚ)))
  rintro _ ⟨n, rfl⟩
  exact h n

/-- `P_π` (Milne 10.9): the polynomial with `P_π(n) = deg(n - π)` for every `n : ℤ`. -/
noncomputable def charPoly : ℚ[X] := D.polyOf 1 (-X)

theorem charPoly_eval (n : ℤ) : D.charPoly.eval (n : ℚ) = (D.deg ((n : ℤ[X]) - X) : ℚ) := by
  rw [charPoly, polyOf_eval, zsmul_one, sub_eq_add_neg]

theorem charPoly_natDegree_le : D.charPoly.natDegree ≤ 2 * g := D.polyOf_natDegree_le _ _

theorem eq_charPoly {Q : ℚ[X]} (h : ∀ n : ℤ, Q.eval (n : ℚ) = (D.deg ((n : ℤ[X]) - X) : ℚ)) :
    Q = D.charPoly :=
  eq_of_eval_intCast_eq fun n => by rw [h, charPoly_eval]

theorem mem_ker_natCast (n : ℕ) (x : A) :
    x ∈ LinearMap.ker (aeval π (n : ℤ[X])) ↔ n • x = 0 := by
  simp [map_natCast]

include D in
/-- (D2) + (D3): `#A[n] = n ^ (2g)` for `p ∤ n` (first half of A1). -/
theorem card_ker_natCast (n : ℕ) (hn : ¬ (p : ℤ) ∣ n) :
    Nat.card (LinearMap.ker (aeval π (n : ℤ[X]))) = n ^ (2 * g) := by
  rw [← D.deg_eq_card_ker _ (by simpa using hn), D.deg_natCast]

/-- `deg F ≠ 0` iff `Ker F(π)` is finite. -/
theorem deg_ne_zero_iff (F : ℤ[X]) :
    D.deg F ≠ 0 ↔ (LinearMap.ker (aeval π F) : Set A).Finite := by
  rw [Ne, D.deg_eq_zero_iff, Set.not_infinite]

/-- `deg π ≠ 0` when `π` is injective on `A` (so the roots of `P_π` are nonzero). -/
theorem deg_X_ne_zero (hπ : Function.Injective π) : D.deg X ≠ 0 := by
  rw [D.deg_ne_zero_iff, aeval_X]
  have : (LinearMap.ker π : Set A) = {0} := by
    rw [LinearMap.ker_eq_bot.mpr hπ]; simp
  rw [this]; exact Set.finite_singleton 0

end DegreeData

end RamanujanPetersson.JacAlg

end

-- ===== S4.Def_RP_DegPoly =====
section

/-!
# Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)

Milne, *Abelian Varieties*, Lemma 10.12 and Prop. 10.13, in hypothesis form and over pure algebra.

`I` is a `g`-linear integer form on an abelian group `M` (the intersection form on divisors of an abelian variety of
dimension `g`), `c : R → M` sends an endomorphism `a` to the class `a^* D` of a divisor `D = c 1`, and
`deg : R → ℕ` is the degree. Two classes are *numerically equivalent* when their difference lies in `numKer I`.
Assume
* `(D^g) ≠ 0`;
* the projection formula `((a^* D)^g) = deg a · (D^g)`;
* the quadratic relation `(n a + b)^* D ≡ n² a^* D + n e(a, b) + b^* D` for all `a, b` (this is where `D` symmetric
  enters), and `0^* D ≡ 0`.
Then `n ↦ deg (n a + b)` is a polynomial of degree `≤ 2g` with rational coefficients, and `deg n = n ^ (2g)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

open Polynomial

variable {M : Type*} [AddCommGroup M] {g : ℕ}

/-- The numerical kernel of a `g`-linear form: the classes `u` with `I (w₁, …, u, …, w_g) = 0` in every slot. -/
def numKer (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) : AddSubgroup M where
  carrier := {u | ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0}
  zero_mem' := fun w i => I.map_update_zero w i
  add_mem' {u v} hu hv w i := by
    have hu' : ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0 := hu
    have hv' : ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i v) = 0 := hv
    rw [I.map_update_add, hu' w i, hv' w i, add_zero]
  neg_mem' {u} hu w i := by
    have hu' : ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0 := hu
    rw [I.map_update_neg, hu' w i, neg_zero]

theorem mem_numKer {I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ} {u : M} :
    u ∈ numKer I ↔ ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0 :=
  Iff.rfl

/-- A `g`-linear form over `ℤ` from a function that is additive in each slot (for example `IntersectB.iform`). -/
def formOfAdd (f : (Fin g → M) → ℤ)
    (hf : ∀ (w : Fin g → M) (i : Fin g) (x y : M),
      f (Function.update w i (x + y)) = f (Function.update w i x) + f (Function.update w i y)) :
    MultilinearMap ℤ (fun _ : Fin g => M) ℤ :=
  MultilinearMap.mk' f hf (fun w i k x =>
    map_zsmul (AddMonoidHom.mk' (fun y => f (Function.update w i y)) (hf w i)) k x)

theorem formOfAdd_apply (f : (Fin g → M) → ℤ)
    (hf : ∀ (w : Fin g → M) (i : Fin g) (x y : M),
      f (Function.update w i (x + y)) = f (Function.update w i x) + f (Function.update w i y))
    (w : Fin g → M) : formOfAdd f hf w = f w :=
  rfl

variable (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)

/-- Adding a numerically trivial class does not change the self-intersection. -/
theorem map_add_of_mem {u : M} (hu : u ∈ numKer I) (y : M) :
    I (fun _ => u + y) = I (fun _ => y) := by
  have h := I.map_add_univ (fun _ => u) (fun _ => y)
  rw [show ((fun _ : Fin g => u) + fun _ => y) = fun _ => u + y from rfl] at h
  rw [h, Finset.sum_eq_single (∅ : Finset (Fin g))]
  · simp
  · intro s _ hs
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have he : Function.update (s.piecewise (fun _ => u) (fun _ => y)) i u =
        s.piecewise (fun _ => u) (fun _ => y) :=
      Function.update_eq_self_iff.mpr (by simp [Finset.piecewise_eq_of_mem _ _ _ hi])
    rw [← he]
    exact hu _ i
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Numerically equivalent classes have the same self-intersection. -/
theorem self_eq_of_sub_mem {x y : M} (h : x - y ∈ numKer I) : I (fun _ => x) = I (fun _ => y) := by
  have := map_add_of_mem I h y
  rwa [sub_add_cancel] at this

/-- Milne 10.12, the algebraic core: `n ↦ ((n² x + n y + z)^g)` is a polynomial of degree `≤ 2g`. -/
theorem exists_poly (x y z : M) : ∃ P : ℤ[X], P.natDegree ≤ 2 * g ∧
    ∀ n : ℤ, I (fun _ => n ^ 2 • x + n • y + z) = P.eval n := by
  let v : Fin 3 → M := ![z, y, x]
  refine ⟨∑ r : Fin g → Fin 3, C (I (fun i => v (r i))) * X ^ (∑ i, (r i : ℕ)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun r _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
    calc ∑ i, (r i : ℕ) ≤ ∑ _i : Fin g, 2 :=
          Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (r i).isLt
      _ = 2 * g := by simp [mul_comm]
  · intro n
    have hv : (fun _ : Fin g => n ^ 2 • x + n • y + z) =
        fun _ => ∑ j : Fin 3, n ^ (j : ℕ) • v j := by
      funext _
      simp [v, Fin.sum_univ_succ]
      abel
    rw [hv, I.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [I.map_smul_univ (fun i => n ^ (r i : ℕ)) (fun i => v (r i))]
    simp [Finset.prod_pow_eq_pow_sum, mul_comm]

variable {R : Type*} [Ring R]

/-- `deg 1 = 1` from the projection formula. -/
theorem deg_one_of_proj (c : R → M) (deg : R → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ a, I (fun _ => c a) = deg a * I (fun _ => c 1)) : deg 1 = 1 := by
  have h := hproj 1
  have h1 : ((deg 1 : ℕ) : ℤ) = 1 := by
    have := mul_right_cancel₀ hD (h.symm.trans (one_mul _).symm)
    exact this
  exact_mod_cast h1

/-- **Milne Lemma 10.12 / Prop. 10.13 (L37), (D2) first half.** `n ↦ deg (n a + b)` is a polynomial in `n ∈ ℤ`
of degree `≤ 2g` with rational coefficients. -/
theorem deg_poly_of_quad (c : R → M) (deg : R → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ a, I (fun _ => c a) = deg a * I (fun _ => c 1))
    (hquad : ∀ a b : R, ∃ e : M, ∀ n : ℤ, c (n * a + b) - (n ^ 2 • c a + n • e + c b) ∈ numKer I)
    (a b : R) : ∃ P : ℚ[X], P.natDegree ≤ 2 * g ∧
      ∀ n : ℤ, (deg (n * a + b) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨e, he⟩ := hquad a b
  obtain ⟨P, hPdeg, hP⟩ := exists_poly I (c a) e (c b)
  refine ⟨C ((I (fun _ => c 1) : ℚ)⁻¹) * P.map (Int.castRingHom ℚ), ?_, fun n => ?_⟩
  · exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hPdeg)
  · have h1 := hproj (n * a + b)
    rw [self_eq_of_sub_mem I (he n), hP n] at h1
    have hd : ((I (fun _ => c 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD
    rw [eval_mul, eval_C, eval_intCast_map, Int.cast_id, h1, map_mul, map_natCast, eq_intCast]
    field_simp

/-- **(D2) second half.** For symmetric `D` (quadratic relation with the `n²` coefficient, and `0^* D ≡ 0`):
`deg n = n ^ (2g)`. -/
theorem deg_natCast_of_quad (c : R → M) (deg : R → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ a, I (fun _ => c a) = deg a * I (fun _ => c 1))
    (hquad : ∀ a b : R, ∃ e : M, ∀ n : ℤ, c (n * a + b) - (n ^ 2 • c a + n • e + c b) ∈ numKer I)
    (hzero : c 0 ∈ numKer I) (n : ℕ) : deg (n : R) = n ^ (2 * g) := by
  obtain ⟨e, he⟩ := hquad 1 0
  have h1 := he 1
  simp only [Int.cast_one, one_mul, add_zero, one_pow, one_smul] at h1
  have he0 : e ∈ numKer I := by
    have : e = -(c 1 - (c 1 + e + c 0)) - c 0 := by abel
    rw [this]
    exact sub_mem (neg_mem h1) hzero
  have hn := he n
  simp only [Int.cast_natCast, mul_one, add_zero] at hn
  have hk : c (n : R) - ((n : ℤ) ^ 2 • c 1) ∈ numKer I := by
    have : c (n : R) - (n : ℤ) ^ 2 • c 1 =
        (c (n : R) - ((n : ℤ) ^ 2 • c 1 + (n : ℤ) • e + c 0)) + ((n : ℤ) • e + c 0) := by abel
    rw [this]
    exact add_mem hn (add_mem (zsmul_mem he0 _) hzero)
  have h2 := hproj (n : R)
  rw [self_eq_of_sub_mem I hk, I.map_smul_univ (fun _ => ((n : ℤ) ^ 2)) (fun _ => c 1)] at h2
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  have h3 := mul_right_cancel₀ hD h2
  have h4 : ((deg (n : R) : ℕ) : ℤ) = ((n ^ (2 * g) : ℕ) : ℤ) := by
    rw [← h3]
    push_cast
    rw [← pow_mul]
  exact_mod_cast h4

end RamanujanPetersson.DegPoly

end

-- ===== S4.Def_RP_DegPoly_Data =====
section

/-!
# Degree polynomiality, part 2: (D2) in `DegreeData` form (unit S4-DegPoly, L37)

For `R = ℤ[X]` (where `c F` is the class of `F(π_J)^* D` and `deg F` the degree of `F(π_J)`), the quadratic-relation
data of `Def_RP_DegPoly` gives the fields `deg_one`, `deg_natCast` and `deg_poly` of `JacAlg.DegreeData`.
`degreeDataOfQuad` assembles a `DegreeData` from that data together with (D1) multiplicativity and (D3).
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

open Polynomial RamanujanPetersson.JacAlg

variable {A : Type*} [AddCommGroup A] {M : Type*} [AddCommGroup M] {g : ℕ}

/-- (D2), first half, in the exact shape of the field `DegreeData.deg_poly`. -/
theorem deg_poly_zsmul (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) (c : ℤ[X] → M) (deg : ℤ[X] → ℕ)
    (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ F, I (fun _ => c F) = deg F * I (fun _ => c 1))
    (hquad : ∀ F G : ℤ[X], ∃ e : M, ∀ n : ℤ,
      c (n * F + G) - (n ^ 2 • c F + n • e + c G) ∈ numKer I)
    (F G : ℤ[X]) : ∃ P : ℚ[X], P.natDegree ≤ 2 * g ∧
      ∀ n : ℤ, (deg (n • F + G) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P, h1, h2⟩ := deg_poly_of_quad I c deg hD hproj hquad F G
  exact ⟨P, h1, fun n => by rw [zsmul_eq_mul]; exact h2 n⟩

/-- **L37 output.** A `DegreeData` from the quadratic-relation data ((D2) and `deg 1 = 1`), multiplicativity and
(D3). -/
def degreeDataOfQuad (π : Module.End ℤ A) (g p : ℕ) (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)
    (c : ℤ[X] → M) (deg : ℤ[X] → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ F, I (fun _ => c F) = deg F * I (fun _ => c 1))
    (hquad : ∀ F G : ℤ[X], ∃ e : M, ∀ n : ℤ,
      c (n * F + G) - (n ^ 2 • c F + n • e + c G) ∈ numKer I)
    (hzero : c 0 ∈ numKer I)
    (deg_mul : ∀ F G : ℤ[X], deg (F * G) = deg F * deg G)
    (deg_eq_zero_iff : ∀ F : ℤ[X], deg F = 0 ↔ (LinearMap.ker (aeval π F) : Set A).Infinite)
    (deg_eq_card_ker : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      deg F = Nat.card (LinearMap.ker (aeval π F))) :
    DegreeData π g p where
  deg := deg
  deg_one := deg_one_of_proj I c deg hD hproj
  deg_mul := deg_mul
  deg_natCast := deg_natCast_of_quad I c deg hD hproj hquad hzero
  deg_poly := deg_poly_zsmul I c deg hD hproj hquad
  deg_eq_zero_iff := deg_eq_zero_iff
  deg_eq_card_ker := deg_eq_card_ker

theorem degreeDataOfQuad_deg (π : Module.End ℤ A) (g p : ℕ) (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)
    (c : ℤ[X] → M) (deg : ℤ[X] → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ F, I (fun _ => c F) = deg F * I (fun _ => c 1))
    (hquad : ∀ F G : ℤ[X], ∃ e : M, ∀ n : ℤ,
      c (n * F + G) - (n ^ 2 • c F + n • e + c G) ∈ numKer I)
    (hzero : c 0 ∈ numKer I)
    (deg_mul : ∀ F G : ℤ[X], deg (F * G) = deg F * deg G)
    (deg_eq_zero_iff : ∀ F : ℤ[X], deg F = 0 ↔ (LinearMap.ker (aeval π F) : Set A).Infinite)
    (deg_eq_card_ker : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      deg F = Nat.card (LinearMap.ker (aeval π F))) :
    (degreeDataOfQuad π g p I c deg hD hproj hquad hzero deg_mul deg_eq_zero_iff deg_eq_card_ker).deg = deg :=
  rfl

end RamanujanPetersson.DegPoly

end

-- ===== S4.Def_RP_JacDivisors_H =====
section

/-!
# S4-JacDivisors H (O11: Weil divisors on integral locally Noetherian schemes)
* `finite_coheight_one_not_mem_basicOpen`: on an affine open `U`, a nonzero section `a` vanishes at only
  finitely many codimension-one points.
* `div f : AlgebraicCycle X ℤ`: the principal divisor `z ↦ ord_z f` (locally finite support).
* `div_mul`, `div_one`, `div_inv`, `div_isWeil`, `div_germ_nonneg`.
* `weilDivisors X`, `principalDivisors X`, `LinEquiv` (linear equivalence, an equivalence relation).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A nonzero section on an affine open vanishes at finitely many codimension-one points. -/
lemma finite_coheight_one_not_mem_basicOpen {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (a : Γ(X, U)) (ha : a ≠ 0) :
    {z : X | z ∈ U ∧ coheight z = 1 ∧ z ∉ X.basicOpen a}.Finite := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hS : {y : Spec Γ(X, U) | y.asIdeal ∈ (Ideal.span {a}).minimalPrimes}.Finite :=
    (Ideal.span {a}).finite_minimalPrimes_of_isNoetherianRing.preimage
      (fun y _ y' _ h => PrimeSpectrum.ext h)
  refine (hS.image hU.fromSpec).subset ?_
  rintro z ⟨hzU, hz1, hza⟩
  have hzU' : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
  obtain ⟨y, rfl⟩ := hzU'
  refine ⟨y, ?_, rfl⟩
  have hy1 : y.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec]
    exact hz1
  have hay : a ∈ y.asIdeal := by
    have h : y ∉ hU.fromSpec ⁻¹ᵁ X.basicOpen a := hza
    rw [hU.fromSpec_preimage_basicOpen] at h
    by_contra hn
    exact h hn
  have : y.asIdeal.IsPrime := y.isPrime
  have : y.asIdeal.FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (Or.inr (lt_of_eq_of_lt hy1 ENat.one_lt_top))
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr hay) ?_
  rw [hy1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero ha)

/-- A section has order zero wherever it is a unit. -/
lemma ord_germ_eq_zero {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {z : X}
    (hz : z ∈ X.basicOpen a) : Scheme.ord (X.germToFunctionField U a) z = 0 := by
  have : Nonempty (X.basicOpen a) := ⟨⟨z, hz⟩⟩
  have : Nonempty (X.toRingedSpace.basicOpen a) := ⟨⟨z, hz⟩⟩
  have h := Scheme.ord_of_isUnit (X.toRingedSpace.isUnit_res_basicOpen a) hz
  convert h using 2
  exact (X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le a)) _ _ a).symm

lemma ord_one (z : X) : Scheme.ord (1 : X.functionField) z = 0 := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have h := Scheme.ord_of_isUnit (U := ⊤) (f := 1) isUnit_one (x := z) trivial
  rwa [map_one] at h

/-- Sections are regular: `ord_z a ≥ 0` at every point of `U`. -/
lemma ord_germ_nonneg {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {z : X} (hz : z ∈ U) :
    0 ≤ Scheme.ord (X.germToFunctionField U a) z := by
  by_cases ha : a = 0
  · simp [ha]
  have h := Scheme.ord_le_smul hz ha (1 : X.functionField)
  rw [ord_one, Algebra.smul_def, mul_one] at h
  exact h

lemma finite_support_ord_inter {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) :
    ((U : Set X) ∩ Function.support (fun z => Scheme.ord f z)).Finite := by
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hf
  refine ((finite_coheight_one_not_mem_basicOpen hU a ha).union
    (finite_coheight_one_not_mem_basicOpen hU b hb0)).subset ?_
  rintro z ⟨hzU, hz⟩
  have h1 : coheight z = 1 := by
    by_contra h; exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h _)
  by_contra hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hmem
  apply hz
  have hA : algebraMap Γ(X, U) X.functionField a ≠ 0 := by
    rintro h; apply hf; rw [h, zero_div]
  have hB : algebraMap Γ(X, U) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ(X, U) X.functionField)).mpr hb0
  have hq : algebraMap Γ(X, U) X.functionField a / algebraMap Γ(X, U) X.functionField b ≠ 0 :=
    div_ne_zero hA hB
  have key := Scheme.ord_mul (x := z) hq hB
  rw [div_mul_cancel₀ _ hB] at key
  have e1 : Scheme.ord (algebraMap Γ(X, U) X.functionField a) z = 0 :=
    ord_germ_eq_zero a (hmem.1 hzU h1)
  have e2 : Scheme.ord (algebraMap Γ(X, U) X.functionField b) z = 0 :=
    ord_germ_eq_zero b (hmem.2 hzU h1)
  change Scheme.ord _ z = 0
  omega

lemma locallyFinite_ord (f : X.functionField) (z : X) :
    ∃ t ∈ 𝓝 z, (t ∩ Function.support (fun z => Scheme.ord f z)).Finite := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  exact ⟨U, U.isOpen.mem_nhds hzU, finite_support_ord_inter hU f⟩

variable (X) in
/-- The principal divisor of a rational function, `z ↦ ord_z f` (junk value `0` for `f = 0`). -/
noncomputable def div (f : X.functionField) : AlgebraicCycle X ℤ where
  toFun z := Scheme.ord f z
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' z _ := locallyFinite_ord f z

lemma div_apply (f : X.functionField) (z : X) : div X f z = Scheme.ord f z := rfl

lemma div_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    div X (f * g) = div X f + div X g := by
  ext z; simp [div_apply, Scheme.ord_mul hf hg]

lemma div_one : div X (1 : X.functionField) = 0 := by
  ext z; simp [div_apply, ord_one]

lemma div_zero : div X (0 : X.functionField) = 0 := by
  ext z; simp [div_apply]

lemma div_inv {f : X.functionField} (hf : f ≠ 0) : div X f⁻¹ = -div X f := by
  have h := div_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, div_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma div_div {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    div X (f / g) = div X f - div X g := by
  rw [div_eq_mul_inv, div_mul hf (inv_ne_zero hg), div_inv hg, sub_eq_add_neg]

/-- Sections are effective on their domain. -/
lemma div_germ_nonneg {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {z : X} (hz : z ∈ U) :
    0 ≤ div X (X.germToFunctionField U a) z :=
  ord_germ_nonneg a hz

lemma div_germ_eq_zero {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {z : X}
    (hz : z ∈ X.basicOpen a) : div X (X.germToFunctionField U a) z = 0 :=
  ord_germ_eq_zero a hz

variable (X) in
/-- Weil divisors: cycles supported on codimension-one points. -/
def weilDivisors : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {D | ∀ z, D z ≠ 0 → coheight z = 1}
  zero_mem' z h := (h rfl).elim
  add_mem' {D E} hD hE z h := by
    by_contra hz
    exact h (by simp [Function.locallyFinsuppWithin.coe_add, not_not.mp (mt (hD z) hz),
      not_not.mp (mt (hE z) hz)])
  neg_mem' {D} hD z h := hD z (by simp at h; exact h)

lemma div_mem_weilDivisors (f : X.functionField) : div X f ∈ weilDivisors X := by
  intro z h
  by_contra hz
  exact h (Scheme.ord_eq_zero_of_coheight_neq_one hz f)

variable (X) in
/-- Principal divisors `div f`, `f ≠ 0`. -/
def principalDivisors : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {D | ∃ f : X.functionField, f ≠ 0 ∧ div X f = D}
  zero_mem' := ⟨1, one_ne_zero, div_one⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_ne_zero hf hg, div_mul hf hg⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f⁻¹, inv_ne_zero hf, div_inv hf⟩

lemma div_mem_principalDivisors {f : X.functionField} (hf : f ≠ 0) :
    div X f ∈ principalDivisors X := ⟨f, hf, rfl⟩

lemma principalDivisors_le_weilDivisors : principalDivisors X ≤ weilDivisors X := by
  rintro _ ⟨f, -, rfl⟩
  exact div_mem_weilDivisors f

variable (X) in
/-- Linear equivalence of cycles: `D - D'` is principal. -/
def LinEquiv (D D' : AlgebraicCycle X ℤ) : Prop := D - D' ∈ principalDivisors X

lemma linEquiv_iff {D D' : AlgebraicCycle X ℤ} :
    LinEquiv X D D' ↔ ∃ f : X.functionField, f ≠ 0 ∧ D = D' + div X f := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, by rw [h]; abel⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, by rw [h]; abel⟩

lemma linEquiv_equivalence : Equivalence (LinEquiv X) where
  refl D := by simpa [LinEquiv] using (principalDivisors X).zero_mem
  symm {D D'} h := by
    have := (principalDivisors X).neg_mem h
    rwa [neg_sub] at this
  trans {D D' D''} h h' := by
    have := (principalDivisors X).add_mem h h'
    rwa [sub_add_sub_cancel] at this

lemma linEquiv_add {D D' E E' : AlgebraicCycle X ℤ} (h : LinEquiv X D D') (h' : LinEquiv X E E') :
    LinEquiv X (D + E) (D' + E') := by
  have := (principalDivisors X).add_mem h h'
  unfold LinEquiv
  convert this using 1
  abel

lemma linEquiv_div {D : AlgebraicCycle X ℤ} {f : X.functionField} (hf : f ≠ 0) :
    LinEquiv X (D + div X f) D :=
  linEquiv_iff.mpr ⟨f, hf, rfl⟩

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_JacDivisors_I =====
section

/-!
# S4-JacDivisors I (O12 bridges: orders of sections at codimension-one points, affine charts)
* `ord_algebraMap_stalk`: `ord_z b = length (O_z ⧸ b)` for `b` in the stalk at a codimension-one point.
* `ord_germ_pos`: a nonzero section vanishing at `z` has positive order there.
* `ord_germ_eq_one`: a section whose germ generates the maximal ideal has order one.
* affine chart dictionary: `fromSpec_mem_basicOpen_iff`, `coheight_fromSpec`, `fromSpec_specializes_iff`,
  `fromSpec_mem`, `exists_fromSpec_eq`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

variable {X : Scheme.{u}}

section
variable [IsIntegral X] [IsLocallyNoetherian X]

lemma ord_algebraMap_stalk {z : X} (hz : coheight z = 1) {b : X.presheaf.stalk z} (hb : b ≠ 0)
    {n : ℕ} (hn : Ring.ord (X.presheaf.stalk z) b = n) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z = n := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hK : algebraMap (X.presheaf.stalk z) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb
  rw [Scheme.ord_eq_iff hz hK]
  change Ring.ordFrac (X.presheaf.stalk z) (algebraMap _ X.functionField b) = _
  rw [Ring.ordFrac_eq_ord _ hb]
  exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hb) hn

lemma ord_algebraMap_stalk_pos {z : X} (hz : coheight z = 1) {b : X.presheaf.stalk z} (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal (X.presheaf.stalk z)) :
    0 < Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk z) (mem_nonZeroDivisors_of_ne_zero hb))
  rw [ord_algebraMap_stalk hz hb hn.symm]
  have hnt : Nontrivial (X.presheaf.stalk z ⧸ Ideal.span {b}) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun h =>
      (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr hbm)))
  have hpos : 0 < Ring.ord (X.presheaf.stalk z) b := Module.length_pos
  rw [← hn] at hpos
  exact_mod_cast hpos

lemma ord_algebraMap_stalk_eq_one {z : X} (hz : coheight z = 1) {b : X.presheaf.stalk z}
    (hb : b ≠ 0) (hbm : Ideal.span {b} = maximalIdeal (X.presheaf.stalk z)) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z = 1 := by
  have h1 : Ring.ord (X.presheaf.stalk z) b = ((1 : ℕ) : ℕ∞) := by
    have : IsSimpleModule (X.presheaf.stalk z) (X.presheaf.stalk z ⧸ Ideal.span {b}) := by
      rw [hbm]
      exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal _))
    show Module.length _ _ = _
    rw [Module.length_eq_one]
    rfl
  exact_mod_cast ord_algebraMap_stalk hz hb h1

lemma germ_ne_zero {U : X.Opens} {z : X} (hz : z ∈ U) {r : Γ(X, U)} (hr : r ≠ 0) :
    X.presheaf.germ U z hz r ≠ 0 := by
  intro h
  exact hr (germ_injective_of_isIntegral X z hz (h.trans (map_zero _).symm))

/-- A nonzero section vanishing at a codimension-one point has positive order there. -/
lemma ord_germ_pos {U : X.Opens} [Nonempty U] {z : X} (hz : z ∈ U) (hz1 : coheight z = 1)
    {r : Γ(X, U)} (hr : r ≠ 0) (hzr : z ∉ X.basicOpen r) :
    0 < Scheme.ord (X.germToFunctionField U r) z := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz r]
  refine ord_algebraMap_stalk_pos hz1 (germ_ne_zero hz hr) ?_
  rw [Scheme.mem_basicOpen X r z hz] at hzr
  exact (mem_maximalIdeal _).mpr hzr

/-- A section whose germ generates the maximal ideal at a codimension-one point has order one. -/
lemma ord_germ_eq_one {U : X.Opens} [Nonempty U] {z : X} (hz : z ∈ U) (hz1 : coheight z = 1)
    {r : Γ(X, U)} (hr : r ≠ 0)
    (hspan : Ideal.span {X.presheaf.germ U z hz r} = maximalIdeal (X.presheaf.stalk z)) :
    Scheme.ord (X.germToFunctionField U r) z = 1 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz r]
  exact ord_algebraMap_stalk_eq_one hz1 (germ_ne_zero hz hr) hspan

end

lemma fromSpec_mem_basicOpen_iff {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    (y : Spec Γ(X, U)) : hU.fromSpec y ∈ X.basicOpen r ↔ r ∉ y.asIdeal := by
  change y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _
  rw [hU.fromSpec_preimage_basicOpen]
  rfl

lemma coheight_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (y : Spec Γ(X, U)) :
    coheight (hU.fromSpec y) = y.asIdeal.height := by
  rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec]

lemma fromSpec_specializes_iff {U : X.Opens} (hU : IsAffineOpen U) (y y' : Spec Γ(X, U)) :
    hU.fromSpec y ⤳ hU.fromSpec y' ↔ y.asIdeal ≤ y'.asIdeal := by
  rw [hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes y y').symm

lemma fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : Spec Γ(X, U)) :
    hU.fromSpec y ∈ U := by
  show hU.fromSpec y ∈ (U : Set X)
  rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩

lemma exists_fromSpec_eq {U : X.Opens} (hU : IsAffineOpen U) {z : X} (hz : z ∈ U) :
    ∃ y : Spec Γ(X, U), hU.fromSpec y = z := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec] at hz; exact hz

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_JacDivisors_J =====
section

/-!
# S4-JacDivisors J (O12b: algebraic Hartogs at points with factorial stalks)
* `maximalIdeal_stalk_fromSpec`: `m_{fromSpec y} = y.map germ`.
* `height_comap_germ`, `comap_germ_le`: contraction of primes of the stalk at `fromSpec y` to `Γ(X, U)`.
* `ord_stalk_chart`: for a prime `Q` of `O_x` (`x = fromSpec y`) contracting to `q` with `w = fromSpec q` of
  codimension one, `ord_w a > 0` for `0 ≠ a ∈ Q` and `ord_w a = 0` for `a ∉ Q`.
* `mem_range_algebraMap_stalk_of_ord_nonneg` (Hartogs): if `O_x` is a UFD and `ord_z f ≥ 0` at every
  codimension-one generalization `z` of `x`, then `f` lies in `O_x`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- The maximal ideal of the stalk at `fromSpec y` is generated by the germs of the elements of `y`. -/
lemma maximalIdeal_stalk_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) :
    maximalIdeal (X.presheaf.stalk (hU.fromSpec y)) =
      y.asIdeal.map (X.presheaf.germ U (hU.fromSpec y) (fromSpec_mem hU y)).hom := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  exact (IsLocalization.AtPrime.map_eq_maximalIdeal y.asIdeal
    (X.presheaf.stalk (hU.fromSpec y))).symm

set_option backward.isDefEq.respectTransparency.types false in
lemma height_comap_germ {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (Q : Ideal (X.presheaf.stalk (hU.fromSpec y))) :
    (Q.comap (X.presheaf.germ U (hU.fromSpec y) (fromSpec_mem hU y)).hom).height = Q.height := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  exact IsLocalization.height_under y.asIdeal.primeCompl Q

set_option backward.isDefEq.respectTransparency.types false in
lemma comap_germ_le {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (Q : Ideal (X.presheaf.stalk (hU.fromSpec y))) (hQ : Q ≠ ⊤) :
    Q.comap (X.presheaf.germ U (hU.fromSpec y) (fromSpec_mem hU y)).hom ≤ y.asIdeal := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  intro r hr
  by_contra h
  exact hQ (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hr)
    (IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec y))
      (⟨r, h⟩ : y.asIdeal.primeCompl)))

section
variable [IsIntegral X] [IsLocallyNoetherian X]

set_option backward.isDefEq.respectTransparency.types false in
/-- Orders at a codimension-one point `w = fromSpec q` of elements of the stalk at `fromSpec y`, where
`q` is the contraction of a prime `Q` of that stalk. -/
lemma ord_stalk_chart {U : X.Opens} (hU : IsAffineOpen U) (y q : PrimeSpectrum Γ(X, U))
    (Q : Ideal (X.presheaf.stalk (hU.fromSpec y))) [hQ : Q.IsPrime]
    (hq : ∀ r : Γ(X, U), r ∈ q.asIdeal ↔ X.presheaf.germ U _ (fromSpec_mem hU y) r ∈ Q)
    (hw : coheight (hU.fromSpec q) = 1)
    {a : X.presheaf.stalk (hU.fromSpec y)} (ha : a ≠ 0) :
    (a ∈ Q → 0 < Scheme.ord (algebraMap _ X.functionField a) (hU.fromSpec q)) ∧
    (a ∉ Q → Scheme.ord (algebraMap _ X.functionField a) (hU.fromSpec q) = 0) := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  have : Nonempty U := ⟨⟨_, fromSpec_mem hU y⟩⟩
  have hg : ∀ t : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) t =
      X.presheaf.germ U _ (fromSpec_mem hU y) t := fun _ => rfl
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq y.asIdeal.primeCompl a
  have hsu := IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec y)) s
  have hsQ : algebraMap Γ(X, U) _ (s : Γ(X, U)) ∉ Q :=
    fun h => hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hsu)
  have hsq : (s : Γ(X, U)) ∉ q.asIdeal := fun h => hsQ ((hq _).mp h)
  have hr0 : r ≠ 0 := by rintro rfl; exact ha (IsLocalization.mk'_zero _)
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (hU.fromSpec y)) r s
  have hK := congrArg (algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField) hspec
  rw [map_mul, hg, hg, Scheme.algebraMap_germ_eq_germToFunctionField X (fromSpec_mem hU y),
    Scheme.algebraMap_germ_eq_germToFunctionField X (fromSpec_mem hU y)] at hK
  have hA : algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField
      (IsLocalization.mk' _ r s) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha
  have hS : X.germToFunctionField U (s : Γ(X, U)) ≠ 0 := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (fromSpec_mem hU y)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (germ_ne_zero _ (fun h => hsq (h ▸ q.asIdeal.zero_mem)))
  have hmul := Scheme.ord_mul (x := hU.fromSpec q) hA hS
  rw [hK, ord_germ_eq_zero _ ((fromSpec_mem_basicOpen_iff hU _ q).mpr hsq), add_zero] at hmul
  have hiff : IsLocalization.mk' (X.presheaf.stalk (hU.fromSpec y)) r s ∈ Q ↔ r ∈ q.asIdeal := by
    rw [hq, ← hg, ← hspec]
    exact ⟨fun h => Q.mul_mem_right _ h, fun h => (hQ.mem_or_mem h).resolve_right hsQ⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hmul]
    refine ord_germ_pos (fromSpec_mem hU q) hw hr0 ?_
    rw [fromSpec_mem_basicOpen_iff]
    exact not_not.mpr (hiff.mp h)
  · rw [← hmul]
    exact ord_germ_eq_zero _ ((fromSpec_mem_basicOpen_iff hU _ q).mpr (fun h' => h (hiff.mpr h')))

/-- Algebraic Hartogs: at a point with factorial stalk, a rational function with nonnegative order at
every codimension-one generalization is regular. -/
theorem mem_range_algebraMap_stalk_of_ord_nonneg (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (f : X.functionField)
    (hf : ∀ z : X, z ⤳ x → coheight z = 1 → 0 ≤ Scheme.ord f z) :
    f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hxU
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (hU.fromSpec y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have key : f * algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField b =
      algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hbK]
  suffices H : ∀ b : X.presheaf.stalk (hU.fromSpec y), b ≠ 0 → ∀ a,
      f * algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField b =
        algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField a →
      f ∈ Set.range (algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField) from
    H b hb0 a key
  clear hab hb hbK key hb0 a b
  intro b
  induction b using WfDvdMonoid.induction_on_irreducible with
  | zero => intro h; exact absurd rfl h
  | unit u hu =>
    intro _ a key
    refine ⟨a * ↑hu.unit⁻¹, ?_⟩
    rw [map_mul, ← key, mul_assoc, ← map_mul, hu.mul_val_inv, map_one, mul_one]
  | mul b i hb hi ih =>
    intro _ a key
    by_cases hia : i ∣ a
    · obtain ⟨a', rfl⟩ := hia
      have hi0 : algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField i ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hi.ne_zero
      refine ih hb a' (mul_left_cancel₀ hi0 ?_)
      rw [map_mul, map_mul] at key
      rw [← key]; ring
    · exfalso
      have hip : Prime i := UniqueFactorizationMonoid.irreducible_iff_prime.mp hi
      have ha0 : a ≠ 0 := by rintro rfl; exact hia (dvd_zero i)
      have hQ : (Ideal.span {i}).IsPrime := Ideal.isPrime_span_singleton_of_prime hip
      let q : PrimeSpectrum Γ(X, U) :=
        ⟨(Ideal.span {i}).comap (X.presheaf.germ U _ (fromSpec_mem hU y)).hom, Ideal.IsPrime.comap _⟩
      have hq1 : coheight (hU.fromSpec q) = 1 := by
        refine (coheight_fromSpec hU q).trans ((height_comap_germ hU y _).trans ?_)
        exact
          (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
            (mem_nonZeroDivisors_of_ne_zero hip.ne_zero) hip.not_isUnit)
      have hqy : hU.fromSpec q ⤳ hU.fromSpec y :=
        (fromSpec_specializes_iff hU q y).mpr (comap_germ_le hU y _ hQ.ne_top)
      have hfa : f ≠ 0 := by
        rintro rfl
        rw [zero_mul] at key
        exact ha0 (IsFractionRing.injective _ X.functionField (key.symm.trans (map_zero _).symm))
      have hib : i * b ≠ 0 := mul_ne_zero hi.ne_zero hb
      have h1 := ord_stalk_chart hU y q (Ideal.span {i}) (fun _ => Iff.rfl) hq1 ha0
      have h2 := ord_stalk_chart hU y q (Ideal.span {i}) (fun _ => Iff.rfl) hq1 hib
      have hmul := Scheme.ord_mul (x := hU.fromSpec q) hfa
        ((map_ne_zero_iff _ (IsFractionRing.injective _ X.functionField)).mpr hib)
      rw [key, h1.2 (fun h' => hia (Ideal.mem_span_singleton.mp h'))] at hmul
      have hpos := h2.1 (Ideal.mem_span_singleton.mpr (dvd_mul_right i b))
      have := hf _ hqy hq1
      omega

end

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_JacDivisors_K =====
section

/-!
# S4-JacDivisors K (O12a: Weil divisors are locally principal at factorial points)
* `ord_inv'`, `ord_zpow`, `ord_prod_zpow`: `ord` turns finite products of powers into sums.
* `exists_isOpen_eq_zero_of_specializes`: a cycle vanishing at every generalization of `x` vanishes near `x`.
* `exists_uniformizer`: for a codimension-one generalization `z` of `x = fromSpec y` with `O_x` a UFD there is
  a section `r` with `ord_w r = δ_{wz}` at every codimension-one generalization `w` of `x`.
* `exists_locally_principal`: a Weil divisor equals `div f` on a neighbourhood of a point with factorial stalk.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

variable {X : Scheme.{u}}

/-- A cycle vanishing at every generalization of `x` vanishes on an open neighbourhood of `x`. -/
lemma exists_isOpen_eq_zero_of_specializes (E : AlgebraicCycle X ℤ) (x : X)
    (hE : ∀ w, w ⤳ x → E w = 0) : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ w ∈ V, E w = 0 := by
  obtain ⟨t, ht, hfin⟩ := E.supportLocallyFiniteWithinDomain' x (Set.mem_univ x)
  refine ⟨interior t \ ⋃ w ∈ t ∩ Function.support E, closure {w},
    isOpen_interior.sdiff (hfin.isClosed_biUnion fun _ _ => isClosed_closure),
    ⟨mem_interior_iff_mem_nhds.mpr ht, ?_⟩, ?_⟩
  · simp only [Set.mem_iUnion, not_exists]
    intro w hw hxw
    exact (Function.mem_support.mp hw.2) (hE w (specializes_iff_mem_closure.mpr hxw))
  · rintro w ⟨hwt, hw⟩
    by_contra h
    exact hw (Set.mem_biUnion (⟨interior_subset hwt, Function.mem_support.mpr h⟩ :
      w ∈ t ∩ Function.support E) (subset_closure rfl))

section
variable [IsIntegral X] [IsLocallyNoetherian X]

lemma ord_inv' {f : X.functionField} (hf : f ≠ 0) (z : X) :
    Scheme.ord f⁻¹ z = -Scheme.ord f z := by
  have h := Scheme.ord_mul (x := z) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

lemma ord_zpow {f : X.functionField} (hf : f ≠ 0) (z : X) (n : ℤ) :
    Scheme.ord (f ^ n) z = n * Scheme.ord f z := by
  refine Int.induction_on n ?_ ?_ ?_
  · rw [zpow_zero, ord_one, zero_mul]
  · intro k ih
    rw [zpow_add_one₀ hf, Scheme.ord_mul (zpow_ne_zero _ hf) hf, ih]; ring
  · intro k ih
    rw [zpow_sub_one₀ hf, Scheme.ord_mul (zpow_ne_zero _ hf) (inv_ne_zero hf), ih, ord_inv' hf]
    ring

lemma ord_prod_zpow {ι : Type*} (s : Finset ι) (g : ι → X.functionField) (n : ι → ℤ)
    (hg : ∀ i ∈ s, g i ≠ 0) (z : X) :
    Scheme.ord (∏ i ∈ s, g i ^ n i) z = ∑ i ∈ s, n i * Scheme.ord (g i) z := by
  classical
  revert hg
  refine Finset.induction_on s ?_ ?_
  · intro _; simp [ord_one]
  · intro a s ha ih hg
    have hga := hg a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, g i ≠ 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Scheme.ord_mul (zpow_ne_zero _ hga)
      (Finset.prod_ne_zero_iff.mpr fun i hi => zpow_ne_zero _ (hs i hi)), ord_zpow hga, ih hs]

lemma germToFunctionField_ne_zero {U : X.Opens} [Nonempty U] {r : Γ(X, U)} (hr : r ≠ 0) :
    X.germToFunctionField U r ≠ 0 := by
  obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty U›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (germ_ne_zero hz hr)

set_option backward.isDefEq.respectTransparency.types false in
open Classical in
/-- A local equation of a prime divisor through a factorial point. -/
lemma exists_uniformizer {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (y : PrimeSpectrum Γ(X, U)) [UniqueFactorizationMonoid (X.presheaf.stalk (hU.fromSpec y))]
    (z : X) (hz : z ⤳ hU.fromSpec y) (hz1 : coheight z = 1) :
    ∃ r : Γ(X, U), r ≠ 0 ∧ ∀ w : X, w ⤳ hU.fromSpec y → coheight w = 1 →
      Scheme.ord (X.germToFunctionField U r) w = if w = z then 1 else 0 := by
  obtain ⟨q, rfl⟩ := exists_fromSpec_eq hU (hz.mem_open U.isOpen (fromSpec_mem hU y))
  have hqy : q.asIdeal ≤ y.asIdeal := (fromSpec_specializes_iff hU q y).mp hz
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  have hg : ∀ t : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) t =
      X.presheaf.germ U _ (fromSpec_mem hU y) t := fun _ => rfl
  have hdisj : ∀ q' : PrimeSpectrum Γ(X, U), q'.asIdeal ≤ y.asIdeal →
      Disjoint (y.asIdeal.primeCompl : Set Γ(X, U)) q'.asIdeal :=
    fun q' h => Set.disjoint_left.mpr fun a ha ha' => ha (h ha')
  -- the prime `Q = q O_x` and its properties, for any codimension-one generalization `q'`
  have hloc : ∀ q' : PrimeSpectrum Γ(X, U), q'.asIdeal ≤ y.asIdeal →
      coheight (hU.fromSpec q') = 1 →
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).IsPrime ∧
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).comap
        (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) = q'.asIdeal ∧
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).height = 1 := by
    intro q' hq' h1
    have hc := IsLocalization.under_map_of_isPrime_disjoint y.asIdeal.primeCompl
      (X.presheaf.stalk (hU.fromSpec y)) q'.isPrime (hdisj q' hq')
    refine ⟨IsLocalization.isPrime_of_isPrime_disjoint y.asIdeal.primeCompl _ _ q'.isPrime
      (hdisj q' hq'), hc, ?_⟩
    have h := height_comap_germ hU y
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))))
    have hc' : (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).comap
        (X.presheaf.germ U _ (fromSpec_mem hU y)).hom = q'.asIdeal := hc
    rw [hc', ← coheight_fromSpec hU q', h1] at h
    exact h.symm
  obtain ⟨hQp, hQc, hQh⟩ := hloc q hqy hz1
  obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh).principal
  change _ = Ideal.span {π} at hπ
  obtain ⟨r, s, hrs⟩ := IsLocalization.exists_mk'_eq y.asIdeal.primeCompl π
  have hsu := IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec y)) s
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (hU.fromSpec y)) r s
  rw [hrs] at hspec
  have hπQ : π ∈ q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) :=
    hπ ▸ Ideal.mem_span_singleton_self π
  have hrq : r ∈ q.asIdeal := by
    rw [← hQc, Ideal.mem_comap, ← hspec]; exact Ideal.mul_mem_right _ _ hπQ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hQh (hπ.trans (Ideal.span_singleton_eq_bot.mpr rfl))
  have hr0 : r ≠ 0 := by rintro rfl; exact hπ0 (hrs.symm.trans (IsLocalization.mk'_zero _))
  refine ⟨r, hr0, fun w hw hw1 => ?_⟩
  split_ifs with hwz
  · subst hwz
    refine ord_germ_eq_one (fromSpec_mem hU q) hz1 hr0 (le_antisymm ?_ ?_)
    · rw [Ideal.span_singleton_le_iff_mem, maximalIdeal_stalk_fromSpec hU q]
      exact Ideal.mem_map_of_mem _ hrq
    · rw [maximalIdeal_stalk_fromSpec hU q, Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      have hcQ := Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) hc
      rw [hπ, Ideal.mem_span_singleton'] at hcQ
      obtain ⟨d, hd⟩ := hcQ
      obtain ⟨r', s', rfl⟩ := IsLocalization.exists_mk'_eq y.asIdeal.primeCompl d
      rw [← hrs, ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, hg, hg] at hd
      have hR := germ_injective_of_isIntegral X _ (fromSpec_mem hU y) hd
      have hss : ((s' * s : y.asIdeal.primeCompl) : Γ(X, U)) ∉ q.asIdeal :=
        fun h => (s' * s).2 (hqy h)
      have hu := (Scheme.mem_basicOpen X _ _ (fromSpec_mem hU q)).mp
        ((fromSpec_mem_basicOpen_iff hU _ q).mpr hss)
      have e := congrArg (X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q)) hR
      rw [map_mul, map_mul] at e
      refine ⟨X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) r' * ↑hu.unit⁻¹, ?_⟩
      calc X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) r' * ↑hu.unit⁻¹ *
            X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) r
          = X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) c *
            (X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) ↑(s' * s) * ↑hu.unit⁻¹) := by
            rw [← mul_assoc, ← e]; ring
        _ = X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) c := by
            rw [hu.mul_val_inv, mul_one]
  · obtain ⟨q', rfl⟩ := exists_fromSpec_eq hU (hw.mem_open U.isOpen (fromSpec_mem hU y))
    have hq'y : q'.asIdeal ≤ y.asIdeal := (fromSpec_specializes_iff hU q' y).mp hw
    refine ord_germ_eq_zero r ((fromSpec_mem_basicOpen_iff hU r q').mpr fun hrq' => hwz ?_)
    obtain ⟨hQp', hQc', hQh'⟩ := hloc q' hq'y hw1
    have hsQ' : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) (s : Γ(X, U)) ∉
        q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) :=
      fun h => hQp'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hsu)
    have hπQ' : π ∈ q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) := by
      have h := Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) hrq'
      rw [← hspec] at h
      exact (hQp'.mem_or_mem h).resolve_right hsQ'
    have : (q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).FiniteHeight :=
      Ideal.finiteHeight_iff_lt.mpr (Or.inr (lt_of_eq_of_lt hQh ENat.one_lt_top))
    have hle : q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) ≤
        q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) := by
      rw [hπ, Ideal.span_singleton_le_iff_mem]; exact hπQ'
    have heq := Ideal.eq_of_le_of_height_le _ hle (le_of_eq (hQh'.trans hQh.symm))
    have : q' = q := PrimeSpectrum.ext (by rw [← hQc', ← heq, hQc])
    rw [this]

/-- Weil divisors are locally principal at points with factorial stalks. -/
theorem exists_locally_principal {D : AlgebraicCycle X ℤ} (hD : D ∈ weilDivisors X) (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ f : X.functionField, f ≠ 0 ∧ ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ w ∈ V, D w = div X f w := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hxU
  obtain ⟨t, ht, hfin⟩ := D.supportLocallyFiniteWithinDomain' (hU.fromSpec y) (Set.mem_univ _)
  have hZ : {z : X | z ⤳ hU.fromSpec y ∧ D z ≠ 0}.Finite :=
    hfin.subset fun z hz => ⟨mem_of_mem_nhds ((specializes_iff_nhds.mp hz.1) ht), hz.2⟩
  have hr : ∀ z ∈ hZ.toFinset, ∃ r : Γ(X, U), r ≠ 0 ∧ ∀ w : X, w ⤳ hU.fromSpec y →
      coheight w = 1 → Scheme.ord (X.germToFunctionField U r) w = if w = z then 1 else 0 := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    exact exists_uniformizer hU y z hz.1 (hD z hz.2)
  choose! r hr0 hrord using hr
  have hne : ∀ z ∈ hZ.toFinset, X.germToFunctionField U (r z) ≠ 0 :=
    fun z hz => germToFunctionField_ne_zero (hr0 z hz)
  refine ⟨∏ z ∈ hZ.toFinset, X.germToFunctionField U (r z) ^ D z,
    Finset.prod_ne_zero_iff.mpr fun z hz => zpow_ne_zero _ (hne z hz), ?_⟩
  have hE : ∀ w, w ⤳ hU.fromSpec y →
      (D - div X (∏ z ∈ hZ.toFinset, X.germToFunctionField U (r z) ^ D z)) w = 0 := by
    intro w hw
    simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, div_apply]
    rw [sub_eq_zero]
    by_cases hw1 : coheight w = 1
    · rw [ord_prod_zpow _ _ _ hne, Finset.sum_congr rfl fun z hz => by rw [hrord z hz w hw hw1]]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      split_ifs with hwZ
      · rfl
      · by_contra h
        exact hwZ ((Set.Finite.mem_toFinset hZ).mpr ⟨hw, h⟩)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hw1]
      by_contra h
      exact hw1 (hD w h)
  obtain ⟨V, hV, hxV, hVE⟩ := exists_isOpen_eq_zero_of_specializes _ _ hE
  refine ⟨V, hV, hxV, fun w hw => ?_⟩
  have h := hVE w hw
  exact sub_eq_zero.mp h

end

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_IsogDegA_FF =====
section

/-!
# S4-IsogDegA, file FF: the function-field map of a dominant morphism and the degree (O2, O5)

For a dominant morphism `f : X ⟶ Y` of irreducible schemes, `f` sends the generic point to the
generic point, so the stalk map at the generic point gives `ffMap f : K(Y) ⟶ K(X)` (the pull-back
`f^*`). `degree f = [K(X) : f^* K(Y)]` for dominant `f` and `0` otherwise. It is multiplicative
on dominant pairs, `degree (𝟙 X) = 1`, and `degree = sepdeg * insepdeg` with `insepdeg = q ^ e`.
The algebra structure `ffAlgebra f` is never a global instance (endomorphisms have `X = Y`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- A dominant morphism of irreducible schemes sends the generic point to the generic point. -/
theorem map_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

/-- The pull-back of rational functions `K(Y) ⟶ K(X)` along a dominant morphism. -/
noncomputable def ffMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq (map_genericPoint f)) ≫
    f.stalkMap (genericPoint X)

theorem ffMap_id (X : Scheme.{u}) [IrreducibleSpace X] : ffMap (𝟙 X) = 𝟙 _ := by
  simp [ffMap]

theorem ffMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace Z] [IsDominant f] [IsDominant g] :
    ffMap (f ≫ g) = ffMap g ≫ ffMap f := by
  simp only [ffMap, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc, TopCat.Presheaf.stalkSpecializes_comp_assoc,
    Scheme.Hom.stalkMap_comp]
  rfl

/-- `K(X)` as a `K(Y)`-algebra through `f^*` (a `def`, never an instance). -/
noncomputable abbrev ffAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : Algebra Y.functionField X.functionField :=
  (ffMap f).hom.toAlgebra

/-- `[K(X) : f^* K(Y)]` for a dominant morphism. -/
noncomputable def degDom {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : ℕ :=
  @Module.finrank Y.functionField X.functionField _ _ (ffAlgebra f).toModule

open Classical in
/-- The degree: `[K(X) : f^* K(Y)]` for dominant `f`, and `0` otherwise. -/
noncomputable def degree {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] : ℕ :=
  if _h : IsDominant f then degDom f else 0

theorem degree_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : degree f = degDom f := by
  rw [degree]
  exact dif_pos ‹IsDominant f›

theorem degree_of_not_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] (hf : ¬ IsDominant f) : degree f = 0 := by
  rw [degree, dif_neg hf]

theorem degree_id (X : Scheme.{u}) [IsIntegral X] : degree (𝟙 X) = 1 := by
  rw [degree_of_isDominant, degDom]
  have h : (ffAlgebra (𝟙 X)) = Algebra.id _ := by
    apply Algebra.algebra_ext
    intro r
    simp [ffMap_id, RingHom.algebraMap_toAlgebra]
  rw [h]
  exact Module.finrank_self _

theorem isScalarTower_ffAlgebra {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z] [IsDominant f]
    [IsDominant g] :
    letI := ffAlgebra f; letI := ffAlgebra g; letI := ffAlgebra (f ≫ g)
    IsScalarTower Z.functionField Y.functionField X.functionField := by
  letI := ffAlgebra f; letI := ffAlgebra g; letI := ffAlgebra (f ≫ g)
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra, ffMap_comp, CommRingCat.hom_comp]

/-- Multiplicativity of the degree on dominant pairs. -/
theorem degree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] [IsDominant f] [IsDominant g] :
    degree (f ≫ g) = degree f * degree g := by
  rw [degree_of_isDominant, degree_of_isDominant, degree_of_isDominant, degDom, degDom, degDom,
    mul_comm]
  letI := ffAlgebra f; letI := ffAlgebra g; letI := ffAlgebra (f ≫ g)
  haveI := isScalarTower_ffAlgebra f g
  exact (Module.finrank_mul_finrank Z.functionField Y.functionField X.functionField).symm

/-- `deg = sepdeg * insepdeg` (L25, first half). -/
theorem degDom_eq_sep_mul_insep {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] :
    letI := ffAlgebra f
    degDom f = Field.finSepDegree Y.functionField X.functionField *
      Field.finInsepDegree Y.functionField X.functionField := by
  letI := ffAlgebra f
  rw [Field.finSepDegree_mul_finInsepDegree]
  rfl

/-- The inseparable degree is a power of the exponential characteristic (L25, second half). -/
theorem finInsepDegree_ffAlgebra_eq_pow {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] (q : ℕ) [ExpChar Y.functionField q] :
    letI := ffAlgebra f
    FiniteDimensional Y.functionField X.functionField →
      ∃ n, Field.finInsepDegree Y.functionField X.functionField = q ^ n := by
  letI := ffAlgebra f
  intro _
  exact _root_.finInsepDegree_eq_pow _ _ q

end RamanujanPetersson.IsogDegA

end



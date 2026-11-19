-- Prove2me | Definitions.Def_RPLib_S4_CDPack23
-- name    : RPLib_S4_CDPack23
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:23:05.632471+00:00
-- url     : https://prove2.me/theorems/1a766c21-9564-4aa6-b9a8-4b155be39d75
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 23 of 71
-- statement:
--   Part 23 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_Sep2`: The Jacobian (unit S4-JacComplete), part `Sep2` (separating elements; Mathlib only)
--   * `Def_RP_JacComplete_GenF`: The Jacobian (unit S4-JacComplete), part `GenF` (the synonym with coordinate `h`)
--   * `Def_RP_JacRRFam_G`: Riemann-Roch over an arbitrary field, part G: the local axioms for function fields over `K`
--   * `Def_RP_JacRRFam_B`: Riemann-Roch over an arbitrary constant field (S4-JacRRFam, part B)
--   * `Def_RP_JacRRFam_H`: Riemann-Roch over an arbitrary field, part H: the Riemann input and Riemann-Roch for function fields
--   * `Def_RP_JacRRFam_I`: Riemann-Roch over an arbitrary field, part I: the classical statements for function fields
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack17
import Definitions.Def_RPLib_S3_RRC
import Definitions.Def_RPLib_S3_RRB

/-!
# Curve-duality library package, part 23 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_Sep2`: The Jacobian (unit S4-JacComplete), part `Sep2` (separating elements; Mathlib only)
* `Def_RP_JacComplete_GenF`: The Jacobian (unit S4-JacComplete), part `GenF` (the synonym with coordinate `h`)
* `Def_RP_JacRRFam_G`: Riemann-Roch over an arbitrary field, part G: the local axioms for function fields over `K`
* `Def_RP_JacRRFam_B`: Riemann-Roch over an arbitrary constant field (S4-JacRRFam, part B)
* `Def_RP_JacRRFam_H`: Riemann-Roch over an arbitrary field, part H: the Riemann input and Riemann-Roch for function fields
* `Def_RP_JacRRFam_I`: Riemann-Roch over an arbitrary field, part I: the classical statements for function fields
-/

set_option autoImplicit false

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

/-- The new coordinate is `h`. -/
theorem genAlg_X : algebraMap K[X] (GenF K F h) X = genEquiv K F h h := by
  rw [genAlg_apply, aeval_X]

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

/-- The Weil differentials form a one-dimensional `F`-space: a nonzero `ω` and, for every Weil
differential `ω'`, a unique `x` with `ω' = x • ω`. -/
theorem weilDiff_one_dimK (hd : d.AxiomsK) :
    ∃ ω : Module.Dual K d.adeles, d.IsWeilDiff ω ∧ ω ≠ 0 ∧
      ∀ ω' : Module.Dual K d.adeles, d.IsWeilDiff ω' → ∃! x : F, ω' = d.wsmul x ω := by
  obtain ⟨ω, A, hA, hω⟩ := exists_weilDiff_ne_zeroK hd
  refine ⟨ω, ⟨A, hA⟩, hω, fun ω' ⟨A', hA'⟩ => ?_⟩
  obtain ⟨x, hx⟩ := exists_eq_wsmulK hd hA hA' hω
  refine ⟨x, hx, fun y hy => d.wsmulL_injective hω ?_⟩
  simp only [wsmulL_apply]
  rw [← hy, hx]

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

/-- `(x ω) = (x) + (ω)`. -/
theorem isCanonical_add_divK {W : ι →₀ ℤ} (hW : d.IsCanonical W) {x : F} (hx : x ≠ 0) :
    d.IsCanonical (W + d.div x) := by
  obtain ⟨ω, hω, hWω⟩ := hW
  refine ⟨d.wsmul x ω, fun h => hω ?_, fun D => ?_⟩
  · rw [← d.inv_wsmul_wsmul hx ω, h, wsmul_zero]
  · rw [d.wsmul_mem_Omega_iff hx, hWω, Finsupp.le_def, Finsupp.le_def]
    refine forall_congr' fun i => ?_
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply]
    omega

/-- Canonical divisors form one linear equivalence class. -/
theorem isCanonical_eq_add_divK (hd : d.AxiomsK) {W W' : ι →₀ ℤ} (hW : d.IsCanonical W)
    (hW' : d.IsCanonical W') : ∃ x : F, x ≠ 0 ∧ W' = W + d.div x := by
  obtain ⟨ω, hω, hWω⟩ := hW
  obtain ⟨ω', hω', hWω'⟩ := hW'
  obtain ⟨x, rfl⟩ := exists_eq_wsmulK hd ((hWω W).2 le_rfl) ((hWω' W').2 le_rfl) hω
  have hx : x ≠ 0 := by rintro rfl; exact hω' (d.zero_wsmul ω)
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · have h := (hWω' W').2 le_rfl
    rw [d.wsmul_mem_Omega_iff hx, hWω] at h
    rw [Finsupp.le_def] at h ⊢
    intro i; have := h i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply] at this ⊢
    omega
  · have h : W + d.div x - d.div x ≤ W := by rw [add_sub_cancel_right]
    rw [← hWω, ← d.wsmul_mem_Omega_iff hx, hWω'] at h
    exact h

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

/-- `ℓ D ≤ deg D + ℓ 0` for `deg D ≥ 0` (`ℓ D ≤ deg D + 1` for constant field `K`). -/
theorem ell_le_degD_addK (hd : d.AxiomsK) {D : ι →₀ ℤ} (hD : 0 ≤ d.degD D) :
    (d.ell D : ℤ) ≤ d.degD D + d.ell 0 := by
  rcases Nat.eq_zero_or_pos (d.ell D) with h | h
  · rw [h]; have := Nat.zero_le (d.ell 0); omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_posK h
  have hnn : 0 ≤ D + d.div z := by rw [add_comm]; exact (d.mem_LD_iff_div hz0).1 hz
  have := (ell_sub_leK hd.1 hnn).1
  rw [d.ell_add_div hz0, degD_add, hd.deg_div z hz0, degD_zero] at this
  linarith

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

/-- A place of degree one forces `ℓ(0) = 1`. -/
theorem ellFK_zero_of_deg_one {P : Places.Place K F} (hP : P.deg = 1) : ellFK K F 0 = 1 :=
  ellFK_zero_of_bot (PlacesK.constField_eq_bot_of_deg_one K F hP)

theorem ellFK_eq_zero_of_deg_neg {D : Places.Divisor K F} (hD : D.deg < 0) : ellFK K F D = 0 :=
  Data.ell_eq_zero_of_degD_negK ffDataK_axioms hD

/-- The index formula `dim_K A / (A(D) + F) = ℓ D - deg D + γ`. -/
theorem cd_adelesFK (D : Places.Divisor K F) :
    cd ((ffDataK K F).AD D ⊔ (ffDataK K F).Fs) (ffDataK K F).adeles = ((ffDataK K F).iota D : ℕ∞) :=
  Data.cd_adelesK ffDataK_axioms D

theorem genusFK_eq_iota : genusFK K F = (ffDataK K F).iota 0 := rfl

/-- The Weil differentials form a one-dimensional `F`-vector space. -/
theorem weilDiffFK_one_dim :
    ∃ ω : Module.Dual K (ffDataK K F).adeles, (ffDataK K F).IsWeilDiff ω ∧ ω ≠ 0 ∧
      ∀ ω' : Module.Dual K (ffDataK K F).adeles, (ffDataK K F).IsWeilDiff ω' →
        ∃! x : F, ω' = (ffDataK K F).wsmul x ω :=
  Data.weilDiff_one_dimK ffDataK_axioms

theorem exists_isCanonicalFK : ∃ W : Places.Divisor K F, IsCanonicalFK K F W :=
  Data.exists_isCanonicalK ffDataK_axioms

/-- Canonical divisors form one linear equivalence class. -/
theorem isCanonicalFK_eq_add_div {W W' : Places.Divisor K F} (hW : IsCanonicalFK K F W)
    (hW' : IsCanonicalFK K F W') : ∃ x : F, x ≠ 0 ∧ W' = W + PlacesK.div x := by
  obtain ⟨x, hx, h⟩ := Data.isCanonical_eq_add_divK ffDataK_axioms hW hW'
  exact ⟨x, hx, by rw [h, ffDataK_div]⟩

theorem isCanonicalFK_add_div {W : Places.Divisor K F} (hW : IsCanonicalFK K F W) {x : F}
    (hx : x ≠ 0) : IsCanonicalFK K F (W + PlacesK.div x) := by
  have := Data.isCanonical_add_divK (d := ffDataK K F) hW hx
  rwa [ffDataK_div] at this

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

/-- `ℓ(W) = g`. -/
theorem ellFK_canonical {W : Places.Divisor K F} (hW : IsCanonicalFK K F W) :
    ellFK K F W = genusFK K F :=
  Data.ell_canonicalK ffDataK_axioms hW

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

/-- `ℓ(D) ≤ deg D + 1` for `deg D ≥ 0`. -/
theorem ellFK_le {D : Places.Divisor K F} (hD : 0 ≤ D.deg) : (ellFK K F D : ℤ) ≤ D.deg + 1 := by
  have h1 := ellFK_zero_of_bot hk
  simp only [ellFK] at h1
  have := Data.ell_le_degD_addK ffDataK_axioms (D := D) hD
  rw [h1] at this
  exact_mod_cast this

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

theorem poleBK_inl (P : HeightOneSpectrum (Places.Rfin K F)) : poleBK K F (Sum.inl P) = 0 := by
  have hv : ffv K F (Sum.inl P) (xF K F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zeroK
  rw [poleBK, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffDataK_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_right.2 ((log_nonpos_iff' hv).2 (ffv_xF_inlK P))

theorem poleBK_inr (P : HeightOneSpectrum (Places.Rinf K F)) :
    poleBK K F (Sum.inr P) = log (P.valuation F (xF K F)) := by
  have hv : ffv K F (Sum.inr P) (xF K F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zeroK
  rw [poleBK, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffDataK_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_left.2 ((log_nonneg_iff' hv).2 (one_le_ffv_xF_inrK P))

/-- `L(n B) = Rfin ∩ x ^ n Rinf` for the pole divisor `B` of `x`. -/
theorem mem_LFK_poleB (n : ℕ) (f : F) :
    f ∈ LFK K F (n • poleBK K F) ↔ f ∈ (algebraMap (Places.Rfin K F) F).range ∧
      f * (xF K F)⁻¹ ^ n ∈ (algebraMap (Places.Rinf K F) F).range := by
  rw [mem_range_iff_valuation_le_oneK, mem_range_iff_valuation_le_oneK, Data.mem_LD, Sum.forall]
  refine and_congr (forall_congr' fun P => ?_) (forall_congr' fun P => ?_)
  · rw [Finsupp.smul_apply, poleBK_inl, smul_zero, exp_zero]; rfl
  · have hv : P.valuation F (xF K F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zeroK
    obtain ⟨k, hk⟩ : ∃ k : ℤ, P.valuation F (xF K F) = exp k := ⟨_, (exp_log hv).symm⟩
    show P.valuation F f ≤ _ ↔ _
    rw [Finsupp.smul_apply, poleBK_inr, hk, log_exp, map_mul, map_pow, map_inv₀, hk, ← exp_neg,
      ← exp_nsmul, mul_comm, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_mul_le_exp_iff, smul_neg,
      sub_neg_eq_add, zero_add]

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

/-- `F' / L` is the constant field extension `L F` of `F / K` for a FINITE extension `L / K` (any
fields), in coordinates: for a `K`-basis `c` of `L`, the `c j` form an `F`-basis of `F'`, both rings
of integers are spanned coordinatewise (`Rfin L F' = L ⊗ Rfin K F`, `Rinf L F' = L ⊗ Rinf K F`, which
holds for separable `L / K`), and the separating element `x` is kept. -/
structure IsConstExtK {ι : Type*} [Fintype ι] (c : Module.Basis ι K L) : Prop where
  linearIndependent : LinearIndependent F fun j => algebraMap L F' (c j)
  span : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j))
  xF_eq : algebraMap F F' (xF K F) = xF L F'
  fin : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap (Places.Rfin L F') F').range ↔
    ∀ j, f j ∈ (algebraMap (Places.Rfin K F) F).range
  inf : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap (Places.Rinf L F') F').range ↔
    ∀ j, f j ∈ (algebraMap (Places.Rinf K F) F).range

variable {K L}
variable {ι : Type*} [Fintype ι]

/-- The coordinate map `(f_j) ↦ Σ f_j c_j`. -/
noncomputable def coordMapK (c : Module.Basis ι K L) : (ι → F) →ₗ[K] F' where
  toFun f := ∑ j, f j • algebraMap L F' (c j)
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.smul_sum, smul_assoc]

variable {F F'}
variable {c : Module.Basis ι K L}

theorem coordMapK_apply (f : ι → F) : coordMapK F F' c f = ∑ j, f j • algebraMap L F' (c j) := rfl

theorem IsConstExtK.mem_LFK_iff (h : IsConstExtK K F L F' c) (n : ℕ) (f : ι → F) :
    coordMapK F F' c f ∈ LFK L F' (n • poleBK L F') ↔ ∀ j, f j ∈ LFK K F (n • poleBK K F) := by
  simp only [mem_LFK_poleB, coordMapK_apply]
  rw [h.fin, ← h.xF_eq]
  have e : (∑ j, f j • algebraMap L F' (c j)) * (algebraMap F F' (xF K F))⁻¹ ^ n =
      ∑ j, (f j * (xF K F)⁻¹ ^ n) • algebraMap L F' (c j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, map_inv₀]; ring
  rw [e, h.inf, forall_and]

/-- The coordinate isomorphism `L(D)^ι ≃ L'(D')` (over `K`). -/
noncomputable def IsConstExtK.psi (_h : IsConstExtK K F L F' c) {D : Places.Divisor K F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMapK F F' c f ∈ LFK L F' D' ↔ ∀ j, f j ∈ LFK K F D) :
    (ι → LFK K F D) →ₗ[K] LFK L F' D' where
  toFun f := ⟨coordMapK F F' c fun j => (f j : F), (hD _).2 fun j => (f j).2⟩
  map_add' f g := Subtype.ext (by
    simp only [Pi.add_apply, Submodule.coe_add]
    exact map_add (coordMapK F F' c) (fun j => (f j : F)) fun j => (g j : F))
  map_smul' a f := Subtype.ext (by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply]
    exact map_smul (coordMapK F F' c) a fun j => (f j : F))

theorem IsConstExtK.psi_bijective (h : IsConstExtK K F L F' c) {D : Places.Divisor K F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMapK F F' c f ∈ LFK L F' D' ↔ ∀ j, f j ∈ LFK K F D) :
    Function.Bijective (h.psi hD) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : coordMapK F F' c (fun j => (f j : F)) = 0 := congrArg Subtype.val hf
    rw [coordMapK_apply] at h0
    funext j
    exact Subtype.ext (Fintype.linearIndependent_iff.1 h.linearIndependent _ h0 j)
  · intro y
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun F).1
      (h.span (Submodule.mem_top (x := (y : F'))))
    have hgy : coordMapK F F' c g = y := hg
    have hmem := (hD g).1 (by rw [hgy]; exact y.2)
    exact ⟨fun j => ⟨g j, hmem j⟩, Subtype.ext hgy⟩

/-- **Invariance of `ℓ` under (finite, separable) constant field extension over any field**:
`ℓ'(D') = ℓ(D)` whenever `L'(D') = L ⊗ L(D)` coordinatewise. -/
theorem IsConstExtK.ellFK_eq (h : IsConstExtK K F L F' c) {D : Places.Divisor K F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMapK F F' c f ∈ LFK L F' D' ↔ ∀ j, f j ∈ LFK K F D) :
    ellFK L F' D' = ellFK K F D := by
  have := finiteDimensional_LFK (K := K) (F := F) D
  have : Module.Finite K L := Module.Finite.of_basis c
  have e1 := (LinearEquiv.ofBijective (h.psi hD) (h.psi_bijective hD)).finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Module.finrank_mul_finrank K L (LFK L F' D'), ← Module.finrank_eq_card_basis c] at e1
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos e1).symm

/-- `ℓ'(n B') = ℓ(n B)` for the pole divisors of `x` in the constant field extension. -/
theorem IsConstExtK.ellFK_poleB (h : IsConstExtK K F L F' c) (n : ℕ) :
    ellFK L F' (n • poleBK L F') = ellFK K F (n • poleBK K F) :=
  h.ellFK_eq (h.mem_LFK_iff n)

theorem IsConstExtK.ellFK_zero (h : IsConstExtK K F L F' c) : ellFK L F' 0 = ellFK K F 0 := by
  simpa using h.ellFK_poleB 0

/-- **Invariance of the genus under constant field extension** (together with `deg B' = deg B`). -/
theorem IsConstExtK.genusFK_eq_and (h : IsConstExtK K F L F' c) :
    genusFK L F' = genusFK K F ∧ (poleBK L F').deg = (poleBK K F).deg := by
  have ha : 0 < (poleBK K F).deg := degD_poleBK_pos
  have ha' : 0 < (poleBK L F').deg := degD_poleBK_pos
  have ha1 : (1 : ℤ) ≤ (poleBK K F).deg := by omega
  have ha1' : (1 : ℤ) ≤ (poleBK L F').deg := by omega
  have h0 := h.ellFK_zero
  have key : ∀ m : ℕ, 2 * (genusFK K F + genusFK L F') + 1 ≤ m →
      ((ellFK K F (m • poleBK K F) : ℤ) = m * (poleBK K F).deg + ellFK K F 0 - genusFK K F) ∧
      ((ellFK K F (m • poleBK K F) : ℤ) = m * (poleBK L F').deg + ellFK K F 0 - genusFK L F') := by
    intro m hm
    have hm' : (2 * ((genusFK K F : ℤ) + genusFK L F') + 1 : ℤ) ≤ m := by exact_mod_cast hm
    have hg : (0 : ℤ) ≤ genusFK K F := by positivity
    have hg' : (0 : ℤ) ≤ genusFK L F' := by positivity
    have h00 : (0 : ℤ) ≤ ellFK K F 0 := by positivity
    have h00' : (0 : ℤ) ≤ ellFK L F' 0 := by positivity
    have hma : (m : ℤ) * 1 ≤ m * (poleBK K F).deg := mul_le_mul_of_nonneg_left ha1 (by positivity)
    have hma' : (m : ℤ) * 1 ≤ m * (poleBK L F').deg := mul_le_mul_of_nonneg_left ha1' (by positivity)
    refine ⟨?_, ?_⟩
    · have := Data.ell_eq_of_large_degDK (ffDataK_axioms (K := K) (F := F))
        (D := m • poleBK K F) (by
          rw [Data.degD_nsmul, ffDataK_degD]
          change 2 * ((genusFK K F : ℕ) : ℤ) - 2 * ((ellFK K F 0 : ℕ) : ℤ) < _
          linarith)
      rw [Data.degD_nsmul, ffDataK_degD] at this
      exact this
    · have := Data.ell_eq_of_large_degDK (ffDataK_axioms (K := L) (F := F'))
        (D := m • poleBK L F') (by
          rw [Data.degD_nsmul, ffDataK_degD]
          change 2 * ((genusFK L F' : ℕ) : ℤ) - 2 * ((ellFK L F' 0 : ℕ) : ℤ) < _
          linarith)
      rw [Data.degD_nsmul, ffDataK_degD] at this
      change ((ellFK L F' (m • poleBK L F') : ℕ) : ℤ) = _ + ((ellFK L F' 0 : ℕ) : ℤ) -
        ((genusFK L F' : ℕ) : ℤ) at this
      rw [h.ellFK_poleB m, h0] at this
      exact this
  obtain ⟨h1, h3⟩ := key _ le_rfl
  obtain ⟨h2, h4⟩ := key _ (Nat.le_succ _)
  push_cast at h1 h2 h3 h4
  have haa : (poleBK K F).deg = (poleBK L F').deg := by linear_combination h1 - h2 - h3 + h4
  refine ⟨?_, haa.symm⟩
  have : (genusFK K F : ℤ) = genusFK L F' := by
    linear_combination h1 - h3 + (2 * ((genusFK K F : ℤ) + genusFK L F') + 1) * haa
  exact_mod_cast this.symm

theorem IsConstExtK.genusFK_eq (h : IsConstExtK K F L F' c) : genusFK L F' = genusFK K F :=
  h.genusFK_eq_and.1

theorem IsConstExtK.deg_poleBK (h : IsConstExtK K F L F' c) :
    (poleBK L F').deg = (poleBK K F).deg :=
  h.genusFK_eq_and.2

/-- A full constant field stays full under constant field extension. -/
theorem IsConstExtK.constField_eq_bot (h : IsConstExtK K F L F' c)
    (hk : Places.constField K F = ⊥) : Places.constField L F' = ⊥ := by
  have h1 : ellFK L F' 0 = 1 := by rw [h.ellFK_zero]; exact ellFK_zero_of_bot hk
  rw [RamanujanPetersson.RR.ellFK_zero] at h1
  exact IntermediateField.finrank_eq_one_iff.1 h1

end ConstantFieldExtensionK

end RamanujanPetersson.RR

end



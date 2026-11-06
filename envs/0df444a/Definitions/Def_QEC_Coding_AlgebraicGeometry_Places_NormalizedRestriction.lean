-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
-- name    : QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:10:35.660081+00:00
-- url     : https://prove2.me/theorems/5348a9dc-3b6b-4f5a-984e-3bf423c9fcac
-- title:
--   Normalized Restriction
-- statement:
--   Definitions and structural lemmas for Normalized Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedRestriction.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.FieldTheory.Finite.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer

set_option autoImplicit false
open MonoidWithZeroHom
open scoped WithZero
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
noncomputable section
variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
omit [Algebra k F] in
/-- A nontrivial place stays nontrivial on an algebraic subfield. A
trivial restriction would make an ambient uniformizer transcendental. -/
theorem comap_isNontrivial [Algebra.IsAlgebraic F E] (Q : GlobalPlace k E) :
    (Q.valuation.comap (algebraMap F E)).IsNontrivial := by
  by_contra hn
  letI : Q.valuation.IsTrivialOn F := ⟨fun x hx => by
    by_contra hv
    apply hn
    refine ⟨x, ?_, hv⟩
    exact Q.valuation.ne_zero_iff.mpr (by
      simpa only [map_zero] using (algebraMap F E).injective.ne hx)⟩
  have hu0 : Q.uniformizer ≠ 0 := by
    apply Q.valuation.ne_zero_iff.mp
    rw [Q.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hu1 : Q.valuation Q.uniformizer ≠ 1 := by
    rw [Q.valuation_uniformizer]
    norm_num
  exact (Q.valuation.transcendental_of_ne_one F Q.uniformizer hu0 hu1)
    (Algebra.IsAlgebraic.isAlgebraic Q.uniformizer)
def normalize (v : Valuation F ℤᵐ⁰) [v.IsNontrivial] : GlobalPlace k F := by
  letI : v.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' v
  let e := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
  let hm := e.strictMono
  exact
    { valuation := v.restrict.map e.toMonoidWithZeroHom hm.monotone
      normalized := e.surjective.comp
        (ValueGroup₀.restrict₀_surjective (MonoidWithZeroHom.ofClass v)) }
theorem normalize_valuationRing (v : Valuation F ℤᵐ⁰) [v.IsNontrivial] :
    (normalize (k := k) v).valuationRing = v.valuationSubring := by
  letI : v.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' v
  let e := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
  have hm := e.strictMono
  ext x
  change e (v.restrict x) ≤ 1 ↔ v x ≤ 1
  have he1 : e 1 = 1 := map_one e
  nth_rw 1 [← he1]
  exact hm.le_iff_le.trans (v.restrict_le_one_iff (x := x))
theorem normalize_valuation_lt_one_iff
    (v : Valuation F ℤᵐ⁰) [v.IsNontrivial] (x : F) :
    (normalize (k := k) v).valuation x < 1 ↔ v x < 1 := by
  letI : v.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' v
  let e := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
  have hm := e.strictMono
  change e (v.restrict x) < 1 ↔ v x < 1
  have he1 : e 1 = 1 := map_one e
  nth_rw 1 [← he1]
  exact hm.lt_iff_lt.trans (v.restrict_lt_one_iff (x := x))
def restrict [Algebra.IsAlgebraic F E] (Q : GlobalPlace k E) : GlobalPlace k F := by
  letI := Q.comap_isNontrivial (F := F)
  exact normalize (Q.valuation.comap (algebraMap F E))
theorem restrict_valuationRing [Algebra.IsAlgebraic F E] (Q : GlobalPlace k E) :
    (Q.restrict (F := F)).valuationRing =
      (Q.valuation.comap (algebraMap F E)).valuationSubring := by
  letI := Q.comap_isNontrivial (F := F)
  exact normalize_valuationRing _
theorem restrict_valuation_lt_one_iff [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E) (x : F) :
    (Q.restrict (F := F)).valuation x < 1 ↔ Q.valuation (algebraMap F E x) < 1 := by
  letI := Q.comap_isNontrivial (F := F)
  exact normalize_valuation_lt_one_iff _ x
def restrictValuationRingMap [Algebra.IsAlgebraic F E] (Q : GlobalPlace k E) :
    (Q.restrict (F := F)).valuationRing →+* Q.valuationRing :=
  ((algebraMap F E).comp (Q.restrict (F := F)).valuationRing.subtype).codRestrict
    Q.valuationRing fun a => by
      exact (show (Q.restrict (F := F)).valuationRing ≤
          (Q.valuation.comap (algebraMap F E)).valuationSubring from
        le_of_eq Q.restrict_valuationRing) a.property
instance restrictValuationRingMap_isLocalHom [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E) : IsLocalHom (Q.restrictValuationRingMap (F := F)) where
  map_nonunit a ha := by
    by_contra hn
    have hlt : (Q.restrict (F := F)).valuation (a : F) < 1 :=
      (Q.restrict (F := F)).valuation.mem_maximalIdeal_iff.mp hn
    have hlt' := (Q.restrict_valuation_lt_one_iff (a : F)).mp hlt
    have hnon : Q.restrictValuationRingMap a ∈ IsLocalRing.maximalIdeal Q.valuationRing :=
      Q.valuation.mem_maximalIdeal_iff.mpr hlt'
    exact hnon ha
end
end QEC.Coding.AlgebraicGeometry.GlobalPlace



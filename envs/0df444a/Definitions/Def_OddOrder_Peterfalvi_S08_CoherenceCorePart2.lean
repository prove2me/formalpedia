-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart2
-- name    : OddOrder_Peterfalvi_S08_CoherenceCorePart2
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:31:01.209611+00:00
-- url     : https://prove2.me/theorems/e9ad2f63-da4c-49d0-a2f1-99ad93586a45
-- title:
--   Peterfalvi §8: normalized degree gaps
-- statement:
--   Generic normalized-degree and common-index divisibility lemmas used in the §8 adjoining steps of Peterfalvi, *Character Theory for the Odd Order Theorem*.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceCorePart2.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceCorePart2.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart2_SibleyBounds

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-- **(T8.11m) normalized degree gap from an absolute degree bound.**

If the new character and the prefix member family have natural degree ratios against the same
anchor `χ₁`, then the absolute §6.6 inequality
`2 * χ(1) * χ₁(1) < ∑ χmem(j)(1)^2` is equivalent, after dividing by the positive square
`χ₁(1)^2`, to the normalized `XAdjoinStepInput.hDeg` inequality
`2 * a < ∑ deg(j)^2`. -/
theorem normalizedDegreeGap_of_realDegreeBound
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a : ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hAbs : 2 *
        ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 := by
  classical
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  have hd₁real_pos : 0 < (d₁ : ℝ) := by exact_mod_cast hd₁pos
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re =
        (a : ℝ) * (d₁ : ℝ) := by
    have h := congrArg Complex.re hχdeg
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hmemre : ∀ i ∈ s,
      (OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re =
        (deg i : ℝ) * (d₁ : ℝ) := by
    intro i hi
    have h := congrArg Complex.re (hmemdeg i hi)
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hleft :
      2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) =
        (2 * (a : ℝ)) * (d₁ : ℝ) ^ 2 := by
    rw [hχre, hχ₁re]
    ring
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, (((deg i : ℝ) * (d₁ : ℝ)) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmemre i hi]
      _ = ∑ i ∈ s, ((deg i : ℝ) ^ 2 * (d₁ : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
            rw [← Finset.sum_mul]
  rw [hleft, hright] at hAbs
  have hd₁sq_pos : 0 < (d₁ : ℝ) ^ 2 := sq_pos_of_pos hd₁real_pos
  nlinarith

/-- **(T8.11n1) real absolute degree bound from common-index p-power data.**

This variant of `realDegreeBound_of_natDegreeSumPrimePowerGap` uses the actual §6.6
common-index data instead of asking the caller to name a quotient `q` with
`dχ = q * d₁`.  The strict gap comes from
`two_mul_lt_sq_of_commonIndex_primePower_gap`; square-divisibility then pushes it to
the prefix degree sum. -/
theorem realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_commonIndex_primePower_gap
        hp hidxpos hd₁ hdχ hθ₁ hθχ hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11o1) normalized degree gap from common-index p-power data.**

Combines `realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`.  This is the consumer form used by the
common-index step constructors after the quotient `q` has been removed from their input data. -/
theorem normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos)

end OddOrder.Peterfalvi.S08



-- Prove2me | Definitions.Def_RPLib_S3_DWSOFB
-- name    : RPLib_S3_DWSOFB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:15:35.30508+00:00
-- url     : https://prove2.me/theorems/cb8007e9-b439-4d02-b0d0-a99b725f726f
-- title:
--   Weight-two Ramanujan-Petersson library: the ordinary mass lower bound (D, part 2)
-- statement:
--   The ordinary mass lower bound (D, part 2).
--
--   * `jW W = c₄³/Δ`; `jW_mem_of_hasseA`, **`jW_mem_jSet`** : `p ∣ a_W ⇒ j(W) ∈ jSet p` (general-`W` copies of
--     `SS_HasseC.jv_mem_of_hasseA` / `SS_Super.jv_mem_jSet`).
--   * `card_ss_le` : `#{W : Δ ≠ 0, p ∣ a_W} ≤ (deg HZ_p + 2) Kj q⁴`.
--   * **`card_ord_ge`** : `q⁵ - K_p q⁴ ≤ #{W : Δ ≠ 0, p ∤ a_W}`.
--   * **`sum_card_WT`** : `Σ_{|t| ≤ B, p ∤ t} #WT F t = #{W : Δ ≠ 0, p ∤ a_W}` for `B ≥ 2q` (Hasse).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOFA
import Definitions.Def_RPLib_S3_SSSuper

/-!
# S3-DWS-Ordinary, part FB: the ordinary mass lower bound (D, part 2)

* `jW W = c₄³/Δ`; `jW_mem_of_hasseA`, **`jW_mem_jSet`** : `p ∣ a_W ⇒ j(W) ∈ jSet p` (general-`W` copies of
  `SS_HasseC.jv_mem_of_hasseA` / `SS_Super.jv_mem_jSet`).
* `card_ss_le` : `#{W : Δ ≠ 0, p ∣ a_W} ≤ (deg HZ_p + 2) Kj q⁴`.
* **`card_ord_ge`** : `q⁵ - K_p q⁴ ≤ #{W : Δ ≠ 0, p ∤ a_W}`.
* **`sum_card_WT`** : `Σ_{|t| ≤ B, p ∤ t} #WT F t = #{W : Δ ≠ 0, p ∤ a_W}` for `B ≥ 2q` (Hasse).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve RPLib

namespace RamanujanPetersson.S3.DWSO

open RamanujanPetersson.S3.DWSS

section J

variable {F : Type} [Field F]

/-- `j = c₄³/Δ` for any Weierstrass curve. -/
noncomputable def jW (W : WeierstrassCurve F) : F := W.c₄ ^ 3 / W.Δ

theorem jW_mem_of_hasseA (p : ℕ) [Fact p.Prime] [CharP F p] {W : WeierstrassCurve F} (hD : W.Δ ≠ 0)
    (hA : hasseA p W = 0) :
    jW W = 0 ∨ jW W = 1728 ∨ ∃ t, (HF F p).eval t = 0 ∧ jW W = 1728 + 1 / t := by
  by_cases j0 : jW W = 0
  · exact Or.inl j0
  by_cases j1 : jW W = 1728
  · exact Or.inr (Or.inl j1)
  refine Or.inr (Or.inr ⟨(jW W - 1728)⁻¹, ?_, by rw [one_div, inv_inv]; ring⟩)
  set t := (jW W - 1728)⁻¹ with ht_def
  have ht' : t * (jW W - 1728) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr j1)
  have ht : t ≠ 0 := inv_ne_zero (sub_ne_zero.mpr j1)
  have h1 : 1 + 1728 * t ≠ 0 := by
    intro h; apply j0
    have : jW W * t = 0 := by linear_combination ht' + h
    exact (mul_eq_zero.mp this).resolve_right ht
  have : (Et t).IsElliptic := ⟨by rw [Et_Δ]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero ht (pow_ne_zero 2 h1))⟩
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hD⟩
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hj : (W.map (algebraMap F (AlgebraicClosure F))).j =
      ((Et t).map (algebraMap F (AlgebraicClosure F))).j := by
    rw [map_j, map_j]
    congr 1
    rw [j_eq_div W, j_eq_div (Et t), Et_c₄, Et_Δ, eq_div_iff (mul_ne_zero ht (pow_ne_zero 2 h1))]
    have e : W.c₄ ^ 3 / W.Δ = jW W := rfl
    rw [e]
    linear_combination (1 + 1728 * t) ^ 2 * ht'
  obtain ⟨V, hV⟩ := exists_variableChange_of_j_eq _ _ hj
  have hL : hasseA p ((Et t).map (algebraMap F (AlgebraicClosure F))) = 0 := by
    rw [← hV, hasseA_variableChange_eq_zero, hasseA_map, hA, map_zero]
  rw [hasseA_map, map_eq_zero] at hL
  rw [← hasseA_Et]; exact hL

variable [Fintype F] [DecidableEq F]

/-- **Supersingular `j`.** Over `F_{p^m}`, `p ∣ a_W` puts `j(W)` in `jSet p`. -/
theorem jW_mem_jSet (p : ℕ) [Fact p.Prime] [CharP F p] {m : ℕ} (hq : Fintype.card F = p ^ m)
    {W : WeierstrassCurve F} (hD : W.Δ ≠ 0) (h : (p : ℤ) ∣ EllFq.trace W) : jW W ∈ jSet (F := F) p := by
  have hp : p.Prime := Fact.out
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hD⟩
  rcases hp.eq_two_or_odd with h2 | hpo
  · subst h2
    have hF : ringChar F = 2 := ringChar.eq F 2
    have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
    have ha : W.a₁ = 0 := by
      by_contra ha
      have hP := two_dvd_numPoints hF W ha
      obtain ⟨n, -, hn⟩ := FiniteField.card F 2
      have hq2 : 2 ∣ Nat.card F := by
        rw [Nat.card_eq_fintype_card, hn]; exact dvd_pow_self 2 n.ne_zero
      rw [EllFq.trace] at h
      omega
    have hc : W.c₄ = 0 := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, ha]
      linear_combination (8 * W.a₂ ^ 2 - 24 * W.a₄) * h2F
    simp [jW, jSet, hc]
  · have hp2 : p ≠ 2 := by omega
    have hA := hasseA_eq_zero_of_dvd_trace p hp2 hq W h
    rcases jW_mem_of_hasseA p hD hA with h0 | h1 | ⟨t, ht, hj⟩
    · simp [jSet, h0]
    · simp [jSet, h1]
    · rw [hj]; unfold jSet
      apply Finset.mem_union_right
      apply Finset.mem_image_of_mem
      rw [Multiset.mem_toFinset, mem_roots (HF_ne_zero p hpo)]; exact ht

/-- `#{W : Δ ≠ 0, p ∣ a_W} ≤ (deg HZ_p + 2) Kj q⁴`. -/
theorem card_ss_le (p : ℕ) [Fact p.Prime] [CharP F p] {m : ℕ} (hq : Fintype.card F = p ^ m) :
    (Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ (p : ℤ) ∣ EllFq.trace W)).card ≤
      ((HZ p).natDegree + 2) * (Kj * Fintype.card F ^ 4) := by
  classical
  have hsub : Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ (p : ℤ) ∣ EllFq.trace W) ⊆
      (jSet (F := F) p).biUnion
        (fun j₀ => Finset.univ.filter (fun W : WeierstrassCurve F => W.c₄ ^ 3 = j₀ * W.Δ)) := by
    intro W hW
    rw [Finset.mem_filter] at hW
    rw [Finset.mem_biUnion]
    refine ⟨jW W, jW_mem_jSet p hq hW.2.1 hW.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [jW, div_mul_cancel₀ _ hW.2.1]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum (fun j₀ _ => card_j_le j₀)).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_jSet_le p)

end J

/-- The constant of the ordinary mass bound. -/
noncomputable def Kp (p : ℕ) : ℕ := Wu.Δ.totalDegree + ((HZ p).natDegree + 2) * Kj

section Mass

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`q⁵ - K_p q⁴ ≤ #{W : Δ ≠ 0, p ∤ a_W}`.** -/
theorem card_ord_ge (p : ℕ) [Fact p.Prime] [CharP F p] {m : ℕ} (hq : Fintype.card F = p ^ m) :
    (Fintype.card F : ℤ) ^ 5 - Kp p * (Fintype.card F : ℤ) ^ 4 ≤
      (Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ EllFq.trace W)).card := by
  classical
  set A := Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ = 0) with hA
  set B := Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ (p : ℤ) ∣ EllFq.trace W) with hB
  set C := Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ EllFq.trace W) with hC
  have hU : (Finset.univ : Finset (WeierstrassCurve F)) ⊆ (A ∪ B) ∪ C := by
    intro W _
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hD : W.Δ = 0
    · exact Or.inl (Or.inl hD)
    · by_cases hp : (p : ℤ) ∣ EllFq.trace W
      · exact Or.inl (Or.inr ⟨hD, hp⟩)
      · exact Or.inr ⟨hD, hp⟩
  have hc := (Finset.card_le_card hU).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [Finset.card_univ, card_weierstrass] at hc
  have hc' : (Fintype.card F : ℤ) ^ 5 ≤ (A.card : ℤ) + B.card + C.card := by exact_mod_cast hc
  have h1 : (A.card : ℤ) ≤ Wu.Δ.totalDegree * (Fintype.card F : ℤ) ^ 4 := by
    exact_mod_cast card_Δ_zero_le (F := F)
  have h2 : (B.card : ℤ) ≤ ((HZ p).natDegree + 2) * (Kj * (Fintype.card F : ℤ) ^ 4) := by
    exact_mod_cast card_ss_le p hq
  unfold Kp
  push_cast
  linarith

/-- **Hasse range.** `Σ_{|t| ≤ B, p ∤ t} #WT F t = #{W : Δ ≠ 0, p ∤ a_W}` once `2q ≤ B`. -/
theorem sum_card_WT (p : ℕ) (B : ℤ) (hB : 2 * (Fintype.card F : ℤ) ≤ B) :
    ∑ t ∈ (Finset.Icc (-B) B).filter (fun t => ¬ (p : ℤ) ∣ t), (Nat.card (WT F t) : ℚ) =
      (Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ EllFq.trace W)).card := by
  have hmaps : ∀ W ∈ Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ EllFq.trace W),
      EllFq.trace W ∈ (Finset.Icc (-B) B).filter (fun t => ¬ (p : ℤ) ∣ t) := by
    intro W hW
    rw [Finset.mem_filter] at hW
    have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW.2.1⟩
    have h := RPLib.Hasse.trace_sq_le_four_mul W
    rw [← Nat.card_eq_fintype_card (α := F)] at h
    have hq1 : (1 : ℤ) ≤ Nat.card F := by exact_mod_cast Nat.card_pos (α := F)
    have h4 : EllFq.trace W ^ 2 ≤ (2 * (Nat.card F : ℤ)) ^ 2 := by
      rw [EllFq.trace, EllFq.numPoints]; nlinarith
    obtain ⟨hl, hr⟩ := abs_le_of_sq_le_sq' h4 (by positivity)
    rw [Nat.card_eq_fintype_card] at hl hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by linarith, by linarith⟩, hW.2.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_filter] at ht
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  congr 2
  apply Finset.filter_congr
  intro W _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ ht.2⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩

end Mass

end RamanujanPetersson.S3.DWSO



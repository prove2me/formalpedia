-- Prove2me | Definitions.Def_RPLib_S3_DWSOFA
-- name    : RPLib_S3_DWSOFA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:13:27.071733+00:00
-- url     : https://prove2.me/theorems/bf049d8d-7cc4-4ecb-9c30-3b0ac9312ded
-- title:
--   Weight-two Ramanujan-Petersson library: Schwartz-Zippel counts of Weierstrass curves (D, part 1)
-- statement:
--   Schwartz-Zippel counts of Weierstrass curves (D, part 1).
--
--   * `vecEquiv` : `WeierstrassCurve F ≃ (Fin 5 → F)`; `card_weierstrass` : `#{W} = q⁵`.
--   * `vcEquiv`, `card_variableChange` : `#G = (q - 1) q³`.
--   * `Wu` : the universal curve over `ℤ[a₁, a₂, a₃, a₄, a₆]`; `PΔ F`, `Pj j₀` : `Δ` and `c₄³ - j₀ Δ` over `F`.
--   * `card_zero_le` : Schwartz-Zippel, `#{v : P(v) = 0} ≤ deg P · q⁴`.
--   * **`card_Δ_zero_le`** : `#{W : Δ = 0} ≤ KΔ q⁴`; **`card_j_le`** : `#{W : c₄³ = j₀ Δ} ≤ Kj q⁴`
--     (`KΔ = deg Δ_ℤ`, `Kj` : total degrees over `ℤ`, independent of `F`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSODA

/-!
# S3-DWS-Ordinary, part FA: Schwartz-Zippel counts of Weierstrass curves (D, part 1)

* `vecEquiv` : `WeierstrassCurve F ≃ (Fin 5 → F)`; `card_weierstrass` : `#{W} = q⁵`.
* `vcEquiv`, `card_variableChange` : `#G = (q - 1) q³`.
* `Wu` : the universal curve over `ℤ[a₁, a₂, a₃, a₄, a₆]`; `PΔ F`, `Pj j₀` : `Δ` and `c₄³ - j₀ Δ` over `F`.
* `card_zero_le` : Schwartz-Zippel, `#{v : P(v) = 0} ≤ deg P · q⁴`.
* **`card_Δ_zero_le`** : `#{W : Δ = 0} ≤ KΔ q⁴`; **`card_j_le`** : `#{W : c₄³ = j₀ Δ} ≤ Kj q⁴`
  (`KΔ = deg Δ_ℤ`, `Kj` : total degrees over `ℤ`, independent of `F`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve

namespace RamanujanPetersson.S3.DWSO

section Vec

variable {F : Type*} [CommRing F]

/-- The coefficient vector of a Weierstrass curve. -/
def vecEquiv : WeierstrassCurve F ≃ (Fin 5 → F) where
  toFun W := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  invFun v := ⟨v 0, v 1, v 2, v 3, v 4⟩
  left_inv _ := rfl
  right_inv v := by ext i; fin_cases i <;> rfl

lemma vecEquiv_apply (W : WeierstrassCurve F) : vecEquiv W = ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆] := rfl

lemma totalDegree_map_le' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (P : MvPolynomial (Fin 5) R) : (MvPolynomial.map f P).totalDegree ≤ P.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset (f := f) (p := P))

/-- The changes of variables as `Fˣ × F³`. -/
def vcEquiv : VariableChange F ≃ Fˣ × F × F × F where
  toFun C := (C.u, C.r, C.s, C.t)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The universal Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆]`. -/
noncomputable def Wu : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

lemma Wu_map (W : WeierstrassCurve F) :
    Wu.map (MvPolynomial.eval₂Hom (Int.castRingHom F) (vecEquiv W)) = W := by
  rcases W with ⟨a₁, a₂, a₃, a₄, a₆⟩
  simp [Wu, vecEquiv_apply, WeierstrassCurve.map]

lemma eval_vec (W : WeierstrassCurve F) (P : MvPolynomial (Fin 5) ℤ) :
    MvPolynomial.eval (vecEquiv W) (MvPolynomial.map (Int.castRingHom F) P) =
      MvPolynomial.eval₂Hom (Int.castRingHom F) (vecEquiv W) P :=
  MvPolynomial.eval_map _ _ _

/-- `Δ` of the universal curve, over `F`. -/
noncomputable def PΔ (F : Type*) [CommRing F] : MvPolynomial (Fin 5) F :=
  MvPolynomial.map (Int.castRingHom F) Wu.Δ

/-- `c₄³ - j₀ Δ` of the universal curve, over `F`. -/
noncomputable def Pj (j₀ : F) : MvPolynomial (Fin 5) F :=
  MvPolynomial.map (Int.castRingHom F) (Wu.c₄ ^ 3) - MvPolynomial.C j₀ * PΔ F

lemma eval_PΔ (W : WeierstrassCurve F) : MvPolynomial.eval (vecEquiv W) (PΔ F) = W.Δ := by
  have h := WeierstrassCurve.map_Δ (W := Wu) (f := MvPolynomial.eval₂Hom (Int.castRingHom F) (vecEquiv W))
  rw [Wu_map] at h
  rw [h, PΔ, eval_vec]

lemma eval_Pj (W : WeierstrassCurve F) (j₀ : F) :
    MvPolynomial.eval (vecEquiv W) (Pj j₀) = W.c₄ ^ 3 - j₀ * W.Δ := by
  have h := WeierstrassCurve.map_c₄ (W := Wu) (f := MvPolynomial.eval₂Hom (Int.castRingHom F) (vecEquiv W))
  rw [Wu_map] at h
  rw [Pj, RingHom.map_sub, RingHom.map_mul, MvPolynomial.eval_C, eval_PΔ, eval_vec, RingHom.map_pow, ← h]

lemma totalDegree_PΔ : (PΔ F).totalDegree ≤ Wu.Δ.totalDegree := by
  unfold PΔ
  exact totalDegree_map_le' (Int.castRingHom F) Wu.Δ

/-- The degree bound for `c₄³ - j₀ Δ`. -/
noncomputable def Kj : ℕ := max (Wu.c₄ ^ 3).totalDegree Wu.Δ.totalDegree

lemma totalDegree_Pj (j₀ : F) : (Pj j₀).totalDegree ≤ Kj := by
  unfold Pj
  refine (MvPolynomial.totalDegree_sub (MvPolynomial.map (Int.castRingHom F) (Wu.c₄ ^ 3))
    (MvPolynomial.C j₀ * PΔ F)).trans (max_le ?_ ?_)
  · exact (totalDegree_map_le' (Int.castRingHom F) (Wu.c₄ ^ 3)).trans (le_max_left _ _)
  · refine (MvPolynomial.totalDegree_mul (MvPolynomial.C j₀) (PΔ F)).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact totalDegree_PΔ.trans (le_max_right _ _)

end Vec

section Field

variable {F : Type*} [Field F]

lemma PΔ_ne_zero : PΔ F ≠ 0 := by
  intro h
  by_cases h3 : (3 : F) = 0
  · have e := eval_PΔ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve F)
    rw [h, map_zero] at e
    have e2 : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve F).Δ = 21 * 3 + 1 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈]
      ring
    rw [e2, h3] at e
    simp at e
  · have e := eval_PΔ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve F)
    rw [h, map_zero] at e
    have e2 : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve F).Δ = -(3 ^ 3) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈]
      ring
    rw [e2] at e
    exact neg_ne_zero.mpr (pow_ne_zero 3 h3) e.symm

lemma Pj_ne_zero (j₀ : F) : Pj j₀ ≠ 0 := by
  intro h
  have e := eval_Pj (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve F) j₀
  rw [h, map_zero] at e
  have e2 : (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve F).c₄ ^ 3 - j₀ * (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve F).Δ = 1 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [e2] at e
  exact one_ne_zero e.symm

variable [Fintype F] [DecidableEq F]

lemma card_weierstrass : Fintype.card (WeierstrassCurve F) = Fintype.card F ^ 5 := by
  rw [Fintype.card_congr vecEquiv, Fintype.card_fun, Fintype.card_fin]

lemma card_variableChange : Nat.card (VariableChange F) = (Fintype.card F - 1) * Fintype.card F ^ 3 := by
  rw [Nat.card_congr vcEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fˣ),
    Fintype.card_units, Nat.card_eq_fintype_card (α := F)]
  ring

/-- **Schwartz-Zippel** on `F⁵`: `#{v : P(v) = 0} ≤ deg P · q⁴`. -/
lemma card_zero_le {P : MvPolynomial (Fin 5) F} (hP : P ≠ 0) :
    (Finset.univ.filter (fun v : Fin 5 → F => MvPolynomial.eval v P = 0)).card ≤
      P.totalDegree * Fintype.card F ^ 4 := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hP (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  have hq : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (pow_pos hq 5) hq] at h
  have h' : ((Finset.univ.filter (fun v : Fin 5 → F => MvPolynomial.eval v P = 0)).card : ℚ≥0) ≤
      P.totalDegree * (Fintype.card F : ℚ≥0) ^ 4 := by
    refine le_of_mul_le_mul_right ?_ hq
    calc _ ≤ (P.totalDegree : ℚ≥0) * (Fintype.card F : ℚ≥0) ^ 5 := h
      _ = _ := by ring
  exact_mod_cast h'

lemma card_W_le (P : MvPolynomial (Fin 5) F) (hP : P ≠ 0) (Φ : WeierstrassCurve F → Prop) [DecidablePred Φ]
    (hΦ : ∀ W, Φ W → MvPolynomial.eval (vecEquiv W) P = 0) :
    (Finset.univ.filter Φ).card ≤ P.totalDegree * Fintype.card F ^ 4 := by
  refine le_trans ?_ (card_zero_le hP)
  refine Finset.card_le_card_of_injOn vecEquiv ?_ vecEquiv.injective.injOn
  intro W hW
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
  exact hΦ W hW

/-- **`#{W : Δ = 0} ≤ KΔ q⁴`.** -/
theorem card_Δ_zero_le :
    (Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ = 0)).card ≤ Wu.Δ.totalDegree * Fintype.card F ^ 4 :=
  (card_W_le (PΔ F) PΔ_ne_zero _ (fun W hW => by rw [eval_PΔ]; exact hW)).trans
    (Nat.mul_le_mul_right _ totalDegree_PΔ)

/-- **`#{W : c₄³ = j₀ Δ} ≤ Kj q⁴`.** -/
theorem card_j_le (j₀ : F) :
    (Finset.univ.filter (fun W : WeierstrassCurve F => W.c₄ ^ 3 = j₀ * W.Δ)).card ≤ Kj * Fintype.card F ^ 4 :=
  (card_W_le (Pj j₀) (Pj_ne_zero j₀) _ (fun W hW => by rw [eval_Pj, hW, sub_self])).trans
    (Nat.mul_le_mul_right _ (totalDegree_Pj j₀))

end Field

end RamanujanPetersson.S3.DWSO



-- Prove2me | Definitions.Def_RPLib_S3_SSFib
-- name    : RPLib_S3_SSFib
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:35.880527+00:00
-- url     : https://prove2.me/theorems/5137ee92-6193-4f17-b341-4ba737095cd7
-- title:
--   Weight-two Ramanujan-Petersson library: `j`-fibres of `Y₁(M)`
-- statement:
--   `j`-fibres of `Y₁(M)`.
--
--   * `jv b c = c₄³/Δ` of `E(b,c)` (the `j`-invariant on `Y₁(M)`, where `Δ ≠ 0`).
--   * `card_fibre_le` : for `M ≥ 4` and `(M : F) ≠ 0`, `#{(b,c) ∈ Y₁(M)(F) : j(b,c) = j₀} ≤ M²`
--     (over `L = F̄` all curves of the fibre are isomorphic, and `(b,c) ↦` the image of `(0,0)` in `E₀(L)[M]` is
--     injective by the rigidity of the Tate normal form).
--   * `card_jFibre_le` : `#{(b,c) ∈ Y₁(M)(F) : c₄ = 0 ∨ c₆ = 0} ≤ 2 M²` (the fibres `j = 0` and `j = 1728`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_Statements
import Definitions.Def_RPLib_S2_Torsion

/-!
# S3-DWS-Supersingular, part A: `j`-fibres of `Y₁(M)`

* `jv b c = c₄³/Δ` of `E(b,c)` (the `j`-invariant on `Y₁(M)`, where `Δ ≠ 0`).
* `card_fibre_le` : for `M ≥ 4` and `(M : F) ≠ 0`, `#{(b,c) ∈ Y₁(M)(F) : j(b,c) = j₀} ≤ M²`
  (over `L = F̄` all curves of the fibre are isomorphic, and `(b,c) ↦` the image of `(0,0)` in `E₀(L)[M]` is
  injective by the rigidity of the Tate normal form).
* `card_jFibre_le` : `#{(b,c) ∈ Y₁(M)(F) : c₄ = 0 ∨ c₆ = 0} ≤ 2 M²` (the fibres `j = 0` and `j = 1728`).
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine RPLib RPLib.TateNF RPLib.Torsion

namespace RamanujanPetersson.S3.DWSS

section Fib

variable {F : Type*} [Field F]

/-- The `j`-invariant `c₄³/Δ` of `E(b,c)`. -/
noncomputable def jv (b c : F) : F := (tate b c).c₄ ^ 3 / (tate b c).Δ

lemma tate_map {L : Type*} [Field L] (f : F →+* L) (b c : F) :
    (tate b c).map f = tate (f b) (f c) := by
  ext <;> simp [tate]

lemma jv_map {L : Type*} [Field L] (f : F →+* L) (b c : F) : jv (f b) (f c) = f (jv b c) := by
  simp only [jv, ← tate_map, map_c₄, map_Δ, map_div₀, map_pow]

lemma tateDisc_map {L : Type*} [Field L] (f : F →+* L) (b c : F) :
    tateDisc (f b) (f c) = f (tateDisc b c) := by
  rw [← tate_Δ, ← tate_Δ, ← tate_map, map_Δ]

lemma isElliptic_tate {b c : F} (h : tateDisc b c ≠ 0) : (tate b c).IsElliptic :=
  ⟨by rw [tate_Δ]; exact isUnit_iff_ne_zero.mpr h⟩

lemma j_eq_div (W : WeierstrassCurve F) [W.IsElliptic] : W.j = W.c₄ ^ 3 / W.Δ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', div_eq_inv_mul]

lemma jv_eq_j {b c : F} [(tate b c).IsElliptic] : jv b c = (tate b c).j := (j_eq_div _).symm

variable [DecidableEq F]

lemma hasExactOrder_map {L : Type*} [Field L] [DecidableEq L] (f : F →+* L) {M : ℕ} (hM : 4 ≤ M)
    {b c : F} (h : HasExactOrder M b c) : HasExactOrder M (f b) (f c) := by
  rw [hasExactOrder_iff_tateF hM] at h ⊢
  obtain ⟨hb, hN, hF⟩ := h
  refine ⟨(map_ne_zero f).mpr hb, fun j h2 hj => ?_, ?_⟩
  · rw [← map_tateN]; exact (map_ne_zero f).mpr (hN j h2 hj)
  · rw [← map_tateF, hF, map_zero]

/-- The fibre lemma over a given separably closed extension `L` (`ι : F →+* L`). -/
theorem card_fibre_le_of (L : Type*) [Field L] [IsSepClosed L] [DecidableEq L] (ι : F →+* L) {M : ℕ}
    (hM : 4 ≤ M) (hMF : (M : F) ≠ 0) (j₀ : F) :
    Finite {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀} ∧
      Nat.card {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀} ≤ M ^ 2 := by
  by_cases hne : IsEmpty {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀}
  · exact ⟨inferInstance, by simp [Nat.card_of_isEmpty]⟩
  rw [not_isEmpty_iff] at hne
  obtain ⟨⟨⟨b₀, c₀⟩, h₀Y, h₀j⟩⟩ := hne
  have hD : ∀ bc : F × F, bc ∈ Y1 F M → tateDisc (ι bc.1) (ι bc.2) ≠ 0 := fun bc h => by
    rw [tateDisc_map]; exact (map_ne_zero ι).mpr h.1
  have : (tate (ι b₀) (ι c₀)).IsElliptic := isElliptic_tate (hD _ h₀Y)
  have key : ∀ x : {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀},
      ∃ C : VariableChange L, C • tate (ι x.1.1) (ι x.1.2) = tate (ι b₀) (ι c₀) := by
    intro x
    have : (tate (ι x.1.1) (ι x.1.2)).IsElliptic := isElliptic_tate (hD _ x.2.1)
    apply exists_variableChange_of_j_eq
    rw [← jv_eq_j, ← jv_eq_j, jv_map, jv_map, x.2.2, h₀j]
  choose C hC using key
  have hMem : ∀ x : {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀},
      ptMap (C x) (hC x) (tatePt (ι x.1.1) (ι x.1.2)) ∈ tors (tate (ι b₀) (ι c₀)) M := fun x => by
    rw [mem_tors, ← ptMap_nsmul, (hasExactOrder_map ι hM x.2.1.2).1, ptMap_zero]
  let f : {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀} → tors (tate (ι b₀) (ι c₀)) M :=
    fun x => ⟨_, hMem x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' := congrArg Subtype.val hxy
    simp only [f] at hxy'
    have h' := inv_smul_eq (C y) (hC y)
    have hDxy : ((C y)⁻¹ * C x) • tate (ι x.1.1) (ι x.1.2) = tate (ι y.1.1) (ι y.1.2) := by
      rw [mul_smul, hC x, h']
    have hiso : IsPtIso ((C y)⁻¹ * C x) (tatePt (ι x.1.1) (ι x.1.2)) (tatePt (ι y.1.1) (ι y.1.2)) :=
      ⟨hDxy, by rw [ptMap_mul _ _ (hC x) h' hDxy, hxy', ptMap_inv_ptMap]⟩
    have hb : ι x.1.1 ≠ 0 := ne_zero_of_tateDisc_ne_zero (hD _ x.2.1)
    obtain ⟨-, h1, h2⟩ := tate_rigid hb _ hiso
    exact Subtype.ext (Prod.ext (ι.injective h1) (ι.injective h2))
  have hML : ((M : ℕ) : L) ≠ 0 := by rw [← map_natCast ι]; exact (map_ne_zero ι).mpr hMF
  have hcard : Nat.card (tors (tate (ι b₀) (ι c₀)) M) = M ^ 2 := card_tors M hML
  have : Finite (tors (tate (ι b₀) (ι c₀)) M) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 (by omega))
  exact ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans hcard.le⟩

/-- **Fibre lemma.** At most `M²` points of `Y₁(M)(F)` have a given `j`-invariant. -/
theorem card_fibre_le {M : ℕ} (hM : 4 ≤ M) (hMF : (M : F) ≠ 0) (j₀ : F) :
    Finite {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀} ∧
      Nat.card {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = j₀} ≤ M ^ 2 := by
  classical
  exact card_fibre_le_of (AlgebraicClosure F) (algebraMap F (AlgebraicClosure F)) hM hMF j₀

omit [DecidableEq F] in
lemma jv_of_c₄ {b c : F} (h : (tate b c).c₄ = 0) : jv b c = 0 := by simp [jv, h]

omit [DecidableEq F] in
lemma jv_of_c₆ {b c : F} (hD : tateDisc b c ≠ 0) (h : (tate b c).c₆ = 0) : jv b c = 1728 := by
  have hr := (tate b c).c_relation
  rw [h, tate_Δ] at hr
  rw [jv, tate_Δ, div_eq_iff hD]; linear_combination -hr

/-- **`JFibre`.** At most `2 M²` points of `Y₁(M)(F)` have `j ∈ {0, 1728}` (`c₄ = 0` or `c₆ = 0`). -/
theorem card_jFibre_le {M : ℕ} (hM : 4 ≤ M) (hMF : (M : F) ≠ 0) :
    Nat.card {bc : F × F // bc ∈ Y1 F M ∧ ((tate bc.1 bc.2).c₄ = 0 ∨ (tate bc.1 bc.2).c₆ = 0)} ≤
      2 * M ^ 2 := by
  classical
  obtain ⟨hf0, hc0⟩ := card_fibre_le hM hMF 0
  obtain ⟨hf1, hc1⟩ := card_fibre_le hM hMF 1728
  let g : {bc : F × F // bc ∈ Y1 F M ∧ ((tate bc.1 bc.2).c₄ = 0 ∨ (tate bc.1 bc.2).c₆ = 0)} →
      {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = 0} ⊕ {bc : F × F // bc ∈ Y1 F M ∧ jv bc.1 bc.2 = 1728} :=
    fun x => if h : (tate x.1.1 x.1.2).c₄ = 0 then .inl ⟨x.1, x.2.1, jv_of_c₄ h⟩
      else .inr ⟨x.1, x.2.1, jv_of_c₆ x.2.1.1 (x.2.2.resolve_left h)⟩
  have hval : ∀ x, Sum.elim (fun z => z.1) (fun z => z.1) (g x) = x.1 := fun x => by
    simp only [g]; split_ifs <;> rfl
  have hg : Function.Injective g := fun x y hxy => Subtype.ext (by rw [← hval x, ← hval y, hxy])
  calc _ ≤ Nat.card (_ ⊕ _) := Nat.card_le_card_of_injective g hg
    _ = _ := Nat.card_sum
    _ ≤ M ^ 2 + M ^ 2 := add_le_add hc0 hc1
    _ = 2 * M ^ 2 := by ring

end Fib

end RamanujanPetersson.S3.DWSS



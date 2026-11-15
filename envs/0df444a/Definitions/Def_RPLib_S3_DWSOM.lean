-- Prove2me | Definitions.Def_RPLib_S3_DWSOM
-- name    : RPLib_S3_DWSOM
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:56.467726+00:00
-- url     : https://prove2.me/theorems/dca94255-1835-49bf-ba5f-8ce80de33801
-- title:
--   Weight-two Ramanujan-Petersson library: the moduli count for one curve (O2)
-- statement:
--   The moduli count for one curve (O2).
--
--   For a Weierstrass curve `W` over a field `F` with `Δ ≠ 0` and `M ≥ 4`:
--   * `AutVC W`: the stabiliser of `W` in the group of variable changes (`Aut_F(W)` as Weierstrass changes);
--   * `yclSet W M`: the points `(b,c) ∈ Y₁(M)(F)` whose Tate curve `E(b,c)` is a change of variables of `W`;
--   * `PtOrd W M`: the points of `W(F)` of exact order `M`.
--   **`card_ptOrd`**: `#PtOrd W M = #yclSet W M · #AutVC W` (`(bc, A) ↦ A(P₀(bc))` is a bijection, by the
--   uniqueness of the Tate normal form and `aut_trivial`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S2_TateNFB

/-!
# S3-DWS-Ordinary, part M: the moduli count for one curve (O2)

For a Weierstrass curve `W` over a field `F` with `Δ ≠ 0` and `M ≥ 4`:
* `AutVC W`: the stabiliser of `W` in the group of variable changes (`Aut_F(W)` as Weierstrass changes);
* `yclSet W M`: the points `(b,c) ∈ Y₁(M)(F)` whose Tate curve `E(b,c)` is a change of variables of `W`;
* `PtOrd W M`: the points of `W(F)` of exact order `M`.
**`card_ptOrd`**: `#PtOrd W M = #yclSet W M · #AutVC W` (`(bc, A) ↦ A(P₀(bc))` is a bijection, by the
uniqueness of the Tate normal form and `aut_trivial`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Aut_F(W)` as Weierstrass changes of variables. -/
abbrev AutVC (W : WeierstrassCurve F) : Subgroup (VariableChange F) := MulAction.stabilizer (VariableChange F) W

/-- The points of `Y₁(M)(F)` whose Tate curve is isomorphic to `W` by a change of variables. -/
def yclSet (W : WeierstrassCurve F) (M : ℕ) : Set (F × F) :=
  {bc | bc ∈ Y1 F M ∧ ∃ C : VariableChange F, C • W = tate bc.1 bc.2}

/-- The points of `W(F)` of exact order `M`. -/
def PtOrd (W : WeierstrassCurve F) (M : ℕ) : Type _ := {P : W.toAffine.Point // addOrderOf P = M}

section IsPtIso

lemma isPtIso_ptMap (C : VariableChange F) {W W' : WeierstrassCurve F} (h : C • W = W')
    (P : W.toAffine.Point) : IsPtIso C P (ptMap C h P) := ⟨h, rfl⟩

lemma isPtIso_comp {C C' : VariableChange F} {W₁ W₂ W₃ : WeierstrassCurve F} {P₁ : W₁.toAffine.Point}
    {P₂ : W₂.toAffine.Point} {P₃ : W₃.toAffine.Point} (h₁ : IsPtIso C' P₁ P₂) (h₂ : IsPtIso C P₂ P₃) :
    IsPtIso (C * C') P₁ P₃ := by
  obtain ⟨h₁, hP₁⟩ := h₁
  obtain ⟨h₂, hP₂⟩ := h₂
  have h : (C * C') • W₁ = W₃ := by rw [mul_smul, h₁, h₂]
  exact ⟨h, by rw [ptMap_mul C C' h₁ h₂ h, hP₁, hP₂]⟩

lemma isPtIso_inv {C : VariableChange F} {W W' : WeierstrassCurve F} {P : W.toAffine.Point}
    {P' : W'.toAffine.Point} (h : IsPtIso C P P') : IsPtIso C⁻¹ P' P := by
  obtain ⟨h, hP⟩ := h
  exact ⟨inv_smul_eq C h, by rw [← hP]; exact ptMap_inv_ptMap C h _ _⟩

end IsPtIso

section Count

variable {W : WeierstrassCurve F} {M : ℕ}

lemma small_ne_zero (hM : 4 ≤ M) {P : W.toAffine.Point} (hP : addOrderOf P = M) {k : ℕ} (hk0 : k ≠ 0)
    (hk : k < 4) : k • P ≠ 0 :=
  nsmul_ne_zero_of_lt_addOrderOf hk0 (by omega)

lemma ne_zero_of_order (hM : 4 ≤ M) {P : W.toAffine.Point} (hP : addOrderOf P = M) : P ≠ 0 := by
  simpa using small_ne_zero hM hP one_ne_zero (by norm_num)

/-- The chosen change of variables `W → E(b,c)` for `(b,c) ∈ yclSet W M`. -/
noncomputable def yclC (bc : yclSet W M) : VariableChange F := Classical.choose bc.2.2

lemma yclC_spec (bc : yclSet W M) : yclC bc • W = tate bc.1.1 bc.1.2 := Classical.choose_spec bc.2.2

/-- The base point `P₀(bc) ∈ W(F)` corresponding to `(0,0)` on `E(b,c)`. -/
noncomputable def yclPt (bc : yclSet W M) : W.toAffine.Point :=
  ptMap (yclC bc)⁻¹ (inv_smul_eq _ (yclC_spec bc)) (tatePt bc.1.1 bc.1.2)

lemma isPtIso_yclPt (bc : yclSet W M) : IsPtIso (yclC bc) (yclPt bc) (tatePt bc.1.1 bc.1.2) := by
  have h := isPtIso_inv (isPtIso_ptMap (yclC bc)⁻¹ (inv_smul_eq _ (yclC_spec bc)) (tatePt bc.1.1 bc.1.2))
  rwa [inv_inv] at h

lemma yclPt_order (hM : 4 ≤ M) (bc : yclSet W M) : addOrderOf (yclPt bc) = M := by
  rw [yclPt, addOrderOf_ptMap]
  exact (hasExactOrder_iff (by omega) _ _).mp bc.2.1.2

lemma ycl_b_ne_zero (bc : yclSet W M) : bc.1.1 ≠ 0 := ne_zero_of_tateDisc_ne_zero bc.2.1.1

/-- The map `(bc, A) ↦ A(P₀(bc))`. -/
noncomputable def cntMap (hM : 4 ≤ M) (x : yclSet W M × AutVC W) : PtOrd W M :=
  ⟨ptMap x.2.1 (MulAction.mem_stabilizer_iff.mp x.2.2) (yclPt x.1), by
    rw [addOrderOf_ptMap]; exact yclPt_order hM x.1⟩

lemma isPtIso_cntMap (hM : 4 ≤ M) (x : yclSet W M × AutVC W) :
    IsPtIso (yclC x.1 * x.2.1⁻¹) (cntMap hM x).1 (tatePt x.1.1.1 x.1.1.2) :=
  isPtIso_comp (isPtIso_inv (isPtIso_ptMap x.2.1 (MulAction.mem_stabilizer_iff.mp x.2.2) _))
    (isPtIso_yclPt x.1)

theorem cntMap_injective (hM : 4 ≤ M) : Function.Injective (cntMap (W := W) hM) := by
  rintro ⟨bc, A⟩ ⟨bc', A'⟩ h
  have h₁ := isPtIso_cntMap hM (bc, A)
  have h₂ := isPtIso_cntMap hM (bc', A')
  rw [h] at h₁
  obtain ⟨-, hb, hc⟩ := normalForm_unique (ycl_b_ne_zero bc') h₂ h₁
  have hbc : bc = bc' := Subtype.ext (Prod.ext hb.symm hc.symm)
  subst hbc
  have hP := congrArg Subtype.val h
  simp only [cntMap] at hP
  have hA : IsPtIso (A'.1⁻¹ * A.1) (yclPt bc) (yclPt bc) :=
    isPtIso_comp (isPtIso_ptMap A.1 (MulAction.mem_stabilizer_iff.mp A.2) _)
      (isPtIso_inv (hP ▸ isPtIso_ptMap A'.1 (MulAction.mem_stabilizer_iff.mp A'.2) _))
  have hord := yclPt_order hM bc
  have h1 := aut_trivial (ne_zero_of_order hM hord) (small_ne_zero hM hord two_ne_zero (by norm_num))
    (small_ne_zero hM hord three_ne_zero (by norm_num)) hA
  have hAA : A = A' := Subtype.ext (inv_mul_eq_one.mp h1).symm
  rw [hAA]

theorem cntMap_surjective (hΔ : W.Δ ≠ 0) (hM : 4 ≤ M) : Function.Surjective (cntMap (W := W) hM) := by
  rintro ⟨P, hP⟩
  obtain ⟨b, c, C, hb, hC⟩ := exists_normalForm W P (ne_zero_of_order hM hP)
    (small_ne_zero hM hP two_ne_zero (by norm_num)) (small_ne_zero hM hP three_ne_zero (by norm_num))
  have hΔ' : tateDisc b c ≠ 0 := by
    rw [← tate_Δ, ← hC.1, variableChange_Δ]
    exact mul_ne_zero (by simp) hΔ
  have hord : addOrderOf (tatePt b c) = M := by
    obtain ⟨h, hP'⟩ := hC
    rw [← hP', addOrderOf_ptMap, hP]
  let y : yclSet W M := ⟨(b, c), ⟨hΔ', (hasExactOrder_iff (by omega) b c).mpr hord⟩, C, hC.1⟩
  have hA : IsPtIso (C⁻¹ * yclC y) (yclPt y) P := isPtIso_comp (isPtIso_yclPt y) (isPtIso_inv hC)
  obtain ⟨hA1, hA2⟩ := hA
  refine ⟨(y, ⟨C⁻¹ * yclC y, MulAction.mem_stabilizer_iff.mpr hA1⟩), ?_⟩
  exact Subtype.ext hA2

/-- **(O2) Moduli count.** `#{P ∈ W(F) of exact order M} = #{(b,c) ∈ Y₁(M)(F) : E(b,c) ≅ W} · #Aut_F(W)`. -/
theorem card_ptOrd (hΔ : W.Δ ≠ 0) (hM : 4 ≤ M) :
    Nat.card (PtOrd W M) = Nat.card (yclSet W M) * Nat.card (AutVC W) := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨cntMap_injective hM, cntMap_surjective hΔ hM⟩)).symm

/-- `yclSet` only depends on the change-of-variables class of `W`. -/
lemma yclSet_smul (C : VariableChange F) (W : WeierstrassCurve F) (M : ℕ) :
    yclSet (C • W) M = yclSet W M := by
  ext bc
  refine and_congr Iff.rfl ⟨fun ⟨C', h⟩ => ⟨C' * C, by rw [mul_smul, h]⟩, fun ⟨C', h⟩ => ⟨C' * C⁻¹, ?_⟩⟩
  rw [mul_smul, inv_smul_smul, h]

lemma mem_yclSet_tate {M : ℕ} {bc : F × F} (h : bc ∈ Y1 F M) : bc ∈ yclSet (tate bc.1 bc.2) M :=
  ⟨h, 1, one_smul _ _⟩

end Count

end RamanujanPetersson.S3.DWSO



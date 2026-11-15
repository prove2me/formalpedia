-- Prove2me | Definitions.Def_RPLib_S3_DWSODA
-- name    : RPLib_S3_DWSODA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:09:38.392679+00:00
-- url     : https://prove2.me/theorems/ce36a2f6-0b2d-496d-af88-29f40ab0be18
-- title:
--   Weight-two Ramanujan-Petersson library: the double count (A1) and `#PtOrd = L_f` (A1')
-- statement:
--   The double count (A1) and `#PtOrd = L_f` (A1').
--
--   * `finite_weierstrass`, `fintype_weierstrass` : over a finite field there are finitely many Weierstrass curves.
--   * `WT F t` : the Weierstrass curves over `F` with `Δ ≠ 0` and trace `t`.
--   * `fibEquiv` : for `W` of trace `t`, `{(x, C) : C • W = E(x)} ≃ yclSet W M × Aut_VC(W)`.
--   * `sigmaEquiv` : `Σ_W {(x, C) : C • W = E(x)} ≃ TS F M t × G` (`W = C⁻¹ • E(x)`).
--   * **`card_G_mul_pairCount`** : `#G · pairCount F M t = Σ_{W ∈ WT F t} #W(F)[exact M]`.
--   * **`card_ptOrd_eq_Lval`** : `#W(F)[exact M] = L_f(t, (t² - 4q)/f²)` for order data `d`, `f = d.f`.
--   * `Lval_le` (`≤ M²`), `Lval_one` (`= 1` at level `1`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOCC

/-!
# S3-DWS-Ordinary, part DA: the double count (A1) and `#PtOrd = L_f` (A1')

* `finite_weierstrass`, `fintype_weierstrass` : over a finite field there are finitely many Weierstrass curves.
* `WT F t` : the Weierstrass curves over `F` with `Δ ≠ 0` and trace `t`.
* `fibEquiv` : for `W` of trace `t`, `{(x, C) : C • W = E(x)} ≃ yclSet W M × Aut_VC(W)`.
* `sigmaEquiv` : `Σ_W {(x, C) : C • W = E(x)} ≃ TS F M t × G` (`W = C⁻¹ • E(x)`).
* **`card_G_mul_pairCount`** : `#G · pairCount F M t = Σ_{W ∈ WT F t} #W(F)[exact M]`.
* **`card_ptOrd_eq_Lval`** : `#W(F)[exact M] = L_f(t, (t² - 4q)/f²)` for order data `d`, `f = d.f`.
* `Lval_le` (`≤ M²`), `Lval_one` (`= 1` at level `1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Fin

variable {F : Type*} [Field F]

instance finite_weierstrass [Finite F] : Finite (WeierstrassCurve F) :=
  Finite.of_injective (fun W : WeierstrassCurve F => (W.a₁, W.a₂, W.a₃, W.a₄, W.a₆)) (by
    rintro ⟨a₁, a₂, a₃, a₄, a₆⟩ ⟨b₁, b₂, b₃, b₄, b₆⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl)

noncomputable instance fintype_weierstrass [Finite F] : Fintype (WeierstrassCurve F) := Fintype.ofFinite _

end Fin

/-- The elliptic Weierstrass curves over `F` with trace `t`. -/
abbrev WT (F : Type) [Field F] (t : ℤ) : Type :=
  {W : WeierstrassCurve F // W.Δ ≠ 0 ∧ RPLib.EllFq.trace W = t}

instance WT.isElliptic {F : Type} [Field F] {t : ℤ} (x : WT F t) : x.1.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr x.2.1⟩

section Count

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ} {t : ℤ}

/-- The fibre of the triple count over one curve. -/
noncomputable def fibEquiv (x : WT F t) :
    {y : TS F M t × VariableChange F // y.2 • x.1 = y.1.W} ≃ yclSet x.1 M × AutVC x.1 where
  toFun y := (⟨y.1.1.1, y.1.1.2.1, y.1.2, y.2⟩,
    ⟨(yclC (⟨y.1.1.1, y.1.1.2.1, y.1.2, y.2⟩ : yclSet x.1 M))⁻¹ * y.1.2, by
      rw [MulAction.mem_stabilizer_iff, mul_smul, y.2, inv_smul_eq_iff]
      exact (yclC_spec (⟨y.1.1.1, y.1.1.2.1, y.1.2, y.2⟩ : yclSet x.1 M)).symm⟩)
  invFun z := ⟨(⟨z.1.1, z.1.2.1, by
      show RPLib.EllFq.trace (tate z.1.1.1 z.1.1.2) = t
      rw [← yclC_spec z.1, RPLib.EllFq.trace_variableChange]; exact x.2.2⟩, yclC z.1 * z.2.1), by
      show (yclC z.1 * z.2.1) • x.1 = tate z.1.1.1 z.1.1.2
      rw [mul_smul, MulAction.mem_stabilizer_iff.mp z.2.2, yclC_spec z.1]⟩
  left_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show yclC _ * ((yclC _)⁻¹ * y.1.2) = y.1.2
      rw [mul_inv_cancel_left]
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      show (yclC z.1)⁻¹ * (yclC z.1 * z.2.1) = z.2.1
      rw [inv_mul_cancel_left]

/-- The triple count, summed over the curves. -/
def sigmaEquiv (M : ℕ) (t : ℤ) :
    (Σ x : WT F t, {y : TS F M t × VariableChange F // y.2 • x.1 = y.1.W}) ≃ TS F M t × VariableChange F where
  toFun z := z.2.1
  invFun y := ⟨⟨y.2⁻¹ • y.1.W, by
      rw [variableChange_Δ]; exact mul_ne_zero (by simp) y.1.W.isUnit_Δ.ne_zero, by
      rw [RPLib.EllFq.trace_variableChange]; exact y.1.2.2⟩, y, smul_inv_smul y.2 _⟩
  left_inv := by
    rintro ⟨⟨W, hW⟩, y, hy⟩
    have e : y.2⁻¹ • y.1.W = W := by rw [← hy, inv_smul_smul]
    subst e
    rfl
  right_inv _ := rfl

/-- **(A1) Double count.** `#G · pairCount F M t = Σ_{W : Δ ≠ 0, a_W = t} #W(F)[exact M]`. -/
theorem card_G_mul_pairCount (hM4 : 4 ≤ M) (t : ℤ) :
    Nat.card (VariableChange F) * pairCount F M t = ∑ x : WT F t, Nat.card (PtOrd x.1 M) := by
  have h1 : ∀ x : WT F t, Nat.card (PtOrd x.1 M) =
      Nat.card {y : TS F M t × VariableChange F // y.2 • x.1 = y.1.W} := by
    intro x
    rw [card_ptOrd x.2.1 hM4, ← Nat.card_prod, Nat.card_congr (fibEquiv x)]
  simp_rw [h1]
  rw [← Nat.card_sigma, Nat.card_congr (sigmaEquiv M t), Nat.card_prod, mul_comm]
  rfl

end Count

section Lval

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L]
  [DecidableEq L] {W : WeierstrassCurve F} [W.IsElliptic] {M : ℕ} [NeZero M]

attribute [local instance] finite_coordinateRing decEqFF

/-- **(A1')** `#W(F)[exact M] = L_f(a_W, (a_W² - 4q)/f²)`. -/
theorem card_ptOrd_eq_Lval (d : OrdData W L) (hM : (M : F) ≠ 0) :
    Nat.card (PtOrd W M) = Lval M (RPLib.EllFq.trace W) d.f
      ((RPLib.EllFq.trace W ^ 2 - 4 * (Fintype.card F : ℤ)) / d.f ^ 2) := by
  have hπ : d.toOAct.ι (⟨d.b, d.f⟩ : Ord d) = piE W L := by
    rw [OrdData.toOAct_ι]; exact θ_pi d
  rw [div_eq_of_ord d, ← Lval_eq M (a := -(deg d.w : ℤ)) (x := d.b) d.htr.symm,
    card_ptOrd_eq_levelCount d.toOAct hM hπ]

end Lval

lemma Lval_le (M : ℕ) [NeZero M] (t f D : ℤ) : Lval M t f D ≤ M ^ 2 := by
  unfold Lval levelCount
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ, ZMod.card]

lemma Lval_one (t f D : ℤ) : Lval 1 t f D = 1 := by
  unfold Lval levelCount
  rw [Finset.filter_true_of_mem]
  · rfl
  · intro v _
    refine ⟨fun d hd hd0 => ?_, Subsingleton.elim _ _⟩
    rw [Finset.mem_range] at hd
    omega

end RamanujanPetersson.S3.DWSO



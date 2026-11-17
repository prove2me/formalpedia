-- Prove2me | Definitions.Def_RPLib_S4T_FFBridgeA
-- name    : RPLib_S4T_FFBridgeA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:20:00.941798+00:00
-- url     : https://prove2.me/theorems/de6bf1a4-77e4-48dd-bfe4-b60b7f299d71
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: the evaluation calculus used by the L9 bridge
-- statement:
--   The evaluation calculus used by the L9 bridge.
--
--   `W` an elliptic curve over a field `F`, `L ⊇ F` algebraically closed, `L(E) = FF W L`.
--
--   * `ev A a b : F[X][Y] →+* A` (`= evalEvalBC A · a b`), `evalEvalBC_algHom` (algebra maps commute with it);
--   * `HV_ev` : if `a, b ∈ L(E)` have values `c, d` at `P`, then `p(a, b)` has value `p(c, d)`;
--   * `ptX a` : a point with abscissa `a`; `eq_zero_of_HV` : a function with value `0` at all affine points outside
--     a finite set is `0`;
--   * `finite_px` : finitely many points have abscissa in a finite set; `finite_preimage` : finite preimages under an
--     additive map with finite kernel.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateN
import Definitions.Def_WeierstrassCurve_RationalEnd

/-!
# S4T-FFBridge, part A: the evaluation calculus used by the L9 bridge

`W` an elliptic curve over a field `F`, `L ⊇ F` algebraically closed, `L(E) = FF W L`.

* `ev A a b : F[X][Y] →+* A` (`= evalEvalBC A · a b`), `evalEvalBC_algHom` (algebra maps commute with it);
* `HV_ev` : if `a, b ∈ L(E)` have values `c, d` at `P`, then `p(a, b)` has value `p(c, d)`;
* `ptX a` : a point with abscissa `a`; `eq_zero_of_HV` : a function with value `0` at all affine points outside
  a finite set is `0`;
* `finite_px` : finitely many points have abscissa in a finite set; `finite_preimage` : finite preimages under an
  additive map with finite kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.S4T.FFB

open RPLib.Weil RPLib.DWS

section Ev

variable {F : Type*} [Field F] (A : Type*) [Field A] [Algebra F A]

/-- Evaluation of `F`-coefficient bivariate polynomials at `(a, b) ∈ A²`. -/
noncomputable def ev (a b : A) : F[X][Y] →+* A :=
  (evalEvalRingHom a b).comp (mapRingHom (mapRingHom (algebraMap F A)))

variable {A}

lemma ev_apply (a b : A) (p : F[X][Y]) : ev A a b p = evalEvalBC A p a b := rfl

@[simp] lemma ev_CC (a b : A) (r : F) : ev A a b (C (C r)) = algebraMap F A r := by
  simp [ev]

@[simp] lemma ev_CX (a b : A) : ev A a b (C X : F[X][Y]) = a := by
  simp [ev]

@[simp] lemma ev_X (a b : A) : ev A a b (X : F[X][Y]) = b := by
  simp [ev]

lemma ringHom_ext2 {B : Type*} [Semiring B] {φ ψ : F[X][Y] →+* B} (h1 : ∀ r, φ (C (C r)) = ψ (C (C r)))
    (h2 : φ (C X) = ψ (C X)) (h3 : φ X = ψ X) : φ = ψ := by
  apply Polynomial.ringHom_ext
  · intro q
    have : φ.comp C = ψ.comp C := by
      apply Polynomial.ringHom_ext
      · intro r; exact h1 r
      · exact h2
    exact RingHom.congr_fun this q
  · exact h3

lemma evalEvalBC_algHom {B : Type*} [Field B] [Algebra F B] (φ : A →ₐ[F] B) (p : F[X][Y]) (a b : A) :
    φ (evalEvalBC A p a b) = evalEvalBC B p (φ a) (φ b) := by
  have h : (φ : A →+* B).comp (ev (F := F) A a b) = ev (F := F) B (φ a) (φ b) :=
    ringHom_ext2 (fun r => by simp) (by simp) (by simp)
  exact RingHom.congr_fun h p

end Ev

section HV

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma HV_algF {P : Pt W L} {hP : P ≠ 0} (r : F) :
    HV W L P hP (algebraMap F (FF W L) r) (algebraMap F L r) := by
  refine (HV_alg (algebraMap F L r)).congr ?_ rfl
  exact (IsScalarTower.algebraMap_apply F L (FF W L) r).symm

/-- Values of polynomial expressions. -/
lemma HV_ev {P : Pt W L} {hP : P ≠ 0} (p : F[X][Y]) {a b : FF W L} {c d : L}
    (ha : HV W L P hP a c) (hb : HV W L P hP b d) : HV W L P hP (ev (FF W L) a b p) (ev L c d p) := by
  have hX : HV W L P hP (ev (FF W L) a b (C X : F[X][Y])) (ev L c d (C X : F[X][Y])) := ha.congr (ev_CX a b).symm (ev_CX c d).symm
  have hY : HV W L P hP (ev (FF W L) a b (X : F[X][Y])) (ev L c d (X : F[X][Y])) := hb.congr (ev_X a b).symm (ev_X c d).symm
  have hC : ∀ q : F[X], HV W L P hP (ev (FF W L) a b (C q)) (ev L c d (C q)) := by
    intro q
    induction q using Polynomial.induction_on with
    | C r => exact (HV_algF r).congr (ev_CC a b r).symm (ev_CC c d r).symm
    | add p q hp hq =>
      rw [C_add, (ev (FF W L) a b).map_add, (ev L c d).map_add]
      exact hp.add hq
    | monomial n r h =>
      rw [show (C (C r * X ^ (n + 1)) : F[X][Y]) = C (C r * X ^ n) * C X by rw [pow_succ, ← mul_assoc, C_mul],
        (ev (FF W L) a b).map_mul, (ev L c d).map_mul]
      exact h.mul hX
  induction p using Polynomial.induction_on with
  | C q => exact hC q
  | add p q hp hq =>
    rw [(ev (FF W L) a b).map_add, (ev L c d).map_add]
    exact hp.add hq
  | monomial n q h =>
    rw [show (C q * X ^ (n + 1) : F[X][Y]) = C q * X ^ n * X by rw [pow_succ, ← mul_assoc],
      (ev (FF W L) a b).map_mul, (ev L c d).map_mul]
    exact h.mul hY

/-- A function with value `0` at infinitely many affine points vanishes. -/
lemma eq_zero_of_HV_inf {f : FF W L} {S : Set (Pt W L)} (hS : S.Infinite)
    (h : ∀ (P : Pt W L) (hP : P ≠ 0), P ∈ S → HV W L P hP f 0) : f = 0 := by
  by_contra hf
  obtain ⟨P, hPS, hP⟩ := hS.exists_notMem_finite ((ord_finite hf).union (Set.finite_singleton (0 : Pt W L)))
  have hP0 : P ≠ 0 := fun h0 => hP (Or.inr h0)
  have h1 := nu_eq_one_of_ord hP0 hf (Function.notMem_support.mp (fun hm => hP (Or.inl hm)))
  have h2 := h P hP0 hPS
  unfold HV at h2
  rw [map_zero, sub_zero, h1] at h2
  exact lt_irrefl _ h2

variable (W) in
/-- A point of `W⁄L` with abscissa `a`. -/
noncomputable def ptX (a : L) : Pt W L :=
  Point.some _ _ (equation_iff_nonsingular.mp (exists_y_alg (W.baseChange L) a).choose_spec)

lemma px_ptX (a : L) : px (ptX W a) = a := rfl

lemma ptX_ne (a : L) : ptX W a ≠ 0 := Point.some_ne_zero _

/-- A function with value `0` at every affine point outside a finite set vanishes. -/
lemma eq_zero_of_HV {f : FF W L} {T : Set (Pt W L)} (hT : T.Finite)
    (h : ∀ (P : Pt W L) (hP : P ≠ 0), P ∉ T → HV W L P hP f 0) : f = 0 := by
  by_contra hf
  have hfin : (px '' (Function.support (ord W L f) ∪ T)).Finite := ((ord_finite hf).union hT).image _
  obtain ⟨a, ha⟩ := hfin.exists_notMem
  have hS : ptX W a ∉ Function.support (ord W L f) ∪ T := fun hm => ha ⟨_, hm, px_ptX a⟩
  have h1 := nu_eq_one_of_ord (ptX_ne a) hf
    (Function.notMem_support.mp (fun hm => hS (Or.inl hm)))
  have h2 := h (ptX W a) (ptX_ne a) (fun hm => hS (Or.inr hm))
  unfold HV at h2
  rw [map_zero, sub_zero, h1] at h2
  exact lt_irrefl _ h2

/-- Finitely many points have abscissa in a finite set. -/
lemma finite_px {B : Set L} (hB : B.Finite) : {P : Pt W L | P ≠ 0 ∧ px P ∈ B}.Finite := by
  refine ((hB.image (fun a => ptX W a)).union (hB.image (fun a => -ptX W a))).subset ?_
  rintro P ⟨hP, hPB⟩
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    have e := (exists_y_alg (W.baseChange L) x).choose_spec
    rcases Y_eq_of_X_eq h.1 e rfl with hy | hy
    · exact Or.inl ⟨x, hPB, some_eq_some rfl hy.symm⟩
    · refine Or.inr ⟨x, hPB, ?_⟩
      show -Point.some _ _ _ = _
      rw [Point.neg_some]
      exact some_eq_some rfl hy.symm

end HV

/-- Preimages of finite sets under an additive map with finite kernel are finite. -/
lemma finite_preimage {G H : Type*} [AddCommGroup G] [AddCommGroup H] (φ : G →+ H)
    (hk : {P | φ P = 0}.Finite) {S : Set H} (hS : S.Finite) : (φ ⁻¹' S).Finite := by
  refine hS.preimage' (fun b _ => ?_)
  by_cases hb : ∃ P₀, φ P₀ = b
  · obtain ⟨P₀, rfl⟩ := hb
    refine (hk.image (· + P₀)).subset ?_
    intro P hP
    refine ⟨P - P₀, ?_, by abel⟩
    show φ (P - P₀) = 0
    rw [map_sub, show φ P = φ P₀ from hP, sub_self]
  · convert Set.finite_empty
    ext P
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => hb ⟨P, h⟩

end RPLib.S4T.FFB



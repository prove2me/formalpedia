-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
-- name    : OAI_NumberTheory_SingleFold_DescentMap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:07:09.67927+00:00
-- url     : https://prove2.me/theorems/fff31388-7e81-4efd-81a2-d2749818924b
-- title:
--   The 2-descent map of $y^2=x^3-25x$
-- statement:
--   Let $E$ be the elliptic curve $y^2=x^3-25x$ over $\mathbb{Q}$, with point at infinity $O$. Let $e$ be one of the roots $0,\pm5$ of $x^3-25x$, so that $b=3e^2-25\ne0$.
--
--   1. **Adjusted value.** $\alpha_e(O)=1$ and $\alpha_e(x,y)=x-e$ if $x\ne e$, while $\alpha_e(e,0)=b$.
--   2. **Square classes.** $\mathrm{cl}:\mathbb{Q}\to\mathbb{Q}^\times/(\mathbb{Q}^\times)^2$ sends $x\ne0$ to its class and $0$ to $1$. Every square class has order dividing $2$.
--   3. **Descent homomorphism.** For all points $P,Q$ the product $\alpha_e(P)\alpha_e(Q)\alpha_e(P+Q)$ is a square, so
--   $$
--   P\mapsto\mathrm{cl}(\alpha_e(P))
--   $$
--      is a group homomorphism $E(\mathbb{Q})\to\mathbb{Q}^\times/(\mathbb{Q}^\times)^2$.
--   4. **Kummer map.** $\kappa=(\mathrm{cl}\,\alpha_0,\mathrm{cl}\,\alpha_5)$. It kills $2E(\mathbb{Q})$, and conversely $\kappa(P)=0$ implies $P=2Q$ for some $Q$. Indeed, if $x$, $x-5$ and $x+5$ are squares $r^2,s^2,t^2$, then $P$ is the double of the point with $X=x+rs+rt+st$ and $Y=-(r+s)(r+t)(s+t)$.
--
--   This is the classical complete $2$-descent for a curve with full rational $2$-torsion. It identifies $E(\mathbb{Q})/2E(\mathbb{Q})$ with a subgroup of pairs of square classes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/DescentMap.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/DescentMap.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

namespace SingleFold.Descent

section
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

abbrev E : WeierstrassCurve.Affine ℚ := ⟨0,0,0,-25,0⟩
instance : E.IsElliptic := by
  constructor
  norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma equation {x y : ℚ} (h : E.Nonsingular x y) : y^2 = x^3-25*x := by
  simpa [WeierstrassCurve.Affine.equation_iff, E, sub_eq_add_neg] using h.1

@[simp] lemma negY (x y : ℚ) : E.negY x y = -y := by simp []

def adjusted (b x : ℚ) : ℚ := if x = 0 then b else x

lemma adjusted_triple {b m v x z r : ℚ} (hb : b ≠ 0)
    (hp : x*z+x*r+z*r = b-2*m*v) (hv : x*z*r=v^2) :
    IsSquare (adjusted b x * adjusted b z * adjusted b r) := by
  have hz (x z r : ℚ) (hp : x*z+x*r+z*r = b-2*m*v) (hv : x*z*r=v^2)
      (hx : x=0) : IsSquare (adjusted b x * adjusted b z * adjusted b r) := by
    subst x
    have hv0 : v=0 := by nlinarith [sq_nonneg v]
    rw [hv0] at hp
    have he : z*r=b := by nlinarith
    have hzn : z ≠ 0 := by intro h; simp [h] at he; exact hb he.symm
    have hrn : r ≠ 0 := by intro h; simp [h] at he; exact hb he.symm
    refine ⟨b, ?_⟩
    simp [adjusted, hzn, hrn, mul_assoc, he]
  by_cases hx : x=0
  · exact hz x z r hp hv hx
  by_cases hzz : z=0
  · have hh := hz z x r (by nlinarith [hp]) (by nlinarith [hv]) hzz
    simpa [mul_comm, mul_left_comm, mul_assoc] using hh
  by_cases hr : r=0
  · have hh := hz r z x (by nlinarith [hp]) (by nlinarith [hv]) hr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hh
  refine ⟨v, ?_⟩
  simpa [adjusted, hx, hzz, hr, pow_two] using hv

lemma distinct_pair {x z y w m : ℚ} (hx : x ≠ z)
    (h₁ : y^2=x^3-25*x) (h₂ : w^2=z^3-25*z)
    (hm : m*(x-z)=y-w) :
    x*z+(m^2-x-z)*(x+z) = -25-2*m*(y-m*x) := by
  have hh : (x-z)*(x*z+(m^2-x-z)*(x+z)-(-25-2*m*(y-m*x)))=0 := by
    linear_combination h₁-h₂+(y+w-m*(x-z))*hm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hx))

lemma shifted_line {x z y m e : ℚ} (he : e^3-25*e=0)
    (h₁ : y^2=x^3-25*x)
    (hp : x*z+(m^2-x-z)*(x+z) = -25-2*m*(y-m*x)) :
    let r := m^2-x-z
    let v := y-m*(x-e)
    (x-e)*(z-e)+(x-e)*(r-e)+(z-e)*(r-e) =
      (3*e^2-25)-2*m*v ∧
    (x-e)*(z-e)*(r-e)=v^2 := by
  dsimp
  constructor
  · linear_combination hp
  · linear_combination -h₁ + (x-e)*hp - he

def alphaVal (e : ℚ) : E.Point → ℚ
  | .zero => 1
  | .some x _ _ => adjusted (3*e^2-25) (x-e)

@[simp] lemma alphaVal_zero (e : ℚ) : alphaVal e 0 = 1 := rfl
@[simp] lemma alphaVal_some (e : ℚ) {x y : ℚ} (h : E.Nonsingular x y) :
    alphaVal e (.some x y h) = adjusted (3*e^2-25) (x-e) := rfl

lemma alphaVal_ne_zero (e : ℚ) (hb : 3*e^2-25 ≠ 0) (P : E.Point) :
    alphaVal e P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h => simp only [alphaVal, adjusted]; split_ifs <;> assumption

@[simp] lemma alphaVal_neg (e : ℚ) (P : E.Point) : alphaVal e (-P) = alphaVal e P := by
  cases P with
  | zero => simp only [← zero_def, _root_.neg_zero]
  | some x y h => rfl

lemma alphaVal_add_square (e : ℚ) (he : e^3-25*e=0) (hb : 3*e^2-25 ≠ 0)
    (P Q : E.Point) : IsSquare (alphaVal e P * alphaVal e Q * alphaVal e (P+Q)) := by
  cases P with
  | zero => simpa only [← zero_def, zero_add, alphaVal_zero, one_mul] using
      (IsSquare.mul_self (alphaVal e Q))
  | some x y h =>
    cases Q with
    | zero => simpa only [← zero_def, add_zero, alphaVal_zero, mul_one] using
        (IsSquare.mul_self (alphaVal e (some x y h)))
    | some z w h' =>
      by_cases hneg : (some x y h : E.Point) = -(some z w h')
      · rw [hneg, neg_add_cancel, alphaVal_neg, alphaVal_zero, mul_one]
        exact IsSquare.mul_self _
      have hxneg : ¬(x=z ∧ y=E.negY z w) := by
        rintro ⟨rfl, hy⟩
        apply hneg
        simp only [neg_some, hy]
      by_cases hx : x=z
      · subst z
        have hyw : y=w := by
          have hh : y=w ∨ y=-w := by
            have heq := equation h
            have heq' := equation h'
            exact (sq_eq_sq_iff_eq_or_eq_neg).mp (heq.trans heq'.symm)
          exact hh.resolve_right (fun hy => hxneg ⟨rfl, by simpa only [negY] using hy⟩)
        subst w
        have hy : y ≠ E.negY x y := fun hy => hxneg ⟨rfl,hy⟩
        have hy0 : y ≠ 0 := by
          intro hz
          exact hy (by simp [hz])
        have hm : (E.slope x x y y)*(2*y)=3*x^2-25 := by
          rw [slope_of_Y_ne rfl hy]
          simp [ WeierstrassCurve.Affine.negY]
          field_simp
          ring
        have hp : x*x+((E.slope x x y y)^2-x-x)*(x+x) =
            -25-2*(E.slope x x y y)*(y-(E.slope x x y y)*x) := by
          linear_combination hm
        have hc := shifted_line he (equation h) hp
        dsimp at hc
        rw [add_self_of_Y_ne hy, alphaVal_some, alphaVal_some]
        change IsSquare (adjusted (3*e^2-25) (x-e) * adjusted (3*e^2-25) (x-e) *
          adjusted (3*e^2-25) (E.addX x x (E.slope x x y y)-e))
        simpa [WeierstrassCurve.Affine.addX, E] using adjusted_triple hb hc.1 hc.2
      · have hm : E.slope x z y w * (x-z)=y-w := by
          rw [slope_of_X_ne hx]
          exact div_mul_cancel₀ _ (sub_ne_zero.mpr hx)
        have hp := distinct_pair hx (equation h) (equation h') hm
        have hc := shifted_line he (equation h) hp
        dsimp at hc
        rw [add_of_X_ne hx, alphaVal_some, alphaVal_some, alphaVal_some]
        simpa [WeierstrassCurve.Affine.addX, E] using adjusted_triple hb hc.1 hc.2

end

abbrev Squares : Subgroup ℚˣ := (powMonoidHom (α := ℚˣ) 2).range
abbrev SquareClass := ℚˣ ⧸ Squares

noncomputable def classOf (x : ℚ) : SquareClass :=
  if hx : x=0 then 1 else QuotientGroup.mk (Units.mk0 x hx)

@[simp] lemma classOf_zero : classOf 0 = 1 := by simp [classOf]
@[simp] lemma classOf_one : classOf 1 = 1 := by simp [classOf]

lemma classOf_mul {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    classOf (x*y)=classOf x * classOf y := by
  simp only [classOf, dite_eq_right hx, dite_eq_right hy, dite_eq_right (mul_ne_zero hx hy)]
  rw [Units.mk0_mul]
  rfl

lemma classOf_eq_one_iff {x : ℚ} (hx : x ≠ 0) : classOf x = 1 ↔ IsSquare x := by
  simp only [classOf, dite_eq_right hx, QuotientGroup.eq_one_iff, MonoidHom.mem_range,
    powMonoidHom_apply]
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨(r:ℚ), ?_⟩
    have hh := congrArg (fun a : ℚˣ => (a:ℚ)) hr
    simpa [pow_two] using hh.symm
  · rintro ⟨r,hr⟩
    have hr0 : r ≠ 0 := by intro h; simp [h] at hr; exact hx hr
    refine ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    simpa [pow_two] using hr.symm

lemma classOf_square (x : ℚ) : classOf (x*x)=1 := by
  by_cases hx : x=0
  · simp [hx]
  · exact (classOf_eq_one_iff (mul_ne_zero hx hx)).mpr (IsSquare.mul_self _)

lemma classOf_self_mul (x : ℚ) : classOf x * classOf x = 1 := by
  by_cases hx : x=0
  · simp [hx]
  · rw [← classOf_mul hx hx, classOf_square]

lemma squareClass_self_mul (c : SquareClass) : c*c=1 := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective c
  have hu : (u:ℚ) ≠ 0 := u.ne_zero
  have he : classOf (u:ℚ) = QuotientGroup.mk u := by
    simp only [classOf, dite_eq_right hu]
    congr 1
    ext
    rfl
  rw [← he]
  exact classOf_self_mul _

lemma squareClass_inv (c : SquareClass) : c⁻¹=c := by
  exact inv_eq_of_mul_eq_one_left (squareClass_self_mul c)

noncomputable def alpha (e : ℚ) (he : e^3-25*e=0) (hb : 3*e^2-25 ≠ 0) :
    E.Point →+ Additive SquareClass where
  toFun P := Additive.ofMul (classOf (alphaVal e P))
  map_zero' := by simp
  map_add' P Q := by
    change classOf (alphaVal e (P+Q)) = classOf (alphaVal e P)*classOf (alphaVal e Q)
    have hP := alphaVal_ne_zero e hb P
    have hQ := alphaVal_ne_zero e hb Q
    have hS := alphaVal_ne_zero e hb (P+Q)
    have hh := (classOf_eq_one_iff (mul_ne_zero (mul_ne_zero hP hQ) hS)).mpr
      (alphaVal_add_square e he hb P Q)
    rw [classOf_mul (mul_ne_zero hP hQ) hS, classOf_mul hP hQ] at hh
    exact (inv_eq_of_mul_eq_one_right hh).symm.trans (squareClass_inv _)

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma half_algebra {x r s t : ℚ} (hr : r^2=x) (hs : s^2=x-5) (ht : t^2=x+5) :
    let X := x+r*s+r*t+s*t
    let Y := -(r+s)*(r+t)*(s+t)
    Y ≠ 0 ∧ Y^2 = X^3-25*X ∧ (-(r+s+t))*(2*Y)=3*X^2-25 ∧
    (-(r+s+t))^2-2*X=x := by
  dsimp
  have hA : r+s ≠ 0 := by
    intro h
    have he : r = -s := by linarith
    rw [he] at hr
    nlinarith
  have hB : r+t ≠ 0 := by
    intro h
    have he : r = -t := by linarith
    rw [he] at hr
    nlinarith
  have hC : s+t ≠ 0 := by
    intro h
    have he : s = -t := by linarith
    rw [he] at hs
    nlinarith
  have h₁ : (r+s)*(r+t)=x+r*s+r*t+s*t := by nlinarith
  have h₂ : (r+s)*(s+t)=x+r*s+r*t+s*t-5 := by nlinarith
  have h₃ : (r+t)*(s+t)=x+r*s+r*t+s*t+5 := by nlinarith
  refine ⟨mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hA) hB) hC, ?_, ?_, ?_⟩
  · calc
      (-(r+s)*(r+t)*(s+t))^2 =
          ((r+s)*(r+t))*((r+s)*(s+t))*((r+t)*(s+t)) := by ring
      _ = (x+r*s+r*t+s*t)^3-25*(x+r*s+r*t+s*t) := by rw [h₁,h₂,h₃]; ring
  · have hid : (r+s)*(r+t)*((r+s)*(s+t)) + (r+s)*(r+t)*((r+t)*(s+t)) +
        (r+s)*(s+t)*((r+t)*(s+t)) =
        (-(r+s+t))*(2*(-(r+s)*(r+t)*(s+t))) := by ring
    rw [h₁,h₂,h₃] at hid
    nlinarith only [hid]
  · nlinarith only [hr,hs,ht]

lemma exists_half_of_squares {x y : ℚ} (h : E.Nonsingular x y)
    (h₀ : IsSquare x) (hp : IsSquare (x-5)) (hn : IsSquare (x+5)) :
    ∃ Q : E.Point, (2:ℕ) • Q = some x y h := by
  obtain ⟨r,hr⟩ := h₀
  obtain ⟨s,hs⟩ := hp
  obtain ⟨t,ht⟩ := hn
  have hr' : r^2=x := by simpa only [pow_two] using hr.symm
  have hs' : s^2=x-5 := by simpa only [pow_two] using hs.symm
  have ht' : t^2=x+5 := by simpa only [pow_two] using ht.symm
  let X := x+r*s+r*t+s*t
  let Y := -(r+s)*(r+t)*(s+t)
  obtain ⟨hY,heq,htan,hdup⟩ := half_algebra hr' hs' ht'
  change Y ≠ 0 at hY
  change Y^2=X^3-25*X at heq
  change (-(r+s+t))*(2*Y)=3*X^2-25 at htan
  change (-(r+s+t))^2-2*X=x at hdup
  have hQ : E.Nonsingular X Y := E.equation_iff_nonsingular.mp (by
    simpa [WeierstrassCurve.Affine.equation_iff, E, sub_eq_add_neg] using heq)
  have hYn : Y ≠ E.negY X Y := by rw [negY]; intro hh; apply hY; linarith
  have hm : E.slope X X Y Y = -(r+s+t) := by
    rw [slope_of_Y_ne rfl hYn]
    simp only [ WeierstrassCurve.Affine.negY]
    convert (div_eq_iff (mul_ne_zero (by norm_num : (2:ℚ) ≠ 0) hY)).mpr htan.symm using 1; ring
  have hx : E.addX X X (E.slope X X Y Y)=x := by
    rw [WeierstrassCurve.Affine.addX, hm]
    simp only []
    linarith only [hdup]
  have hsame : ((2:ℕ) • (some X Y hQ : E.Point)).xRep = (some x y h).xRep := by
    rw [two_smul, add_self_of_Y_ne hYn]
    simp only [xRep_some, hx]
  rcases eq_or_eq_neg_of_xRep_eq_xRep hsame with hp | hp
  · exact ⟨some X Y hQ,hp⟩
  · refine ⟨-(some X Y hQ), ?_⟩
    simpa only [two_smul, neg_add, neg_neg] using congrArg Neg.neg hp

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma not_isSquare_prime (p : ℕ) (hp : p.Prime) : ¬IsSquare (p:ℚ) := by
  rintro ⟨r,hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have hv := congrArg (padicValRat p) hr
  rw [← pow_two, padicValRat.pow, padicValRat.self hp.one_lt] at hv
  omega

noncomputable def kummer : E.Point →+ Additive SquareClass × Additive SquareClass :=
  (alpha 0 (by norm_num) (by norm_num)).prod (alpha 5 (by norm_num) (by norm_num))

lemma kummer_halves (P : E.Point) : kummer ((2:ℕ) • P) = 0 := by
  rw [map_nsmul]
  rw [two_smul]
  apply Prod.ext <;> change (classOf _)*(classOf _)=1 <;> exact classOf_self_mul _

theorem kummer_eq_zero_iff (P : E.Point) : kummer P = 0 ↔ ∃ Q : E.Point, (2:ℕ) • Q=P := by
  constructor
  · intro hp
    have h₀ := congrArg Prod.fst hp
    have h₅ := congrArg Prod.snd hp
    cases P with
    | zero => exact ⟨0,by simp only [← zero_def, two_smul, zero_add]⟩
    | some x y h =>
      change classOf (adjusted (3*0^2-25) (x-0))=1 at h₀
      change classOf (adjusted (3*5^2-25) (x-5))=1 at h₅
      norm_num only [sub_zero] at h₀ h₅
      have hx : x ≠ 0 := by
        intro hx
        rw [hx] at h₀
        have hh := (classOf_eq_one_iff (by norm_num : (-25:ℚ) ≠ 0)).mp (by simpa [adjusted] using h₀)
        exact (by norm_num : ¬ (0:ℚ) ≤ -25) hh.nonneg
      have hs₀ : IsSquare x := (classOf_eq_one_iff hx).mp (by simpa [adjusted,hx] using h₀)
      have hx5 : x-5 ≠ 0 := by
        intro hh
        have he : x=5 := by linarith
        rw [he] at hs₀
        exact not_isSquare_prime 5 (by norm_num) hs₀
      have hs₅ : IsSquare (x-5) := (classOf_eq_one_iff hx5).mp (by simpa [adjusted,hx5] using h₅)
      apply exists_half_of_squares h hs₀ hs₅
      obtain ⟨r,hr⟩ := hs₀
      obtain ⟨s,hs⟩ := hs₅
      have hrr : r ≠ 0 := by intro hh; simp [hh] at hr; exact hx hr
      have hss : s ≠ 0 := by intro hh; simp [hh] at hs; exact hx5 hs
      refine ⟨y/(r*s), ?_⟩
      have he := equation h
      have he' : (r*s)^2*(x+5)=y^2 := by
        calc
          (r*s)^2*(x+5) = x*(x-5)*(x+5) := by rw [mul_pow, pow_two, pow_two, ←hr, ←hs]
          _ = y^2 := by nlinarith only [he]
      field_simp
      nlinarith only [he']
  · rintro ⟨Q,rfl⟩
    exact kummer_halves Q

end SingleFold.Descent

end OAI



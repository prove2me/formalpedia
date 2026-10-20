-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
-- name    : OAI_NumberTheory_SingleFold_EllipticHeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:11:48.418297+00:00
-- url     : https://prove2.me/theorems/242d045d-950e-459c-94d5-96ec1c17588b
-- title:
--   The naive height on $y^2=x^3-25x$ is almost a quadratic form
-- statement:
--   Let $E$ be the elliptic curve $y^2=x^3-25x$ over $\mathbb{Q}$, with point at infinity $O$. Let $h$ denote the logarithmic Weil height on projective space.
--
--   1. **Symmetric products.** There is a constant $C$ (for any field with admissible absolute values) such that for nonzero $u,v\in K^2$
--   $$
--   \bigl|h(u_0v_0:u_0v_1+u_1v_0:u_1v_1)-h(u)-h(v)\bigr|\le C .
--   $$
--   2. **Addition–subtraction map.** The map $(s,t,u)\mapsto\bigl((s+25u)^2,\,2t(s-25u),\,t^2-4su\bigr)$ sends the symmetric coordinates of $(x(P),x(Q))$ to a nonzero multiple of the symmetric coordinates of $(x(P+Q),x(P-Q))$.
--   3. **Naive height.** $h_{\mathrm{naive}}(P)$ is the height of $x(P)\in\mathbb{P}^1(\mathbb{Q})$, and there is $C$ with
--   $$
--   \bigl|h_{\mathrm{naive}}(P+Q)+h_{\mathrm{naive}}(P-Q)-2h_{\mathrm{naive}}(P)-2h_{\mathrm{naive}}(Q)\bigr|\le C .
--   $$
--
--   This approximate parallelogram law is the input of Tate's limit construction of the canonical height.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticHeight.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticHeight.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent

namespace OAI

namespace SingleFold.CurveHeight

section

open Height MvPolynomial

universe u

variable {K : Type u} [Field K]

noncomputable def symPoly : Fin 3 → MvPolynomial (Fin 2 × Fin 2) K :=
  ![X (0,0), X (0,1) + X (1,0), X (1,1)]

noncomputable def symCoeff : (Fin 2 × Fin 2) × Fin 3 → MvPolynomial (Fin 2 × Fin 2) K :=
  fun ij =>
    (if ij.1 = (0,0) then ![X (0,0), 0, 0]
    else if ij.1 = (1,1) then ![0, 0, X (1,1)]
    else ![-X (1,1), X ij.1, 0]) ij.2

lemma symPoly_homogeneous (i : Fin 3) : (symPoly (K := K) i).IsHomogeneous 1 := by
  fin_cases i <;> simp [symPoly, isHomogeneous_X, IsHomogeneous.add]

lemma symCoeff_homogeneous (ij : (Fin 2 × Fin 2) × Fin 3) :
    (symCoeff (K := K) ij).IsHomogeneous 1 := by
  rcases ij with ⟨⟨i,j⟩,k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [symCoeff, isHomogeneous_X, isHomogeneous_zero, IsHomogeneous.neg]

lemma symCoeff_condition (u v : Fin 2 → K) (k : Fin 2 × Fin 2) :
    ∑ j : Fin 3, (symCoeff (k,j)).eval (fun ij => u ij.1 * v ij.2) *
      (symPoly j).eval (fun ij => u ij.1 * v ij.2) = (u k.1 * v k.2) ^ (1 + 1) := by
  rcases k with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [symCoeff, symPoly, Fin.sum_univ_three] <;> ring

theorem symmetric_height_bound [AdmissibleAbsValues K] :
    ∃ C : ℝ, ∀ u v : Fin 2 → K, u ≠ 0 → v ≠ 0 →
      |logHeight ![u 0 * v 0, u 0 * v 1 + u 1 * v 0, u 1 * v 1] -
        (logHeight u + logHeight v)| ≤ C := by
  obtain ⟨C₁,h₁⟩ := logHeight_eval_le' (symPoly_homogeneous (K := K))
  obtain ⟨C₂,h₂⟩ := logHeight_eval_ge' (N := 1) (symCoeff_homogeneous (K := K))
  refine ⟨max C₁ (-C₂), ?_⟩
  intro u v hu hv
  have hlo := h₂ symPoly (symCoeff_condition u v)
  have hhi := h₁ (fun ij => u ij.1 * v ij.2)
  have hev : (fun j => (symPoly (K := K) j).eval (fun ij => u ij.1 * v ij.2)) =
      ![u 0 * v 0, u 0 * v 1 + u 1 * v 0, u 1 * v 1] := by
    ext j
    fin_cases j <;> simp [symPoly]
  rw [hev, logHeight_fun_mul_eq hu hv] at hlo hhi
  simp only [Nat.cast_one, one_mul] at hlo hhi
  apply abs_le.mpr
  constructor
  · have := le_max_right C₁ (-C₂)
    linarith
  · have := le_max_left C₁ (-C₂)
    linarith

end

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

abbrev E : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -25, 0⟩

instance : E.IsElliptic := by
  constructor
  norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma E_equation {x y : ℚ} (h : E.Nonsingular x y) : y ^ 2 = x ^ 3 - 25*x := by
  simpa [WeierstrassCurve.Affine.equation_iff, E, sub_eq_add_neg] using h.1

@[simp] lemma E_negY (x y : ℚ) : E.negY x y = -y := by simp []

lemma E_addSub_eval (s t u : ℚ) :
    (fun j => (WeierstrassCurve.addSubMap E j).eval ![s,t,u]) =
      ![(s+25*u)^2, 2*t*(s-25*u), t^2-4*s*u] := by
  ext j
  fin_cases j <;>
    simp [WeierstrassCurve.addSubMap, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;> ring

lemma difference_coordinates {x z y w : ℚ} (hx : x ≠ z)
    (h₁ : y^2 = x^3 - 25*x) (h₂ : w^2 = z^3 - 25*z) :
    let A := ((y-w)/(x-z))^2-x-z
    let B := ((y+w)/(x-z))^2-x-z
    (x-z)^2 * (A+B) = 2*(x+z)*(x*z-25) ∧
    (x-z)^2 * (A*B) = (x*z+25)^2 := by
  dsimp
  have hd : x-z ≠ 0 := sub_ne_zero.mpr hx
  constructor
  · field_simp
    linear_combination 2*h₁ + 2*h₂
  · field_simp
    linear_combination
      (y^2 + (x^3-25*x) - 2*w^2 - 2*(x+z)*(x-z)^2)*h₁ +
      (-2*(x^3-25*x) + w^2 + (z^3-25*z) - 2*(x+z)*(x-z)^2)*h₂

lemma addSub_diagonal (P : E.Point) :
    ∃ c : ℚ, c ≠ 0 ∧
      (fun j => (WeierstrassCurve.addSubMap E j).eval (P.sym2x P)) =
        c • (P+P).sym2x 0 := by
  cases P with
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    simp only [← zero_def, zero_add, sym2x_zero_zero, E_addSub_eval, one_smul]
    norm_num
  | some x y h =>
    have he := E_equation h
    rw [sym2x_some_some, E_addSub_eval]
    by_cases hy : y = 0
    · have hadd : (some x y h + some x y h : E.Point) = 0 :=
        add_self_of_Y_eq (by simp [hy])
      rw [hadd, sym2x_zero_zero]
      refine ⟨(x*x+25)^2, ?_, ?_⟩
      · have : 0 < x*x+25 := by nlinarith [sq_nonneg x]
        positivity
      · ext i
        fin_cases i
        · simp
        · change 2*(x+x)*(x*x-25*1) = (x*x+25)^2*0
          rw [hy] at he
          linear_combination -4*he
        · change (x+x)^2-4*(x*x)*1 = (x*x+25)^2*0
          ring
    · have hy' : y ≠ E.negY x y := by rw [E_negY]; intro hz; apply hy; linarith
      have hs : E.slope x x y y = (3*x^2-25)/(2*y) := by
        rw [slope_of_Y_ne rfl hy']
        simp []
        congr 1 <;> ring
      have hcoord : (4*y^2) * (((3*x^2-25)/(2*y))^2-x-x) = (x*x+25)^2 := by
        field_simp
        linear_combination -32*x*he
      rw [add_self_of_Y_ne hy', sym2x_some_zero]
      refine ⟨4*y^2, by positivity, ?_⟩
      ext i
      fin_cases i
      · change (x*x+25*1)^2 = (4*y^2)*
          (E.addX x x (E.slope x x y y))
        rw [WeierstrassCurve.Affine.addX, hs]
        simpa [E] using hcoord.symm
      · change 2*(x+x)*(x*x-25*1) = (4*y^2)*1
        linear_combination -4*he
      · change (x+x)^2-4*(x*x)*1 = (4*y^2)*0
        ring

lemma addSub_distinct {x z y w : ℚ} (h : E.Nonsingular x y) (h' : E.Nonsingular z w)
    (hx : x ≠ z) :
    ∃ c : ℚ, c ≠ 0 ∧
      (fun j => (WeierstrassCurve.addSubMap E j).eval
        ((some x y h).sym2x (some z w h'))) =
      c • ((some x y h + some z w h').sym2x (some x y h - some z w h')) := by
  have hc := difference_coordinates hx (E_equation h) (E_equation h')
  dsimp at hc
  rw [sub_eq_add_neg, neg_some, add_of_X_ne hx, add_of_X_ne hx, sym2x_some_some,
    sym2x_some_some, E_addSub_eval]
  refine ⟨(x-z)^2, pow_ne_zero _ (sub_ne_zero.mpr hx), ?_⟩
  ext i
  fin_cases i
  · change (x*z+25*1)^2 = (x-z)^2 *
      (E.addX x z (E.slope x z y w) * E.addX x z (E.slope x z y (E.negY z w)))
    rw [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addX,
      slope_of_X_ne hx, slope_of_X_ne hx, E_negY]
    simpa [E] using hc.2.symm
  · change 2*(x+z)*(x*z-25*1) = (x-z)^2 *
      (E.addX x z (E.slope x z y w) + E.addX x z (E.slope x z y (E.negY z w)))
    rw [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addX,
      slope_of_X_ne hx, slope_of_X_ne hx, E_negY]
    simpa [E] using hc.1.symm
  · change (x+z)^2-4*(x*z)*1 = (x-z)^2*1
    ring

theorem addSub_projective (P Q : E.Point) :
    ∃ c : ℚ, c ≠ 0 ∧
      (fun j => (WeierstrassCurve.addSubMap E j).eval (P.sym2x Q)) =
        c • (P+Q).sym2x (P-Q) := by
  by_cases hx : P.xRep = Q.xRep
  · rcases xRep_eq_xRep_iff.mp hx with heq | heq
    · subst P
      simpa only [sub_self] using addSub_diagonal Q
    · subst P
      obtain ⟨c,hc,he⟩ := addSub_diagonal Q
      refine ⟨c,hc,?_⟩
      rw [sym2x_neg_left, neg_add_cancel]
      have hsub : -Q-Q = -(Q+Q) := by abel
      rw [hsub, sym2x_neg_right, sym2x_comm (0 : E.Point) (Q+Q)]
      exact he
  · cases P with
    | zero =>
      cases Q with
      | zero => exact (hx rfl).elim
      | some x y h =>
        refine ⟨1, one_ne_zero, ?_⟩
        simp only [← zero_def, zero_add, zero_sub, sym2x_neg_right,
          sym2x_zero_some, sym2x_some_some, E_addSub_eval, one_smul]
        ext i
        fin_cases i <;> simp <;> ring
    | some x y h =>
      cases Q with
      | zero =>
        refine ⟨1, one_ne_zero, ?_⟩
        simp only [← zero_def, add_zero, sub_zero, sym2x_some_zero,
          sym2x_some_some, E_addSub_eval, one_smul]
        ext i
        fin_cases i <;> simp <;> ring
      | some z w h' =>
        apply addSub_distinct h h'
        intro hsame
        apply hx
        simp [hsame]

noncomputable def naiveHeight (P : E.Point) : ℝ := Height.logHeight P.xRep

theorem approximate_parallelogram :
    ∃ C : ℝ, ∀ P Q : E.Point,
      |naiveHeight (P+Q) + naiveHeight (P-Q) -
        2*(naiveHeight P+naiveHeight Q)| ≤ C := by
  obtain ⟨C₁,h₁⟩ := symmetric_height_bound (K := ℚ)
  obtain ⟨C₂,h₂⟩ := E.abs_logHeight_addSubMap_sub_two_mul_logHeight_le
  refine ⟨3*C₁+C₂, ?_⟩
  intro P Q
  have hPQ := h₁ P.xRep Q.xRep P.xRep_ne_zero Q.xRep_ne_zero
  have hpm := h₁ (P+Q).xRep (P-Q).xRep (P+Q).xRep_ne_zero (P-Q).xRep_ne_zero
  change |Height.logHeight (P.sym2x Q) - (naiveHeight P + naiveHeight Q)| ≤ C₁ at hPQ
  change |Height.logHeight ((P+Q).sym2x (P-Q)) -
    (naiveHeight (P+Q)+naiveHeight (P-Q))| ≤ C₁ at hpm
  obtain ⟨c,hc,he⟩ := addSub_projective P Q
  have hmap := h₂ (P.sym2x Q)
  rw [he, Height.logHeight_smul_eq_logHeight _ hc] at hmap
  rcases abs_le.mp hPQ with ⟨hl₁,hu₁⟩
  rcases abs_le.mp hpm with ⟨hl₂,hu₂⟩
  rcases abs_le.mp hmap with ⟨hl₃,hu₃⟩
  apply abs_le.mpr
  constructor <;> linarith

end SingleFold.CurveHeight

end OAI



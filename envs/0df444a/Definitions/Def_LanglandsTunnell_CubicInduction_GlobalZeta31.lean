-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
-- name    : LanglandsTunnell_CubicInduction_GlobalZeta31
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/b69c0c24-9d04-55a5-be3b-fa5d5b1bed02
-- title:
--   Weyl and unipotent elements; global zeta integrals for GL(3)
-- statement:
--   The first part of the module records explicit elements of $GL_3(A)$ over a commutative ring $A$, each given together with its inverse matrix: `lowerUnipotent21 x` is the lower unipotent matrix with $1$ on the diagonal and the single off-diagonal entry $x$ in position $(2,1)$; `longWeyl3` is the antidiagonal permutation matrix $w_3$ with $1$'s in positions $(1,3),(2,2),(3,1)$; and `weylPrime3` is the transposition matrix $w'$ fixing the first basis vector and interchanging the second and third. For a function $W$ on $GL_3(A)$ with values in any type, `dualWhittakerFn3` is the function $g \mapsto W(w_3\,{}^t g^{-1})$, the transpose-inverse being Mathlib-free project notation `transposeInv3`. The accompanying identities state that $w'$ is an involution, hence equal to its own inverse and to its own transpose-inverse; that $w'\,{}^t(\mathrm{radicalP21}\,v)^{-1}\,w'$ has matrix with $1$'s on the diagonal, $-v_0$ in position $(2,1)$ and $-v_1$ in position $(2,3)$; and that ${}^t(\mathrm{lowerUnipotent21}\,x)^{-1} = \mathrm{upperUnipotent3}\,(-x)\,0\,0$.
--
--   The second part defines, for a complex-valued $W$ on the adelic $GL_3$ over $\mathbb{Q}$, a character $\chi$ of the idele group, $s \in \mathbb{C}$ and $g$ in the adelic $GL_3$, three Bochner integrals (so the value is $0$ where the integrand is not integrable). `globalZeta31` is
--   $$\int_{\mathbb{A}^\times}\Big(\int_{\mathbb{A}} W\big(\mathrm{iotaGL}(\mathrm{diagUnitGL2}\,a)\cdot \mathrm{lowerUnipotent21}(x)\cdot g\big)\,dx\Big)\,\chi(a)\,\|a\|^{s-1}\,d^\times a,$$
--   the inner integral against the adelic additive Haar measure, the outer against the Haar measure `idelicHaar` on the ideles (for the Borel $\sigma$-algebra `ideleBorel`), and $\|a\|$ the idele norm defined through the modulus character of the adeles; here $a$ enters through the $GL_2$-element `diagUnitGL2 a` embedded in $GL_3$ by `iotaGL`. `globalZeta30` is the same integral with the unipotent integration omitted, and `globalZetaDual31 W χ s g` is defined as `globalZeta31` applied to $\tilde W$, the character $\chi^{-1}$, the same $s$, and the point $w'\,{}^t g^{-1}$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient objects — `GL (Fin 3) A`, the adele and idele rings of a number field, Haar measure and the modulus character underlying the idele norm; the explicit Weyl and unipotent elements, the transpose-inverse dual of a function on $GL_3$, and the three zeta integrals are the project's own.
--
--   **Where it is used.** These are the integrals whose analytic continuation and functional equation are needed in the cubic-induction analysis of the $GL_3$ automorphic form attached to a cubic extension, the analytic input to the Langlands–Tunnell theorem used to start the modularity argument for Fermat's Last Theorem. The Weyl-element identities are what relate the zeta integral at $g$ to its dual at $w'\,{}^t g^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_GlobalZeta31.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Furniture

variable {A : Type*} [CommRing A]

def lowerUnipotent21 (x : A) : GL (Fin 3) A where
  val := !![1, 0, 0; x, 1, 0; 0, 0, 1]
  inv := !![1, 0, 0; -x, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem lowerUnipotent21_coe (x : A) :
    ((lowerUnipotent21 x : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; x, 1, 0; 0, 0, 1] :=
  rfl

def longWeyl3 : GL (Fin 3) A where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem longWeyl3_coe :
    ((longWeyl3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  rfl

def dualWhittakerFn3 {R : Type*} (W : GL (Fin 3) A → R) : GL (Fin 3) A → R :=
  fun g => W (longWeyl3 * transposeInv3 g)

theorem dualWhittakerFn3_apply {R : Type*} (W : GL (Fin 3) A → R) (g : GL (Fin 3) A) :
    dualWhittakerFn3 W g = W (longWeyl3 * transposeInv3 g) :=
  rfl

def weylPrime3 : GL (Fin 3) A where
  val := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  inv := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem weylPrime3_coe :
    ((weylPrime3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem weylPrime3_mul_self : (weylPrime3 : GL (Fin 3) A) * weylPrime3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylPrime3_inv : (weylPrime3 : GL (Fin 3) A)⁻¹ = weylPrime3 :=
  inv_eq_of_mul_eq_one_right weylPrime3_mul_self

theorem transposeInv3_weylPrime3 : transposeInv3 (weylPrime3 : GL (Fin 3) A) = weylPrime3 := by
  refine Units.ext ?_
  change (((weylPrime3 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [weylPrime3_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3 (v : Fin 2 → A) :
    ((weylPrime3 * transposeInv3 (radicalP21 v) * weylPrime3 : GL (Fin 3) A) :
        Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; -(v 0), 1, -(v 1); 0, 0, 1] := by
  have hinv : (((radicalP21 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, -(v 0); 0, 1, -(v 1); 0, 0, 1] := by
    rw [Matrix.coe_units_inv, radicalP21_coe]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have htr : ((transposeInv3 (radicalP21 v) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; 0, 1, 0; -(v 0), -(v 1), 1] := by
    change (((radicalP21 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  rw [Units.val_mul, Units.val_mul, htr, weylPrime3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem transposeInv3_lowerUnipotent21 (x : A) :
    transposeInv3 (lowerUnipotent21 x) = upperUnipotent3 (-x) 0 0 := by
  refine Units.ext ?_
  have hinv : (((lowerUnipotent21 x : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -x, 1, 0; 0, 0, 1] := by
    rw [Matrix.coe_units_inv, lowerUnipotent21_coe]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  change (((lowerUnipotent21 x : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [hinv, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

end Furniture

section Global

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

def globalZeta31 (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  ∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∫ x : AdeleRing (𝓞 ℚ) ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) *
        ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
    ∂(NumberField.Idele.idelicHaar ℚ)

def globalZeta30 (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
    ∂(NumberField.Idele.idelicHaar ℚ)

def globalZetaDual31 (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (s : ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  globalZeta31 (dualWhittakerFn3 W) χ⁻¹ s (weylPrime3 * transposeInv3 g)

end Global

end LanglandsTunnell.CubicInduction

end

#check @LanglandsTunnell.CubicInduction.lowerUnipotent21
#check @LanglandsTunnell.CubicInduction.longWeyl3
#check @LanglandsTunnell.CubicInduction.dualWhittakerFn3
#check @LanglandsTunnell.CubicInduction.globalZeta31
#check @LanglandsTunnell.CubicInduction.weylPrime3
#check @LanglandsTunnell.CubicInduction.globalZeta30
#check @LanglandsTunnell.CubicInduction.globalZetaDual31
#print axioms LanglandsTunnell.CubicInduction.weylPrime3_mul_self
#print axioms LanglandsTunnell.CubicInduction.transposeInv3_weylPrime3
#print axioms LanglandsTunnell.CubicInduction.weylPrime3_mul_transposeInv3_radicalP21_mul_weylPrime3
#print axioms LanglandsTunnell.CubicInduction.transposeInv3_lowerUnipotent21
#print axioms LanglandsTunnell.CubicInduction.globalZeta30
#print axioms LanglandsTunnell.CubicInduction.globalZetaDual31
#print axioms LanglandsTunnell.CubicInduction.globalZeta31



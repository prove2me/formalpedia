-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
-- name    : LanglandsTunnell_CubicInduction_TorusValues
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/efed58ef-0132-5e71-b526-832915606a4f
-- title:
--   Spherical torus values and the GL₃ Whittaker-value clause
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, let $p$ denote the absolute norm of $v$, regarded through `ratPrimeUnit` as a unit of the completion $\mathbb{Q}_v$, and write $\iota$ for the embedding `iotaGL` of $GL_2$ into $GL_3$ as the upper-left block with $1$ in the last diagonal entry. Three things are defined. First, `sphericalTorusValue e₁ e₂ e₃ : ℕ → ℂ` for complex parameters $e_1,e_2,e_3$: the values at $0,1,2$ are $1$, $e_1$, $e_1^2-e_2$, and thereafter $h_{n+3}=e_1h_{n+2}-e_2h_{n+1}+e_3h_n$; these are the complete homogeneous symmetric functions of three variables expressed through their elementary symmetric values. Second, over any commutative ring $A$, `diagUnits2 x y` is the element of $GL_2(A)$ with underlying matrix $\mathrm{diag}(x,y)$ and inverse $\mathrm{diag}(x^{-1},y^{-1})$, for units $x,y$; `coe_diagUnits2` records its matrix and `diagUnits2_one_right` identifies $\mathrm{diag}(x,1)$ with `diagUnitGL2 x`. From it, `twoRowPointLocal v k₁ k₂` $:= \iota(\mathrm{diag}(p^{k_1},p^{k_2}))$, i.e. $\mathrm{diag}(p^{k_1},p^{k_2},1)$ in $GL_3(\mathbb{Q}_v)$, with `twoRowPointLocal_zero_right` giving `twoRowPointLocal v k 0 = iotaTorusLocal v k`.
--
--   Third, for a number-field setting $\mathcal{O}_{\mathbb{Q}}\to\mathcal{O}_K$ integral and a function $c$ on the primes of $\mathcal{O}_K$, with $e_i=$ `inducedE1/2/3 ℚ c v`, the coefficients (up to sign) of the induced Euler polynomial $\prod_{\mathfrak{P}\mid v}\bigl(1-c(\mathfrak{P})X^{f(\mathfrak{P}/v)}\bigr)$ in degrees $1,2,3$, the predicate `HasSphericalTorusValuesAt c v W` on functions $W$ on $GL_3(\mathbb{Q}_v)$ is the conjunction of: $W(\mathrm{diag}(p^n,1,1)) = N(v)^{-n}h_n$ for all $n$, and, whenever $k_2+1\le k_1$, $W(\mathrm{diag}(p^{k_1},p^{k_2+1},1)) = N(v)^{-k_1}\bigl(h_{k_1}h_{k_2+1}-h_{k_1+1}h_{k_2}\bigr)$, where $N(v)=$ `cNormQ v` is the absolute norm of $v$ in $\mathbb{C}$. The second expression is the $2\times 2$ Jacobi–Trudi determinant, so the prescribed values are Schur functions at the dominant weights. The predicate only prescribes values; it asserts nothing about existence. Finally, `not_hasSphericalTorusValuesAt_zero` states that the identically zero function fails it, since the clause at $n=0$ would force $0=1$.
--
--   **Relation to Mathlib.** Mathlib supplies the general linear groups, adic completions and ideal norms used here; the recursion `sphericalTorusValue`, the $GL_3$ torus points and the value predicate are the project's own, and the symmetric functions are set up by their own three-term recursion rather than through any symmetric-function API.
--
--   **Where it is used.** These values are the normalisation used in the cubic-induction construction entering the Langlands–Tunnell input to modularity: a candidate Whittaker function on $GL_3$ over $\mathbb{Q}_v$ is pinned down on the diagonal torus by the Euler data coming from a character of a cubic extension, whose local factors are encoded by `inducedE1`, `inducedE2`, `inducedE3`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_TorusValues.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix
open LanglandsTunnell.RankinSelberg

noncomputable section

namespace LanglandsTunnell.CubicInduction

def sphericalTorusValue (e₁ e₂ e₃ : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => e₁
  | 2 => e₁ ^ 2 - e₂
  | n + 3 =>
    e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1) +
      e₃ * sphericalTorusValue e₁ e₂ e₃ n

section TwoRowPoint

variable {A : Type*} [CommRing A]

def diagUnits2 (x y : Aˣ) : GL (Fin 2) A where
  val := !![(x : A), 0; 0, (y : A)]
  inv := !![((x⁻¹ : Aˣ) : A), 0; 0, ((y⁻¹ : Aˣ) : A)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem coe_diagUnits2 (x y : Aˣ) :
    ((diagUnits2 x y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, (y : A)] :=
  rfl

theorem diagUnits2_one_right (x : Aˣ) : diagUnits2 x 1 = diagUnitGL2 x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, diagUnitGL2]

variable (v : HeightOneSpectrum (𝓞 ℚ))

def twoRowPointLocal (k₁ k₂ : ℕ) : GL (Fin 3) (v.adicCompletion ℚ) :=
  iotaGL (diagUnits2 (ratPrimeUnit v ^ k₁) (ratPrimeUnit v ^ k₂))

theorem twoRowPointLocal_zero_right (k : ℕ) : twoRowPointLocal v k 0 = iotaTorusLocal v k := by
  simp only [twoRowPointLocal, iotaTorusLocal, pow_zero, diagUnits2_one_right, diagHom_apply]

end TwoRowPoint

section Clause

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def HasSphericalTorusValuesAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ) : Prop :=
  (∀ n : ℕ, W (iotaTorusLocal v n) =
    (cNormQ v)⁻¹ ^ n * sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) n) ∧
  (∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
    (cNormQ v)⁻¹ ^ k₁ *
      (sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) k₁ *
          sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) (k₂ + 1) -
        sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) (k₁ + 1) *
          sphericalTorusValue (inducedE1 ℚ c v) (inducedE2 ℚ c v) (inducedE3 ℚ c v) k₂))

theorem not_hasSphericalTorusValuesAt_zero (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : ¬ HasSphericalTorusValuesAt c v (fun _ => (0 : ℂ)) := by
  intro h
  have h0 := h.1 0
  simp [sphericalTorusValue] at h0

end Clause

end LanglandsTunnell.CubicInduction

end



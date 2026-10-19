-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:05:07.594191+00:00
-- url     : https://prove2.me/theorems/ad78ec97-cd63-4f12-868a-b07f6d367a0b
-- title:
--   Sorting coordinates of functions on the cube
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   Let $F:\{0,1\}^n\to\mathbb{R}$, and for a coordinate $i$ and bit $b$ let $x^{i\to b}$ be $x$ with coordinate $i$ set to $b$. Then $x^{i\to x_i}=x$, and setting twice keeps the last value.
--
--   1. **Monotone in one coordinate.** $F$ is increasing in $i$ if $F(x^{i\to0})\le F(x^{i\to1})$ for all $x$.
--   2. **Sorting a coordinate.** $\sigma_iF(x)=\max\bigl(F(x^{i\to0}),F(x^{i\to1})\bigr)$ if $x_i=1$, and the minimum otherwise. Along coordinate $i$ the pair mean is unchanged and the half-difference becomes its absolute value:
--   $$
--   \frac{\sigma_iF(x^{i\to0})+\sigma_iF(x^{i\to1})}{2}=\frac{F(x^{i\to0})+F(x^{i\to1})}{2},\qquad \frac{\sigma_iF(x^{i\to1})-\sigma_iF(x^{i\to0})}{2}=\Bigl|\frac{F(x^{i\to1})-F(x^{i\to0})}{2}\Bigr| .
--   $$
--   3. **Noise off one coordinate.** The kernel $\prod_{j\ne i}\bigl(\frac{1+u}2$ or $\frac{1-u}2\bigr)$ acts on all coordinates except $i$. The associated operator is $x\mapsto\sum_y\frac12K^{(i)}_u(x,y)F(y)$.
--   4. **Sorting a list of coordinates.** Apply $\sigma_i$ successively for $i$ in a given list.
--
--   Sorting every coordinate turns $F$ into an increasing function while preserving the quantities relevant to the information bound. This reduces the problem to monotone functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SoftChannel204 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def setBit (i : Fin n) (b : Bool) (x : Cube n) : Cube n := Function.update x i b

@[simp] theorem setBit_apply_same (i : Fin n) (b : Bool) (x : Cube n) :
    setBit i b x i = b := Function.update_self _ _ _

@[simp] theorem setBit_self (i : Fin n) (x : Cube n) : setBit i (x i) x = x :=
  Function.update_eq_self _ _

@[simp] theorem setBit_setBit (i : Fin n) (a b : Bool) (x : Cube n) :
    setBit i b (setBit i a x) = setBit i b x := Function.update_idem _ _ _

def IsIncreasingIn (i : Fin n) (F : Cube n → ℝ) : Prop :=
  ∀ x, F (setBit i false x) ≤ F (setBit i true x)

def sortCoordinate (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  if x i then max (F (setBit i false x)) (F (setBit i true x))
  else min (F (setBit i false x)) (F (setBit i true x))

@[simp] theorem sortCoordinate_false (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    sortCoordinate i F (setBit i false x) =
      min (F (setBit i false x)) (F (setBit i true x)) := by
  simp [sortCoordinate]

@[simp] theorem sortCoordinate_true (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    sortCoordinate i F (setBit i true x) =
      max (F (setBit i false x)) (F (setBit i true x)) := by
  simp [sortCoordinate]

def coordinatePairMean (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i false x) + F (setBit i true x)) / 2

def coordinatePairDifference (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i true x) - F (setBit i false x)) / 2

def coordinateOffKernel (i : Fin n) (u : ℝ) (x y : Cube n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    if x j = y j then (1 + u) / 2 else (1 - u) / 2

def coordinateOffNoise (i : Fin n) (u : ℝ) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, coordinateOffKernel i u x y / 2 * F y

@[simp] theorem coordinatePairMean_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    coordinatePairMean i (sortCoordinate i F) = coordinatePairMean i F := by
  funext x
  simp only [coordinatePairMean, sortCoordinate_false, sortCoordinate_true, min_add_max]

@[simp] theorem coordinatePairDifference_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    coordinatePairDifference i (sortCoordinate i F) =
      fun x => |coordinatePairDifference i F x| := by
  funext x
  simp only [coordinatePairDifference, sortCoordinate_false, sortCoordinate_true]
  rcases le_total (F (setBit i false x)) (F (setBit i true x)) with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonneg (div_nonneg (sub_nonneg.mpr h) (by norm_num))]
  · rw [min_eq_right h, max_eq_left h, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr h) (by norm_num))]
    ring

def sortCoordinates : List (Fin n) → (Cube n → ℝ) → Cube n → ℝ
  | [], F => F
  | i :: is, F => sortCoordinates is (sortCoordinate i F)

end LeanBlast.CourtadeKumar

end

end OAI



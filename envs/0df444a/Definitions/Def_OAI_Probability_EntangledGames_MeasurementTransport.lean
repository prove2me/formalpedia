-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
-- name    : OAI_Probability_EntangledGames_MeasurementTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:53:30.710666+00:00
-- url     : https://prove2.me/theorems/31ad808c-0e92-41ec-a32b-7b2c0b8ae90a
-- title:
--   Support inverse, range projection, and transport of a measurement through a linear map
-- statement:
--   Let $m,n$ be finite index sets and $A$ a finite set of outcomes. For a complex matrix $F$, $F^*$ is its conjugate transpose and $I$ an identity matrix of the appropriate size.
--
--   1. **Support inverse.** For $T\in\mathbb{C}^{n\times n}$, $T^{+}$ is the functional calculus of $t\mapsto t^{-1}$ with the convention $0^{-1}=0$. For Hermitian $T=\sum_i\lambda_i\,u_iu_i^*$ (orthonormal eigenvectors $u_i$) this is
--   $$T^{+}=\sum_{i:\,\lambda_i\neq 0}\lambda_i^{-1}\,u_iu_i^*,$$
--   the Moore–Penrose pseudo-inverse: it inverts $T$ on its support and vanishes on its kernel.
--   2. **Range projection.** For $F\in\mathbb{C}^{m\times n}$, $\Pi_F=F\,(F^*F)^{+}\,F^*\in\mathbb{C}^{m\times m}$, the orthogonal projection onto the column space of $F$.
--   3. **Transported effects.** For $F\in\mathbb{C}^{m\times n}$, a family $(G_a)_{a\in A}$ of $n\times n$ matrices and a default outcome $a_0\in A$,
--   $$E_a=\bigl(F(F^*F)^{+}\bigr)\,G_a\,\bigl(F(F^*F)^{+}\bigr)^{*}+[a=a_0]\,(I-\Pi_F)\in\mathbb{C}^{m\times m}\qquad(a\in A),$$
--   where $[a=a_0]$ equals $1$ if $a=a_0$ and $0$ otherwise.
--
--   The file proves: $T^{+}$ is Hermitian for every $T$, and $T^{+}TT^{+}=T^{+}$ for Hermitian $T$; $\Pi_F$ is Hermitian and idempotent, and $I-\Pi_F$ is positive semidefinite; if every $G_a$ is positive semidefinite then every $E_a$ is positive semidefinite; and if $\sum_aG_a=F^*F$ then $\sum_aE_a=I$.
--
--   Hence a decomposition $F^*F=\sum_aG_a$ into positive semidefinite parts on the input side of $F$ is transported to a genuine measurement (a POVM) $(E_a)_{a\in A}$ on the output space $\mathbb{C}^m$, the weight $I-\Pi_F$ outside the range of $F$ being assigned to the default outcome $a_0$. Under these two hypotheses the transported measurement satisfies the pull-back identity $F^*E_aF=G_a$ for every $a$, so a measurement performed after the linear map $F$ can be replaced by a measurement on the target space.
--
--   **Formalization Note** `supportInverse T` is `cfc (fun t => t⁻¹) T`; Lean has `0⁻¹ = 0`, and `cfc` returns $0$ for a non-Hermitian argument, which is why `supportInverse T` is Hermitian without hypotheses. The definitions are `supportInverse`, `rangeProjection` and `transportedEffect`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/MeasurementTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/MeasurementTransport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification

namespace OAI

universe u_n u_m u_A

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace ThresholdParallelRepetition.MeasurementTransport
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def supportInverse (T : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun t : ℝ => t⁻¹) T

lemma supportInverse_isHermitian (T : Matrix n n ℂ) : (supportInverse T).IsHermitian :=
  (cfc_predicate (fun t : ℝ => t⁻¹) T).isHermitian

lemma supportInverse_mul_self_mul {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    supportInverse T * T * supportInverse T = supportInverse T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change cfc (fun t : ℝ => t⁻¹) T * T * cfc (fun t : ℝ => t⁻¹) T = _
  calc
    _ = cfc (fun t : ℝ => t⁻¹) T * cfc (fun t : ℝ => t) T *
        cfc (fun t : ℝ => t⁻¹) T := by rw [hid]
    _ = cfc (fun t : ℝ => t⁻¹ * t * t⁻¹) T := by
      erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t⁻¹ * t) (fun t : ℝ => t⁻¹) T
          (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = _ := by apply cfc_congr; intro t _; by_cases ht : t = 0 <;> simp [ht]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

def rangeProjection (F : Matrix m n ℂ) : Matrix m m ℂ :=
  F * supportInverse (Fᴴ * F) * Fᴴ

omit [DecidableEq m] in
lemma rangeProjection_isHermitian (F : Matrix m n ℂ) :
    (rangeProjection F).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [rangeProjection, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (supportInverse_isHermitian _).eq, Matrix.mul_assoc]

omit [DecidableEq m] in
lemma rangeProjection_sq (F : Matrix m n ℂ) :
    rangeProjection F * rangeProjection F = rangeProjection F := by
  have h := supportInverse_mul_self_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  unfold rangeProjection
  calc
    _ = F * (supportInverse (Fᴴ * F) * (Fᴴ * F) * supportInverse (Fᴴ * F)) * Fᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

lemma complement_posSemidef (F : Matrix m n ℂ) : (1 - rangeProjection F).PosSemidef := by
  have h : (1 - rangeProjection F)ᴴ * (1 - rangeProjection F) = 1 - rangeProjection F := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (rangeProjection_isHermitian F).eq,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, rangeProjection_sq]
    abel
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

variable {A : Type u_A} [Fintype A] [DecidableEq A]

def transportedEffect (F : Matrix m n ℂ) (G : A → Matrix n n ℂ) (a₀ a : A) : Matrix m m ℂ :=
  (F * supportInverse (Fᴴ * F)) * G a * (F * supportInverse (Fᴴ * F))ᴴ +
    if a = a₀ then 1 - rangeProjection F else 0

omit [Fintype A] in
lemma transportedEffect_pos (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (a₀ a : A) : (transportedEffect F G a₀ a).PosSemidef := by
  apply ((hG a).mul_mul_conjTranspose_same _).add
  split_ifs
  · exact complement_posSemidef F
  · exact Matrix.PosSemidef.zero

lemma transportedEffect_sum (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∑ a, G a = Fᴴ * F) (a₀ : A) : ∑ a, transportedEffect F G a₀ a = 1 := by
  have h := supportInverse_mul_self_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  simp only [transportedEffect, Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hG, Matrix.conjTranspose_mul,
    (supportInverse_isHermitian _).eq]
  rw [show (F * supportInverse (Fᴴ * F)) * (Fᴴ * F) * (supportInverse (Fᴴ * F) * Fᴴ) =
      F * (supportInverse (Fᴴ * F) * (Fᴴ * F) * supportInverse (Fᴴ * F)) * Fᴴ by
      simp only [Matrix.mul_assoc], h]
  unfold rangeProjection
  abel

end ThresholdParallelRepetition.MeasurementTransport

end

end OAI



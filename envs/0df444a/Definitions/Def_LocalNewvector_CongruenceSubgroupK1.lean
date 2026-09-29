-- Prove2me | Definitions.Def_LocalNewvector_CongruenceSubgroupK1
-- name    : LocalNewvector_CongruenceSubgroupK1
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/d001c569-1a34-50a0-bb5a-a584ac2baee7
-- title:
--   Congruence subgroups K0​(ϖn), K1​(ϖn) of GL2​
-- statement:
--   Throughout, $R$ is a commutative ring, $\varpi \in R$ an element, and $K$ a field equipped with an $R$-algebra structure; the $p$-adic instance is $R = \mathbb{Z}_p$, $K = \mathbb{Q}_p$, $\varpi = p$. For each $n \in \mathbb{N}$ two subgroups of $\mathrm{GL}_2(K)$ are defined, membership in both being stated in terms of the existence of a lift along the group homomorphism $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ induced by $\operatorname{algebraMap} R K$. An element $x \in \mathrm{GL}_2(K)$ lies in `congruenceK0 ϖ n` when there is $y \in \mathrm{GL}_2(R)$ mapping to $x$ whose lower-left entry $y_{1,0}$ lies in the ideal $(\varpi^n)$; it lies in `congruenceK1 ϖ n` when in addition the chosen lift satisfies $y_{1,1} - 1 \in (\varpi^n)$. Thus the invertibility requirement is carried by the type $\mathrm{GL}_2(R)$ rather than by a determinant condition, and the congruence conditions are imposed on some lift, not on all of them; when $R \to K$ is injective this reproduces the usual definitions. Closure under multiplication and inversion is proved by the explicit $2 \times 2$ entry formulas, inversion using the adjugate together with invertibility of the determinant of a lift.
--
--   The accompanying lemmas record: the membership criteria `mem_congruenceK0_iff` and `mem_congruenceK1_iff`, restating the defining conditions; the inclusion $K_1(\varpi^n) \le K_0(\varpi^n)$; that at $n = 0$ both subgroups equal the image of $\mathrm{GL}_2(R)$ in $\mathrm{GL}_2(K)$, i.e. the range of the induced homomorphism; and that both families are antitone in $n$, since $m \le n$ gives $(\varpi^n) \subseteq (\varpi^m)$. Finally, for a prime $p$, `padicK0 p n` and `padicK1 p n` are abbreviations for the two subgroups of $\mathrm{GL}_2(\mathbb{Q}_p)$ obtained from $R = \mathbb{Z}_p$ and $\varpi = p$.
--
--   **Relation to Mathlib.** Mathlib's congruence subgroups `Gamma0`/`Gamma1` are defined for $\mathrm{SL}_2(\mathbb{Z})$ by reduction of entries; the subgroups of $\mathrm{GL}_2(K)$ defined here, by existence of a lift to $\mathrm{GL}_2(R)$ with prescribed congruences on the bottom row, are the project's own.
--
--   **Where it is used.** These are the open compact subgroups whose fixed vectors govern local newvector theory for smooth representations of $\mathrm{GL}_2(\mathbb{Q}_p)$, and hence the conductor bookkeeping used on the automorphic side of the modularity argument; the conductor condition itself is formulated in the companion module on conductor data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalNewvector_CongruenceSubgroupK1.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def congruenceK0 (ϖ : R) (n : ℕ) : Subgroup (GL (Fin 2) K) where
  carrier := {x | ∃ y : GL (Fin 2) R,
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
    (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n}}
  one_mem' := ⟨1, map_one _, by simp⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨y₁, rfl, h₁⟩ ⟨y₂, rfl, h₂⟩
    refine ⟨y₁ * y₂, map_mul _ _ _, ?_⟩
    have hentry : ((y₁ * y₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0
        = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 0
          + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 0 := by
      simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hentry]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  inv_mem' := by
    rintro x ⟨y, rfl, h⟩
    refine ⟨y⁻¹, map_inv _ _, ?_⟩
    have hco : ((y⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
        = ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ := Matrix.coe_units_inv y
    have hadj : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 0
        = Ring.inverse (y : Matrix (Fin 2) (Fin 2) R).det
            * (-(y : Matrix (Fin 2) (Fin 2) R) 1 0) := by
      rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
      simp [smul_eq_mul]
    rw [hco, hadj]
    exact Ideal.mul_mem_left _ _ (Submodule.neg_mem _ h)

theorem mem_congruenceK0_iff {ϖ : R} {n : ℕ} {x : GL (Fin 2) K} :
    x ∈ congruenceK0 (K := K) ϖ n ↔
      ∃ y : GL (Fin 2) R,
        Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
        (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n} :=
  Iff.rfl

theorem congruenceK0_zero (ϖ : R) :
    congruenceK0 (K := K) ϖ 0
      = (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  ext x
  simp [mem_congruenceK0_iff, MonoidHom.mem_range, pow_zero, Ideal.span_singleton_one]

def congruenceK1 (ϖ : R) (n : ℕ) : Subgroup (GL (Fin 2) K) where
  carrier := {x | ∃ y : GL (Fin 2) R,
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
    (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n} ∧
    (y : Matrix (Fin 2) (Fin 2) R) 1 1 - 1 ∈ Ideal.span {ϖ ^ n}}
  one_mem' := ⟨1, map_one _, by simp, by simp⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨y₁, rfl, hc₁, hd₁⟩ ⟨y₂, rfl, hc₂, hd₂⟩
    refine ⟨y₁ * y₂, map_mul _ _ _, ?_, ?_⟩
    · have hentry : ((y₁ * y₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0
          = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 0
            + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 0 := by
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hentry]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc₁) (Ideal.mul_mem_left _ _ hc₂)
    · have hentry : ((y₁ * y₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1
          = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 1
            + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 1 := by
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      have hsplit : (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 1
            + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 1 - 1
          = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 1
            + (((y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 - 1) * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 1
              + ((y₂ : Matrix (Fin 2) (Fin 2) R) 1 1 - 1)) := by ring
      rw [hentry, hsplit]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc₁)
        (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hd₁) hd₂)
  inv_mem' := by
    rintro x ⟨y, rfl, hc, hd⟩
    refine ⟨y⁻¹, map_inv _ _, ?_, ?_⟩
    · have hco : ((y⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
          = ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ := Matrix.coe_units_inv y
      have hadj : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 0
          = Ring.inverse (y : Matrix (Fin 2) (Fin 2) R).det
              * (-(y : Matrix (Fin 2) (Fin 2) R) 1 0) := by
        rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
        simp [smul_eq_mul]
      rw [hco, hadj]
      exact Ideal.mul_mem_left _ _ (Submodule.neg_mem _ hc)
    · have hco : ((y⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
          = ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ := Matrix.coe_units_inv y
      have hadj : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 1
          = Ring.inverse (y : Matrix (Fin 2) (Fin 2) R).det
              * (y : Matrix (Fin 2) (Fin 2) R) 0 0 := by
        rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
        simp [smul_eq_mul]
      have hone : Ring.inverse ((y : Matrix (Fin 2) (Fin 2) R).det)
          * ((y : Matrix (Fin 2) (Fin 2) R)).det = 1 := by
        refine Ring.inverse_mul_cancel _ ?_
        refine ⟨⟨(y : Matrix (Fin 2) (Fin 2) R).det, (y.inv).det, ?_, ?_⟩, rfl⟩
        · rw [← Matrix.det_mul, y.val_inv, Matrix.det_one]
        · rw [← Matrix.det_mul, y.inv_val, Matrix.det_one]
      have hsplit : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 1 - 1
          = Ring.inverse ((y : Matrix (Fin 2) (Fin 2) R).det)
              * ((y : Matrix (Fin 2) (Fin 2) R) 0 0
                  * (1 - (y : Matrix (Fin 2) (Fin 2) R) 1 1)
                + (y : Matrix (Fin 2) (Fin 2) R) 0 1
                  * (y : Matrix (Fin 2) (Fin 2) R) 1 0) := by
        rw [hadj]
        rw [Matrix.det_fin_two] at hone ⊢
        linear_combination hone
      rw [hco, hsplit]
      refine Ideal.mul_mem_left _ _ (Ideal.add_mem _ ?_ ?_)
      · have hneg : (1 : R) - (y : Matrix (Fin 2) (Fin 2) R) 1 1
            = -((y : Matrix (Fin 2) (Fin 2) R) 1 1 - 1) := by ring
        rw [hneg]
        exact Ideal.mul_mem_left _ _ (Submodule.neg_mem _ hd)
      · exact Ideal.mul_mem_left _ _ hc

theorem mem_congruenceK1_iff {ϖ : R} {n : ℕ} {x : GL (Fin 2) K} :
    x ∈ congruenceK1 (K := K) ϖ n ↔
      ∃ y : GL (Fin 2) R,
        Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
        (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n} ∧
        (y : Matrix (Fin 2) (Fin 2) R) 1 1 - 1 ∈ Ideal.span {ϖ ^ n} :=
  Iff.rfl

theorem congruenceK1_le_congruenceK0 (ϖ : R) (n : ℕ) :
    congruenceK1 (K := K) ϖ n ≤ congruenceK0 (K := K) ϖ n := by
  rintro x ⟨y, rfl, hc, _⟩
  exact ⟨y, rfl, hc⟩

theorem congruenceK1_zero (ϖ : R) :
    congruenceK1 (K := K) ϖ 0
      = (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  ext x
  simp [mem_congruenceK1_iff, MonoidHom.mem_range, pow_zero, Ideal.span_singleton_one]

theorem congruenceK0_antitone {ϖ : R} {m n : ℕ} (hmn : m ≤ n) :
    congruenceK0 (K := K) ϖ n ≤ congruenceK0 (K := K) ϖ m := by
  rintro x ⟨y, rfl, hc⟩
  exact ⟨y, rfl, Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hmn) hc⟩

theorem congruenceK1_antitone {ϖ : R} {m n : ℕ} (hmn : m ≤ n) :
    congruenceK1 (K := K) ϖ n ≤ congruenceK1 (K := K) ϖ m := by
  rintro x ⟨y, rfl, hc, hd⟩
  exact ⟨y, rfl, Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hmn) hc,
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hmn) hd⟩

section Padic

variable (p : ℕ) [Fact p.Prime]

abbrev padicK0 (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) :=
  congruenceK0 ((p : ℤ_[p])) n

abbrev padicK1 (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) :=
  congruenceK1 ((p : ℤ_[p])) n

end Padic

end LocalNewvector



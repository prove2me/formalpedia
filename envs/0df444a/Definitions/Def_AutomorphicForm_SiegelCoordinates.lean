-- Prove2me | Definitions.Def_AutomorphicForm_SiegelCoordinates
-- name    : AutomorphicForm_SiegelCoordinates
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/38ba548e-fe5d-5c69-a2a7-c037d46a8183
-- title:
--   Coordinate laws for the GL2​ window functionals
-- statement:
--   Working over an arbitrary normed field $K$, this module develops the elementary coordinate calculus of the four functionals attached to $g\in\mathrm{GL}_2(K)$ in the windowed Siegel set definitions: $\mathrm{topNormSq}(g)=\|g_{00}\|^2+\|g_{01}\|^2$, $\mathrm{rowNormSq}(g)=\|g_{10}\|^2+\|g_{11}\|^2$, the local height $\mathrm{localHeight}(g)=\|\det g\|/\mathrm{rowNormSq}(g)$ and the squared window $\mathrm{xWindowSq}(g)=\mathrm{topNormSq}(g)/\mathrm{rowNormSq}(g)-\mathrm{localHeight}(g)^2$. The inequality $\|\det M\|^2\le\mathrm{topNormSq}(M)\,\mathrm{rowNormSq}(M)$ is proved for every $2\times 2$ matrix by the triangle inequality together with a real quadratic estimate, giving $\mathrm{xWindowSq}(g)\ge 0$; from it follow $\|\gamma_{10}\|^2\|\det g\|^2\le \mathrm{rowNormSq}(\gamma g)\,\mathrm{rowNormSq}(g)$ and, when $\gamma_{10}\neq 0$, the bound $\mathrm{localHeight}(\gamma g)\,\mathrm{localHeight}(g)\le\|\det\gamma\|/\|\gamma_{10}\|^2$. For a left factor $s$ with $s_{00}=a$, $s_{10}=0$, $s_{11}=t$ one gets $\det(sg)=at\det g$ and $\mathrm{localHeight}(sg)=(\|a\|/\|t\|)\,\mathrm{localHeight}(g)$, and if moreover $s_{01}=0$ then $\mathrm{xWindowSq}(sg)=(\|a\|/\|t\|)^2\mathrm{xWindowSq}(g)$; the hypothesis $t\neq0$ is carried as an explicit binder. The only definitions introduced are `upperUnit a b t`, the invertible matrix $\begin{pmatrix}a&b\\0&t\end{pmatrix}$ built from $a\neq0$, $t\neq0$ (with its four entry lemmas and its compatibility with entrywise ring maps), and, over $\mathbb{C}$, the coordinate $\mathrm{xCoord}(g)=(g_{00}\overline{g_{10}}+g_{01}\overline{g_{11}})/\mathrm{rowNormSq}(g)$. All four functionals are unchanged by applying entrywise a ring homomorphism $K\to L$ that preserves norms. Over $\mathbb{C}$ the Lagrange identity $\mathrm{topNormSq}\cdot\mathrm{rowNormSq}=|g_{00}\overline{g_{10}}+g_{01}\overline{g_{11}}|^2+|\det g|^2$ yields $\mathrm{xWindowSq}(g)=|\mathrm{xCoord}(g)|^2$ and the affine law $\mathrm{xCoord}(sg)=(a/t)\,\mathrm{xCoord}(g)+b/t$; composing with a norm-preserving embedding $K\to\mathbb{C}$ transports the first identity to $K$, and the isometry of the extension embedding of a completion at an infinite place supplies such an embedding for archimedean completions.
--
--   **Relation to Mathlib.** The functionals and `upperUnit` are the project's own; only standard Mathlib material on $2\times2$ determinants, normed fields and the isometric extension embedding of a completion at an infinite place is used.
--
--   **Where it is used.** These identities are the coordinate input for the theory of windowed Siegel sets in the adelic $\mathrm{GL}_2$ setting: the height bound $\mathrm{localHeight}(\gamma g)\,\mathrm{localHeight}(g)\le\|\det\gamma\|/\|\gamma_{10}\|^2$ controls translates of a Siegel set by global elements, while the upper-triangular laws describe the effect of diagonal and unipotent elements at a single archimedean place. Reduction to $\mathbb{C}$ via the isometric embedding of each archimedean completion avoids a separate treatment of real and complex places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SiegelCoordinates.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField Matrix

noncomputable section

namespace AutomorphicForm

namespace SiegelCoordinates

open WindowedSiegel

section General

variable {K : Type*} [NormedField K]

theorem norm_det_sq_le (M : Matrix (Fin 2) (Fin 2) K) :
    ‖M.det‖ ^ 2 ≤ topNormSq M * rowNormSq M := by
  have h1 : ‖M.det‖ ≤ ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by
    rw [Matrix.det_fin_two]
    exact (norm_sub_le _ _).trans (by rw [norm_mul, norm_mul])
  have h2 : ‖M.det‖ ^ 2 ≤ (‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans ?_
  unfold topNormSq rowNormSq
  nlinarith [sq_nonneg (‖M 0 0‖ * ‖M 1 0‖ - ‖M 0 1‖ * ‖M 1 1‖), norm_nonneg (M 0 0),
    norm_nonneg (M 0 1), norm_nonneg (M 1 0), norm_nonneg (M 1 1)]

theorem xWindowSq_nonneg (g : GL (Fin 2) K) : 0 ≤ xWindowSq g := by
  have hrow := rowNormSq_pos g
  have h := norm_det_sq_le (g : Matrix (Fin 2) (Fin 2) K)
  unfold xWindowSq localHeight
  rw [div_pow, sub_nonneg, div_le_div_iff₀ (pow_pos hrow 2) hrow]
  nlinarith [h, hrow]

theorem sq_mul_sq_le_rowNormSq_mul (γ g : GL (Fin 2) K) :
    ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2
      ≤ rowNormSq ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  set G : Matrix (Fin 2) (Fin 2) K := (γ : Matrix (Fin 2) (Fin 2) K) with hG
  set H : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hH
  have hcoe : ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = G * H := rfl

  let M : Matrix (Fin 2) (Fin 2) K := !![(G * H) 1 0, (G * H) 1 1; H 1 0, H 1 1]
  have hdet : M.det = G 1 0 * H.det := by
    simp only [M, Matrix.det_fin_two_of]
    rw [Matrix.det_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have htop : topNormSq M = rowNormSq (G * H) := by
    simp [M, topNormSq, rowNormSq]
  have hrow : rowNormSq M = rowNormSq H := by
    simp [M, rowNormSq]
  have h := norm_det_sq_le M
  rw [hdet, htop, hrow, norm_mul, mul_pow] at h
  rw [hcoe]
  exact h

theorem localHeight_mul_mul_localHeight_le (γ g : GL (Fin 2) K)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    localHeight (γ * g) * localHeight g
      ≤ ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ / ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 := by
  have hcoe : ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hr1 := rowNormSq_pos (γ * g)
  have hr2 := rowNormSq_pos g
  have hc : 0 < ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hγ) 2
  have hdg : 0 < ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (Matrix.GeneralLinearGroup.det_ne_zero g)) 2
  have hkey := sq_mul_sq_le_rowNormSq_mul γ g
  have hdet : ‖((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [hcoe, Matrix.det_mul, norm_mul]
  unfold localHeight
  rw [hdet, div_mul_div_comm, div_le_div_iff₀ (mul_pos hr1 hr2) hc]
  calc ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ *
        ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
      = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ *
          (‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2) := by
        ring
    _ ≤ ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ *
          (rowNormSq ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            rowNormSq (g : Matrix (Fin 2) (Fin 2) K)) :=
        mul_le_mul_of_nonneg_left hkey (norm_nonneg _)

theorem det_upper_entries_mul {s : GL (Fin 2) K} {a t : K}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t)
    (g : GL (Fin 2) K) :
    ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = a * t * (g : Matrix (Fin 2) (Fin 2) K).det := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = a * t := by
    rw [Matrix.det_fin_two, h00, h10, h11]
    ring
  rw [hcoe, Matrix.det_mul, hdets]

theorem localHeight_upper_entries_mul {s : GL (Fin 2) K} {a t : K} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t)
    (g : GL (Fin 2) K) :
    localHeight (s * g) = ‖a‖ / ‖t‖ * localHeight g := by
  have ht0 : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  have hrow := rowNormSq_scalar_entries_mul h10 h11 g
  unfold localHeight
  rw [det_upper_entries_mul h00 h10 h11 g, hrow, norm_mul, norm_mul]
  field_simp

theorem xWindowSq_diag_entries_mul {s : GL (Fin 2) K} {a t : K} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t)
    (g : GL (Fin 2) K) :
    xWindowSq (s * g) = (‖a‖ / ‖t‖) ^ 2 * xWindowSq g := by
  have ht0 : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  have hrow := rowNormSq_pos g
  unfold xWindowSq
  rw [topNormSq_scalar_entries_mul h00 h01 g, rowNormSq_scalar_entries_mul h10 h11 g,
    localHeight_upper_entries_mul ht h00 h10 h11 g]
  field_simp

def upperUnit (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, t]
    (by rw [Matrix.det_fin_two_of]; simp [ha, ht])

@[simp] theorem upperUnit_apply_zero_zero (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperUnit a b t ha ht : Matrix (Fin 2) (Fin 2) K) 0 0 = a := rfl

@[simp] theorem upperUnit_apply_zero_one (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperUnit a b t ha ht : Matrix (Fin 2) (Fin 2) K) 0 1 = b := rfl

@[simp] theorem upperUnit_apply_one_zero (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperUnit a b t ha ht : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := rfl

@[simp] theorem upperUnit_apply_one_one (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (upperUnit a b t ha ht : Matrix (Fin 2) (Fin 2) K) 1 1 = t := rfl

variable {L : Type*} [NormedField L]

theorem topNormSq_map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (M : Matrix (Fin 2) (Fin 2) K) :
    topNormSq (M.map φ) = topNormSq M := by
  simp [topNormSq, hφ]

theorem rowNormSq_map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (M : Matrix (Fin 2) (Fin 2) K) :
    rowNormSq (M.map φ) = rowNormSq M := by
  simp [rowNormSq, hφ]

theorem coe_map (φ : K →+* L) (g : GL (Fin 2) K) :
    ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = (g : Matrix (Fin 2) (Fin 2) K).map φ := rfl

theorem localHeight_map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (g : GL (Fin 2) K) :
    localHeight (Matrix.GeneralLinearGroup.map φ g) = localHeight g := by
  unfold localHeight
  rw [coe_map, rowNormSq_map φ hφ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hφ]

theorem xWindowSq_map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (g : GL (Fin 2) K) :
    xWindowSq (Matrix.GeneralLinearGroup.map φ g) = xWindowSq g := by
  unfold xWindowSq
  rw [localHeight_map φ hφ, coe_map, topNormSq_map φ hφ, rowNormSq_map φ hφ]

theorem map_upperUnit (φ : K →+* L) (a b t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    Matrix.GeneralLinearGroup.map φ (upperUnit a b t ha ht)
      = upperUnit (φ a) (φ b) (φ t) ((map_ne_zero φ).2 ha) ((map_ne_zero φ).2 ht) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero]

end General

section Complex

open ComplexConjugate

def xCoord (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (g 0 0 * conj (g 1 0) + g 0 1 * conj (g 1 1)) / (rowNormSq g : ℂ)

theorem ofReal_rowNormSq (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ((rowNormSq g : ℝ) : ℂ) = g 1 0 * conj (g 1 0) + g 1 1 * conj (g 1 1) := by
  simp [rowNormSq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem topNormSq_mul_rowNormSq (g : Matrix (Fin 2) (Fin 2) ℂ) :
    topNormSq g * rowNormSq g = ‖g 0 0 * conj (g 1 0) + g 0 1 * conj (g 1 1)‖ ^ 2 + ‖g.det‖ ^ 2 := by
  simp only [topNormSq, rowNormSq, Matrix.det_fin_two, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem xWindowSq_eq_norm_xCoord_sq (g : GL (Fin 2) ℂ) :
    xWindowSq g = ‖xCoord (g : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 := by
  have hrow := rowNormSq_pos g
  have hlag := topNormSq_mul_rowNormSq (g : Matrix (Fin 2) (Fin 2) ℂ)
  unfold xWindowSq localHeight xCoord
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hrow.le, div_pow, div_pow,
    div_sub_div _ _ hrow.ne' (pow_pos hrow 2).ne', div_eq_div_iff (mul_pos hrow (pow_pos hrow 2)).ne'
      (pow_pos hrow 2).ne']
  have hnum : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
      + (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)‖ ^ 2
      = topNormSq (g : Matrix (Fin 2) (Fin 2) ℂ) * rowNormSq (g : Matrix (Fin 2) (Fin 2) ℂ)
        - ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 := by
    rw [hlag]; ring
  rw [hnum]
  ring

theorem xCoord_upper_entries_mul {s : GL (Fin 2) ℂ} {a b t : ℂ} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a)
    (h01 : (s : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b)
    (h10 : (s : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = t)
    (g : GL (Fin 2) ℂ) :
    xCoord ((s * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = a / t * xCoord (g : Matrix (Fin 2) (Fin 2) ℂ) + b / t := by
  have hcoe : ((s * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (s : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  have hrow := rowNormSq_pos g
  have hrowC : ((rowNormSq (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 hrow.ne'
  have hrow' := rowNormSq_scalar_entries_mul h10 h11 g
  have hconj : conj t ≠ 0 := (map_ne_zero _).2 ht
  have hentry : ∀ i j, ((s : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j
      = (s : Matrix (Fin 2) (Fin 2) ℂ) i 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 j
        + (s : Matrix (Fin 2) (Fin 2) ℂ) i 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 j := fun i j => by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hnsq : ((‖t‖ ^ 2 : ℝ) : ℂ) = t * conj t := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold xCoord
  rw [hrow', hcoe, hentry, hentry, hentry, hentry, h00, h01, h10, h11, Complex.ofReal_mul, hnsq,
    ofReal_rowNormSq]
  rw [ofReal_rowNormSq] at hrowC
  simp only [map_mul, zero_mul, zero_add]
  field_simp
  ring

end Complex

section Embedding

variable {K : Type*} [NormedField K]

theorem xWindowSq_eq_norm_xCoord_map_sq (φ : K →+* ℂ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (g : GL (Fin 2) K) :
    xWindowSq g = ‖xCoord ((g : Matrix (Fin 2) (Fin 2) K).map φ)‖ ^ 2 := by
  rw [← xWindowSq_map φ hφ g, xWindowSq_eq_norm_xCoord_sq, coe_map]

end Embedding

section InfinitePlace

variable {F : Type*} [Field F]

theorem norm_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

end InfinitePlace

end SiegelCoordinates

end AutomorphicForm



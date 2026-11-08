-- Prove2me | Definitions.Def_ProperHalfspace_HeadTail
-- name    : ProperHalfspace_HeadTail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:58.168769+00:00
-- url     : https://prove2.me/theorems/693610eb-a25f-426b-9603-5b1f4c4a5d10
-- title:
--   Head condition (8), the tail matrix (9), and the normal space $\mathrm{span}\{e_i:i\in H\}+E$
-- statement:
--   For $H\subseteq[n]$, condition (8) says $\mathrm{Inf}_i[f^{\mathrm{sm}}]\le\rho\alpha$ for every $i\in H^c$. The tail matrix is $M_{\mathrm{tail}}(H)=M_\rho(f)[T,T]$ with $T=H^c$. A subspace $E\subseteq\mathbb R^{H^c}$ is identified with its embedding in $\mathbb R^n$ supported on $H^c$, and the normal space is $\mathrm{span}\{e_i:i\in H\}+E$. A normal with head $w_H$ and tail $u$ is glued into a vector of $\mathbb R^n$.
--
--   These express that one subspace, determined by $f$ alone, carries the normals of nearly optimal competitors.
--
--   **Formalization Note** $H^c$ is the subtype `{i // i ∉ H}`. $E$ lives in `EuclideanSpace ℝ {i // i ∉ H}`, so its orthogonal complement is taken inside $\mathbb R^{H^c}$, as on the page.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), (8), p.22; (9), p.23; Theorem 18, p.23

import Mathlib
import Definitions.Def_ProperHalfspace_Fourier
import Definitions.Def_ProperHalfspace_InfluencePCA

namespace ProperHalfspace

/-!
# Heads, tails and the common normal space

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), (8), p.22; (9), p.23; Theorem 18, p.23.

**Formalization Note.** `Hᶜ` is the subtype `{i // i ∉ H}`. A subspace `E ⊆ ℝ^{Hᶜ}` lives in `EuclideanSpace ℝ {i // i ∉ H}`, so
its orthogonal complement is taken inside `ℝ^{Hᶜ}`, as on the page; `embedTail` pads with zeros on `H`.
-/

/-- Equation (8), p.22: `Inf_i[f^sm] ≤ ρα` for every `i ∈ Hᶜ`. -/
def HeadCond {n : ℕ} (ρ α : ℝ) (f : Cube n → ℝ) (H : Finset (Fin n)) : Prop :=
  ∀ i, i ∉ H → influence (smooth ρ f) i ≤ ρ * α

/-- Equation (9), p.23: `M_tail(H) = M_ρ(f)[T, T]` with `T = Hᶜ`. -/
noncomputable def tailMatrix {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) (H : Finset (Fin n)) :
    Matrix {i // i ∉ H} {i // i ∉ H} ℝ :=
  (pcaMatrix ρ f).submatrix Subtype.val Subtype.val

/-- The normal with head `w_H` and tail `u`. -/
noncomputable def glue {n : ℕ} (H : Finset (Fin n)) (w : Fin n → ℝ) (u : {i // i ∉ H} → ℝ) : Fin n → ℝ :=
  fun i => if h : i ∉ H then u ⟨i, h⟩ else w i

/-- The embedding `ℝ^{Hᶜ} → ℝⁿ` that pads with zeros on `H`. -/
noncomputable def embedTail {n : ℕ} (H : Finset (Fin n)) :
    EuclideanSpace ℝ {i // i ∉ H} →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun v := WithLp.toLp 2 fun i => if h : i ∈ H then 0 else v ⟨i, h⟩
  map_add' u v := by
    ext i
    by_cases h : i ∈ H <;> simp [h]
  map_smul' c v := by
    ext i
    by_cases h : i ∈ H <;> simp [h]

/-- The space `span{eᵢ : i ∈ H} + E` of Theorem 18, with `E ⊆ ℝ^{Hᶜ}` embedded in `ℝⁿ`. -/
noncomputable def normalSpace {n : ℕ} (H : Finset (Fin n))
    (E : Submodule ℝ (EuclideanSpace ℝ {i // i ∉ H})) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ ((fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) '' (H : Set (Fin n))) ⊔
    E.map (embedTail H)

end ProperHalfspace



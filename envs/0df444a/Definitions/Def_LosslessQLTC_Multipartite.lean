-- Prove2me | Definitions.Def_LosslessQLTC_Multipartite
-- name    : LosslessQLTC_Multipartite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:47.603622+00:00
-- url     : https://prove2.me/theorems/dfccca39-3f17-403a-b9ba-91e2b6f940fa
-- title:
--   The complete multipartite complex $K(D_1,\dots,D_d)$
-- statement:
--   The complete $d$-partite complex has parts of sizes $D_1,\dots,D_d$, and its faces are the sets with at most one vertex in each part, with the empty face at level $-1$. A face of type $I$ has weight $D_I^{-1}$, the norm of a cochain is the total weight of its support, $\delta$ sums over codimension-one subfaces over $\mathbb F_2$, and $\operatorname{dist}(f)=\min_h\|f+\delta h\|$. This is the reference complex whose expansion the links inherit.
--
--   **Formalization Note.** Parts are types $\sigma_i$ with $D_i=|\sigma_i|$. A face is a partial choice in $\prod_i\mathrm{Option}(\sigma_i)$. Levels are indexed by the number $j=r+1$ of vertices. At $j=0$ there is no image, so $\operatorname{dist}(f)=\|f\|$.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Definition 2.2, p.14; §3, p.20; p.17

import Mathlib

namespace LosslessQLTC

variable {d : ℕ}

/-- A face of the complete `d`-partite complex `K(D_1, …, D_d)` with parts `σ i`, recorded as a
partial choice of at most one vertex in each part (arXiv:2610.00525, held version, sha256
d61f0ed9…, Definition 2.2, p.14, and p.20). -/
abbrev MFace (σ : Fin d → Type) : Type := ∀ i, Option (σ i)

/-- The type `I ⊆ [d]` of a face: the parts it meets. -/
def mType {σ : Fin d → Type} (x : MFace σ) : Finset (Fin d) :=
  Finset.univ.filter fun i => (x i).isSome

/-- The `j`-vertex faces: the source's `M(r)` with `r = j − 1`, so `j = 0` is the empty face
(p.14, footnote 4). -/
def MLevel (σ : Fin d → Type) (j : ℕ) : Type :=
  {x : MFace σ // (mType x).card = j}

instance (σ : Fin d → Type) [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (j : ℕ) :
    Fintype (MLevel σ j) :=
  inferInstanceAs (Fintype {x : MFace σ // (mType x).card = j})

instance (σ : Fin d → Type) [∀ i, DecidableEq (σ i)] (j : ℕ) : DecidableEq (MLevel σ j) :=
  inferInstanceAs (DecidableEq {x : MFace σ // (mType x).card = j})

/-- The face inclusion `x ⊆ y`. -/
def mLe {σ : Fin d → Type} (x y : MFace σ) : Prop :=
  ∀ i, (x i).isSome → y i = x i

instance {σ : Fin d → Type} [∀ i, DecidableEq (σ i)] (x y : MFace σ) : Decidable (mLe x y) :=
  inferInstanceAs (Decidable (∀ i, (x i).isSome → y i = x i))

/-- The coboundary of the complete multipartite complex: `(δf)(y)` is the sum of `f` over the
codimension-one subfaces of `y`, over `F₂`. -/
def mDelta (σ : Fin d → Type) [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] (j : ℕ) :
    (MLevel σ j → ZMod 2) →ₗ[ZMod 2] (MLevel σ (j + 1) → ZMod 2) where
  toFun f y := ∑ x : MLevel σ j, if mLe x.1 y.1 then f x else 0
  map_add' f g := by
    funext w
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
  map_smul' a f := by
    funext w
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp

/-- The norm on `K(D_1, …, D_d)` (p.17, p.20): a face of type `I` has weight `D_I⁻¹` with
`D_i = |σ i|`, and the norm of a cochain is the total weight of its support. -/
noncomputable def mNorm (σ : Fin d → Type) [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] {j : ℕ}
    (f : MLevel σ j → ZMod 2) : ℝ :=
  ∑ x : MLevel σ j,
    if f x ≠ 0 then 1 / ((∏ i ∈ mType x.1, Fintype.card (σ i) : ℕ) : ℝ) else 0

/-- `dist(f) = min_h ∥f + δh∥`. At `j = 0` (level `−1`) there is no image and `dist(f) = ∥f∥`.
The minimum is over a finite nonempty set. -/
noncomputable def mDist (σ : Fin d → Type) [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)] :
    (j : ℕ) → (MLevel σ j → ZMod 2) → ℝ
  | 0, f => mNorm σ f
  | j + 1, f => (Finset.univ : Finset (MLevel σ j → ZMod 2)).inf' ⟨0, Finset.mem_univ _⟩
      fun h => mNorm σ (f + mDelta σ j h)

end LosslessQLTC



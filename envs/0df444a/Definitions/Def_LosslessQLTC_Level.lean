-- Prove2me | Definitions.Def_LosslessQLTC_Level
-- name    : LosslessQLTC_Level
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:35.375244+00:00
-- url     : https://prove2.me/theorems/a92f08ac-bc89-4e15-a2c5-a761494ca2af
-- title:
--   Levels $V_s$, coboundary $\delta_s$ and boundary $\partial_s$ over $\mathbb F_2$
-- statement:
--   The $s$-th level is $V_s=\bigsqcup_{|I|=s}V_I$, and $C_s(X)=C^s(X)=\mathbb F_2^{V_s}$. The coboundary and boundary maps are
--
--   $$(\delta_sf)(w)=\sum_{v\lessdot w}f(v),\qquad(\partial_sf)(u)=\sum_{u\lessdot v}f(v),$$
--
--   with all sums over $\mathbb F_2$. Thus $\partial_s=\delta_{s-1}^T$. These maps are the parity checks of the code.
--
--   **Formalization Note.** The boundary is indexed by its target level, so `partialMap X s` is the source's $\partial_{s+1}$ and no natural-number subtraction occurs.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), §2.2, p.16

import Mathlib
import Definitions.Def_LosslessQLTC_SquareComplex

namespace LosslessQLTC

variable {k : ℕ}

/-- The `s`-th level `V_s = ⊔_{|I| = s} V_I` (arXiv:2610.00525, held version, sha256 d61f0ed9…,
p.16). -/
def Level (X : SquareComplex k) (s : ℕ) : Type :=
  {v : X.Vtx // (X.type v).card = s}

instance (X : SquareComplex k) (s : ℕ) : Fintype (Level X s) :=
  inferInstanceAs (Fintype {v : X.Vtx // (X.type v).card = s})

instance (X : SquareComplex k) (s : ℕ) : DecidableEq (Level X s) :=
  inferInstanceAs (DecidableEq {v : X.Vtx // (X.type v).card = s})

/-- The coboundary `δ_s : C^s(X) → C^{s+1}(X)`, `(δ_s f)(w) = Σ_{v ⋖ w} f(v)` over `F₂`
(arXiv:2610.00525, p.16). -/
def delta (X : SquareComplex k) (s : ℕ) :
    (Level X s → ZMod 2) →ₗ[ZMod 2] (Level X (s + 1) → ZMod 2) where
  toFun f w := ∑ v : Level X s, if X.up v.1 w.1 then f v else 0
  map_add' f g := by
    funext w
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
  map_smul' a f := by
    funext w
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp

/-- The boundary `∂_{s+1} : C_{s+1}(X) → C_s(X)`, `(∂ f)(u) = Σ_{u ⋖ v} f(v)` over `F₂`; it is the
transpose `δ_s^T` (arXiv:2610.00525, p.16).

**Formalization Note.** The index is the target level: `partialMap X s` is the source's `∂_{s+1}`,
so that no natural-number subtraction appears. In the code of §5, `H_X = δ_1^t` is
`partialMap X 1`. -/
def partialMap (X : SquareComplex k) (s : ℕ) :
    (Level X (s + 1) → ZMod 2) →ₗ[ZMod 2] (Level X s → ZMod 2) where
  toFun f u := ∑ v : Level X (s + 1), if X.up u.1 v.1 then f v else 0
  map_add' f g := by
    funext w
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
  map_smul' a f := by
    funext w
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp

end LosslessQLTC



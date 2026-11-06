-- Prove2me | Definitions.Def_UCalibDirichlet_IsNormalized
-- name    : UCalibDirichlet_IsNormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:09.608764+00:00
-- url     : https://prove2.me/theorems/5f43677e-bedd-45d6-9101-336496dd54d2
-- title:
--   Normalization (4): $F(\mathbf 1/K)=0$, $g(\mathbf 1/K)=0$
-- statement:
--   A potential $F:\Delta_K\to\mathbb R$ is **normalized** if, with $u=\mathbf 1/K$ the uniform distribution,
--   $$F(u)=0\qquad\text{and}\qquad 0\in\partial F(u),$$
--   that is, $F(u)=0$ and $F(u)\le F(p)$ for every $p\in\Delta_K$; in particular $F\ge0$ on $\Delta_K$. Adding an affine function to $F$ only adds $p$-independent terms to $\ell_F$ and does not change the regret, so the paper adopts this normalization without loss of generality.
--
--   **Formalization Note** A subgradient $g$ of $F$ at $u$ relative to the simplex satisfies $F(p)\ge F(u)+\langle g,p-u\rangle$ for $p\in\Delta_K$; $g=0$ is exactly the minimality of $u$.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1.1.1, display (4), p.3

import Mathlib

namespace UCalibDirichlet

/-- **The normalization convention (4).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), §1.1.1, p.3: "we adopt the following normalization convention (that is without loss
of generality): `F(1/K) = 0`, `g(1/K) = 0`, (4) which, together with convexity, implies `F(p) ≥ 0`
for all `p ∈ Δ_K`."

`IsNormalized F` says `F(u) = 0` and `F(u) ≤ F(p)` for every `p ∈ Δ_K`, where `u = 𝟏/K` is the
uniform distribution.

**Formalization Note.** `g(1/K) = 0` with `g(1/K) ∈ ∂F(1/K)` for `F : Δ_K → ℝ` says that `0` is a
subgradient of `F` at `u` relative to `Δ_K`, i.e. `F(p) ≥ F(u) + ⟨0, p − u⟩` for all `p ∈ Δ_K`,
which is exactly the second clause. -/
def IsNormalized {K : ℕ} (F : (Fin K → ℝ) → ℝ) : Prop :=
  F (fun _ => (K : ℝ)⁻¹) = 0 ∧ ∀ p ∈ stdSimplex ℝ (Fin K), F (fun _ => (K : ℝ)⁻¹) ≤ F p

end UCalibDirichlet



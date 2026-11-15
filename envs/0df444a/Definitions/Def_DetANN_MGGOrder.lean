-- Prove2me | Definitions.Def_DetANN_MGGOrder
-- name    : DetANN_MGGOrder
-- status  : Definition
-- author  : @milia
-- created : 2026-11-14T21:24:25.528962+00:00
-- url     : https://prove2.me/theorems/d6ca3749-284e-487d-a900-cdae59184b15
-- title:
--   Partial order and edge weight on $\mathbb Z_m^2$ (HLW §8)
-- statement:
--   Let $m\ge1$. Represent each residue $u\in\mathbb Z_m$ by $\tilde u\in(-m/2,m/2]$, so $|\tilde u|$ is the distance from $u$ to $0$ on the cycle $\mathbb Z_m$. For $z,w\in\mathbb Z_m^2$, say that **$w$ is farther out than $z$**, written $w\succ z$, if
--
--   $$|\tilde w_1|\ge|\tilde z_1|\quad\text{and}\quad|\tilde w_2|\ge|\tilde z_2|,\ \text{with at least one inequality strict.}$$
--
--   For $\alpha>0$, the edge weight is
--
--   $$\gamma_\alpha(z,w)=\begin{cases}\alpha^{-1}&\text{if } w\succ z,\\ \alpha&\text{if } z\succ w,\\ 1&\text{otherwise.}\end{cases}$$
--
--   These are the partial order and the weight function of Hoory–Linial–Wigderson's proof of the Gabber–Galil bound. Since $\succ$ is a strict partial order, $\gamma_\alpha(z,w)\,\gamma_\alpha(w,z)=1$, which is HLW's identity (14). The weight is what makes the term-by-term analysis of that proof possible.
--
--   **Formalization Note.** HLW use representatives in $[-n/2,n/2)$, while Mathlib's `ZMod.valMinAbs` takes values in $(-m/2,m/2]$. Only absolute values enter, and they agree, so the order is the same. `mggFarther z w` means $w\succ z$, and `mggWeight α z w` is $\gamma_\alpha(z,w)$.
-- source:
--   Hoory, Linial, Wigderson, Expander graphs and their applications, Bull. Amer. Math. Soc. 43 (2006), 439–561, https://www.ams.org/journals/bull/2006-43-04/S0273-0979-06-01126-8/, §8.2: the weight γ and identity (14) on p. 506; the partial order on p. 508.

import Mathlib

namespace DetANN

/-- Coordinatewise "strictly farther from the origin" on `ℤ_m²`, measuring each coordinate by
its distance to `0` (absolute value of the representative in `(-m/2, m/2]`).
Source: Hoory–Linial–Wigderson, *Expander graphs and their applications*, Bull. AMS 43 (2006), §8.2,
the partial order defined after Proposition 8.9. -/
def mggFarther {m : ℕ} (z w : ZMod m × ZMod m) : Prop :=
  z.1.valMinAbs.natAbs ≤ w.1.valMinAbs.natAbs ∧ z.2.valMinAbs.natAbs ≤ w.2.valMinAbs.natAbs ∧
    (z.1.valMinAbs.natAbs < w.1.valMinAbs.natAbs ∨ z.2.valMinAbs.natAbs < w.2.valMinAbs.natAbs)

open Classical in
/-- The edge weight `γ(z, w)` of HLW §8.2: `α⁻¹` if `w` is farther out than `z`, `α` if `w`
is nearer, and `1` otherwise. -/
noncomputable def mggWeight (α : ℝ) {m : ℕ} (z w : ZMod m × ZMod m) : ℝ :=
  if mggFarther z w then α⁻¹ else if mggFarther w z then α else 1

end DetANN



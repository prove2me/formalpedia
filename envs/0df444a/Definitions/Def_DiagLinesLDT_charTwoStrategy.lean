-- Prove2me | Definitions.Def_DiagLinesLDT_charTwoStrategy
-- name    : DiagLinesLDT_charTwoStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:54:13.394138+00:00
-- url     : https://prove2.me/theorems/c75776d4-737d-4e71-9750-bbcfe6867c99
-- title:
--   The strategy of characteristic two: $U_\ell$, $A^u_a$, $P^\ell_\lambda$, $B^\ell_g$
-- statement:
--   Let $q=2^r$. For a horizontal line $\ell=\{y=y_0\}$ put $U_\ell:=V$. For a vertical line $\ell=\{x=x_0\}$ and $v=(a,b,c;\dots)$ put
--
--   $$U_\ell(v):=\sigma_\ell(v)V(v),\qquad\sigma_\ell(v):=\chi\big(x_0ac+\sqrt{x_0}\,b\big),$$
--
--   where $\sqrt{x_0}$ is the unique element of $\mathbb F_q$ whose square is $x_0$. The measurements are
--
--   $$A^u_a=\frac1q\sum_{t\in\mathbb F_q}\chi(ta)V(tw(u)),\qquad P^\ell_\lambda=\frac{1}{|S_\ell|}\sum_{v\in S_\ell}\chi(\lambda(v))U_\ell(v),\qquad B^\ell_g=\sum_{\lambda:\,h^\ell_\lambda=g}P^\ell_\lambda.$$
--
--   Alice uses $A^u_a$ and $B^\ell_g$, Bob uses the transposes, and the shared state is $|\Phi\rangle$. The sign is needed because in characteristic two isotropy does not remove the cocycle factor of $V$ on vertical lines.
--
--   **Formalization Note** $\sqrt x$ is $x^{q/2}$, whose square is $x^q=x$ in characteristic two. A line of $\mathbb F_q^2$ is of exactly one kind, and $x_0$ is unique on a vertical line. The data are written for every finite field and are the source's strategy when `ringChar F = 2`, which every statement about them assumes.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §7.2 and Proposition 7.2, p.23

import Mathlib
import Definitions.Def_DiagLinesLDT_Strategy
import Definitions.Def_DiagLinesLDT_Gamma
import Definitions.Def_DiagLinesLDT_labelMap

namespace DiagLinesLDT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `√x := x^{q/2}`, the unique square root of `x` in a finite field of characteristic two.

**Formalization Note** `q / 2` is natural-number division, exact when `q` is even. In odd characteristic
the value has no meaning here and is not used. `Solutions/verification/DiagLinesLDT_sanity.lean` checks
`(√x)² = x` in characteristic two. -/
def sqrtTwo (x : F) : F := x ^ (Fintype.card F / 2)

/-- The sign `σ_ℓ(v) := χ(x₀ a c + √x₀ b)` of a vertical line `{x = x₀}`, for `v = (a, b, c; …)`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §7.2, p.23. -/
noncomputable def sigma (x₀ : F) (v : PS F) : ℂ :=
  chi F (x₀ * v.1 0 * v.1 2 + sqrtTwo x₀ * v.1 1)

open scoped Classical in
/-- The corrected operators of §7.2: `U_ℓ := V` on a horizontal line `{y = y₀}`, and
`U_ℓ(v) := σ_ℓ(v) V(v)` on a vertical line `{x = x₀}`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §7.2, p.23.

**Formalization Note** A line of `𝔽_q²` is of exactly one kind, and on a vertical line `x₀` is unique,
so the choice below is not a choice of value. The formula reads `a, b, c` off the phase part of `v`. -/
noncomputable def Uop (ℓ : AxisLine F 2) (v : PS F) : Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  if h : ∃ x₀ : F, ℓ.1 = {u | u 0 = x₀} then sigma h.choose v • Vop v else Vop v

variable (F)

/-- The point measurement `A^u_a = (1/q) Σ_t χ(ta) V(t w(u))` (Proposition 7.2, p.23). -/
noncomputable def pointTwo (u : Fin 2 → F) (a : F) : Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  ((Fintype.card F : ℂ))⁻¹ • ∑ t : F, chi F (t * a) • Vop (t • w u)

/-- The Fourier projection `P^ℓ_λ = (1/|S_ℓ|) Σ_{v ∈ S_ℓ} χ(λ(v)) U_ℓ(v)` (Proposition 7.2, p.23). -/
noncomputable def projTwo (ℓ : AxisLine F 2) (lam : Module.Dual F (lineSpan ℓ)) :
    Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  ((Fintype.card (lineSpan ℓ) : ℂ))⁻¹ •
    ∑ v : lineSpan ℓ, chi F (lam v) • Uop ℓ (v : PS F)

open scoped Classical in
/-- The line measurement `B^ℓ_g := Σ_{λ : h^ℓ_λ = g} P^ℓ_λ` (Proposition 7.2, p.23). -/
noncomputable def lineTwo (ℓ : AxisLine F 2) (g : LegalAnswer 2 ℓ) :
    Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  ∑ lam : Module.Dual F (lineSpan ℓ) with inducedAnswer ℓ lam = g.1, projTwo F ℓ lam

/-- The strategy of §7.2: Alice uses `A^u_a` and `B^ℓ_g`, Bob the transposes, and the state is the
maximally entangled state on `ℂ^{𝔽_q³} ⊗ ℂ^{𝔽_q³}`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §7.2 and Proposition 7.2, p.23.

**Formalization Note** The data are defined for every finite field, and they are the source's strategy
when `ringChar F = 2`, which every statement about them assumes. -/
noncomputable def charTwoStrategy : Strategy F 2 2 (Fin 3 → F) (Fin 3 → F) where
  state := maxEnt (Fin 3 → F)
  pointA := pointTwo F
  lineA := lineTwo F
  pointB := fun u a => (pointTwo F u a).transpose
  lineB := fun ℓ g => (lineTwo F ℓ g).transpose

end DiagLinesLDT



-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_wronskian
-- name    : TeschlQM_SturmLiouville_wronskian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:43:25.948337+00:00
-- url     : https://prove2.me/theorems/0e18c9c7-ef70-4d00-a2ae-c75d3494fb4f
-- title:
--   Modified Wronskian $W_x$ (9.5) and boundary values $W_a$, $W_b$
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. For $f_1, f_2$ with $f_j, pf_j' \in AC_{loc}(I)$ the **modified Wronskian** is
--   $$W_x(f_1, f_2) = \big(p(f_1 f_2' - f_1' f_2)\big)(x) = f_1(x)\,(pf_2')(x) - (pf_1')(x)\,f_2(x), \qquad x \in I.$$
--   No complex conjugation is involved. Its boundary values are the limits
--   $$W_a(f_1, f_2) = \lim_{x \to a} W_x(f_1, f_2), \qquad W_b(f_1, f_2) = \lim_{x \to b} W_x(f_1, f_2),$$
--   taken inside $I$; they exist for $f_1, f_2 \in \mathfrak{D}(\tau)$ by the Lagrange identity (9.7).
--
--   The boundary values $W_a$, $W_b$ encode all boundary conditions of self-adjoint realizations of $\tau$.
--
--   **Formalization Note.** $W_a$ and $W_b$ are `Filter.limUnder` along `atLeft`/`atRight`; this returns an unspecified value when the limit does not exist, and the mission uses them only for functions in $\mathfrak{D}(\tau)$, where the limit exists (milestone (9.7) states this).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 182, Section 9.1, Eqs. (9.5), (9.7)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_quasiDeriv

namespace TeschlQM.SturmLiouville

/-- Teschl (9.5), p. 182: the modified Wronskian
`W_x(f₁, f₂) = (p (f₁ f₂′ − f₁′ f₂))(x) = f₁(x) (p f₂′)(x) − (p f₁′)(x) f₂(x)`.
There is no complex conjugation. -/
noncomputable def wronskian (L : SLData) (x : ℝ) (f₁ f₂ : ℝ → ℂ) : ℂ :=
  f₁ x * quasiDeriv L f₂ x - quasiDeriv L f₁ x * f₂ x

/-- Teschl, p. 182, after (9.7): `W_a(f₁, f₂) = lim_{x → a} W_x(f₁, f₂)`, the limit taken inside
`I`. The limit exists for `f₁, f₂ ∈ D(τ)` by (9.7); `Filter.limUnder` returns an unspecified value
when it does not exist, and the mission only evaluates it where the book's limit exists. -/
noncomputable def wronskianLeft (L : SLData) (f₁ f₂ : ℝ → ℂ) : ℂ :=
  Filter.limUnder L.atLeft (fun x => wronskian L x f₁ f₂)

/-- Teschl, p. 182: `W_b(f₁, f₂) = lim_{x → b} W_x(f₁, f₂)`, the limit taken inside `I`. -/
noncomputable def wronskianRight (L : SLData) (f₁ f₂ : ℝ → ℂ) : ℂ :=
  Filter.limUnder L.atRight (fun x => wronskian L x f₁ f₂)

end TeschlQM.SturmLiouville



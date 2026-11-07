-- Prove2me | Definitions.Def_DiagLinesLDT_oddStrategy
-- name    : DiagLinesLDT_oddStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:54:22.552889+00:00
-- url     : https://prove2.me/theorems/a9a7648a-7197-4da2-8e8b-b439ddb2b642
-- title:
--   The strategy of odd characteristic: $A^u_a$, $P^\ell_\lambda$, $B^\ell_g$
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. On $\mathcal H=\mathbb C^{\mathbb F_q^3}$ define
--
--   $$A^u_a=\frac1q\sum_{t\in\mathbb F_q}\chi(-ta)W_\chi(tw(u)),\qquad P^\ell_\lambda=\frac{1}{|S_\ell|}\sum_{v\in S_\ell}\chi(-\lambda(v))W_\chi(v),\qquad B^\ell_g=\sum_{\lambda:\,h^\ell_\lambda=g}P^\ell_\lambda.$$
--
--   Alice uses $A^u_a$ and $B^\ell_g$, Bob uses the transposes $(A^u_a)^{\mathrm T}$ and $(B^\ell_g)^{\mathrm T}$, and the shared state is $|\Phi\rangle$.
--
--   **Formalization Note** The data are written for every finite field, and are the source's strategy when the characteristic is odd, which every statement about them assumes. For $q$ prime these are the formulas of §4 with $\chi(t)=\omega^t$. Line outcomes $g$ are the legal answers of degree at most 2.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §4, pp.6–10, and Proposition 7.1, p.22

import Mathlib
import Definitions.Def_DiagLinesLDT_Strategy
import Definitions.Def_DiagLinesLDT_Gamma
import Definitions.Def_DiagLinesLDT_labelMap

namespace DiagLinesLDT

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The point measurement `A^u_a = (1/q) Σ_t χ(-ta) W_χ(t w(u))`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Proposition 7.1, p.22 (for `q` prime: §4.2, p.6). -/
noncomputable def pointOdd (u : Fin 2 → F) (a : F) : Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  ((Fintype.card F : ℂ))⁻¹ • ∑ t : F, chi F (-(t * a)) • Wop (t • w u)

/-- The Fourier projection `P^ℓ_λ = (1/|S_ℓ|) Σ_{v ∈ S_ℓ} χ(-λ(v)) W_χ(v)`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Proposition 7.1, p.22
(for `q` prime: §4.3, p.10). -/
noncomputable def projOdd (ℓ : AxisLine F 2) (lam : Module.Dual F (lineSpan ℓ)) :
    Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  ((Fintype.card (lineSpan ℓ) : ℂ))⁻¹ •
    ∑ v : lineSpan ℓ, chi F (-(lam v)) • Wop (v : PS F)

open scoped Classical in
/-- The line measurement `B^ℓ_g := Σ_{λ : h^ℓ_λ = g} P^ℓ_λ` for a legal answer `g` of degree at most 2.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §4.3, p.10, and
Proposition 7.1, p.22. -/
noncomputable def lineOdd (ℓ : AxisLine F 2) (g : LegalAnswer 2 ℓ) :
    Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  ∑ lam : Module.Dual F (lineSpan ℓ) with inducedAnswer ℓ lam = g.1, projOdd F ℓ lam

/-- The strategy of §§4 and 7.1: Alice uses `A^u_a` and `B^ℓ_g`, Bob the transposes, and the state is
the maximally entangled state on `ℂ^{𝔽_q³} ⊗ ℂ^{𝔽_q³}`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §4, pp.6–10, and
Proposition 7.1, p.22.

**Formalization Note** The data are defined for every finite field, and they are the source's strategy
when `ringChar F ≠ 2`, which every statement about them assumes. -/
noncomputable def oddStrategy : Strategy F 2 2 (Fin 3 → F) (Fin 3 → F) where
  state := maxEnt (Fin 3 → F)
  pointA := pointOdd F
  lineA := lineOdd F
  pointB := fun u a => (pointOdd F u a).transpose
  lineB := fun ℓ g => (lineOdd F ℓ g).transpose

end DiagLinesLDT



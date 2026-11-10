-- Prove2me | Definitions.Def_OnlineDiscUniv_steerLaw
-- name    : OnlineDiscUniv_steerLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:06.782194+00:00
-- url     : https://prove2.me/theorems/52f51c85-e619-400a-b8b3-545440cea6ef
-- title:
--   The sign rule (3.16) and the joint law of $(\varepsilon,\zeta)$
-- statement:
--   Let $\nu$ be a probability law on $\mathbb R$, $\zeta=(\zeta_1,\dots,\zeta_M)\sim\nu^{\otimes M}$, $v\in\mathbb R^M$ and $\rho\ge0$. After observing $\zeta$, draw an independent $U'\sim\mathrm{Unif}[-1,1]$ and choose
--   $$
--   \varepsilon=\begin{cases}+1,& U'\le\psi_\rho(\langle v,\zeta\rangle),\\-1,& U'>\psi_\rho(\langle v,\zeta\rangle).\end{cases}\qquad(3.16)
--   $$
--   The module defines the uniform law on $[-1,1]$, the sign rule, and the joint law of $(\varepsilon,\zeta)$ on $\{\pm1\}\times\mathbb R^M$.
--
--   **Formalization Note** The joint law is the image of $\nu^{\otimes M}\otimes\mathrm{Unif}[-1,1]$ under $(x,U')\mapsto(\varepsilon(x,U'),x)$; the sign is a real number in $\{-1,+1\}$. The formula $\tfrac12(1+\sigma\psi_\rho(\langle v,x\rangle))\,\nu^{\otimes M}(dx)$ of the proof of Lemma 3.2 is a consequence, not the definition.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), (3.16), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_OnlineDiscUniv_psi

set_option autoImplicit false

open MeasureTheory

namespace OnlineDiscUniv

/-- The uniform law on `[−1, 1]` (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, (3.16),
printed p.8, PDF p.9). -/
noncomputable def unifPM1 : Measure ℝ :=
  (2 : ENNReal)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

/-- The sign rule (3.16) (Jo–Lee, arXiv:2610.00103, p.8, PDF p.9): after observing the vector
`x` and the independent uniform `U' ∈ [−1,1]`, choose `ε = +1` if `U' ≤ ψ_ρ(⟨v, x⟩)` and
`ε = −1` otherwise. -/
noncomputable def steerSign {M : ℕ} (L ρ : ℝ) (v x : Fin M → ℝ) (U' : ℝ) : ℝ :=
  if U' ≤ psi L ρ (∑ j, v j * x j) then 1 else -1

/-- The joint law of the pair `(ε, ζ)` when `ζ ∼ ν^{⊗M}`, `U' ∼ Unif[−1,1]` is independent of
`ζ`, and `ε` is chosen by the rule (3.16) (Jo–Lee, arXiv:2610.00103, (3.16), p.8, PDF p.9;
Lemma 3.2, p.8).

**Formalization Note** The law is the image of `ν^{⊗M} ⊗ Unif[−1,1]` under
`(x, U') ↦ (steerSign L ρ v x U', x)`; the sign is a real number in `{−1, +1}`. The
formula `½(1 + σψ_ρ(⟨v,x⟩)) ν^{⊗M}(dx)` of the proof of Lemma 3.2 is a consequence, not the
definition. -/
noncomputable def steerLaw {M : ℕ} (ν : Measure ℝ) (L ρ : ℝ) (v : Fin M → ℝ) :
    Measure (ℝ × (Fin M → ℝ)) :=
  ((Measure.pi fun _ : Fin M => ν).prod unifPM1).map
    (fun p => (steerSign L ρ v p.1 p.2, p.1))

end OnlineDiscUniv



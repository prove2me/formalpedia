-- Prove2me | Definitions.Def_OnlineDiscUniv_IsProgOn
-- name    : OnlineDiscUniv_IsProgOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:04.420167+00:00
-- url     : https://prove2.me/theorems/f52b58eb-258e-427b-bcb7-627f9b826f36
-- title:
--   Progressive measurability on a horizon $[0,T]$
-- statement:
--   Let $\mathbb F=(\mathcal F_t)_{t\ge0}$ be a filtration and $T\in\mathbb R$. A real process $u=(u_t)_{t\ge0}$ is **progressively measurable on $[0,T]$** if for every $i\le T$ the map $(s,\omega)\mapsto u_s(\omega)$ on $[0,i]\times\Omega$ is measurable for $\mathcal B([0,i])\otimes\mathcal F_i$.
--
--   Controls in the paper live on a finite horizon $[0,T]$; this notion constrains them only up to the horizon.
--
--   **Formalization Note** This is Mathlib's strong progressive measurability restricted to times $i\le T$.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §2.2, (2.3)–(2.4), pp.5–6 (PDF pp.6–7); Appendix A, p.29 (PDF p.30)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace OnlineDiscUniv

/-- A real process `u` indexed by `ℝ≥0` is **progressively measurable on `[0,T]`** with respect to
a filtration `F` (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, §2.2, printed p.5, PDF
p.6, and Appendix A, p.29, PDF p.30): for every `i ≤ T`, the map `(s, ω) ↦ u s ω` on
`[0,i] × Ω` is strongly measurable for the product of the Borel σ-algebra of `[0,i]` and `F_i`.

**Formalization Note** This is Mathlib's `IsStronglyProgressive` restricted to the times
`i ≤ T`, so that a control "on `[0,T]`" is not constrained after the horizon. -/
def IsProgOn {Ω : Type*} {m : MeasurableSpace Ω} (F : Filtration ℝ≥0 m) (T : ℝ)
    (u : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ i : ℝ≥0, (i : ℝ) ≤ T →
    StronglyMeasurable[Subtype.instMeasurableSpace.prod (F i)]
      (fun p : Set.Iic i × Ω => u p.1 p.2)

end OnlineDiscUniv



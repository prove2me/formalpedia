-- Prove2me | Definitions.Def_SelectiveDPT_madv
-- name    : SelectiveDPT_madv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:54.39461+00:00
-- url     : https://prove2.me/theorems/fca4ac1c-959d-4065-9b92-4d0d2443f495
-- title:
--   Relational multiplicative adversary bound $\mathrm{MADV}^{\mathcal D}_{\varepsilon,\lambda,\eta}(R)$
-- statement:
--   For a relation $R$, a distribution $\mu$ on $D$ and parameters $\varepsilon, \lambda, \eta$ with $\eta < 1-\varepsilon$,
--   $$\mathrm{MADV}^{\mathcal D}_{\varepsilon,\lambda,\eta}(R) = \sup_{\Gamma} \log_{c(\Gamma)}\!\Big(1 + (\lambda-1)\big(\sqrt{1-\varepsilon}-\sqrt\eta\big)^2\Big),$$
--   the supremum over valid witnesses $(\Gamma, \lambda, \eta)$ for Proposition 2.14, with $c(\Gamma)$ the progress rate: the largest lower bound on $Q^{\mathcal D}_\varepsilon(R)$ that Proposition 2.14 yields with these parameters.
--
--   **Formalization Note** Values in $[0,\infty]$; a negative logarithm counts as $0$, and the supremum over no witness is $0$. The paper defines MADV only for $\eta < 1-\varepsilon$; outside that range the value is set to $0$. $\log_c$ is $\ln(\cdot)/\ln c$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Definition 2.15, p.17

import Mathlib
import Definitions.Def_SelectiveDPT_IsMultAdvWitness
import Definitions.Def_SelectiveDPT_rate

open scoped ENNReal

namespace SelectiveDPT

/-- `MADV^D_{ε,λ,η}(R)`, the largest lower bound on `Q^D_ε(R)` obtainable with
Proposition 2.14 over all valid `Γ` with the parameters `λ, η` (arXiv:2609.26678,
Definition 2.15, p.17): for `η < 1 − ε`, the supremum over witnesses `Γ` (`IsMultAdvWitness`) of
`log_{c(Γ)}(1 + (λ − 1)(√(1 − ε) − √η)²)`, with `c(Γ)` the progress rate `rate`.

**Formalization Note.** Values in `[0, ∞]`; the supremum over no witness is `0`. Definition 2.15
defines MADV only for `η < 1 − ε`; outside that range the value is set to `0`. `log_c` is
`Real.logb c`, which is `0` when `c = 1` or `c = 0`. -/
noncomputable def madv {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (μ : (ι → ZMod d) → ℝ) (D : Finset (ι → ZMod d)) (R : (ι → ZMod d) → Y → Prop)
    (ε lam η : ℝ) : ℝ≥0∞ :=
  if η < 1 - ε then
    ⨆ (Γ : Matrix D D ℂ) (_ : IsMultAdvWitness μ D R Γ lam η),
      ENNReal.ofReal (Real.logb (rate D Γ) (1 + (lam - 1) * (Real.sqrt (1 - ε) - Real.sqrt η) ^ 2))
  else 0

end SelectiveDPT



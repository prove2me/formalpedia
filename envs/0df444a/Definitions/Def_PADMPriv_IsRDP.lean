-- Prove2me | Definitions.Def_PADMPriv_IsRDP
-- name    : PADMPriv_IsRDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:18.59704+00:00
-- url     : https://prove2.me/theorems/4086b748-dd87-4aa0-8af9-50aba47527e3
-- title:
--   $(\alpha,\varepsilon)$-Rényi differential privacy (Definition 3)
-- statement:
--   A randomized mechanism $\mathcal A$ satisfies **$(\alpha,\varepsilon)$-Rényi differential privacy** if $\alpha>1$, $\varepsilon\ge0$ and
--   $$
--   D_\alpha\big(\mathcal A(D)\,\big\|\,\mathcal A(D')\big)\le\varepsilon\qquad\text{for every } D\sim D'.
--   $$
--
--   **Formalization Note** The mechanism is given by the law $\mathcal A(D)$ of its output for each data set $D$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Definition 3, p.4

import Mathlib
import Definitions.Def_PADMPriv_renyiDiv
import Definitions.Def_PADMPriv_Adjacent

namespace PADMPriv

open MeasureTheory

/-- Rényi differential privacy, Definition 3 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.4: a randomized
mechanism `𝒜` satisfies `(α, ε)`-RDP if `α > 1`, `ε ≥ 0` and `D_α(𝒜(D)‖𝒜(D′)) ≤ ε` for every
`D ∼ D′`.

**Formalization Note** The mechanism is given by its output law `M D` on a measurable space `O`
for each data set `D : Fin n → R`; `D_α` is `renyiDiv` (`EReal`-valued). -/
def IsRDP {R O : Type*} [MeasurableSpace O] {n : ℕ} (α ε : ℝ) (M : (Fin n → R) → Measure O) :
    Prop :=
  1 < α ∧ 0 ≤ ε ∧ ∀ D D' : Fin n → R, Adjacent D D' → renyiDiv α (M D) (M D') ≤ (ε : EReal)

end PADMPriv



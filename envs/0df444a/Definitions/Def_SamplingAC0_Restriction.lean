-- Prove2me | Definitions.Def_SamplingAC0_Restriction
-- name    : SamplingAC0_Restriction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:54.616185+00:00
-- url     : https://prove2.me/theorems/76f2acd9-72ec-4b84-a8f1-40f8e131d33d
-- title:
--   Restrictions, cylinders and the leaf of a decision tree
-- statement:
--   A **restriction** $\rho$ of $s$ input bits fixes some bits to values and leaves the others free. An input $x$ **extends** $\rho$ if it agrees with every fixed bit. $(U\mid\rho)$ is the uniform input conditioned on extending $\rho$; it is uniform on the free bits, which are independent and fair, and it is the input distribution of the **restricted forest** $f|_\rho$. The empty restriction $\rho_0$ leaves every bit free.
--
--   For a decision tree $T$ and an input $x$, the leaf $\gamma$ reached by $x$ is recorded as the restriction that fixes the bits queried on the path of $x$ to their values in $x$.
--
--   **Formalization Note** A restriction is a map from bit positions to "free" or a value. The cylinder of a restriction is never empty, so the conditioning is always defined.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3, pp.8–12 (restrictions ρ, f|ρ; leaves γ, Lemma 15, p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
set_option autoImplicit false

namespace SamplingAC0

/-- **Restriction (partial assignment).** Riazanov–Viola, *Sampling Tools and the Power of AC0*,
STOC 2027 submission (manuscript sha256 99c33d30…), §3, pp.8–12 ("restrict such popular queries",
"a restriction ρ", "f|ρ"). A restriction of `s` input bits fixes some bits to values (`some b`) and
leaves the others free (`none`). -/
abbrev Restriction (s : ℕ) : Type := Fin s → Option Bool

/-- The empty restriction `ρ₀`: every bit free. -/
def Restriction.empty (s : ℕ) : Restriction s := fun _ => none

/-- The input `x` agrees with every bit fixed by `ρ`. -/
def Extends {s : ℕ} (x : Fin s → Bool) (ρ : Restriction s) : Prop :=
  ∀ j b, ρ j = some b → x j = b

/-- The uniform input conditioned on extending `ρ` (`U | ρ`): uniform on the cylinder of `ρ`.
The cylinder is never empty, so the conditioning is always defined. This is the input distribution
of the restricted forest `f|ρ` (the free bits are independent and fair). -/
noncomputable def condRestr {s : ℕ} (ρ : Restriction s) : PMF (Fin s → Bool) :=
  condOn (unif (Fin s)) {x | Extends x ρ}

/-- The restriction fixed by the path of `x` through the decision tree `T` (the leaf `γ` reached by
`x`): the bits queried on that path, fixed to their values in `x`. -/
def pathRestriction {s : ℕ} {α : Type} (T : QAlgorithms.DecisionTree (Fin s) Bool α)
    (x : Fin s → Bool) : Restriction s :=
  fun j => if j ∈ queriedSet T x then some (x j) else none

end SamplingAC0



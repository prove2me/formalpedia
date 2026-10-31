-- Prove2me | Definitions.Def_PlatformCournot_poa
-- name    : PlatformCournot_poa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:38.759074+00:00
-- url     : https://prove2.me/theorems/13ffe0b8-9b0e-486c-bbd1-35cabab46f6a
-- title:
--   Definition 2 — price of anarchy $\rho$ at a supply profile
-- statement:
--   For a cost profile $C$ and a supply profile $q$, the **price of anarchy** at $q$ is the ratio of the efficient welfare of the **complete** edge set to the welfare of $q$:
--
--   $$\rho=\frac{\mathrm{SW}^*(F\times M,C)}{\mathrm{SW}(q,C)},\qquad \rho:=1\ \text{ if both } \mathrm{SW}^*(F\times M,C)=0 \text{ and } \mathrm{SW}(q,C)=0.$$
--
--   The paper's $\rho(\mathcal E,C)$ is this quantity at the Nash equilibrium $q=q^{\mathrm{NE}}(\mathcal E)$ of the game on $\mathcal E$; the numerator is always the efficient welfare of $F\times M$.
--
--   **Formalization Note** The value lies in $[0,\infty]$ (`ℝ≥0∞`): a positive numerator over a zero denominator gives $\infty$, not the real-division junk value $0$. Both welfares enter through `ENNReal.ofReal`, which loses nothing at a Nash equilibrium, where both are nonnegative.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Definition 2, p.13

import Mathlib
import Definitions.Def_PlatformCournot_efficientWelfare

namespace PlatformCournot

open scoped ENNReal

/-- **Price of anarchy, Definition 2, evaluated at a supply profile.**
Pang et al., arXiv:1903.04574v3, Definition 2, p.13: "ρ(ℰ,C) := SW∗(F × M,C) / SW(qNE(ℰ),C). We
define ρ(ℰ,C) := 1 if both SW∗(F × M,C) = 0 and SW(qNE(ℰ),C) = 0."

`poa D C q` is the ratio of the efficient welfare `SW∗(F × M, C)` of the **complete** edge set to the
welfare `SW(q, C)` of the profile `q`, with the value `1` when both are `0`. The paper's `ρ(ℰ, C)`
is `poa D C q` at the Nash equilibrium `q = q^NE(ℰ)` of the game on `ℰ`.

**Formalization Note** The value lies in `ℝ≥0∞`: a positive numerator over a zero denominator is
`⊤`, not the real-division junk value `0`. `ENNReal.ofReal` loses nothing at a Nash equilibrium,
where both welfares are nonnegative. Statements quantify over every Nash equilibrium instead of
naming "the" equilibrium `q^NE(ℰ)` (unique by Lemma 1). -/
noncomputable def poa {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ)
    (q : Fin n → Fin m → ℝ) : ℝ≥0∞ :=
  if efficientWelfare D C Set.univ = 0 ∧ socialWelfare D C q = 0 then 1
  else ENNReal.ofReal (efficientWelfare D C Set.univ) / ENNReal.ofReal (socialWelfare D C q)

end PlatformCournot



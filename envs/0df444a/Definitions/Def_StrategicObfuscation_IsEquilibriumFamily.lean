-- Prove2me | Definitions.Def_StrategicObfuscation_IsEquilibriumFamily
-- name    : StrategicObfuscation_IsEquilibriumFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:04.733818+00:00
-- url     : https://prove2.me/theorems/4124b1bc-9cac-4774-bee5-e04a91f1ece9
-- title:
--   An equilibrium at every $\sigma\in[0,1]$
-- statement:
--   Families $\alpha^*,Q^*$ indexed by $\sigma$ form an **equilibrium family** when $(e^*(\sigma),\alpha^*(\sigma),Q^*(\sigma))$ is an equilibrium at every $\sigma\in[0,1]$. Proposition 2 compares equilibria across resource levels, so this is the object it quantifies over.
--
--   **Formalization Note** The equilibrium at a given $\sigma$ need not be unique, so statements quantify over every family. Values outside $[0,1]$ carry no meaning.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Definition 1, pp.10–11, read at every σ as in Figure 3a, p.13

import Mathlib
import Definitions.Def_StrategicObfuscation_IsEquilibrium
import Definitions.Def_StrategicObfuscation_equilibriumEffort

open Set

namespace StrategicObfuscation

/-- **An equilibrium at every level of resources.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Definition 1, pp.10–11 (PDF pp.10–11), read at every
`σ ∈ [0, 1]`, as in Figure 3a, p.13 (PDF p.13).

`αS` and `QS` give the funding probability and the posterior at each `σ`, and
`(e*(σ), αS σ, QS σ)` is an equilibrium for every `σ ∈ [0, 1]`.

**Formalization Note** The equilibrium at a given `σ` need not be unique, as it is not at `pV = c`, so
statements quantify over every family. `αS` and `QS` carry no meaning outside `[0, 1]`. -/
def IsEquilibriumFamily (π : ℝ → ℝ → ℝ) (V c p : ℝ) (E : ℝ → ℝ → ℝ) (αS QS : ℝ → ℝ) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) 1, IsEquilibrium π V c p E σ (equilibriumEffort E αS σ) (αS σ) (QS σ)

end StrategicObfuscation



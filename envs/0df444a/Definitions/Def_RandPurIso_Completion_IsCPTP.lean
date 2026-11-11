-- Prove2me | Definitions.Def_RandPurIso_Completion_IsCPTP
-- name    : RandPurIso_Completion_IsCPTP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:23.510775+00:00
-- url     : https://prove2.me/theorems/0295922a-3158-45e2-a587-146947461292
-- title:
--   CPTP map: linear, completely positive, trace preserving
-- statement:
--   A map $\Phi:\mathbf L(X)\to\mathbf L(Y)$ between operators on finite-dimensional spaces is a **CPTP map** when
--
--   1. $\Phi$ is $\mathbb C$-linear;
--   2. $\Phi$ is completely positive: for every $n$ and every positive semidefinite $R$ on $X\otimes\mathbb C^n$, $(\Phi\otimes\mathrm{id}_n)(R)$ is positive semidefinite;
--   3. $\Phi$ preserves the trace: $\operatorname{Tr}\Phi(\rho)=\operatorname{Tr}\rho$.
--
--   Oracles and the steps of oracle algorithms in Definition 3.2 are CPTP maps.
--
--   **Formalization Note** Complete positivity is the published `PeresTerno.IsCompletelyPositive` (ampliation by $\mathbb C^n$ for every $n$); a map is any function on matrices, and the three properties are separate conditions.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.1, p. 17

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
open Matrix

namespace RandPurIso.Completion

/-- **CPTP map** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.1, p. 17: oracles and the steps of an oracle algorithm are
"CPTP maps").

`IsCPTP Φ` holds when `Φ : L(X) → L(Y)` is `ℂ`-linear, completely positive in the sense of
`PeresTerno.IsCompletelyPositive` (for every `n` and every positive semidefinite `R` on `X × Fin n`,
`(Φ ⊗ id_n) R` is positive semidefinite) and trace preserving on every matrix.

**Formalization Note.** A map is any function on matrices; the three properties are separate
conditions, so a concrete map is a CPTP map by a proof, not by construction. -/
def IsCPTP {X Y : Type} [Fintype X] [Fintype Y] (Φ : Matrix X X ℂ → Matrix Y Y ℂ) : Prop :=
  IsLinearMap ℂ Φ ∧ PeresTerno.IsCompletelyPositive Φ ∧ ∀ ρ : Matrix X X ℂ, (Φ ρ).trace = ρ.trace

end RandPurIso.Completion



-- Prove2me | Definitions.Def_MWCSherali_MWCHard
-- name    : MWCSherali_MWCHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:08.098415+00:00
-- url     : https://prove2.me/theorems/086b8772-75b5-4b8f-a5c6-fffcf7499c84
-- title:
--   NP-hardness of approximating Multiway Cut within $\rho$
-- statement:
--   **Multiway Cut is NP-hard to approximate within $\rho$** when, for some $c>0$ and $s>\rho c$, it is NP-hard to distinguish instances having a multiway cut of weight at most $cW$ from instances all of whose multiway cuts weigh at least $sW$ ($W>0$ the total weight, at least one terminal). The number of terminals is part of the input: this is Multiway Cut "with an arbitrary number of terminals" (Table 1, p.3).
--
--   It is `MWCHardOn` with no restriction on the number of terminals. Theorem 1.1 of the paper is this property for $\rho=1.22232$, assuming the Unique Games Conjecture.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 1.1, p.2; Table 1, p.3

import Mathlib
import Definitions.Def_MWCSherali_MWCHardOn

namespace MWCSherali

/-- **NP-hardness of approximating Multiway Cut within `ρ` (number of terminals part of the
input).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026),
Theorem 1.1, p.2 ("Multiway Cut is NP-hard to approximate within a factor of `ρ`"), for Multiway
Cut "with an arbitrary number of terminals" (Table 1, p.3).

`MWCHard ρ` is `MWCHardOn` with no restriction on the number of terminals: gap NP-hardness of
distinguishing instances with a multiway cut of weight `≤ c·W` from instances all of whose
multiway cuts weigh `≥ s·W`, for some `0 < c` and `s > ρ·c`. -/
def MWCHard (ρ : ℝ) : Prop := MWCHardOn (fun _ => True) ρ

end MWCSherali



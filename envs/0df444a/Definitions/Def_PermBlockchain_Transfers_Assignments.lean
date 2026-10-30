-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Assignments
-- name    : PermBlockchain_Transfers_Assignments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:44:10.348702+00:00
-- url     : https://prove2.me/theorems/8630ac03-df42-47ef-aed6-9876c8bef893
-- title:
--   The set $\Theta$ of type assignments with $m$ manufacturers of each type
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The paper assumes that $|M_\tau|=m$ for each of the four types $\tau$, where $M_\tau$ is the set of manufacturers of type $\tau$, and that this is common knowledge. The set of admissible type assignments is
--   $$\Theta=\bigl\{\theta:M\to\{A,B\}\times\{h,l\}\;:\;|\{i:\theta(i)=\tau\}|=m\text{ for every type }\tau\bigr\}.$$
--
--   Consumers' prior ("each manufacturer is equally likely to be of each type ex ante", p. 12) is the uniform distribution on $\Theta$, and every equilibrium condition of the mission is required for every $\theta\in\Theta$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered; p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Mfr

namespace PermBlockchain.Transfers

/-- **The set `Θ` of type assignments with exactly `m` manufacturers of each type.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 8 (PDF p. 9), unnumbered: "Letting M_i denote the set of type
i ∈ {A, B} × {h, l}, we assume that |M_i| = m for all i, and that all of this is common
knowledge".

**Formalization Note.** A type assignment is a function `θ : Mfr m → MType`; `Assignments m` is
the finite set of those with `|{i | θ i = τ}| = m` for each of the four types `τ`. Consumers'
uniform prior (p. 12) is the uniform distribution on this set. -/
def Assignments (m : ℕ) : Finset (Mfr m → MType) :=
  Finset.univ.filter (fun θ => ∀ τ : MType, (Finset.univ.filter (fun i => θ i = τ)).card = m)

end PermBlockchain.Transfers



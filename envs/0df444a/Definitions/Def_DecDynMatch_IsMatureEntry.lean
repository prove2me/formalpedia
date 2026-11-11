-- Prove2me | Definitions.Def_DecDynMatch_IsMatureEntry
-- name    : DecDynMatch_IsMatureEntry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:59:06.998864+00:00
-- url     : https://prove2.me/theorems/7c560770-ded5-4e6c-ae44-bf656bca98fc
-- title:
--   Mature entry (Definition 2)
-- statement:
--   A round $c$ is a **mature entry** if, after the round-start updates of round $c$ and before proposals, the root has just entered Work, while every other active player is in Seek with $\rho=0$ and a BUS rejection recorded during its current Seek visit. The Work modes that follow form a **mature execution**.
--
--   Mature executions are the units of the analysis: in a fixed market each of them computes the player-optimal stable matching by deferred acceptance with staggered entries and gives every player one output, at offset $\delta_i$ from the root's.
--
--   **Formalization Note** "Has just entered Work" means a pending Work entry of the root is applied at the start of round $c$; the recorded rejection is the flag $\textsf{seenR}$, which is cleared on every Seek entry.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Definition 2, p.14

import Mathlib
import Definitions.Def_DecDynMatch_exec
import Definitions.Def_DecDynMatch_busRank

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **Mature entry.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*,
arXiv:2610.41912 (held version, sha256 6a27277e…), Definition 2, p.14: "After the round-start
updates in round c and before proposals, suppose the root has just entered Work, while every other
player is in Seek with ρ = 0 and a BUS rejection recorded during its current Seek visit. Then c is
a mature entry, and the resulting Work modes form a mature execution."

`IsMatureEntryWithRoot F I c r`: `r` is the root at round `c`, a pending Work entry of `r` is
applied at the start of round `c` ("has just entered Work"), and every other active player has
round-start mode Seek, `ρ = 0` and `seenR = true` (the recorded BUS rejection; `seenR` is cleared
on every Seek entry, so it records a rejection of the current visit). -/
def IsMatureEntryWithRoot (F : ℕ → ℕ) (I : Instance K ι) (c : ℕ) (r : ι) : Prop :=
  IsRoot I c r ∧ (pre F I c r).ν = some .work ∧
    ∀ i ∈ active I c, i ≠ r →
      (cur F I c i).m = .seek ∧ (cur F I c i).ρ = 0 ∧ (cur F I c i).seenR = true

/-- `c` is a mature entry (Definition 2, p.14), with some root. -/
def IsMatureEntry (F : ℕ → ℕ) (I : Instance K ι) (c : ℕ) : Prop :=
  ∃ r, IsMatureEntryWithRoot F I c r

end DecDynMatch



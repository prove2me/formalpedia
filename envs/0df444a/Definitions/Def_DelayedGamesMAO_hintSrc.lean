-- Prove2me | Definitions.Def_DelayedGamesMAO_hintSrc
-- name    : DelayedGamesMAO_hintSrc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:34.630801+00:00
-- url     : https://prove2.me/theorems/fb7bb3a9-696b-41b0-bba0-c2d2b5c52781
-- title:
--   Hint sources $s_t$ of MAO-OMD
-- statement:
--   For a delay sequence $(d_s)$, the **hint sources** $s_1,s_2,\dots$ are defined by $s_1=0$ and, for $t\ge1$,
--   $$
--   s_{t+1}=\min\bigl(O_{t+1}\setminus\{s_1,\dots,s_t\}\bigr),\qquad s_{t+1}=0\ \text{if this set is empty}.
--   $$
--   So $s_t$ is the earliest observed round whose gradient has not yet served as a hint. The rule depends on the delays only, so two players facing the same delays use the same hint sources.
--
--   **Formalization Note** The definition carries the set $\{s_1,\dots,s_t\}$ along the recursion; the value $0$ may enter that set, which changes nothing since $0\notin O_t$. The value at $t=0$ is a placeholder that is never read.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §3, p.5, and Algorithm 1 line 3, p.12

import Mathlib
import Definitions.Def_DelayedGamesMAO_observed

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Hint sources** `s_1, s_2, …` of MAO-OMD.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §3, p.5, and Algorithm 1 (line 3), p.12: "let `s_t` be the smallest element of
`O_t \ {s_1, …, s_{t−1}}`, with `s_t = 0` if this set is empty"; "Initialize: … `s_1 = 0`".

`hintSrc d t = s_t` for `t ≥ 1`: the earliest observed round whose gradient has not yet served
as a hint, or `0` if there is none. It depends on the delays only.

**Formalization Note.** The auxiliary `state k = ({s_1, …, s_k}, s_k)` carries the set of sources
already used (`state 0 = (∅, 0)`, so `hintSrc d 0 = 0` is a placeholder never read). The value
`0` may be inserted into the set of used sources; this changes nothing because `0 ∉ O_t`.
`s_1 = 0` holds because `O_1 = ∅`. The rule is the paper's for every `t`, including
`s_{T+1}`. -/
def hintSrc (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  (state t).2
where
  /-- `state k = ({s_1, …, s_k}, s_k)`. -/
  state : ℕ → Finset ℕ × ℕ
    | 0 => (∅, 0)
    | k + 1 =>
      let J := observed d (k + 1) \ (state k).1
      let s := if h : J.Nonempty then J.min' h else 0
      (insert s (state k).1, s)

end DelayedGamesMAO



-- Prove2me | Definitions.Def_AntihydraRun
-- name    : AntihydraRun
-- status  : Definition
-- author  : @alon yuval
-- created : 2026-11-23T16:21:03.338545+00:00
-- url     : https://prove2.me/theorems/8ebee033-9d47-46d8-a6bb-5275848edd9a
-- title:
--   Antihydra step simulator with nonnegative counter
-- statement:
--   For $k, a, c \in \mathbb N$, $\mathrm{run}(k,a,c)$ iterates the Antihydra map $a \mapsto \lfloor 3a/2 floor$ for $k$ steps from $a$, while a counter starting at $c$ increases by $2$ whenever the current value is even and decreases by $1$ whenever it is odd. It returns the final pair $(a', c')$, or fails (`none`) as soon as an odd value is met while the counter is $0$, i.e. when the counter would become negative.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean (Antihydra)

namespace AntihydraRun

/-- `run k a c` simulates `k` steps of the Antihydra map `a ↦ ⌊3a/2⌋` starting from value `a`
with counter `c`: the counter gains 2 on even values and loses 1 on odd values. It returns
`some (a', c')` with the final state, or `none` if the counter would become negative. -/
def run : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, a, c => some (a, c)
  | k + 1, a, c =>
    if a % 2 = 0 then run k (3 * a / 2) (c + 2)
    else if c = 0 then none else run k (3 * a / 2) (c - 1)

end AntihydraRun



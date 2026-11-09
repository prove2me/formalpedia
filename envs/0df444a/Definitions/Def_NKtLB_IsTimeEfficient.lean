-- Prove2me | Definitions.Def_NKtLB_IsTimeEfficient
-- name    : NKtLB_IsTimeEfficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:02:14.09241+00:00
-- url     : https://prove2.me/theorems/ab413ff0-0d25-4106-9e6b-cc15d0ea13c6
-- title:
--   Time-efficient universal machines
-- statement:
--   A machine $U$ is **time-efficient** if for every machine $U'$ there is a constant $C$ such that, for every string $x$ and every time bound $t$,
--   $$
--   K^{C\,t\,(\lceil\log t\rceil+1)+C}_U(x)\ \le\ K^t_{U'}(x)+C .
--   $$
--   So $U$ simulates every other machine with a quasi-linear time overhead and a constant additive loss in description length.
--
--   **Formalization Note** The paper writes $K^{C\cdot t\log t}_U(x)\le K^t_{U'}(x)+C$. Read literally, $C\cdot t\log t=0$ for $t\le1$, and then no machine qualifies: a machine $U'$ that halts at once has $K^1_{U'}(\varepsilon)=0$, while $U$ would have to halt in $0$ steps. The time bound $C\,t(\lceil\log t\rceil+1)+C$ agrees with $C\,t\log t$ up to the constant for $t\ge2$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21

import Mathlib
import Definitions.Def_NKtLB_KMachine

namespace NKtLB

/-- **Time-efficient universal machine** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21): "We say that a (universal) machine `U`
is time-efficient if for every machine `U′` there is a constant `C` such that, for every string `x`
and time bound `t`, we have `K^{C·t log t}_U(x) ≤ K^t_{U′}(x) + C`."

**Formalization Note.** `t log t` is `t · (⌈log₂ t⌉ + 1)` and an additive `C` is added to the time
bound. Read literally, `C · t log t` is `0` for `t ≤ 1`, and then no machine `U` qualifies (a machine
`U′` that halts at once has `K^1_{U′}(ε) = 0`, while `U` would have to halt in `0` steps). For
`t ≥ 2` the two bounds agree up to the constant `C`. -/
def IsTimeEfficient (U : Machine) : Prop :=
  ∀ V : Machine, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
    KMachine U (C * (t * (Nat.clog 2 t + 1)) + C) x ≤ KMachine V t x + C

end NKtLB



-- Prove2me | Definitions.Def_MVBlossoms_IsBaseChain
-- name    : MVBlossoms_IsBaseChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:43:00.323921+00:00
-- url     : https://prove2.me/theorems/a9f54e7e-31b7-4f22-a0d2-f29c06bc17ef
-- title:
--   Iterated bases
-- statement:
--   The **iterated bases** of a vertex $u$ are $\mathrm{base}^1(u)=\mathrm{base}(u)$ and $\mathrm{base}^{k+1}(u)=\mathrm{base}(\mathrm{base}^k(u))$, as long as these bases exist.
--
--   The predicate says that a sequence $x_0,x_1,\dots,x_l$ satisfies $x_0=u$ and $x_{i+1}=\mathrm{base}(x_i)$ for $i<l$, so that $x_i=\mathrm{base}^i(u)$ for $1\le i\le l$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 25 and 30, pp.2033, 2037

import Mathlib
import Definitions.Def_MVBlossoms_IsBase

namespace MVBlossoms

/-- **Iterated bases.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 25 (p.2033) and 30 (p.2037):
"base¹(v) = b ... for k ≥ 1, ... base^{k+1}(v) = base(base^k(v))."

`IsBaseChain M u x l`: the sequence `x` starts at `x 0 = u` and `x (i + 1)` is the base of `x i`
for every `i < l`; then `x i = base^i(u)` for `1 ≤ i ≤ l`.

**Formalization Note.** Because `IsBase` is the relation `B(·) = {·}`, such a chain is unique
when it exists. -/
def IsBaseChain {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (u : V) (x : ℕ → V) (l : ℕ) : Prop :=
  x 0 = u ∧ ∀ i < l, IsBase M (x i) (x (i + 1))

end MVBlossoms



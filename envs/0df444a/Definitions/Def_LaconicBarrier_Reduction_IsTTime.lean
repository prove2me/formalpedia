-- Prove2me | Definitions.Def_LaconicBarrier_Reduction_IsTTime
-- name    : LaconicBarrier_Reduction_IsTTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:34.839054+00:00
-- url     : https://prove2.me/theorems/c659ea35-1c5d-4534-b22a-a5532eae697f
-- title:
--   $T$-time reductions
-- statement:
--   A reduction $\mathcal R$ with target-parameter map $f$, run against $(\mathcal C, c)$, is **$T$-time** if there is a constant $c$ such that, with $B = (T(\lambda,n)+2)^c$:
--
--   1. the reduction's coins and actions, and the challenger's coins and actions at $\lambda' = f(1^\lambda, n)$, are at most $B$;
--   2. one machine computes $1^{f(1^\lambda,n)}$ from $(1^\lambda, 1^n)$ within $B$ steps;
--   3. one machine computes the reduction's next action from $(1^\lambda, x, z, \text{coins}, \text{view})$ within $B$ steps, for every index $x$ (in the index set or not), every advice $z$ with $|z| \le T(\lambda, |x|)$ and every view, that is, for every oracle;
--   4. one machine computes the challenger's next action at $\lambda' = f(1^\lambda, n)$ within $B$ steps, for all coins and all messages.
--
--   So the target game is run as a $T$-time falsifiable game, and one execution can be simulated in time $\mathrm{poly}(T(\lambda,|x|))$ given the oracle answers.
--
--   **Formalization Note** The paper bounds the total time of one execution by $T$; the per-step form with a polynomial in $T$ contains every such reduction and is what the paper's arguments use ("the whole execution can be simulated in time poly($T$)", p.21). The bound does not grow with the view: a long oracle reply is read only as far as the clock allows.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.6, pp.20–21 (Syntax)

import Mathlib
import Definitions.Def_LaconicBarrier_Reduction
import Definitions.Def_LaconicBarrier_Game
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace LaconicBarrier

/-- The reduction `R`, run against the target game `G`, is a **`T`-time** reduction (Jain,
Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.6, pp.20–21: "`f(1^λ, n)`
is computable in time `T(λ, n)`"; "The total running time of one target-game execution, including
computing `f(1^λ, |x|)` and the computation of the target challenger `C(1^{λ′})`, is at most
`T(λ, |x|)` whenever `|z| ≤ T(λ, |x|)`, for every oracle and even when `x ∉ X`"; "the whole execution
can be simulated in time `poly(T(λ, |x|))` given oracle answers"). There is a constant `c` such that,
with `B = (T(λ, n) + 2)^c`:

1. the reduction's coins and actions, and the challenger's coins and actions at `λ′ = f(1^λ, n)`, are
   at most `B`;
2. one machine computes `1^{f(1^λ, n)}` from `(1^λ, 1^n)` within `B` steps;
3. one machine computes the reduction's next action from `(1^λ, x, z, ρ, view)` within `B` steps, for
   every index `x` (in the index set or not), every advice `z` with `|z| ≤ T(λ, |x|)`, all coins and
   every view (every oracle reply);
4. one machine computes the challenger's next action at `λ′ = f(1^λ, n)` from `(1^{λ′}, σ, messages)`
   within `B` steps, for all coins and every message list.

**Formalization Note** Each step of the execution is bounded by `poly(T)` and there are at most
`poly(T)` steps, so the whole execution takes `poly(T)` time; every strict `T`-time reduction
satisfies this, so the class is the paper's up to a polynomial in `T`. The bound does not grow with the
length of the view: a long oracle reply is read only as far as the clock allows. -/
def Reduction.IsTTime (R : Reduction) (G : Game) (T : ℕ → ℕ → ℕ) : Prop :=
  ∃ c : ℕ,
    (∀ lam n, R.coins lam n ≤ (T lam n + 2) ^ c ∧ R.fuel lam n ≤ (T lam n + 2) ^ c ∧
      G.coins (R.f lam n) ≤ (T lam n + 2) ^ c ∧ G.fuel (R.f lam n) ≤ (T lam n + 2) ^ c) ∧
    TimeOn (ι := ℕ × ℕ) (fun p => [unary p.1, unary p.2]) (fun p => unary (R.f p.1 p.2))
      (fun p => (T p.1 p.2 + 2) ^ c) ∧
    (∃ M : KarpLiptonOM.OracleTM, ∀ (lam : ℕ) (x z : List Bool)
      (ρ : Fin (R.coins lam x.length) → Bool) (evs : List Ev), z.length ≤ T lam x.length →
        RunsWithin M [unary lam, x, z, bits ρ, QAdvFew.PoQOracle.tup (evs.map Ev.code)]
          (R.next lam x z ρ evs).code ((T lam x.length + 2) ^ c)) ∧
    (∃ M : KarpLiptonOM.OracleTM, ∀ (lam n : ℕ) (σ : Fin (G.coins (R.f lam n)) → Bool)
      (ams : List (List Bool)),
        RunsWithin M [unary (R.f lam n), bits σ, QAdvFew.PoQOracle.tup ams]
          (G.next (R.f lam n) σ ams).code ((T lam n + 2) ^ c))

end LaconicBarrier



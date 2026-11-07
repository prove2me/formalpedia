-- Prove2me | Definitions.Def_SubmodSparsify_SFMTime
-- name    : SubmodSparsify_SFMTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:04.240192+00:00
-- url     : https://prove2.me/theorems/3647c2e4-9e63-4c10-aef7-560fef4ebde2
-- title:
--   $T_{\min}(n) \le T(n)$: one program minimizes every submodular function within $T(n)$ steps
-- statement:
--   Let $T : \mathbb N \to \mathbb N$. The predicate **SFMTime$(T)$** says that one admissible program of the published value-oracle RAM `FasterSFM.Machine` minimizes every submodular function $h : 2^{[n]} \to \mathbb R$ with a unit-cost value oracle, for every $n$: on every coin tape, the run halts with a set $X$ satisfying $h(X) \le h(Y)$ for all $Y$, after at most $T(n)$ executed instructions (each value query counting one).
--
--   This is the paper's parameter "$T_{\min}$, the time complexity of minimizing a submodular function on an $n$-element ground set with a unit-cost value oracle": a bound $O(\cdot\, T_{\min}(n) \cdots)$ is stated as a bound in $T(n)$ that holds for every $T$ with SFMTime$(T)$.
--
--   **Formalization Note** "Minimizing" means outputting a minimizer, not only the minimum value. The bound holds on every coin tape, so it is a deterministic time bound (the program can be run with any fixed tape). Only the program, admissibility and run of `FasterSFM.Machine` are used, not its randomized success event.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), p.3 (PDF p.5)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_FasterSFM_Machine

namespace SubmodSparsify

/-- **`T` bounds the time of submodular function minimization** (`Tmin(n) ≤ T(n)`; p.3).

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), p.3: "let Tmin denote the time
complexity of minimizing a submodular function on an n-element ground set with a unit-cost
value oracle".

`SFMTime T` holds when one admissible program `Q` of the published value-oracle RAM
`FasterSFM.Machine` minimizes every submodular `h : 2^{Fin n} → ℝ`, for every `n`: on every coin
tape the run halts with a minimizer `X` of `h` after at most `T n` executed instructions, each
value query counting one unit.

**Formalization Note.**
* "Minimizing" means outputting a minimizer (the machine halts with a set), not only the
  minimum value.
* The bound holds on every coin tape, so `Q` can be run with any fixed tape: this is a
  deterministic time bound, as the paper's `Tmin` (strongly polynomial algorithms).
* Only `FasterSFM.Program`, `Admissible`, `run` of the published machine are used; its
  randomized success event `Success` is not. -/
def SFMTime (T : ℕ → ℕ) : Prop :=
  ∃ Q : FasterSFM.Program, FasterSFM.Admissible Q ∧
    ∀ (n : ℕ) (h : Finset (Fin n) → ℝ), NonmonotoneSubmod.Shared.Submodular h →
      ∀ ω : ℕ → Bool, ∃ (t : ℕ) (X : Finset (Fin n)),
        (FasterSFM.run Q h ω t).output = some X ∧ (∀ Y : Finset (Fin n), h X ≤ h Y) ∧
        (FasterSFM.run Q h ω t).work ≤ T n

end SubmodSparsify



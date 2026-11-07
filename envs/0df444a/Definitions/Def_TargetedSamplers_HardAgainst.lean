-- Prove2me | Definitions.Def_TargetedSamplers_HardAgainst
-- name    : TargetedSamplers_HardAgainst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:53.792149+00:00
-- url     : https://prove2.me/theorems/98d86882-87d2-479d-a165-e11e67380f57
-- title:
--   Hardness against $\mathsf F(\mathsf{MA}\cap\mathsf{AM})_R\mathsf{TISP}[T,S]$ (Definition 4.20)
-- statement:
--   A function $f$ is **hard against $\mathsf F(\mathsf{MA}\cap\mathsf{AM})_R\mathsf{TISP}[T,S]$ on all but finitely many inputs** if every $\mathsf F(\mathsf{MA}\cap\mathsf{AM})_R\mathsf{TISP}[T,S]$ machine (without an oracle) that is consistent with $f$ computes $f$ at only finitely many inputs $x$.
--
--   **Formalization Note** The heading of Definition 4.20 says "input lengths". Its text and Theorems 4.29–4.30 say "inputs", and the set of inputs (of all lengths) at which $M$ computes $f$ is required to be finite. Consistency is required at every input, as printed.
--
--   The time and space bounds are read up to an additive constant: the machines range over time $T(n)+K$ and space $S(n)+K$, for every constant $K$. With exact bounds the class would be empty of real machines on the log-cost RAM. A halting run costs at least 1 and the first instruction runs on every input, so $T(0)=0$ or $T(1)=1$ (as for $T_0=n$ in Theorem 4.30) leaves only machines that answer $\bot$ at once, and every $f$ would be hard.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.20, p.29 (pdf p.31)

import Mathlib
import Definitions.Def_TargetedSamplers_IsConsistentMachine

namespace TargetedSamplers

/-- `f` is hard against `F(MA ∩ AM)_R TISP[T, S]` on all but finitely many inputs (Chen, Doron,
Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, Definition 4.20,
p.29): every `F(MA ∩ AM)_R TISP[T, S]` machine (no oracle) that is consistent with `f` computes `f`
at finitely many inputs at most.

**Formalization Note** The heading of Definition 4.20 says "all but finitely many input lengths",
its text and Theorems 4.29–4.30 say "finitely many inputs" / "all but finitely many inputs"; the set
of inputs `x` (all lengths together) at which `M` computes `f` is finite. Consistency is required at
every input, as printed.

The bounds `T` and `S` are read up to an additive constant: the machines range over time `T(n) + K`
and space `S(n) + K`, for every constant `K`. Exact bounds would empty the class on the log-cost
RAM: a halting run costs at least 1 and the first instruction runs on every input, so `T(0) = 0` or
`T(1) = 1` (as for `T₀ = n` in Theorem 4.30) leaves only machines that answer `⊥` at once, and every
`f` would be hard. -/
def HardAgainst (f : List Bool → List Bool) (R T S : ℕ → ℕ) : Prop :=
  ∀ (K : ℕ) (M : Program),
    IsConsistentMachine M f R (fun n => T n + K) (fun n => S n + K) (fun O => O = noOracle) →
      {x : List Bool | ComputesAt M f R (fun n => T n + K) noOracle x}.Finite

end TargetedSamplers



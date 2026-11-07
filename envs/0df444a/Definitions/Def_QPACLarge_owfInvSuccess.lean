-- Prove2me | Definitions.Def_QPACLarge_owfInvSuccess
-- name    : QPACLarge_owfInvSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:19.705974+00:00
-- url     : https://prove2.me/theorems/71fce6cc-ae19-4660-b78c-018b047f41e6
-- title:
--   Inversion probability of a clocked randomized inverter
-- statement:
--   For a function $F$ on bit strings, a machine $I$, a time bound $T$ and a length $n$, the **inversion probability** is
--
--   $$
--   \Pr_{x \sim U_n,\ r \sim U_T}\big[I(1^n, F(x), r) \text{ halts within } T \text{ steps with some } x' \in \{0,1\}^n,\ F(x') = F(x)\big],
--   $$
--
--   where $r$ is a string of $T$ uniform coins.
--
--   **Formalization Note** $I$ is a Mathlib multi-stack Turing machine (the published `HMBinPacking.OutputsWithin`); one machine for all $n$, no advice. A run that does not halt within $T$ steps fails. A machine running $T$ steps reads at most $T$ coins, so $T$ coins suffice and their number carries no advice.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.6, p.19

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_HMBinPacking_OutputsWithin

namespace QPACLarge

open QAlgorithms.Complexity

/-- **Inversion probability of a clocked randomized inverter.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.6, p.19: "`Pr_{x∼Uₙ, y=fₙ(x), I}[I(1ⁿ, y) ∈ fₙ⁻¹(y)]`" for an algorithm `I` running
in time at most `T`.

`owfInvSuccess F I T n` is the probability, over a uniform `x ∈ {0,1}ⁿ` and `T` uniform coin bits
`r`, that the machine `I`, started on `1ⁿ0 · F(x) · r`, halts within `T` steps with an `n`-bit
string `x'` such that `F(x') = F(x)`.

**Formalization Note.** `I` is a Mathlib multi-stack Turing machine (the published
`HMBinPacking.OutputsWithin`, i.e. `Turing.TM2OutputsInTime`); one deterministic machine, no
advice. A run that does not halt within `T` steps counts as failure, so every machine is admitted
and clocked at `T`. A machine running for `T` steps reads at most `T` coins, so `T` coin bits are
enough; their number is fixed by `T`, so it carries no advice. -/
noncomputable def owfInvSuccess (F : Str → Str) (I : Turing.TM2ComputableAux Bool Bool) (T n : ℕ) :
    ℝ :=
  open Classical in
  ((2 : ℝ) ^ n * (2 : ℝ) ^ T)⁻¹ *
    ((Finset.univ.filter fun xr : (Fin n → Bool) × (Fin T → Bool) =>
      ∃ out : Str, HMBinPacking.OutputsWithin I (encNat n ++ F (List.ofFn xr.1) ++ List.ofFn xr.2)
        out T ∧ out.length = n ∧ F out = F (List.ofFn xr.1)).card : ℝ)

end QPACLarge



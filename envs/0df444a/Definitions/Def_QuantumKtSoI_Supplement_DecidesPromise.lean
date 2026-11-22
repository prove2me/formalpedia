-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_DecidesPromise
-- name    : QuantumKtSoI_Supplement_DecidesPromise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:21.574099+00:00
-- url     : https://prove2.me/theorems/89972944-e664-42ac-8fe7-9e88eb1013fc
-- title:
--   Deciding a promise problem in time $T$ (convention of p.49)
-- statement:
--   A machine $A$ **decides a promise problem** $(\mathrm{YES},\mathrm{NO})$ **in time** $T$ if there is $n_0$ such that for every $n\ge n_0$ and every input $y$ of length $n$: $A$ on $y$ halts within $T(n)$ steps on every branch,
--   $$P_A(y;T(n),1)\ge 2/3\ \text{ if } y\in\mathrm{YES},\qquad P_A(y;T(n),1)\le 1/3\ \text{ if } y\in\mathrm{NO}.$$
--   Acceptance is halting with the single-bit output $1$; every other halting output counts as rejection. Deciding in time $O(T)$ is deciding in time $CT$ for a constant $C$.
--
--   This is the notion of decision used by the minimization lower bounds (Theorems 4.13, 7.8 and their corollaries).
--
--   **Formalization Note** The machine is a coded machine of the base mission; statements add its validity. A real deadline $T(n)$ means $\lfloor T(n)\rfloor$ steps (p.22).
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), convention after Definition 4.12, p.49

import Mathlib
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- A machine `B` **decides the promise problem** `(YES, NO)` **in time** `T` (convention after
Definition 4.12, p.49 of Myrisiotis, STOC 2027 submission, held version sha256 6616571c…): there is
`n₀` such that for every `n ≥ n₀` and every input `y` of length `n`, `B` on `y` halts within `T(n)`
steps on every branch, `P_B(y; T(n), 1) ≥ 2/3` if `y` is a YES instance and `P_B(y; T(n), 1) ≤ 1/3`
if `y` is a NO instance. Accepting is halting with the single-bit output `1`; every other output
counts as rejection.

**Formalization Note** A real deadline `T(n)` means `⌊T(n)⌋` steps (p.22). The machine is a coded
machine `B`; statements add `B.Valid` (a machine of Definition 3.1). -/
def DecidesPromise (B : CodedMachine) (YES NO : Set (List Bool)) (T : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ y : List Bool, n₀ ≤ y.length →
    B.toMachine.HaltsWithin y ⌊T y.length⌋₊ ∧
      (y ∈ YES → (2 / 3 : ℝ) ≤ B.toMachine.outputProb y ⌊T y.length⌋₊ [true]) ∧
      (y ∈ NO → B.toMachine.outputProb y ⌊T y.length⌋₊ [true] ≤ 1 / 3)

end QuantumKtSoI.Supplement



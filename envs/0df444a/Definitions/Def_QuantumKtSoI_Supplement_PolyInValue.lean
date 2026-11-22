-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_PolyInValue
-- name    : QuantumKtSoI_Supplement_PolyInValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:28:33.452932+00:00
-- url     : https://prove2.me/theorems/72f65f9e-90e7-443d-bb80-8de4472a8667
-- title:
--   Functions computable in time polynomial in the value of their argument; deterministic polynomial-time functions
-- statement:
--   A function $g:\mathbb N\to\mathbb N$ is **computable in time polynomial in the value of its argument** if a deterministic machine, on input the binary expansion $\mathrm b(\lambda)$, halts on every branch within $c(\lambda+2)^k$ steps with output $\mathrm b(g(\lambda))$, for constants $c,k$. A function $f$ on strings is **computable in deterministic polynomial time** if a deterministic machine on input $z$ halts within $c(|z|+2)^k$ steps with output $f(z)$.
--
--   The first notion is the hypothesis on gap functions in Theorems 7.3, 7.10 and F.4; the second is used for reductions, parsers and self-reductions.
--
--   **Formalization Note** A deterministic machine is a valid coded machine without gate states, as in the base mission; "with output $w$" is output probability one at the deadline. The paper names no input format for $g$; with a bound polynomial in the value $\lambda$, unary and binary inputs give the same class.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), pp.100, 110, 235 (gap functions); p.18 (polynomial-time maps)

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- `g : ℕ → ℕ` is **computable in time polynomial in the value of its argument** (Theorems 7.3,
7.10, F.4; Myrisiotis, STOC 2027 submission, held version sha256 6616571c…, pp.100, 110, 235): a
deterministic machine (a valid coded machine without gate states) on input `b(λ)` halts on every
branch within `c(λ+2)^k` steps with output `b(g(λ))` with probability one.

**Formalization Note** The paper names no input format; with a time bound polynomial in the value
`λ`, unary and binary inputs give the same class of functions. -/
def PolyInValue (g : ℕ → ℕ) : Prop :=
  ∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ lam : ℕ,
    F.toMachine.HaltsWithin (bin lam) (c * (lam + 2) ^ k) ∧
      F.toMachine.outputProb (bin lam) (c * (lam + 2) ^ k) (bin (g lam)) = 1

/-- A function `f` on strings is **computable in deterministic polynomial time** (p.18): a valid
coded machine without gate states, on input `z`, halts on every branch within `c(|z|+2)^k` steps
with output `f(z)` with probability one. -/
def PolyTimeFn (f : List Bool → List Bool) : Prop :=
  ∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ z : List Bool,
    F.toMachine.HaltsWithin z (c * (z.length + 2) ^ k) ∧
      F.toMachine.outputProb z (c * (z.length + 2) ^ k) (f z) = 1

end QuantumKtSoI.Supplement



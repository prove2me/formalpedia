-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_SizeAtMost
-- name    : LaconicBarrier_Supplement_SizeAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:29:06.253208+00:00
-- url     : https://prove2.me/theorems/8d7f8d2c-ff14-4d7f-8345-e514d38c2cdd
-- title:
--   Circuit size $\mathrm{size}_L(n)\le s$ and the class $\mathsf{SIZE}[s]$
-- statement:
--   For a language $L \subseteq \{0,1\}^*$, write $\mathrm{size}_L(n)$ for the minimum number of gates of a Boolean circuit with $n$ inputs that decides $L$ on all $n$-bit strings. The predicate $\mathrm{size}_L(n) \le s$ holds when some circuit $C$ with $n$ inputs and at most $s$ gates satisfies
--   $$
--   C(x) = 1 \iff x \in L \qquad \text{for every } x \in \{0,1\}^n .
--   $$
--   For a bound $s : \mathbb N \to \mathbb N$, the class $\mathsf{SIZE}[s]$ consists of the languages with $\mathrm{size}_L(n) \le s(n)$ for every $n$.
--
--   These are the circuit-size conclusions of Theorems 5.2, 6.10 and A.5: a language with a suitable proof system or oracle test has circuits of size $2^{O(\ell_P)}$ times a polynomial.
--
--   **Formalization Note** Circuits are the published fan-in-two circuits `KarpLiptonOM.Circuit` with gates in topological order; the size is the number of gates, as everywhere in this mission. The bound $\mathrm{size}_L(n)\le s$ is stated as the existence of a circuit of size at most $s$, which avoids taking a minimum over a set.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §A.2, p.72 (size_L); Theorem 5.2, p.36 and Theorem 6.10, p.45 (SIZE)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval

namespace LaconicBarrier.Supplement

open KarpLiptonOM

/-- **Circuit size at length `n`** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs:
Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), §A.2,
p.72: "Let `size_L(n)` denote the minimum number of gates of a circuit deciding `L` on all `n`-bit
strings"): `SizeAtMost L n s` says `size_L(n) ≤ s`, i.e. some circuit with `n` inputs and at most `s`
gates outputs `1` on an `n`-bit string `x` exactly when `x ∈ L`.

**Formalization Note** Circuits are the published `KarpLiptonOM.Circuit` (fan-in-two gates in
topological order), and the size is the number of gates, as in the rest of the mission. The minimum
is not taken as a number: "`size_L(n) ≤ s`" is stated as the existence of a circuit of size `≤ s`,
which is the same thing and avoids `sInf` of a set. -/
def SizeAtMost (L : Set (List Bool)) (n s : ℕ) : Prop :=
  ∃ C : Circuit n, C.gates.length ≤ s ∧ ∀ x : List Bool, x.length = n → (C.eval x = true ↔ x ∈ L)

/-- The class **`SIZE[s]`** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), Theorem 5.2, p.36; Theorem 6.10, p.45): `L ∈ SIZE[s(n)]` iff for every `n` the language
restricted to `{0,1}ⁿ` is decided by a circuit with at most `s(n)` gates. -/
def InSIZE (L : Set (List Bool)) (s : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, SizeAtMost L n (s n)

end LaconicBarrier.Supplement



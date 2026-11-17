-- Prove2me | Definitions.Def_TimeSpaceMA_Supplement_InMATIME
-- name    : TimeSpaceMA_Supplement_InMATIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:44:54.913334+00:00
-- url     : https://prove2.me/theorems/73e58d21-1828-46f6-975a-5515de53750c
-- title:
--   The class $\mathrm{MATIME}[T]$
-- statement:
--   A language $L$ is in $\mathrm{MATIME}[T]$ if there is one uniform Merlin–Arthur verifier with perfect completeness and soundness at most $1/3$ whose legal message length plus verifier running time is $O(T(n))$ on inputs of length $n$.
--
--   Concretely, one message cap $m(n)$ and one constant $C>0$ work for all inputs. Arthur halts within the combined budget on every random tape and every message of length at most $m(n)$. On a yes-instance, some legal message is accepted for every random tape; on a no-instance, every finite message is accepted with probability at most $1/3$.
--
--   This is the class in the precise noncontainment statement following Theorem 4.2.
--
--   **Formalization Note** Arthur is a finite program of the published log-cost RAM, and acceptance and the fair-coin measure are the published `TimeSpaceMA.ArthurAccepts` and `coinTape`. The budget uses $\max\{T(n),1\}$ only at the zero-size boundary.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Definition 2.1 and MATIME convention, pp.5–6

import Definitions.Def_TimeSpaceMA_ArthurAccepts

set_option autoImplicit false

open MeasureTheory

namespace TimeSpaceMA
namespace Supplement

/-- `L ∈ MATIME[T]` (Williams–Xi, *Short Non-Interactive Proofs for Time-Space Computations*,
STOC 2027 submission, manuscript sha256 184c2f95…, Definition 2.1, pp.5–6): one uniform
probabilistic verifier has perfect completeness and soundness at most `1/3`, and the sum of the
legal message length and verifier work is `O(T(n))`.

More precisely, `m n` is the legal message-length cap and `C` is one uniform hidden constant.
Arthur halts within the displayed combined budget on every coin tape and every message of length
at most `m n`. On a yes-instance some legal message is accepted on every tape; on a no-instance
every finite message, including an overlong one, is accepted on a set of tapes of measure at most
`1/3`.

**Formalization Note** Arthur is a finite program of the published log-cost `TimeSpaceMA.RAM`,
started with the published `(x, π)` memory layout. The measure is the published fair `coinTape`.
The bound uses `max (T n) 1` only at the degenerate size where an asymptotic budget may be zero;
this does not change the class on positive input lengths. Quantifying over every tape for perfect
completeness is equivalent to probability one for a halting finite-coin computation. -/
def InMATIME (L : Set (List Bool)) (T : ℕ → ℕ) : Prop :=
  ∃ (Arthur : Program) (m : ℕ → ℕ) (C : ℕ), 0 < C ∧
    ∀ x : List Bool,
      (∀ π : List Bool, π.length ≤ m x.length → ∀ τ : ℕ → Bool,
        ∃ st, Arthur.RunsTo τ (arthurMem x π) st ∧
          π.length + st.work ≤ C * max (T x.length) 1) ∧
      (x ∈ L → ∃ π : List Bool, π.length ≤ m x.length ∧
        ∀ τ : ℕ → Bool, ArthurAccepts Arthur x π τ) ∧
      (x ∉ L → ∀ π : List Bool,
        coinTape {τ | ArthurAccepts Arthur x π τ} ≤ 1 / 3)

end Supplement
end TimeSpaceMA



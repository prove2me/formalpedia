-- Prove2me | Definitions.Def_CompNonlocal_Supplement_CheatCommitter
-- name    : CompNonlocal_Supplement_CheatCommitter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:45.569483+00:00
-- url     : https://prove2.me/theorems/c28895b9-95f7-464b-9fd5-294930caa39e
-- title:
--   Computationally unbounded quantum committers
-- statement:
--   A **computationally unbounded quantum committer** $A^*$ has a private memory of arbitrary finite dimension $D$, starts in an arbitrary density matrix, and in each of its rounds applies an arbitrary quantum instrument whose outcome is its classical message, chosen after seeing the transcript so far. Each instrument element is given by Kraus operators; validity means the initial state is a density matrix and every instrument is trace preserving on the set of $N$-bit messages.
--
--   The derived function gives the committer's unnormalized memory after a transcript. Such committers interact with the honest receiver in the statistical sum-binding game of Definition 6.
--
--   **Formalization Note** One memory space for all rounds loses no generality; processing between messages is absorbed into the next instrument. Messages have the protocol's committer message length.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 6, p.23 (statistical sum binding)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Complexity

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- Computationally unbounded quantum committers. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 6, p.23 (statistical sum
binding): "Fix any computationally unbounded quantum committer A∗ interacting with the honest
receiver during the commit phase … The committer may deviate throughout commitment and use
arbitrary private quantum memory."

A committer with a `D`-dimensional memory starts in the state `init`; in each of its rounds `j`
(the even rounds) it applies a quantum instrument whose outcome is its message `m`, chosen after
seeing the transcript so far: the instrument element of outcome `m` is `ρ ↦ Σ_k K ρ K†` with Kraus
operators `K = kraus j T m k` (`T` the transcript prefix). `IsValid A N`: `init` is a density
matrix and, for `N`-bit messages, every instrument is trace preserving (`Σ_m Σ_k K†K = I`).
`mem T j` is the unnormalized memory after rounds `0, …, j−1` of the transcript `T`.

**Formalization Note** The memory dimension `D` and the number `nK` of Kraus operators are
arbitrary (one fixed space for all rounds loses no generality: embed every round's space into the
largest). Any processing of the memory between two of its messages is absorbed into the next
instrument. Messages have the honest committer's message length `N`, the message format of the
protocol. -/
structure CheatCommitter (D nK : ℕ) where
  /-- The initial memory state. -/
  init : Matrix (Fin D) (Fin D) ℂ
  /-- The Kraus operators of the round-`j` instrument element of message `m` after prefix `T`. -/
  kraus : ℕ → List Str → Str → Fin nK → Matrix (Fin D) (Fin D) ℂ

namespace CheatCommitter

open scoped Matrix ComplexOrder

/-- A valid committer for `N`-bit messages: a density matrix and trace-preserving instruments. -/
def IsValid {D nK : ℕ} (A : CheatCommitter D nK) (N : ℕ) : Prop :=
  A.init.PosSemidef ∧ A.init.trace = 1 ∧
    ∀ (j : ℕ) (T : List Str),
      ∑ m : Bits N, ∑ k : Fin nK, (A.kraus j T (List.ofFn m) k)ᴴ * A.kraus j T (List.ofFn m) k = 1

/-- The committer's unnormalized memory after rounds `0, …, j−1` of the transcript `T`. -/
noncomputable def mem {D nK : ℕ} (A : CheatCommitter D nK) (T : List Str) :
    ℕ → Matrix (Fin D) (Fin D) ℂ
  | 0 => A.init
  | j + 1 =>
    if j % 2 = 0 then
      ∑ k : Fin nK, A.kraus j (T.take j) (T.getD j []) k * mem A T j *
        (A.kraus j (T.take j) (T.getD j []) k)ᴴ
    else mem A T j

end CheatCommitter

end CompNonlocal.Supplement



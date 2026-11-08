-- Prove2me | Definitions.Def_SingleInteraction_UniformFamily
-- name    : SingleInteraction_UniformFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:48.891483+00:00
-- url     : https://prove2.me/theorems/0d9cc8ff-4bb7-43cc-9284-8e018233cb21
-- title:
--   Uniform polynomially bounded interaction family $\{h^{(n)}\}$
-- statement:
--   A family $\{h^{(n)}\}_{n\ge1}$ of $k$-qubit matrices is uniform when
--
--   1. a deterministic Turing machine, given $1^n$, a precision $q$ (in unary) and an entry index $s,t$, outputs in polynomial time a Gaussian rational within $2^{-q}$ of $h^{(n)}_{s,t}$, for every $n\ge1$;
--   2. there are constants $C,d$ with $\|h^{(n)}\|\le Cn^d$ for every $n\ge1$ (operator norm).
--
--   These are Definition 32's requirements.
--
--   **Formalization Note** The family is a function on all naturals; its value at $n=0$ is unconstrained.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 32, p.30

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SYKEdge_MatrixNorms

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- A uniform family `{h^(n)}_{n≥1}` of `k`-qubit matrices (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 32, p.30: "We require a
deterministic algorithm which, given `1^n` and a precision parameter `q`, outputs rational approximations
to all entries of `h^(n)` with additive error at most `2^{−q}` in time polynomial in `n` and `q`. We
additionally require `∥h^(n)∥ ≤ poly(n)`").

1. A function `f`, computed by a Turing machine in polynomial time, maps `n` and `q` (both in unary)
   and two basis states `s, t` to a pair of binary rationals `(r, r')` with positive denominators and
   `|r + r' i − h^(n)_{s,t}| ≤ 2^{−q}`, for every `n ≥ 1`;
2. there are `C, d` with `‖h^(n)‖ ≤ C n^d` for every `n ≥ 1` (operator norm).

**Formalization Note** The family is a function on `ℕ`; its value at `n = 0` is unconstrained, as the
paper indexes it by `n ≥ 1`. Conventions as in `EntriesPolyTime`. -/
def UniformFamily {k : ℕ} (hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) : Prop :=
  (∃ f : ℕ × (ℕ × (List ℕ × List ℕ)) → BinaryRational × BinaryRational,
    Nonempty (Turing.TM2ComputableInPolyTime
      (pair unary (pair unary (pair (BinaryEncoding.list natural) (BinaryEncoding.list natural)))).encode
      (pair binaryRationalCodec binaryRationalCodec).encode f) ∧
    ∀ n : ℕ, 1 ≤ n → ∀ (q : ℕ) (s t : Fin k → Fin 2),
      0 < (f (n, q, basisCode s, basisCode t)).1.denominator ∧
      0 < (f (n, q, basisCode s, basisCode t)).2.denominator ∧
      ‖((f (n, q, basisCode s, basisCode t)).1.value : ℂ) +
          ((f (n, q, basisCode s, basisCode t)).2.value : ℂ) * Complex.I - hfam n s t‖ ≤
        (1 / 2 : ℝ) ^ q) ∧
  ∃ C d : ℕ, ∀ n : ℕ, 1 ≤ n → SYKEdge.opNorm (hfam n) ≤ (C : ℝ) * (n : ℝ) ^ d

end SingleInteraction



-- Prove2me | Definitions.Def_CircTrichotomy_NumComputable
-- name    : CircTrichotomy_NumComputable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:46.79031+00:00
-- url     : https://prove2.me/theorems/886e9a0a-9c31-43b2-a6f8-9776cb0e44f5
-- title:
--   $\mathrm{num}[O(f),O(g)]$: numerical predicates computable by small circuits
-- statement:
--   A $k$-ary predicate $R\subseteq\mathbb N^k$ is **computable by a circuit family of size $O(f)$ and depth $O(g)$** if there are circuits $C_n:(\{0,1\}^n)^k\to\{0,1\}$, $n\ge1$, with $|C_n|\in O(f(n))$, $\mathrm{depth}(C_n)\in O(g(n))$ and, for every $n\ge1$ and $(v_1,\dots,v_k)\in[0,2^n-1]^k$,
--   $$(v_1,\dots,v_k)\in R\iff C_n(\mathrm{bin}_n(v_1),\dots,\mathrm{bin}_n(v_k))=1,$$
--   where $\mathrm{bin}_n(v)$ is the $n$-bit binary representation of $v$ with leading zeros. $\mathrm{num}[O(f),O(g)]$ is the class of these predicates.
--
--   **Formalization Note** $C_n$ is a single-output $(k\cdot n)$-circuit over the alphabet $\{0,1\}$ in the model of Definition A.2; bits are most significant first.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.18, p.29

import Mathlib
import Definitions.Def_CircTrichotomy_Circuit
import Definitions.Def_CircTrichotomy_BigO

set_option autoImplicit false

namespace CircTrichotomy

/-- The input `bin_n(v₁) ⋯ bin_n(v_k)` of length `k · n` over `{0, 1}` (`false = 0`, `true = 1`): block `j`
holds the `n`-bit binary representation of `v_j`, padded with leading zeros, most significant bit
first (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.18, p.29: "For x ∈ [0, 2ⁿ − 1], let bin_n(x) denote the n-bit binary
representation of x, padded with leading zeros"). Position `j · n + b` holds bit `n − 1 − b` of `v_j`. -/
def binInput (k n : ℕ) (v : Fin k → ℕ) (p : Fin (k * n)) : Bool :=
  (v (finProdFinEquiv.symm p).1).testBit (n - 1 - (finProdFinEquiv.symm p).2)

/-- **A numerical predicate computable by circuits of size `O(f)` and depth `O(g)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…),
Definition B.18, p.29): "A k-ary numerical predicate R ⊆ ℕᵏ is computable by a circuit family of
size O(f(n)) and depth O(g(n)) if there exists a family of circuits (C_n)_{n∈ℕ>0}, where
C_n : ({0,1}ⁿ)ᵏ → {0,1}, such that |C_n| = O(f(n)), depth(C_n) = O(g(n)), and, for every n ∈ ℕ>0
and every (v₁, …, v_k) ∈ [0, 2ⁿ − 1]ᵏ, (v₁, …, v_k) ∈ R ⟺ C_n(bin_n(v₁), …, bin_n(v_k)) = 1.   (76)"

`R = ⟨k, R'⟩` with `k ≥ 1`; `C_n` is a single-output `(k·n)`-circuit over the alphabet `Bool` (Definition
A.2), `n` is the bit length, and size and depth are `O(f)`, `O(g)` as functions of `n`. -/
def NumComputable (R : Σ r : ℕ, (Fin r → ℕ) → Prop) (f g : ℕ → ℝ) : Prop :=
  0 < R.1 ∧ ∃ C : ∀ n : ℕ, 0 < n → Circuit Bool (R.1 * n) 1,
    BigO (fun n => if h : 0 < n then ((C n h).size : ℝ) else 0) f ∧
    BigO (fun n => if h : 0 < n then ((C n h).depth : ℝ) else 0) g ∧
    ∀ (n : ℕ) (h : 0 < n) (v : Fin R.1 → ℕ), (∀ i, v i < 2 ^ n) →
      (R.2 v ↔ (C n h).Accepts (binInput R.1 n v))

/-- **`num[O(f), O(g)]`** (Definition B.18, p.29): "the class of all numerical predicates computable
by circuit families of size O(f(n)) and depth O(g(n))". -/
def numRels (f g : ℕ → ℝ) : Set (Σ r : ℕ, (Fin r → ℕ) → Prop) :=
  {R | NumComputable R f g}

end CircTrichotomy



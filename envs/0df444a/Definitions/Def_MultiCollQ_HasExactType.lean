-- Prove2me | Definitions.Def_MultiCollQ_HasExactType
-- name    : MultiCollQ_HasExactType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:33.572198+00:00
-- url     : https://prove2.me/theorems/d5035ba5-ad38-43cf-a690-652b1e498639
-- title:
--   Exact type $\lambda=(1^{n_1},\dots,k^{n_k})$ of a function $[N]\to\mathbb Z_q$, the set $F_{\lambda,q}$ and the pure type $(k^n)$
-- statement:
--   Identify an alphabet of size $q$ with $\mathbb Z_q$. For $f:[N]\to\mathbb Z_q$ and $y\in\mathbb Z_q$ let $|f^{-1}(y)|$ be the size of the equality class with value $y$. The function $f$ has **exact type** $\lambda=(1^{n_1},\dots,k^{n_k})$ if its equality classes form a partition of $[N]$ with exactly $n_i$ blocks of size $i$ for each $i\in[k]$:
--
--   $$
--   |f^{-1}(y)|\le k\ \text{ for all } y,\qquad \bigl|\{y : |f^{-1}(y)|=i\}\bigr| = n_i\quad(1\le i\le k).
--   $$
--
--   Then $N=\sum_i i\,n_i$ and $f$ takes $h=\sum_i n_i$ values, so the type is realizable exactly when $q\ge h$. $F_{\lambda,q}$ is the set of functions $[N]\to\mathbb Z_q$ of exact type $\lambda$. The **pure type** $(k^n)$ has $n$ blocks of size $k$ and no others: for $q\ge n$ a function $[kn]\to\mathbb Z_q$ of this type takes exactly $n$ values, each with exactly $k$ preimages.
--
--   These are the input classes of every result of the mission.
--
--   **Formalization Note** $[N]$ is `Fin N` (0-based) and $\mathbb Z_q$ is `ZMod q`. A type is a function $n:\mathbb N\to\mathbb N$ read at $1\le i\le k$. The class counts are `Set.ncard`, finite for $i\ge1$. `exactTypeSet` needs `[NeZero q]` so that `ZMod q` is finite; this excludes only $q=0$.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), §2, p.8 (exact types); §2.4, p.13 ($F_{\lambda,q}$); §1.1, p.3 (pure type)

import Mathlib

namespace MultiCollQ

/-- The size `|f⁻¹(y)|` of the equality class of `f : [N] → Z_q` with value `y` (Peng, Hou, Dong,
*Quantum multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), §2, p.8).

**Formalization Note.** `[N]` is `Fin N` (0-based) and the alphabet of size `q` is `ZMod q`. -/
def fiberCard {N q : ℕ} (f : Fin N → ZMod q) (y : ZMod q) : ℕ :=
  (Finset.univ.filter fun x => f x = y).card

/-- `f : [N] → Z_q` has **exact type** `λ = (1^{n_1}, …, k^{n_k})`: its equality classes form a
partition of `[N]` with exactly `n_i` blocks of size `i` for each `i ∈ [k]` (Peng, Hou, Dong,
manuscript (Oct. 2026), §2, p.8).

**Formalization Note.** The type is the function `n : ℕ → ℕ`, read at `1 ≤ i ≤ k` (values at other
`i` are ignored). The type lists all blocks, so no equality class is larger than `k`; this is the
first conjunct. The number of values with `i` preimages is a `Set.ncard`, finite for `i ≥ 1`. -/
def HasExactType {N q : ℕ} (k : ℕ) (n : ℕ → ℕ) (f : Fin N → ZMod q) : Prop :=
  (∀ y, fiberCard f y ≤ k) ∧
    ∀ i, 1 ≤ i → i ≤ k → Set.ncard {y : ZMod q | fiberCard f y = i} = n i

/-- `F_{λ,q}`, the set of functions `[N] → Z_q` of exact type `λ` (Peng, Hou, Dong, manuscript
(Oct. 2026), §2.4, p.13).

**Formalization Note.** `[NeZero q]` makes `ZMod q` finite; it excludes only `q = 0`. -/
noncomputable def exactTypeSet (N q : ℕ) [NeZero q] (k : ℕ) (n : ℕ → ℕ) :
    Finset (Fin N → ZMod q) := by
  classical
  exact Finset.univ.filter fun f => HasExactType k n f

/-- The **pure type** `(k^n)`: `n` blocks of size `k` and no other blocks (Peng, Hou, Dong,
manuscript (Oct. 2026), §1.1, p.3). -/
def pureType (k n : ℕ) : ℕ → ℕ := fun i => if i = k then n else 0

end MultiCollQ



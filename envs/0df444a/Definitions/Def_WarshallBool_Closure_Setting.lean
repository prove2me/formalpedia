-- Prove2me | Definitions.Def_WarshallBool_Closure_Setting
-- name    : WarshallBool_Closure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:04.795344+00:00
-- url     : https://prove2.me/theorems/62ca4039-1b1b-4ad9-a0bc-937afe80848f
-- title:
--   p. 11 — boolean product, boolean powers $M^i$, the sum $\bigvee_{i=1}^d M^i$, the chain closure $M'$, and footnote 3's recursion
-- statement:
--   Throughout, $d \ge 0$ is a natural number and a **$d \times d$ boolean matrix** is an array $M = (m_{ij})$ whose entries are $0$ or $1$. This file fixes the objects of the first page of Warshall's note.
--
--   1. **Boolean product.** For boolean matrices $A$ and $B$, the boolean product $A \wedge B$ is the matrix whose $(i,j)$ entry is
--   $$
--   (A \wedge B)_{ij} \;=\; \bigvee_{k} \bigl(a_{ik} \wedge b_{kj}\bigr),
--   $$
--   that is, $1$ exactly when some index $k$ has $a_{ik} = b_{kj} = 1$.
--
--   2. **Boolean powers.** $M^1 = M$ and $M^{p+1} = M^p \wedge M$ for $p \ge 1$. Thus $(M^p)_{ij} = 1$ exactly when there is a sequence of $p$ entries of $M$ equal to $1$ leading from row $i$ to column $j$.
--
--   3. **Boolean sum of the powers.** The introduction's matrix
--   $$
--   M' \;=\; \bigvee_{p=1}^{d} M^p ,
--   $$
--   whose $(i,j)$ entry is $1$ exactly when $(M^p)_{ij} = 1$ for some $p$ with $1 \le p \le d$.
--
--   4. **Chain closure.** The THEOREM's definition of $M'$: $m'_{ij} = 1$ if and only if either $m_{ij} = 1$, or there are indices $k_1, \dots, k_n$ with
--   $$
--   m_{ik_1} = m_{k_1k_2} = \cdots = m_{k_{n-1}k_n} = m_{k_nj} = 1 ;
--   $$
--   $m'_{ij} = 0$ otherwise. There is no reflexive part: $m'_{ii} = 1$ only through such a chain from $i$ back to $i$.
--
--   5. **Footnote 3's recursion.** $(m_{ij})_0 = m_{ij}$ and
--   $$
--   (m_{ij})_{n+1} \;=\; (m_{ij})_n \,\vee\, \bigl((m_{i,n+1})_n \wedge (m_{n+1,j})_n\bigr),
--   $$
--   the matrix obtained after using the indices $1, \dots, n+1$ as intermediate points; footnote 3 sets $m^*_{ij} = (m_{ij})_d$.
--
--   These are the objects compared in the mission: Warshall's construction $M^*$ (published separately as Floyd's Algorithm 96) is asserted to equal the matrix of item 3, which footnote 2 identifies with item 4, and footnote 3 identifies $M^*$ with item 5 at stage $d$.
--
--   **Formalization Note** Matrices are functions $\mathrm{Fin}\,d \to \mathrm{Fin}\,d \to \mathrm{Bool}$ with $1$ as `true`; indices are $0, \dots, d-1$ instead of the page's $1, \dots, d$. The boolean product is defined directly by "there exists $k$" and not through Mathlib's matrix product over `Bool`, whose addition is exclusive or. The powers are indexed so that `boolPow M p` is the page's $M^p$ for every $p \ge 1$; the base case `boolPow M 0` is the identity matrix, which is not on the page and does not enter the sum (the sum runs over $p \in \{1, \dots, d\}$). The chain closure is a proposition stating that some list $k_1, \dots, k_n$ (possibly empty) makes $i, k_1, \dots, k_n, j$ a chain of $1$ entries. In the recursion the page's 1-based pivot $n+1$ is the 0-based index $n$; past stage $d$ the recursion leaves the matrix unchanged, a case footnote 3 never uses.
-- source:
--   Warshall, A theorem on Boolean matrices, J. ACM 9 (1962), p. 11, introduction (boolean product, boolean sum, display M′ = ∨_{i=1}^d M^i), THEOREM (definition of M′) and footnote 3

import Mathlib

namespace WarshallBool.Closure

/-- Warshall (1962), p. 11, first sentence: the boolean product `A ∧ B` of two `d × d` boolean
matrices, whose `(i, j)` entry is `∨_k (a_ik ∧ b_kj)`. Written with `∃ k` (boolean OR over `k`),
not with Mathlib's `Matrix` product over `Bool`, whose addition is XOR. -/
def boolProd {d : ℕ} (A B : Fin d → Fin d → Bool) : Fin d → Fin d → Bool :=
  fun i j => decide (∃ k, A i k = true ∧ B k j = true)

/-- Warshall (1962), p. 11, introduction display: the boolean powers `M^p`, with
`M^(p+1) = M^p ∧ M`. The base `boolPow M 0` is the boolean identity matrix, so that
`boolPow M 1 = M` (the page's `M^1 = M`); the exponent `0` is not on the page and is never used
in the sum `powerSum`. -/
def boolPow {d : ℕ} (M : Fin d → Fin d → Bool) : ℕ → Fin d → Fin d → Bool
  | 0 => fun i j => decide (i = j)
  | p + 1 => boolProd (boolPow M p) M

/-- Warshall (1962), p. 11, introduction display: `M′ = ∨_{p=1}^{d} M^p`, the boolean sum of
the boolean powers `M^1, …, M^d`; its `(i, j)` entry is `1` iff some `M^p` with `1 ≤ p ≤ d`
has `(i, j)` entry `1`. -/
def powerSum {d : ℕ} (M : Fin d → Fin d → Bool) : Fin d → Fin d → Bool :=
  fun i j => decide (∃ p ∈ (Finset.Icc 1 d : Finset ℕ), boolPow M p i j = true)

/-- Warshall (1962), p. 11, THEOREM: the chain definition of `M′`. `m′_ij = 1` iff `m_ij = 1`
(`ks = []`) or there are indices `k_1, …, k_n` with
`m_{i k_1} = m_{k_1 k_2} = ⋯ = m_{k_n j} = 1` (`ks = [k_1, …, k_n]`). -/
def ChainRel {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) : Prop :=
  ∃ ks : List (Fin d), List.IsChain (fun a c => M a c = true) (i :: ks ++ [j])

/-- Warshall (1962), p. 11, footnote 3: the recursive definition
`(m_ij)_0 = m_ij`, `(m_ij)_{n+1} = (m_ij)_n ∨ ((m_{i,n+1})_n ∧ (m_{n+1,j})_n)`.
The page's 1-based pivot `n + 1` is the 0-based index `⟨n, h⟩`; for `n ≥ d` (never used by the
footnote, which stops at `(m_ij)_d`) the matrix is left unchanged. -/
def warshallRec {d : ℕ} (M : Fin d → Fin d → Bool) : ℕ → Fin d → Fin d → Bool
  | 0 => M
  | n + 1 => fun i j =>
      if h : n < d then
        warshallRec M n i j || (warshallRec M n i ⟨n, h⟩ && warshallRec M n ⟨n, h⟩ j)
      else warshallRec M n i j

end WarshallBool.Closure



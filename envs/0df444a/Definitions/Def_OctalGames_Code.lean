-- Prove2me | Definitions.Def_OctalGames_Code
-- name    : OctalGames_Code
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:01:59.579262+00:00
-- url     : https://prove2.me/theorems/4c3ea577-b908-416a-b3b6-e8993a19ee9c
-- title:
--   Octal games: codes, nim-values and eventual periodicity
-- statement:
--   An **octal game** is an impartial heap game in which a move removes some tokens from one heap and optionally splits what remains into two heaps. Its rules are given by an **octal code** $d_0.d_1d_2\cdots d_k$ with digits $d_i\in\{0,\dots,7\}$. Write $d_i = e_0 + 2e_1 + 4e_2$ with $e_j\in\{0,1\}$. For a heap of $n$ tokens:
--
--   1. if $e_0(d_i)=1$ and $i=n\ge 1$, the whole heap may be removed, leaving no heap;
--   2. if $e_1(d_i)=1$ and $1\le i<n$, one may remove $i$ tokens and leave a single heap of $n-i$ tokens;
--   3. if $e_2(d_i)=1$, one may remove $i$ tokens and split the rest into two nonempty heaps of sizes $a,b\ge1$ with $a+b=n-i$.
--
--   Digits beyond $d_k$ are $0$. The **nim-value** $\mathcal G(n)$ of a heap of $n$ tokens is defined by the mex rule:
--   $$
--   \mathcal G(n)=\operatorname{mex}\Bigl(\{0 : \text{rule 1}\}\cup\{\mathcal G(n-i) : \text{rule 2}\}\cup\{\mathcal G(a)\oplus\mathcal G(b) : \text{rule 3}\}\Bigr),
--   $$
--   where $\operatorname{mex} S$ is the least natural number not in $S$ and $\oplus$ is bitwise exclusive or. The sequence $\mathcal G$ is **eventually periodic** if there are $n_0\ge0$ and $p\ge1$ with $\mathcal G(n+p)=\mathcal G(n)$ for all $n\ge n_0$.
--
--   For example, Kayles is $0.77$, Dawson's Kayles is $0.07$, and Nim is $0.333\cdots$. By the Sprague–Grundy theorem, $\mathcal G$ determines the outcome of every sum of heaps, so these definitions are the basis for stating periodicity results about octal games.
--
--   **Formalization Note** The code is a finite list $[d_0,d_1,\dots,d_k]$ of elements of `Fin 8`. The values $\mathcal G(0),\dots,\mathcal G(n)$ are computed by a table built by structural recursion, so the definition is executable; the first 84 values of Kayles agree with Siegel's Figure 2.3. Rule 3 with $i=0$ (bit $e_2$ of $d_0$) splits a heap without removing tokens, as in Siegel's convention. Bits $e_0,e_1$ of $d_0$ are ignored: they would describe no move, or a move from a heap to itself.
-- source:
--   A. N. Siegel, Combinatorial Game Theory, Graduate Studies in Mathematics 146, AMS 2013, Section IV.2 'Heap Games', pp. 188-189: octal code d0.d1d2..., digit di = e0 + 2e1 + 4e2, Figure 2.2

import Mathlib

namespace OctalGames

/-- A finite octal code `d₀.d₁d₂…d_k` (Siegel, *Combinatorial Game Theory*, §IV.2),
given by its list of digits `[d₀, d₁, …, d_k]`, each in `{0,…,7}`. -/
structure Code where
  digits : List (Fin 8)

/-- The `i`-th digit `dᵢ` of the code, as a natural number; `0` beyond the end of the list. -/
def Code.digit (c : Code) (i : ℕ) : ℕ :=
  ((c.digits[i]?).map Fin.val).getD 0

/-- Bit `j` of the digit `dᵢ` (`dᵢ = e₀ + 2e₁ + 4e₂`). -/
def Code.bit (c : Code) (i j : ℕ) : Bool :=
  (c.digit i).testBit j

/-- The minimal excludant: the least natural number not in `s`. -/
def mex (s : Finset ℕ) : ℕ :=
  Nat.find (Infinite.exists_notMem_finset s)

/-- The nim-values of the options of a heap of size `n`, given the nim-values `g m` of smaller heaps.
Removing `i ≥ 1` tokens and leaving no heap (`i = n`) is allowed when `e₀(dᵢ) = 1`; removing `i ≥ 1`
tokens and leaving one nonempty heap of size `n - i` is allowed when `e₁(dᵢ) = 1`; removing `i ≥ 0`
tokens and leaving two nonempty heaps of sizes `a, b` with `a + b = n - i` is allowed when
`e₂(dᵢ) = 1`. (The bits `e₀, e₁` of `d₀` describe no legal move.) Only values `g m` with `m < n` are used. -/
def optionValues (c : Code) (g : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (if 1 ≤ n ∧ c.bit n 0 then {0} else ∅) ∪
  ((Finset.Ico 1 n).filter (fun i => c.bit i 1)).image (fun i => g (n - i)) ∪
  ((Finset.Ico 1 n ×ˢ Finset.Ico 1 n).filter
      (fun ab => ab.1 + ab.2 ≤ n ∧ c.bit (n - (ab.1 + ab.2)) 2)).image (fun ab => g ab.1 ^^^ g ab.2)

/-- The table `[𝒢(0), 𝒢(1), …, 𝒢(n-1)]` of nim-values of heaps, built by the mex rule. -/
def table (c : Code) : ℕ → List ℕ
  | 0 => []
  | n + 1 => let t := table c n; t ++ [mex (optionValues c (fun m => t.getD m 0) n)]

/-- The nim-value `𝒢(n)` of a heap of `n` tokens in the octal game with code `c`. -/
def grundy (c : Code) (n : ℕ) : ℕ :=
  (table c (n + 1)).getD n 0

/-- The nim-sequence is eventually periodic: there are `n₀` and `p > 0` with
`𝒢(n + p) = 𝒢(n)` for all `n ≥ n₀`. -/
def EventuallyPeriodic (c : Code) : Prop :=
  ∃ n₀ p : ℕ, 0 < p ∧ ∀ n, n₀ ≤ n → grundy c (n + p) = grundy c n

end OctalGames



-- Prove2me | Definitions.Def_ClosestString_PTAS_Basic
-- name    : ClosestString_PTAS_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T16:17:37.863189+00:00
-- url     : https://prove2.me/theorems/8f7c28a6-fe51-42bc-bdbb-a26ce44e5751
-- title:
--   Strings, restrictions d^T and d^R, length-L substrings, the Closest Substring cost and d_opt, agreement sets Q and ρ_k·d (pp. 2–3, 9–10)
-- statement:
--   This file fixes the objects of Li, Ma and Wang's analysis of Closest String and Closest Substring.
--
--   1. **Strings and Hamming distance** (p. 2). A string of length $m$ over a finite alphabet $\Sigma$ is a map $\{1,\dots,m\}\to\Sigma$; $d(s,s')$ is the Hamming distance, the number of positions where $s$ and $s'$ differ.
--   2. **Restricted distances** (pp. 3, 10). For a position set $T$, $d^T(u,v)=d(u|_T,v|_T)$ is the number of positions $j\in T$ with $u[j]\ne v[j]$. For a position *multiset* $R=\{j_1,\dots,j_k\}$ (repetitions allowed), $d^R(u,v)$ counts the entries $a$ of $R$ with $u[j_a]\ne v[j_a]$, with multiplicity.
--   3. **Substrings.** A length-$L$ substring of a length-$m$ string $s$ is $s[p+1]\cdots s[p+L]$ for a start $p$ with $p+L\le m$.
--   4. **Closest Substring** (p. 2). For strings $s_1,\dots,s_n$ of length $m$ and a center $c$ of length $L$,
--   $$\mathrm{cost}(c)=\max_{1\le i\le n}\ \min_{t_i\sqsubseteq s_i,\ |t_i|=L} d(c,t_i),\qquad d_{\mathrm{opt}}=\min_{c\in\Sigma^L}\mathrm{cost}(c).$$
--   This is the quantity $c$ of Figure 3, step 1(c)(iii), and the optimum $d_{\mathrm{opt}}$ of p. 9.
--   5. **Agreement sets** (p. 3). For strings $u_1,\dots,u_n$ of one length, an index tuple $(i_1,\dots,i_k)$ and a center $c$: $Q_{i_1,\dots,i_k}$ is the set of positions where $u_{i_1},\dots,u_{i_k}$ all agree; $p_{i_1,\dots,i_k}$ is the number of positions of $Q_{i_1,\dots,i_k}$ where $u_{i_1}$ differs from $c$; $\rho_k d=\min_{i_1,\dots,i_k}p_{i_1,\dots,i_k}$, and $\rho_0 d=\max_{i,j}d(u_i,u_j)$.
--   6. **Splicing.** The string equal to $x$ on a position set $P$ and to $f$ off $P$; this is $s'$ of Figure 3 step 1(c)(iii) ($x$ on $P$, $t_{i_1}$ on $Q$) and $s^*$ of p. 10 ($s$ on $P$, $t_{i_1}$ on $Q$).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** The alphabet is a type `A` with decidable equality (finiteness is added where needed); strings of length $m$ are `Fin m → A`, positions are 0-based, and Hamming distance is Mathlib's `hammingDist`. A multiset $R$ of $k$ positions is a function `Fin k → Fin L`. Substrings are indexed by their start `p : Fin m` with `p + L ≤ m`. Index tuples are `Fin k → Fin n` and may repeat indices. The ratios $\rho_k$ are stored multiplied by $d$ (`minMismatch`, `maxPairDist`) so that $d_{\mathrm{opt}}=0$ needs no division. `p_{i1,…,ik}` is written as "some $u_{i_a}$ differs from $c$" on $Q$, which equals "$u_{i_1}$ differs from $c$" there for $k\ge1$. Junk values: `minDistSub` is $0$ when the string has no length-$L$ substring ($L>m$), `minMismatch` is $0$ when no tuple exists ($n=0$, $k\ge1$); every theorem assumes $L\le m$ and $n\ge1$ where these matter.
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, pp. 2–3 (problem definitions, position (multi)sets, Q_{i1,…,ik}, ρ0, p_{i1,…,ik}, ρk), pp. 9–10 (d_opt, d^T, Figure 3 step 1(c)(iii))

import Mathlib

namespace ClosestString.PTAS

/-!
# Li, Ma & Wang, *On the Closest String and Substring Problems* (arXiv:cs/0002012v1), pp. 2–4, 9–10

Strings over a finite alphabet `A` (the paper's `Σ`) are functions `Fin m → A` (positions are 0-based; the paper's
positions `1, …, m` are a relabelling). The Hamming distance of two full strings is Mathlib's
`hammingDist`. This file fixes:

* `distOn T u v` — the Hamming distance of `u|T` and `v|T` for a position **set** `T`;
* `distSample R u v` — the Hamming distance of `u|R` and `v|R` for a position **multiset**
  `R : Fin k → Fin L` (entry `a` of the multiset is the position `R a`; repetitions count with
  multiplicity), i.e. the paper's `d^R(u, v)` (p. 10);
* `Start m L`, `substr` — the length-`L` substrings of a length-`m` string, by start position;
* `minDistSub`, `cost`, `dOpt` — the Closest Substring objective (p. 2, Figure 3 step 1(c)(iii)) and
  its optimum `d_opt` (p. 9);
* `agreeSet`, `mismatchOnAgree`, `minMismatch` — Section 2's `Q_{i1,…,ik}`, `p_{i1,…,ik}` and
  `ρ_k · d_opt` (p. 3), for index tuples with repetitions allowed.
-/

variable {A : Type*}

/-- `d^T(u, v)`: the number of positions `j ∈ T` at which `u` and `v` differ, i.e. the Hamming
distance of the restrictions `u|T` and `v|T` (p. 3, p. 10). -/
def distOn {L : ℕ} [DecidableEq A] (T : Finset (Fin L)) (u v : Fin L → A) : ℕ :=
  (T.filter (fun j => u j ≠ v j)).card

/-- `d^R(u, v)` for a position multiset `R` given as `R : Fin k → Fin L` (its `k` entries, with
repetitions): the number of entries `a` with `u (R a) ≠ v (R a)` (p. 10). -/
def distSample {L k : ℕ} [DecidableEq A] (R : Fin k → Fin L) (u v : Fin L → A) : ℕ :=
  (Finset.univ.filter (fun a => u (R a) ≠ v (R a))).card

/-- Start positions of length-`L` substrings of a length-`m` string: `p` with `p + L ≤ m`
(0-based; for `1 ≤ L ≤ m` there are `m − L + 1` of them). -/
abbrev Start (m L : ℕ) := {p : Fin m // p.val + L ≤ m}

/-- The length-`L` substring of `s` starting at `p`: position `j` of it is `s[p + j]`. -/
def substr {m L : ℕ} (s : Fin m → A) (p : Start m L) : Fin L → A :=
  fun j => s ⟨p.1.val + j.val, by have := p.2; omega⟩

/-- `min_{t ⊑ s} d(c, t)`: the distance from a center `c` of length `L` to its closest length-`L`
substring of `s`. (Junk value `0` when `s` has no length-`L` substring, i.e. `L > m`; every theorem
assumes `L ≤ m`.) -/
noncomputable def minDistSub {m L : ℕ} [DecidableEq A] (c : Fin L → A) (s : Fin m → A) : ℕ :=
  if h : (Finset.univ : Finset (Start m L)).Nonempty then
    Finset.univ.inf' h (fun p => hammingDist c (substr s p))
  else 0

/-- The Closest Substring cost of a center `c` for the instance `S`:
`max_{i} min_{t_i ⊑ s_i} d(c, t_i)` (p. 2; Figure 3 step 1(c)(iii)). -/
noncomputable def cost {n m L : ℕ} [DecidableEq A] (S : Fin n → Fin m → A) (c : Fin L → A) : ℕ :=
  Finset.univ.sup (fun i => minDistSub c (S i))

/-- `d_opt`: the minimum of `cost S c` over all centers `c` of length `L` (p. 9). -/
noncomputable def dOpt {n m : ℕ} (L : ℕ) [Fintype A] [DecidableEq A] [Nonempty A]
    (S : Fin n → Fin m → A) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun c : Fin L → A => cost S c)

/-- Section 2's `Q_{i1,…,ik}` (p. 3) for an index tuple `idx : Fin k → Fin n` (repetitions
allowed): the positions where the strings `u (idx 0), …, u (idx (k-1))` all agree. -/
def agreeSet {n m k : ℕ} [DecidableEq A] (u : Fin n → Fin m → A) (idx : Fin k → Fin n) :
    Finset (Fin m) :=
  Finset.univ.filter (fun j => ∀ a b, u (idx a) j = u (idx b) j)

/-- Section 2's `p_{i1,…,ik}` (p. 3): the number of positions of `Q_{i1,…,ik}` where the first
string `u (idx 0)` differs from the center `c`. Written with "some `u (idx a)` differs from `c`",
which on `Q_{i1,…,ik}` (all `u (idx a)` equal there) is the same condition for every `k ≥ 1`; for
`k = 0` it gives `0`. -/
def mismatchOnAgree {n m k : ℕ} [DecidableEq A] (u : Fin n → Fin m → A) (c : Fin m → A)
    (idx : Fin k → Fin n) : ℕ :=
  ((agreeSet u idx).filter (fun j => ∃ a, u (idx a) j ≠ c j)).card

/-- `ρ_k · d` (p. 3): the minimum of `p_{i1,…,ik}` over all index tuples `idx : Fin k → Fin n`
(repetitions allowed). Junk value `0` when there is no tuple (`n = 0`, `k ≥ 1`). -/
noncomputable def minMismatch {n m : ℕ} [DecidableEq A] (u : Fin n → Fin m → A)
    (c : Fin m → A) (k : ℕ) : ℕ :=
  if h : (Finset.univ : Finset (Fin k → Fin n)).Nonempty then
    Finset.univ.inf' h (fun idx => mismatchOnAgree u c idx)
  else 0

/-- The string equal to `x` on the position set `P` and to `f` off `P`: the paper's `s′` with
`s′|P = x`, `s′|Q = t_{i1}|Q` (Figure 3 step 1(c)(iii)) and `s∗` with `s∗|P = s|P`, `s∗|Q = t_{i1}|Q`
(p. 10), where `Q` is the complement of `P`. -/
def splice {L : ℕ} (P : Finset (Fin L)) (x f : Fin L → A) : Fin L → A :=
  fun j => if j ∈ P then x j else f j

/-- `max_{i,j} d(u_i, u_j)` (`ρ₀ · d_opt`, p. 3). -/
def maxPairDist {n m : ℕ} [DecidableEq A] (u : Fin n → Fin m → A) : ℕ :=
  Finset.univ.sup (fun p : Fin n × Fin n => hammingDist (u p.1) (u p.2))

end ClosestString.PTAS



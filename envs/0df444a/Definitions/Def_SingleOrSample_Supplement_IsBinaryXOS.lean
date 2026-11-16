-- Prove2me | Definitions.Def_SingleOrSample_Supplement_IsBinaryXOS
-- name    : SingleOrSample_Supplement_IsBinaryXOS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:31:10.634539+00:00
-- url     : https://prove2.me/theorems/d920c5df-d1f0-46b4-9842-c88bcdcbd23e
-- title:
--   Binary additive, binary XOS and simple binary XOS valuations
-- statement:
--   Let the goods be $[m]$. A valuation $v$ is **binary additive** if every good is worth $0$ or $1$ and values add up, i.e. $v(S)=|S\cap T|$ for the set $T$ of goods worth $1$.
--
--   A valuation is **binary XOS** if it is the maximum of finitely many additive clauses whose item values are all $0$ or $1$: there is a nonempty finite family $\mathcal F$ of sets (clauses) with
--   $$
--   v(S)=\max_{C\in\mathcal F}|S\cap C|\qquad\text{for all }S\subseteq[m].
--   $$
--
--   For $n$ agents, a valuation is **simple binary XOS** if it has this form with $n$ pairwise disjoint clauses (bins) $C_1,\dots,C_n$ of the same positive size $s$, which need not cover all goods: $v(S)=\max_{j\le n}|S\cap C_j|$. Its maximin share for $n$ bundles is $s$, and placing one bin in each bundle is an MMS partition.
--
--   These classes are the instances of the paper's lower bounds: binary additive for Theorem 2.1, binary XOS for Theorem 2.2, and simple binary XOS (every valuation of the random-pool construction) for Theorem 6.1.
--
--   **Formalization Note** The maximum over a family is a `Finset.sup` of natural numbers, cast to $\mathbb R$. The paper calls an XOS instance simple when each valuation is binary, has $O(n)$ clauses, and its MMS value and MMS partition can be computed in $O(m+n)$ time; the predicate here is the structural form shared by all valuations of the lower-bound construction (App. C.2), and the running-time clause is not encoded.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §2.1, p.6 (XOS); Theorem 2.1, p.7 (binary additive); §6, p.19 (binary XOS); Table 1 note (∗), p.2 and App. C.2, p.35 (simple)

import Mathlib

namespace SingleOrSample.Supplement

/-- The value `max_{C ∈ F} |S ∩ C|` of a bundle `S` under a finite family `F` of 0/1 clauses (Chawla,
Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents,
STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, §2.1, p.6 and §6, p.19). The
maximum over the empty family is `0`; `IsBinaryXOS` asks for a nonempty family. -/
def binaryXOSValue {m : ℕ} (F : Finset (Finset (Fin m))) (S : Finset (Fin m)) : ℝ :=
  ((F.sup fun C => (S ∩ C).card : ℕ) : ℝ)

/-- A **binary additive** valuation (Theorem 2.1, p.7): additive with every item worth `0` or `1`, that
is `v(S) = |S ∩ T|` for the set `T` of items worth `1`. -/
def IsBinaryAdditive {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ T : Finset (Fin m), ∀ S, v S = ((S ∩ T).card : ℝ)

/-- A **binary XOS** valuation (p.6 and §6, p.19: "maxima of additive clauses whose item values are all
zero or one"): `v(S) = max_{C ∈ F} |S ∩ C|` for a nonempty finite family `F` of clauses, a clause being
the set of items it values at `1`.

**Formalization Note.** The page's `l ∈ ℤ₊` clauses is the nonemptiness of `F`; repeated clauses do
not change the maximum, so `F` is a set. -/
def IsBinaryXOS {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ F : Finset (Finset (Fin m)), F.Nonempty ∧ ∀ S, v S = binaryXOSValue F S

/-- A **simple binary XOS** valuation for `n` agents (Theorem 6.1, p.19; Table 1 note (∗), p.2;
App. C.2, p.35): `v(S) = max_{j < n} |S ∩ C_j|` for `n` pairwise disjoint **bins** `C_0, …, C_{n−1}` of
the same positive size `s`, which need not cover all goods.

**Formalization Note.** Table 1 calls an XOS instance simple when each valuation is binary, has `O(n)`
clauses, and its MMS value and partition can be computed in `O(m + n)` time. This predicate is the
structural form of every valuation of the paper's lower-bound construction (App. C.2: "defined by `n`
pairwise disjoint, equal-sized sets of items"): `n` clauses, MMS value `s`, and an MMS partition with one
bin in each bundle. The running-time clause is not a mathematical property and is not encoded. -/
def IsSimpleBinaryXOS {m : ℕ} (n : ℕ) (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ (C : Fin n → Finset (Fin m)) (s : ℕ), 0 < s ∧ (∀ j, (C j).card = s) ∧
    Pairwise (fun j j' => Disjoint (C j) (C j')) ∧
    ∀ S, v S = ((Finset.univ.sup fun j => (S ∩ C j).card : ℕ) : ℝ)

end SingleOrSample.Supplement



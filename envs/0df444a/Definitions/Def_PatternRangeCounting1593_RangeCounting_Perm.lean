-- Prove2me | Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
-- name    : PatternRangeCounting1593_RangeCounting_Perm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:01.441488+00:00
-- url     : https://prove2.me/theorems/69f7e63c-41bc-430d-93da-5a5ea4495181
-- title:
--   Permutation plots, dominance and rectangle counts, pattern avoidance, Stanley–Wilf and Füredi–Hajnal limits
-- statement:
--   A permutation $\tau$ of $[n]=\{1,\dots,n\}$ is a bijection of $[n]$ (in Lean an `Equiv.Perm (Fin n)`, position $i$ and value $\tau(i)$ shifted to one-based coordinates). Its **plot** is
--   $$P_\tau=\{(i,\tau(i)) : i\in[n]\}\subseteq[n]\times[n],$$
--   the first coordinate being the column (position) and the second the row (value). For integers $x,y\ge 0$, with $[0]=\emptyset$,
--   $$\mathrm{Count}_\tau(x,y)=|P_\tau\cap([x]\times[y])|,$$
--   and for inclusive integer intervals the **rectangle count** is $|P_\tau\cap([x_1,x_2]\times[y_1,y_2])|$, which is $0$ when an interval is empty.
--
--   A permutation $\tau$ **contains** a pattern $\pi$ of length $k$ if there are positions $i_1<\dots<i_k$ whose values $\tau(i_1),\dots,\tau(i_k)$ are in the same relative order as $\pi(1),\dots,\pi(k)$; otherwise $\tau$ **avoids** $\pi$. $\mathrm{Av}_n(\pi)$ is the set of $\pi$-avoiding permutations of length $n$. The empty pattern ($k=0$) is contained in every permutation, so it has no avoiders.
--
--   The **Stanley–Wilf limit** is $s_\pi=\lim_{n\to\infty}|\mathrm{Av}_n(\pi)|^{1/n}$. For a 0-1 matrix $M\subseteq[n]\times[n]$, $M$ contains the permutation matrix of $\pi$ if there are increasing maps $r,c:[k]\to[n]$ with $(r(a),c(\pi(a)))\in M$ for all $a$; $\mathrm{ex}(n,\pi)$ is the largest number of ones in an $n\times n$ 0-1 matrix that does not contain it, and the **Füredi–Hajnal limit** is $c_\pi=\lim_{n\to\infty}\mathrm{ex}(n,\pi)/n$. The occupancy bound of the Kozma–Opler hierarchy is $\Delta=\lceil 10c_\pi\rceil$.
--
--   These are the objects of Theorem 1.1 and of the Kozma–Opler interface (Theorem 3.4).
--
--   **Formalization Note** Both limits are `limUnder` values; that they exist for $|\pi|\ge 3$ is stated separately (supporting theorems `stanleyWilf_limit_exists` and `furediHajnal_limit_exists`), so no statement relies on the junk value of a nonexistent limit.
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §1.1, printed p. 1 (PDF p. 2); §3.3, printed p. 11 (PDF p. 12)

import Mathlib

set_option autoImplicit false

namespace PatternRangeCounting1593.RangeCounting

open Filter

/-!
# Permutations, plots, counts, pattern avoidance and the two growth constants

Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §1.1, printed p. 1 (PDF p. 2)
and §3.3, printed p. 10 (PDF p. 11).

A permutation `τ` of `[n] = {1,…,n}` is an `Equiv.Perm (Fin n)`; position `i : Fin n` is the
one-based coordinate `i + 1` and its value is `τ i + 1`.
-/

/-- The plot `P_τ = {(i, τ(i)) : i ∈ [n]}` with one-based coordinates (first coordinate = column
= position, second coordinate = row = value). -/
def plot {n : ℕ} (τ : Equiv.Perm (Fin n)) : Finset (ℕ × ℕ) :=
  Finset.univ.image (fun i : Fin n => ((i : ℕ) + 1, (τ i : ℕ) + 1))

/-- `Count_τ(x, y) = |P_τ ∩ ([x] × [y])|`, with `[0] = ∅`. -/
def Count {n : ℕ} (τ : Equiv.Perm (Fin n)) (x y : ℕ) : ℕ :=
  ((plot τ).filter (fun p => p.1 ≤ x ∧ p.2 ≤ y)).card

/-- The exact rectangle count `|P_τ ∩ ([x₁, x₂] × [y₁, y₂])|` for inclusive integer intervals
(empty when `x₁ > x₂` or `y₁ > y₂`). -/
def rectCount {n : ℕ} (τ : Equiv.Perm (Fin n)) (x₁ x₂ y₁ y₂ : ℕ) : ℕ :=
  ((plot τ).filter (fun p => x₁ ≤ p.1 ∧ p.1 ≤ x₂ ∧ y₁ ≤ p.2 ∧ p.2 ≤ y₂)).card

/-- `τ` contains the pattern `π` (of length `k`): some increasing choice of `k` positions carries
values in exactly the relative order of `π`. The empty pattern (`k = 0`) is contained in every
permutation. -/
def Contains {k n : ℕ} (π : Equiv.Perm (Fin k)) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∃ f : Fin k ↪o Fin n, ∀ a b : Fin k, π a < π b ↔ τ (f a) < τ (f b)

/-- `τ` avoids `π`. -/
def Avoids {k n : ℕ} (π : Equiv.Perm (Fin k)) (τ : Equiv.Perm (Fin n)) : Prop :=
  ¬ Contains π τ

open Classical in
/-- `Av_n(π)`, the set of `π`-avoiding permutations of length `n`. -/
noncomputable def Av (n : ℕ) {k : ℕ} (π : Equiv.Perm (Fin k)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun τ => Avoids π τ)

/-- The Stanley–Wilf limit `s_π = lim_{n→∞} |Av_n(π)|^{1/n}` (value of `limUnder`; its existence
for `|π| ≥ 3` is the supporting theorem `stanleyWilf_limit_exists`). -/
noncomputable def swLimit {k : ℕ} (π : Equiv.Perm (Fin k)) : ℝ :=
  limUnder atTop (fun n : ℕ => ((Av n π).card : ℝ) ^ ((1 : ℝ) / n))

/-- A 0-1 matrix `M ⊆ [n] × [n]` contains the permutation matrix of `π`: there are increasing row
and column embeddings putting a one at `(r a, c (π a))` for every `a`. -/
def ContainsMat {k n : ℕ} (π : Equiv.Perm (Fin k)) (M : Finset (Fin n × Fin n)) : Prop :=
  ∃ r c : Fin k ↪o Fin n, ∀ a : Fin k, (r a, c (π a)) ∈ M

open Classical in
/-- The Füredi–Hajnal extremal function `ex(n, π)`: the largest number of ones in an `n × n` 0-1
matrix not containing the permutation matrix of `π`. -/
noncomputable def exFH (n : ℕ) {k : ℕ} (π : Equiv.Perm (Fin k)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n × Fin n))).filter (fun M => ¬ ContainsMat π M)).sup
    Finset.card

/-- The Füredi–Hajnal limit `c_π = lim_{n→∞} ex(n, π)/n` (value of `limUnder`; its existence for
`|π| ≥ 3` is the supporting theorem `furediHajnal_limit_exists`). -/
noncomputable def fhLimit {k : ℕ} (π : Equiv.Perm (Fin k)) : ℝ :=
  limUnder atTop (fun n : ℕ => (exFH n π : ℝ) / n)

/-- `Δ = ⌈10 c_π⌉`, the occupancy bound of the Kozma–Opler hierarchy (§3.3). -/
noncomputable def Delta {k : ℕ} (π : Equiv.Perm (Fin k)) : ℕ :=
  ⌈10 * fhLimit π⌉₊

end PatternRangeCounting1593.RangeCounting



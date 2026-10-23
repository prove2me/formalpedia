-- Prove2me | Definitions.Def_Erdos195_defs
-- name    : Erdos195_defs
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-22T13:30:03.370242+00:00
-- url     : https://prove2.me/theorems/97cc6ae8-0f5f-4dd5-933f-a7800c7a1744
-- title:
--   Erdős #195: monotone APs, $\varepsilon$-orders on $\mathbb{Z}$, completions and safe words
-- statement:
--   Definitions for Erdős Problem 195.
--
--   1. **Monotone arithmetic progressions.** A list $s$ is an arithmetic progression of length $l$ if $s=(a,a+d,\dots,a+(l-1)d)$ or the reverse of this list, for some $a,d$. A function $f$ from a preorder has a monotone $k$-AP if there are indices $b_1<\dots<b_k$ such that $(f(b_1),\dots,f(b_k))$ is an arithmetic progression of length $k$. These are verbatim copies of `List.IsAPOfLengthWith`, `List.IsAPOfLength` and `HasMonotoneAP` from formal-conjectures.
--   2. **$\varepsilon$-orders.** For $\varepsilon:\mathbb{N}\to\{\mathrm{true},\mathrm{false}\}$ and integers $x\neq y$, let $k=\nu_2(y-x)$, the lowest position where the two's-complement binary expansions of $x$ and $y$ differ. Then $x\prec_\varepsilon y$ iff the $k$-th digit of $x$ equals $1$ exactly when $\varepsilon(k)$ is true.
--   3. **Completion and safety.** For a relation $R$ on $\mathbb{Z}$ and a finite list $P$, the completion order $C_R(P)$ puts the elements of $P$ first, in list order, and then all other integers ordered by $R$. $P$ is **safe** if there are no $a$ and $r\neq0$ with $a,\ a+r,\ a+2r,\ a+3r$ appearing in this order in $C_R(P)$.
--   4. **Order axioms.** No3AP$(R)$: there are no $a$ and $r\ne0$ with $a\mathrel{R}a+r$ and $a+r\mathrel{R}a+2r$. Star$(R)$: $a\mathrel{R}a+r\iff a+2r\mathrel{R}a+3r$ for all $a$ and all $r\ne0$.
--
--   These objects state Erdős Problem 195 and the structural lemmas behind Ho's method for permutations with no monotone 4-term progression.
-- source:
--   formal-conjectures FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean (HasMonotoneAP, List.IsAPOfLength[With]); B. S. Ho, arXiv:2609.12780, §2 (the order ◁, completion C(P), safe words)

import Mathlib

/-!
# Erdős Problem 195 — definitions

* `Erdos195.ListIsAPOfLengthWith`, `Erdos195.ListIsAPOfLength`, `Erdos195.HasMonotoneAP`:
  verbatim copies of `List.IsAPOfLengthWith`, `List.IsAPOfLength`, `HasMonotoneAP` from
  google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`).
* `Erdos195.bitOne`, `Erdos195.epsLt`: the ε-orders on ℤ (2-adic lexicographic orders).
* `Erdos195.compLt`, `Erdos195.Safe`: completion of a finite word and Ho's notion of safety.
* `Erdos195.No3AP`, `Erdos195.Star`: the two order axioms used in Ho's argument.
-/

namespace Erdos195

/-- List version of an arithmetic progression of length `l` with first term `a` and difference
`d`, listed either forwards or backwards (formal-conjectures `List.IsAPOfLengthWith`). -/
def ListIsAPOfLengthWith {α : Type*} [AddCommMonoid α] (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

/-- `s` is an arithmetic progression of length `l` (formal-conjectures `List.IsAPOfLength`). -/
def ListIsAPOfLength {α : Type*} [AddCommMonoid α] (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, ListIsAPOfLengthWith s l a d

/-- `f` has a monotone `k`-term AP: indices `b₁ < ⋯ < b_k` with `f b₁, …, f b_k` an increasing or
decreasing AP (formal-conjectures `HasMonotoneAP`). -/
def HasMonotoneAP {α β : Type*} [AddCommMonoid α] [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

/-- The `k`-th two's-complement binary digit of `x` equals `1`. -/
def bitOne (x : ℤ) (k : ℕ) : Prop := x / 2 ^ k % 2 = 1

/-- The ε-order on ℤ: `x ≺_ε y` iff `x ≠ y` and, at the lowest binary position `k = ν₂(y - x)`
where `x` and `y` differ, the digit of `x` is `1` exactly when `ε k = true`. -/
def epsLt (ε : ℕ → Bool) (x y : ℤ) : Prop :=
  x ≠ y ∧ (bitOne x (padicValInt 2 (y - x)) ↔ ε (padicValInt 2 (y - x)) = true)

/-- The order of the completion `C(P)` of a finite word `P`: elements of `P` first, in list
order, then every other integer, ordered by `R`. -/
def compLt (R : ℤ → ℤ → Prop) (P : List ℤ) (x y : ℤ) : Prop :=
  (x ∈ P ∧ y ∈ P ∧ P.idxOf x < P.idxOf y) ∨ (x ∈ P ∧ y ∉ P) ∨ (x ∉ P ∧ y ∉ P ∧ R x y)

/-- `P` is safe for `R`: the completion order contains no monotone 4-term AP. -/
def Safe (R : ℤ → ℤ → Prop) (P : List ℤ) : Prop :=
  ∀ a r : ℤ, r ≠ 0 →
    ¬ (compLt R P a (a + r) ∧ compLt R P (a + r) (a + 2 * r) ∧ compLt R P (a + 2 * r) (a + 3 * r))

/-- `R` has no monotone 3-term AP. -/
def No3AP (R : ℤ → ℤ → Prop) : Prop :=
  ∀ a r : ℤ, r ≠ 0 → ¬ (R a (a + r) ∧ R (a + r) (a + 2 * r))

/-- Ho's identity (*): `a ≺ a + r ↔ a + 2r ≺ a + 3r`. -/
def Star (R : ℤ → ℤ → Prop) : Prop :=
  ∀ a r : ℤ, r ≠ 0 → (R a (a + r) ↔ R (a + 2 * r) (a + 3 * r))

end Erdos195



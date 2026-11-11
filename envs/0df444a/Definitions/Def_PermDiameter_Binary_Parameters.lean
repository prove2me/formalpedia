-- Prove2me | Definitions.Def_PermDiameter_Binary_Parameters
-- name    : PermDiameter_Binary_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:10:29.68164+00:00
-- url     : https://prove2.me/theorems/62c672e8-0caa-4df7-8108-09b657d05975
-- title:
--   The numbers $q, m, d_c$ of (3.1), inequality (3.2), and the special positions of Lemma 3.4
-- statement:
--   Let $p_1=3,p_2=5,\dots$ be the odd primes in increasing order. For $n\ge1$, (3.1) defines
--   $$q=\prod_{j=1}^{n}p_j^2,\qquad m=\frac{q+3}{4},\qquad d_c=\sum_{j=1}^{n}p_j^4,$$
--   and, for an instance of degree $d_0$ and threshold $k_0$, inequality (3.2) reads $m\ge k_0+10(d_0+d_c)^4+3$.
--
--   For positions $s_1,\dots,s_d$ in the cyclic group $C_r$ and two indices $i,j$, the **special positions** are $S=\{1,s_1,\dots,s_d,x_*\}$ with $x_*=s_i^{-1}s_j$. Lemma 3.4 asks for (i) $|S|=d+2$ and (ii) $S\cap S^{-1}=\{1\}$ and $|S\cap St|\le3$ for every $t\ne1$, where $S^{-1}=\{x^{-1}:x\in S\}$ and $St=\{xt:x\in S\}$.
--
--   These are the numerical parameters of the reduction: $q$ is the order of the clock group, $m$ the output threshold, $d_c$ the degree of the cyclic factors; the special positions control the overlaps of translates in Step 2.
--
--   **Formalization Note.** `oddPrime j` is the $(j+1)$-st odd prime (`Nat.nth` of the odd primes from `0`), so the paper's $p_j$ is `oddPrime (j-1)`. `mOf n = (qOf n + 3) / 4` uses natural-number division, exact because $q$ is an odd square. `SpecialPositionsProp s i j` takes positions indexed by any finite type (the paper's $[1,d]$, or the points of $\Omega_1$), with $d$ its cardinality.
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 11 (Lemma 2.6, odd primes), p. 13 ((3.1), (3.2)), p. 14 (Lemma 3.4)

import Mathlib
import Definitions.Def_PermDiameter_Binary_Wreath

namespace PermDiameter.Binary

/-!
# The numbers of (3.1)–(3.2) and the special positions of Lemma 3.4 (Lohrey–Thumm, pp. 11–15)
-/

/-- The odd primes in increasing order, indexed from `0`: `oddPrime 0 = 3`, `oddPrime 1 = 5`, …
(the paper's `p₁, p₂, …` of Lemma 2.6 are `oddPrime 0, oddPrime 1, …`). -/
noncomputable def oddPrime (j : ℕ) : ℕ := Nat.nth (fun p => Nat.Prime p ∧ p ≠ 2) j

/-- `q = ∏_{j=1}^{n} p_j²` (3.1). -/
noncomputable def qOf (n : ℕ) : ℕ := ∏ j ∈ Finset.range n, oddPrime j ^ 2

/-- `d_c = ∑_{j=1}^{n} p_j⁴` (3.1). -/
noncomputable def dcOf (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, oddPrime j ^ 4

/-- `m = (q + 3)/4` (3.1); the division is exact because `q` is an odd square, `q ≡ 1 (mod 4)`. -/
noncomputable def mOf (n : ℕ) : ℕ := (qOf n + 3) / 4

/-- Inequality (3.2) for the instance data `d₀` (degree) and `k₀` (threshold):
`m ≥ k₀ + 10 (d₀ + d_c)⁴ + 3`. -/
def Cond32 (d0 k0 n : ℕ) : Prop := k0 + 10 * (d0 + dcOf n) ^ 4 + 3 ≤ mOf n

/-- The set of special positions `S = {1, s_ι : ι} ∪ {x∗}` with `x∗ = s_i⁻¹ s_j` (Lemma 3.4),
for positions `s : ι → C_r` indexed by a finite type `ι` (the paper's `[1, d]`). -/
def specialSet {ι : Type} [Fintype ι] {r : ℕ} (s : ι → Pos r) (i j : ι) : Finset (Pos r) :=
  insert 1 (insert ((s i)⁻¹ * s j) (Finset.univ.image s))

/-- Properties (i) and (ii) of Lemma 3.4 for the pair `(i, j)`:
(i) `|S| = d + 2` (`d = |ι|`); (ii) `S ∩ S⁻¹ = {1}` and `|S ∩ S t| ≤ 3` for all `t ≠ 1`. -/
def SpecialPositionsProp {ι : Type} [Fintype ι] {r : ℕ} (s : ι → Pos r) (i j : ι) : Prop :=
  (specialSet s i j).card = Fintype.card ι + 2 ∧
    specialSet s i j ∩ (specialSet s i j).image (fun x => x⁻¹) = {1} ∧
    ∀ t : Pos r, t ≠ 1 → (specialSet s i j ∩ (specialSet s i j).image (fun x => x * t)).card ≤ 3

end PermDiameter.Binary



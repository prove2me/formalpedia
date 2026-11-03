-- Prove2me | Definitions.Def_MultiPurchase_Hardness_Checker
-- name    : MultiPurchase_Hardness_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-11-03T03:51:55.152658+00:00
-- url     : https://prove2.me/theorems/3c2541ca-fadc-417c-a13f-ca8e5aa2b328
-- title:
--   NP checker for BundleMVL-2: integer-list codes, certificates, and the shape / canonicity / revenue conditions
-- statement:
--   Auxiliary objects for the NP-membership half of Theorem 1 (the BundleMVL-2 decision language `bundleLang` is in NP in Cook's sense).
--
--   **Integer-list form of a code.** The code `code I κ` of an instance with $n$ products is the binary code `encInts c` of the integer list
--   $$c = (n,\ \mathrm{num}(q_0), \mathrm{den}(q_0),\ \mathrm{num}(q_1), \mathrm{den}(q_1), \dots),$$
--   where $q_0, q_1, \dots$ are the rationals of the instance in the order $r_0,\dots,r_{n-1}$, $V_{\{0\}},\dots,V_{\{n-1\}}$, the pair weights $V_{\{i,j\}}$ ($i<j$, row by row), $v_0$ and $\kappa$. There are $\mathrm{numRats}(n) = 2n + n(n-1)/2 + 2$ of them, and the pair $\{i,j\}$ ($i<j$) sits at position
--   $$\mathrm{pairIdx}(n,i,j) = i\,n - \tfrac{i(i+1)}{2} + (j-i-1)$$
--   of the pair block. `chkNum c t`, `chkDen c t` and `chkRat c t` $=$ `chkNum c t / chkDen c t` read the $t$-th rational.
--
--   **Checker input.** A certificate is the indicator vector $d \in \{0,1\}^n$ of a recommendation set $C$; the checker reads the word `chkWord c d` $=$ `encInts c` $\#$ $d$ over the alphabet `Option (BSym ⊕ Bool)` (`none` is the separator $\#$).
--
--   **Conditions.**
--   - `ShapeOK c d`: $n = c_0 \ge 0$, $c$ has exactly $2\,\mathrm{numRats}(n)+1$ entries, $|d| = n$, every revenue numerator is positive, every weight numerator ($V_{\{i\}}$, $V_{\{i,j\}}$) is nonnegative and the numerator of $v_0$ is positive.
--   - `CanonOK c`: every denominator entry is positive and coprime to its numerator (so each pair is the normalized form of its rational).
--   - `RevOK c d`: with $x_i = d_i$,
--   $$\kappa\Big(v_0 + \sum_{i} x_i V_{\{i\}} + \sum_{i<j} x_i x_j V_{\{i,j\}}\Big) \le \sum_i x_i r_i V_{\{i\}} + \sum_{i<j} x_i x_j (r_i + r_j) V_{\{i,j\}},$$
--   which (for a well-formed instance, whose denominator is positive) is exactly $R_2(C) \ge \kappa$ of eq. (4).
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17, Theorem 1 (membership half), eq. (4); class NP and checking relations as in S. Cook, The P versus NP problem (Clay Mathematics Institute), §1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

/-! # The NP checker for the BundleMVL-2 decision language

The code `code I κ` of a BundleMVL-2 instance is the binary code `encInts c` of the integer list
`c = n, num(q₀), den(q₀), num(q₁), den(q₁), …` where `q₀, q₁, …` are the instance's rationals in
the order `r₀,…,r_{n-1}, V{0},…,V{n-1}, V{i,j} (i<j, row by row), v0, κ`. A certificate is the
indicator vector `d` of a recommendation set `C`. The checker reads the word
`encInts c # d` (over `Option (BSym ⊕ Bool)`, `none` being `#`). -/

/-- The checker input `encInts c # d`. -/
def chkWord (c : List ℤ) (d : List Bool) : List (Option (BSym ⊕ Bool)) :=
  (encInts c).map (some ∘ Sum.inl) ++ none :: d.map (some ∘ Sum.inr)

/-- The number of rationals in the code of an instance with `n` products:
`n` revenues, `n` singleton weights, `n(n-1)/2` pair weights, `v0` and `κ`. -/
def numRats (n : ℕ) : ℕ := 2 * n + n * (n - 1) / 2 + 2

/-- The position of the pair `{i, j}` (`i < j`) in the row-by-row list of pairs:
`Σ_{i' < i} (n - 1 - i') + (j - i - 1)`. -/
def pairIdx (n i j : ℕ) : ℕ := i * n - i * (i + 1) / 2 + (j - i - 1)

/-- The numerator entry of the `t`-th rational of the integer list `c`. -/
def chkNum (c : List ℤ) (t : ℕ) : ℤ := c.getD (2 * t + 1) 0

/-- The denominator entry of the `t`-th rational of the integer list `c`. -/
def chkDen (c : List ℤ) (t : ℕ) : ℤ := c.getD (2 * t + 2) 0

/-- The `t`-th rational `num / den` of the integer list `c`. -/
def chkRat (c : List ℤ) (t : ℕ) : ℚ := (chkNum c t : ℚ) / (chkDen c t : ℚ)

/-- Shape and sign conditions: `n = c₀ ≥ 0`, `c` holds exactly `numRats n` rationals, the
certificate has `n` bits, the revenue numerators are positive, the weight numerators are
nonnegative and the numerator of `v0` is positive. -/
def ShapeOK (c : List ℤ) (d : List Bool) : Prop :=
  0 ≤ c.getD 0 0 ∧
    c.length = 2 * numRats (c.getD 0 0).toNat + 1 ∧
    d.length = (c.getD 0 0).toNat ∧
    (∀ i, i < (c.getD 0 0).toNat → 0 < chkNum c i) ∧
    (∀ t, (c.getD 0 0).toNat ≤ t → t < numRats (c.getD 0 0).toNat - 2 → 0 ≤ chkNum c t) ∧
    0 < chkNum c (numRats (c.getD 0 0).toNat - 2)

/-- Canonical rationals: every denominator entry is positive and coprime to its numerator. -/
def CanonOK (c : List ℤ) : Prop :=
  ∀ t, t < numRats (c.getD 0 0).toNat →
    0 < chkDen c t ∧ Int.gcd (chkNum c t) (chkDen c t) = 1

/-- The revenue condition `κ · (v0 + Σ V{i} + Σ V{i,j}) ≤ Σ rᵢ V{i} + Σ (rᵢ + rⱼ) V{i,j}`, the sums
running over the products `i` (and pairs `i < j`) selected by the certificate `d`. -/
def RevOK (c : List ℤ) (d : List Bool) : Prop :=
  chkRat c (numRats (c.getD 0 0).toNat - 1) *
      (chkRat c (numRats (c.getD 0 0).toNat - 2) +
        ∑ i ∈ Finset.range (c.getD 0 0).toNat,
          (if d.getD i false then chkRat c ((c.getD 0 0).toNat + i) else 0) +
        ∑ i ∈ Finset.range (c.getD 0 0).toNat, ∑ j ∈ Finset.range (c.getD 0 0).toNat,
          (if i < j ∧ d.getD i false = true ∧ d.getD j false = true then
            chkRat c (2 * (c.getD 0 0).toNat + pairIdx (c.getD 0 0).toNat i j) else 0)) ≤
    ∑ i ∈ Finset.range (c.getD 0 0).toNat,
        (if d.getD i false then chkRat c i * chkRat c ((c.getD 0 0).toNat + i) else 0) +
      ∑ i ∈ Finset.range (c.getD 0 0).toNat, ∑ j ∈ Finset.range (c.getD 0 0).toNat,
        (if i < j ∧ d.getD i false = true ∧ d.getD j false = true then
          (chkRat c i + chkRat c j) *
            chkRat c (2 * (c.getD 0 0).toNat + pairIdx (c.getD 0 0).toNat i j) else 0)

end MultiPurchase.Hardness



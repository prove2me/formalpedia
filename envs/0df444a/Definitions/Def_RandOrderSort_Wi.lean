-- Prove2me | Definitions.Def_RandOrderSort_Wi
-- name    : RandOrderSort_Wi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:40.627918+00:00
-- url     : https://prove2.me/theorems/4fb49327-7ecf-4210-bff4-0a9cfa11163c
-- title:
--   The fixed-tree witnesses $\mathrm{Bad}_\nu$, $D_{\mathrm{err}}$, $N_i(I)$ and $W_i$
-- statement:
--   The fixed tree is (7) on the first $m$ keys with $b=b_1$ leaves. For $\nu=2^e$, let $J_{q,\nu}$ be its node containing $q$ and consisting of $\nu$ initial buckets. With $p=\nu/(2b)$, the event $\mathrm{Bad}_\nu$ holds if $\nu<64$, or if a child $I$ of $J_{q,\nu}$ has $|I|\notin[15p/16,17p/16]$, and
--   $$D_{\mathrm{err}}=4\kappa\sum_{\nu\in\{2,4,\dots,b\}}\nu\mathbf 1[\mathrm{Bad}_\nu].$$
--   $N_i(I)$ counts the inputs of the phase-$i$ block falling in $I$, and for $1\le i<k$,
--   $$W_i=2\kappa\sum_{\substack{2s\le b_i,\ s\in\{1,2,4,\dots\}\\ J_{q,2^is}\ \mathrm{good}}}s\mathbf 1[\exists\text{ child }I:N_i(I)>Bs]+\mathbf 1[i+1<k]\,2\kappa\sum_{\substack{2s\le b_{i+1},\ s\in\{1,2,4,\dots\}\\ J_{q,2^{i+1}s}\ \mathrm{good}}}s\mathbf 1[\exists\text{ child }I:N_i(I)<1.1Bs].$$
--   The module also defines the constants $A_p=2+2(8195)^2$, $M_b$ of (52) and $M_s=1+2e^{-1/3}/(1-e^{-1/6})$, and the charges $\Gamma_q(v)$ of top-marked selected bad parents in an operation of a shrinking phase (`badCharges`).
--
--   **Formalization Note** $|I|$ is the length of $I\cap[0,1]$ (`clipLen`, p.23). A scale is $s=2^h$; $J_{q,2^is}$ is the fixed-tree node of height $i+h$ containing $q$, and its children have height $i+h-1$. A phase-$i$ node of height $h$ consists of $2^{h+i-1}$ initial buckets.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §4.4, pp.32–35, displays (44), (46), (50), (52)

import Mathlib
import Definitions.Def_RandOrderSort_Dop
import Definitions.Def_RandOrderSort_iidUnif

namespace RandOrderSort

/-! # Fixed-tree witnesses: `Bad_ν`, `D_err`, `N_i(I)`, `W_i` (§4.4, pp.32–35, (44), (46), (50))

Kang, Fan, arXiv:2610.15438 (version of 2026-11-01), §4.4.1, p.32: "For each scale ν ∈ {2, 4, . . . ,
b}, let J_{q,ν} be the selected parent containing q and consisting of ν initial buckets. Each of
its two children contains ν/2 initial buckets. … p = ν/(2b), r = mp = mν/(2b), m = |P_L|. For ν ≥
64, define the same length-error event as in that lemma: Bad_ν = {∃ child I of J_{q,ν} : |I| ∉
[15p/16, 17p/16]}. (44)" p.33: "For scales ν < 64, we declare Bad_ν to hold unconditionally …
D_err = 4κ ∑_{ν∈{2,4,...,b}} ν 1[Bad_ν]. (46)" "Recall from Lemma 4.4 that N_i(I) counts arrivals
canonical in I during shrinking phase i. Writing X_t for arrival t, this is the number of phase-i
inputs X_t that fall in I". p.34: "A selected parent with 2s current buckets in phase i contains
2^i s initial buckets, so it is J_{q,2^i s} in the fixed tree. We call this parent good when
Bad_{2^i s} does not occur." p.35, (50): `W_i = 2κ ∑_{2s ≤ b_i, J_{q,2^i s} good} s 1[∃ child I :
N_i(I) > Bs] + 1[i + 1 < k] 2κ ∑_{2s ≤ b_{i+1}, J_{q,2^{i+1} s} good} s 1[∃ child I :
N_i(I) < 1.1Bs]`.

**Formalization Note.**
* The fixed tree is (7) on the first `m` keys with `b = b_1` leaves (Algorithm 1, line 12). Its
  node of height `e` consists of `ν = 2^e` initial buckets; `J_{q,ν}` is the one containing `q`.
  `Bad`, `Derr` read only the prefix `y` (the first `m` inputs); `|I|` is `clipLen` (p.23).
* `N_i(I)` (`Nblk`) counts the inputs of the phase-`i` block, arrivals
  `m + Q_{i−1}, …, m + Q_i − 1`, whose canonical leaf in the fixed tree lies below the node `I`,
  i.e. which fall in `I` (left-closed, right-open; value ties broken by arrival index).
* A scale is `s = 2^h`; `J_{q,2^i s}` is the fixed-tree node of height `i + h`, its children have
  height `i + h − 1`.
-/

/-- The values of the first `m` inputs, as a function of the arrival index. -/
def yval {n : ℕ} (y : Fin (m n) → ℝ) (a : ℕ) : ℝ := vecVal y a

/-- The fixed tree: (7) on the first `m` keys with `b_1` leaves. -/
noncomputable def fixedTreeY {n : ℕ} (y : Fin (m n) → ℝ) : Tree :=
  mkTree (ltOf y 1 1) (Finset.range (m n)) (b n 1)

/-- `Bad_ν` at `ν = 2^e` (44): `ν < 64`, or a child of `J_{q,ν}` has `|I| ∉ [15p/16, 17p/16]`,
`p = ν/(2b)`. -/
def Bad {n : ℕ} (y : Fin (m n) → ℝ) (q : ℝ) (e : ℕ) : Prop :=
  2 ^ e < 64 ∨ ∃ c < 2,
    ¬ (15 / 16 * ((2 : ℝ) ^ e / (2 * b n 1)) ≤
          clipLen (yval y) (fixedTreeY y) (e - 1)
            (2 * (cutLeaf (fun a => decide (q < yval y a)) (fixedTreeY y) / 2 ^ e) + c) ∧
        clipLen (yval y) (fixedTreeY y) (e - 1)
            (2 * (cutLeaf (fun a => decide (q < yval y a)) (fixedTreeY y) / 2 ^ e) + c) ≤
          17 / 16 * ((2 : ℝ) ^ e / (2 * b n 1)))

/-- `D_err = 4κ ∑_{ν ∈ {2,4,…,b}} ν 1[Bad_ν]` (46). -/
noncomputable def Derr {n : ℕ} (y : Fin (m n) → ℝ) (q : ℝ) : ℝ :=
  by classical exact
    4 * kappa * ∑ e ∈ Finset.Icc 1 (Nat.log 2 (b n 1)), (2 : ℝ) ^ e * (if Bad y q e then 1 else 0)

/-- `N_i(I)` for the fixed-tree node `I = (g, idx)`: the inputs of the phase-`i` block falling
in `I`. -/
noncomputable def Nblk {n : ℕ} (X : Fin n → ℝ) (i g idx : ℕ) : ℕ :=
  countIn (iidLt X) (fixedTreeY (prefixOf X))
    (Finset.Ico (m n + Q n (i - 1)) (m n + Q n i)) g idx

/-- The index of `J_{q,2^e}` (the fixed-tree node of height `e` containing `q`). -/
noncomputable def parIdx {n : ℕ} (X : Fin n → ℝ) (q : ℝ) (e : ℕ) : ℕ :=
  cutLeaf (fun a => decide (q < yval (prefixOf X) a)) (fixedTreeY (prefixOf X)) / 2 ^ e

/-- `W_i` (50). -/
noncomputable def Wi {n : ℕ} (X : Fin n → ℝ) (q : ℝ) (i : ℕ) : ℝ :=
  by classical exact
    2 * kappa * ∑ h ∈ Finset.range (k n),
      (if 2 ^ (h + 1) ≤ b n i ∧ ¬ Bad (prefixOf X) q (i + h) ∧
          ∃ c < 2, B n * 2 ^ h < Nblk X i (i + h - 1) (2 * parIdx X q (i + h) + c)
        then (2 : ℝ) ^ h else 0) +
    (if i + 1 < k n then
      2 * kappa * ∑ h ∈ Finset.range (k n),
        (if 2 ^ (h + 1) ≤ b n (i + 1) ∧ ¬ Bad (prefixOf X) q (i + 1 + h) ∧
            ∃ c < 2, (Nblk X i (i + h) (2 * parIdx X q (i + 1 + h) + c) : ℝ) <
              11 / 10 * (B n : ℝ) * 2 ^ h
          then (2 : ℝ) ^ h else 0)
     else 0)

/-- The future sum `∑_{i=1}^{k−1} W_i`. -/
noncomputable def WSum {n : ℕ} (X : Fin n → ℝ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (k n - 1), Wi X q i

/-- `A_p = 2 + 2(8195)²` (Lemma 4.7, (30)). -/
noncomputable def Ap : ℝ := 2 + 2 * 8195 ^ 2

/-- `M_b = e^{62/3584}(1 + A_p e^{−64/1792}/(1 − e^{−1/1792}))` (52). -/
noncomputable def Mb : ℝ :=
  Real.exp (62 / 3584) * (1 + Ap * (Real.exp (-(64 / 1792)) / (1 - Real.exp (-(1 / 1792)))))

/-- `M_s = 1 + 2e^{−1/3}/(1 − e^{−1/6})` (proof of Lemma 4.13, p.35). -/
noncomputable def Ms : ℝ := 1 + 2 * Real.exp (-(1 / 3)) / (1 - Real.exp (-(1 / 6)))

/-- The charges `Γ_q(v)` of the top-marked selected bad parents (internal nodes of the selected
chain whose fixed-tree parent `J_{q,ν}` is bad) in the operation of type `arr` of shrinking phase
`i` of the i.i.d. run on `X`; a phase-`i` node of height `h` consists of `ν = 2^{h+i−1}` initial
buckets (§4.4.1, proof of Lemma 4.11, p.33). -/
noncomputable def badCharges {n : ℕ} (X : Fin n → ℝ) (q : ℝ) (i : ℕ) (arr : Bool) : ℝ :=
  by classical exact
    ∑ h ∈ Finset.Icc 1 (k n),
      (if TopMarked (opReqs (runState n (iidLt X) n) (L n + i - 1) arr)
            (h, cutLeaf (fun a => decide (q < vecVal X a)) (phaseTree n (iidLt X) (L n + i - 1)) / 2 ^ h) ∧
          Bad (prefixOf X) q (h + i - 1)
        then (Gamma (fun a => decide (q < vecVal X a)) (opReqs (runState n (iidLt X) n) (L n + i - 1) arr)
            (h, cutLeaf (fun a => decide (q < vecVal X a)) (phaseTree n (iidLt X) (L n + i - 1)) / 2 ^ h) : ℝ)
        else 0)

end RandOrderSort



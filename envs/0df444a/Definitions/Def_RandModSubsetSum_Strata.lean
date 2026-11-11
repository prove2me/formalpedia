-- Prove2me | Definitions.Def_RandModSubsetSum_Strata
-- name    : RandModSubsetSum_Strata
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:12.88728+00:00
-- url     : https://prove2.me/theorems/1553aff5-b77f-4ebe-b477-a396a11f310b
-- title:
--   The paper's stratum weights $w_r=W_r/10^{20}$, the strata $I_r$, root counts and near balance
-- statement:
--   The coordinates $[n]$ are split into $13$ **strata** $I_1,\dots,I_{13}$ of consecutive coordinates (Definition 2.8, §3.1). For weights $w_r>0$ with $\sum_r w_r=1$, the sizes $n_r=|I_r|$ start at $\lfloor w_rn\rfloor$; one is then added to the required number of terms with the largest fractional parts of $w_rn$ (ties by increasing $r$), so that $\sum_r n_r=n$ and $|n_r-w_rn|<1$. This is the m-type rounding $n\lfloor w\rceil_n$.
--
--   The paper's weights are $w_r=W_r/10^{20}$ with the numerators $W_r$ of Table 4, which sum to $10^{20}$.
--
--   For a binary vector $x$, the **root count** of stratum $r$ is $h_r=\sum_{k\in I_r}x_k$, and $\rho_r=h_r/n_r$. The root is **nearly balanced** if
--   $$|h_r-n_r/2|\le 10^{-10}n_r\qquad(r=1,\dots,13)$$
--   (Problem 3.1).
--
--   These objects define Problem 3.1 and the representation family.
--
--   **Formalization Note** Coordinates are `Fin n` (0-indexed); $I_r$ is the block $[\sum_{r'<r}n_{r'},\sum_{r'\le r}n_{r'})$.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Definition 2.8, p. 11; §3.1, p. 11; Problem 3.1, p. 16; Table 4, p. 42

import Mathlib
import Definitions.Def_RandModSubsetSum_Types

open scoped BigOperators

namespace RandModSubsetSum

/-- The weight numerators `W_r` of Table 4 (p. 42), for strata `r = 1, …, 13` (index `r − 1`).
They are positive and sum to `10²⁰`.
Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Table 4, p. 42. -/
def paperWNum : Fin 13 → ℕ :=
  ![1675629228498733141, 16977773421718744857, 996053412671605093, 131475488563929695,
    4239825947424213936, 8544153189890216236, 25206509263910281740, 4036541710445202418,
    6207275065703520709, 2077199667841899902, 10907155499484767783, 3155231958098091158,
    15845176145748793332]

/-- The paper's stratum weights `w_r = W_r / 10²⁰` (§6.1, p. 41; Table 4, p. 42). -/
noncomputable def paperWeight : Fin 13 → ℝ := fun r => (paperWNum r : ℝ) / 10 ^ 20

/-- Stratum sizes `n_r = |I_r|` for weights `w` and length `n` (§3.1, p. 11): "Set `n_r = |I_r|`
initially to `⌊w_r n⌋`, then add one to the required number of terms with the largest fractional
parts of `w_r n` so that `Σ_r n_r = n` (ties by increasing `r`)." This is the m-type rounding
`n ⌊w⌉_n` of Definition 2.2 with the order `r = 1 < ⋯ < 13`. -/
noncomputable def stratumSize (w : Fin 13 → ℝ) (n : ℕ) (r : Fin 13) : ℕ :=
  roundCount Finset.univ (fun r : Fin 13 => r) w n r

/-- First coordinate (0-indexed) of stratum `r`: `Σ_{r' < r} n_{r'}`. -/
noncomputable def stratumStart (w : Fin 13 → ℝ) (n : ℕ) (r : Fin 13) : ℕ :=
  ∑ r' ∈ Finset.univ.filter (fun r' : Fin 13 => r' < r), stratumSize w n r'

open Classical in
/-- The stratum `I_r ⊆ [n]` (Definition 2.8, p. 11; §3.1, p. 11): "Use consecutive coordinate sets
of these lengths". Coordinates are `Fin n` (0-indexed); `I_r` is the block
`[Σ_{r'<r} n_{r'}, Σ_{r'≤r} n_{r'})`. -/
noncomputable def stratum (w : Fin 13 → ℝ) (n : ℕ) (r : Fin 13) : Finset (Fin n) :=
  Finset.univ.filter (fun k => stratumStart w n r ≤ k.val ∧ k.val < stratumStart w n r + stratumSize w n r)

open Classical in
/-- Root count `h_r = Σ_{k ∈ I_r} x_k` of a binary vector in stratum `r` (Problem 3.1, p. 16). -/
noncomputable def rootCount (w : Fin 13 → ℝ) {n : ℕ} (x : Fin n → Fin 2) (r : Fin 13) : ℕ :=
  ((stratum w n r).filter (fun k => x k = 1)).card

/-- **Near balance** (Problem 3.1, p. 16): `|h_r − n_r/2| ≤ 10⁻¹⁰ n_r` for every stratum `r`. -/
def NearBalanced (w : Fin 13 → ℝ) {n : ℕ} (x : Fin n → Fin 2) : Prop :=
  ∀ r, |(rootCount w x r : ℝ) - (stratumSize w n r : ℝ) / 2| ≤ (1 / 10 ^ 10) * (stratumSize w n r : ℝ)

/-- The fraction of ones of the root in each stratum, `ρ_r = h_r / n_r` (§4.1, p. 22). -/
noncomputable def rho (w : Fin 13 → ℝ) {n : ℕ} (x : Fin n → Fin 2) (r : Fin 13) : ℝ :=
  (rootCount w x r : ℝ) / (stratumSize w n r : ℝ)

end RandModSubsetSum



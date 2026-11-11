-- Prove2me | Definitions.Def_OneTrap_Core_Blocks
-- name    : OneTrap_Core_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:46.184734+00:00
-- url     : https://prove2.me/theorems/b74b6f68-69f4-424e-9fe8-620ab8167bc4
-- title:
--   Known index levels $\lambda_j$, unknown blocks $B_j$, block maxima $Z_j$, $\overline Z_j$ and the trap level index $j^\star$ (§B.1.3)
-- statement:
--   Let $A=K\cup\mathcal U$ with known boxes $K$ and unknown boxes $\mathcal U$, a contract $w$ and a realized profile $y_{\mathcal U}$ of the unknown outputs. Let $\lambda_1>\lambda_2>\dots>\lambda_{\ell_K}>0$ be the distinct positive finite reservation values of known boxes and $\lambda_{\ell_K+1}=0$. If $\ell_K\ge 1$, $B_0=\{i\in\mathcal U:\rho_i>\lambda_1\}$ and $B_j=\{i\in\mathcal U:\lambda_{j+1}<\rho_i<\lambda_j\}$ for $j=1,\dots,\ell_K$; if $\ell_K=0$, $B_0=\{i\in\mathcal U:\rho_i>0\}$. Then
--   $$Z_j=\max(\{0\}\cup\{X^{\mathrm{cov}}_i:i\in B_j\}),\qquad \overline Z_j=\max_{0\le r\le j}Z_r .$$
--   $j^\star$ is the smallest $j<\ell_K$ with $\overline Z_j\ge\lambda_{j+1}$; if there is none but $\overline Z_{\ell_K}>0$, $j^\star=\ell_K$; otherwise $j^\star$ is undefined (§B.1.3, pp. 26–27). Used only by Lemma B.7.
--
--   **Formalization Note** Unknown boxes are `N : ν → Box`, known `K : κ → Box`, the profile `yU : ν → ℝ`. `knownLevels` is the finite set of `(ρ_k).toReal` over known `k` with `0 < ρ_k < ⊤`; `level w K j` is the `j`-th largest for `1 ≤ j ≤ ℓ_K` (via the sorted list) and `0` for `j = ℓ_K + 1`. `unknownBlock`, `blockMax` ($Z_j$, an `EReal`, `0` on an empty block), `cumBlockMax` ($\overline Z_j$) and `jStar : Option ℕ` (`none` = undefined) follow the page.
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), §B.1.3, pp. 26–27 (PDF 27–28)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Index

/-!
# Known index levels, unknown blocks and the trap level (§B.1.3, pp. 26–27)

Feldman, Fu, Peng, Tang (2026), held STOC 2027 submission, §B.1.3, pp. 26–27. Used only by
Lemma B.7. The extension is `K ⊕ N`: known boxes `K : κ → Box`, unknown boxes `N : ν → Box`,
and `yU : ν → ℝ` is a realized profile of the unknown outputs.

* `λ₁ > λ₂ > ⋯ > λ_{ℓ_K} > 0` are the distinct positive finite known reservation values,
  `λ_{ℓ_K + 1} = 0`.
* `B₀ = {i ∈ U : ρ_i > λ₁}` and `B_j = {i ∈ U : λ_{j+1} < ρ_i < λ_j}` for `j = 1, …, ℓ_K`
  when `ℓ_K ≥ 1`; `B₀ = {i ∈ U : ρ_i > 0}` when `ℓ_K = 0`.
* `Z_j = max ({0} ∪ {X^cov_i : i ∈ B_j})`, `Z̄_j = max_{0 ≤ r ≤ j} Z_r`.
* `j⋆` is the smallest `j < ℓ_K` with `Z̄_j ≥ λ_{j+1}`; if there is none but `Z̄_{ℓ_K} > 0`,
  `j⋆ = ℓ_K`; otherwise `j⋆` is undefined (`none`).
-/

noncomputable section

open MeasureTheory

namespace OneTrap.Core

variable {κ ν : Type*} [Fintype κ] [Fintype ν]

/-- The set of distinct positive finite known reservation values. -/
def knownLevels (w : ℝ → ℝ) (K : κ → Box) : Finset ℝ :=
  (Finset.univ.filter fun k => 0 < resv w (K k) ∧ resv w (K k) < ⊤).image
    fun k => (resv w (K k)).toReal

/-- `ℓ_K`, the number of distinct positive finite known index levels. -/
def numLevels (w : ℝ → ℝ) (K : κ → Box) : ℕ :=
  (knownLevels w K).card

/-- `λ_j` for `j = 1, …, ℓ_K` (the `j`-th largest known level) and `λ_{ℓ_K + 1} = 0`. -/
def level (w : ℝ → ℝ) (K : κ → Box) (j : ℕ) : ℝ :=
  ((knownLevels w K).sort (· ≤ ·)).reverse.getD (j - 1) 0

/-- The unknown blocks `B_j` (p. 26). -/
def unknownBlock (w : ℝ → ℝ) (K : κ → Box) (N : ν → Box) (j : ℕ) : Finset ν :=
  if j = 0 then
    if 1 ≤ numLevels w K then
      Finset.univ.filter fun i => ((level w K 1 : ℝ) : EReal) < resv w (N i)
    else
      Finset.univ.filter fun i => (0 : EReal) < resv w (N i)
  else
    Finset.univ.filter fun i =>
      ((level w K (j + 1) : ℝ) : EReal) < resv w (N i) ∧ resv w (N i) < ((level w K j : ℝ) : EReal)

/-- `Z_j(y_U) = max ({0} ∪ {X^cov_i(y_U) : i ∈ B_j})`, an empty block giving `0`. -/
def blockMax (w : ℝ → ℝ) (K : κ → Box) (N : ν → Box) (yU : ν → ℝ) (j : ℕ) : EReal :=
  max 0 ((unknownBlock w K N j).sup fun i => coveredWage w (N i) (yU i))

/-- `Z̄_j(y_U) = max_{0 ≤ r ≤ j} Z_r(y_U)`. -/
def cumBlockMax (w : ℝ → ℝ) (K : κ → Box) (N : ν → Box) (yU : ν → ℝ) (j : ℕ) : EReal :=
  (Finset.range (j + 1)).sup fun r => blockMax w K N yU r

open Classical in
/-- The index `j⋆` (p. 27), `none` when it is undefined. -/
def jStar (w : ℝ → ℝ) (K : κ → Box) (N : ν → Box) (yU : ν → ℝ) : Option ℕ :=
  if h : ∃ j, j < numLevels w K ∧
      ((level w K (j + 1) : ℝ) : EReal) ≤ cumBlockMax w K N yU j then
    some (Nat.find h)
  else if 0 < cumBlockMax w K N yU (numLevels w K) then
    some (numLevels w K)
  else
    none

end OneTrap.Core



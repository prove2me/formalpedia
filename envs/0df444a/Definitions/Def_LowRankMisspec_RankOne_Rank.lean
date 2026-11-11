-- Prove2me | Definitions.Def_LowRankMisspec_RankOne_Rank
-- name    : LowRankMisspec_RankOne_Rank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:15:41.725067+00:00
-- url     : https://prove2.me/theorems/e8c63af3-349b-41aa-af53-d6c9a6e07668
-- title:
--   Joint probability matrices $J_t(P)$, distribution rank (Definition 2.1), $\mathcal R_r$ and $d_r$
-- statement:
--   For a law $P$ on $[\sigma]^T$ and $t\in\{0,\dots,T\}$ the **joint probability matrix** $J_t(P)\in\mathbb R^{[\sigma]^{T-t}\times[\sigma]^t}$ has rows indexed by futures and columns by histories,
--   $$J_t(P)[f,h]=P[hf].$$
--   **Definition 2.1.** The **distribution rank** is $\mathrm{drank}(P)=\max_{0\le t\le T}\operatorname{rank}(J_t(P))$ (rank over $\mathbb R$). For an integer $r\ge1$, $\mathcal R_r=\{Q\in\Delta([\sigma]^T):\mathrm{drank}(Q)\le r\}$ and $d_r(P)=\min_{Q\in\mathcal R_r}\|P-Q\|_1$.
--
--   **Formalization Note.** `catStr h f` is the string $hf$; `drank` is the supremum of `Matrix.rank (jointMatrix P t)` over `t ∈ Finset.range (T + 1)`. `dR r P` is the infimum (`sInf`) of $\|P-Q\|_1$ over $Q\in\mathcal R_r$; the set is nonempty for $r\ge1$, $\sigma\ge1$ (it contains the product laws) and bounded below by $0$, and Proposition A.10 (a milestone) says the infimum is attained, which is the paper's minimum. $d_1$ is **not** defined as the distance to product laws: that identification is Proposition A.7.
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 3 (PDF 4), §2.2, Definition 2.1

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace LowRankMisspec.RankOne

/-!
# Joint probability matrices `J_t`, distribution rank, `R_r` and `d_r` (Definition 2.1)

Hasrati, Risteski, *Understanding Model Misspecification in Low-Rank Distributions: Tolerant
Testing and Agnostic Learning*, STOC 2027 submission (manuscript sha256 235f2a4f…), §2.2, p. 3
(PDF 4), Definition 2.1.

* `catStr h f = hf`, the string with history `h ∈ [σ]^t` followed by future `f ∈ [σ]^{T−t}`.
* `jointMatrix P t = J_t(P) ∈ ℝ^{[σ]^{T−t} × [σ]^t}`, `J_t(P)[f, h] = P[hf]` (rows futures,
  columns histories), for `t ∈ {0, …, T}`.
* `drank P = max_{0 ≤ t ≤ T} rank J_t(P)`, the rank over `ℝ`.
* `RClass σ T r = R_r = {Q ∈ Δ([σ]^T) : drank Q ≤ r}`.
* `dR r P = d_r(P)`, the infimum of `‖P − Q‖₁` over `Q ∈ R_r`. The paper writes a minimum;
  Proposition A.10 says it is attained. `R_r` is nonempty for `r ≥ 1` and `σ ≥ 1` (it contains the
  product laws) and the distances are `≥ 0`, so the infimum is that of a nonempty set bounded
  below.
-/

/-- The concatenation `hf` of a history `h ∈ [σ]^t` and a future `f ∈ [σ]^{T−t}`. -/
def catStr {σ T t : ℕ} (h : Fin t → Fin σ) (f : Fin (T - t) → Fin σ) : Str σ T :=
  fun i => if hi : i.val < t then h ⟨i.val, hi⟩ else f ⟨i.val - t, by have := i.isLt; omega⟩

/-- The joint probability matrix `J_t(P)[f, h] = P[hf]`, rows futures `f ∈ [σ]^{T−t}`, columns
histories `h ∈ [σ]^t`. -/
def jointMatrix {σ T : ℕ} (P : Str σ T → ℝ) (t : ℕ) :
    Matrix (Fin (T - t) → Fin σ) (Fin t → Fin σ) ℝ :=
  Matrix.of fun f h => P (catStr h f)

/-- Definition 2.1: the distribution rank `drank(P) = max_{0 ≤ t ≤ T} rank(J_t(P))`. -/
def drank {σ T : ℕ} (P : Str σ T → ℝ) : ℕ :=
  (Finset.range (T + 1)).sup fun t => (jointMatrix P t).rank

/-- `R_r = {Q ∈ Δ([σ]^T) : drank(Q) ≤ r}`. -/
def RClass (σ T r : ℕ) : Set (Str σ T → ℝ) :=
  {Q | IsLaw Q ∧ drank Q ≤ r}

/-- `d_r(P)`: the infimum of `‖P − Q‖₁` over `Q ∈ R_r`. -/
def dR {σ T : ℕ} (r : ℕ) (P : Str σ T → ℝ) : ℝ :=
  sInf ((fun Q => l1 P Q) '' RClass σ T r)

end LowRankMisspec.RankOne



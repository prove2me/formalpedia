-- Prove2me | Definitions.Def_LowRankMisspec_RankOne_Laws
-- name    : LowRankMisspec_RankOne_Laws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:14:43.991046+00:00
-- url     : https://prove2.me/theorems/b586f2ae-379b-4d01-8622-16425110e414
-- title:
--   Laws on $[\sigma]^T$, $\ell_1$ distance, prefix masses, conditionals, marginals, product laws
-- statement:
--   Fix an alphabet size $\sigma$ and a length $T$. A **string** is $x=(x_1,\dots,x_T)\in[\sigma]^T$; a **law** on a finite set $\Omega$ is a function $P:\Omega\to\mathbb R$ with $P\ge 0$ and $\sum_x P[x]=1$ (a point of the simplex $\Delta(\Omega)$). The **$\ell_1$ distance** is $\|P-Q\|_1=\sum_x|P[x]-Q[x]|$, so $d_{TV}(P,Q)=\tfrac12\|P-Q\|_1$.
--
--   For a history $h\in[\sigma]^t$ ($t\le T$) the **prefix mass** is
--   $$P^{(t)}[h]=\sum_{f\in[\sigma]^{T-t}}P[hf],$$
--   and for $f\in[\sigma]^s$ with $t+s\le T$ and $P^{(t)}[h]>0$ the **conditional** is $P[f\mid h]=P^{(t+s)}[hf]/P^{(t)}[h]$. The **marginal** of coordinate $j$ is $P_j[a]=\sum_{x:x_j=a}P[x]$. $P$ is a **product distribution** when $P[x]=\prod_{j=1}^T P_j[x_j]$ for every $x$. For rows $p_1,\dots,p_T\in\Delta([\sigma])$ the **product law** is $(\bigotimes_t p_t)[x]=\prod_t p_t[x_t]$.
--
--   **Formalization Note.** Strings are `Fin T → Fin σ` (0-based symbols and coordinates). A history is a list of naturals `h`; `IsPrefix h x` requires `|h| ≤ T` and that `x` begins with `h`, so a list longer than `T` or with an entry `≥ σ` has mass `0`. `condProb P h f` divides by `P^{(|h|)}[h]` and is used only where that is positive. `strCells x` is the list of symbols of `x`.
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 2–3 (PDF 3–4), §2.1 and §2.3; p. 8 (PDF 9), §5.1; p. 15 (PDF 16), proof of Proposition A.7

import Mathlib

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace LowRankMisspec.RankOne

/-!
# Laws on `[σ]^T`, ℓ1 distance, prefix masses, conditionals, marginals, product laws

Hasrati, Risteski, *Understanding Model Misspecification in Low-Rank Distributions: Tolerant
Testing and Agnostic Learning*, STOC 2027 submission (manuscript sha256 235f2a4f…), §2.1 and §2.3,
pp. 2–3 (PDF 3–4); §5.1, p. 8 (PDF 9); Proposition A.7, p. 15 (PDF 16).

* A string `x ∈ [σ]^T` is `x : Fin T → Fin σ`: the paper's symbol `a ∈ {1, …, σ}` is `a − 1`, its
  coordinate `j ∈ {1, …, T}` is `j − 1`.
* A law (a point of `Δ([σ]^T)`, or of `Δ([σ])`) is a real function, nonnegative, summing to `1`.
* `l1 P Q = ‖P − Q‖₁ = Σ_x |P[x] − Q[x]|` (so `d_TV = l1 / 2`).
* A history `h` is a list of naturals (the symbols `h₁ − 1, …, h_t − 1`). `IsPrefix h x` says that
  `|h| ≤ T` and `x` begins with `h`; `prefMass P h = P^(|h|)[h] = Σ_f P[hf]` (a list with an entry
  `≥ σ` or longer than `T` is a prefix of no string and has mass `0`).
* `condProb P h f = P[f | h] = P^(|h|+|f|)[hf] / P^(|h|)[h]` (used only where `P^(|h|)[h] > 0`).
* `marginal P j a = P_j[a]`, the marginal of coordinate `j`.
* `IsProductDist P`: `P[x] = Π_j P_j[x_j]` for every `x` (the paper's "product distribution",
  in the form of the proof of Proposition A.7).
* `prodLaw p = ⊗_t p_t`, `(⊗_t p_t)[x] = Π_t p_t[x_t]`, for rows `p_t` on `[σ]`.
* `strCells x` is the list of the symbols of `x` (the oracle's and the machine's encoding).
-/

/-- A string `x ∈ [σ]^T`. -/
abbrev Str (σ T : ℕ) := Fin T → Fin σ

/-- `P` is a probability law on the finite set `Ω` (a point of the simplex `Δ(Ω)`). -/
def IsLaw {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1

/-- The ℓ1 distance `‖P − Q‖₁ = Σ_x |P[x] − Q[x]|`. -/
def l1 {Ω : Type*} [Fintype Ω] (P Q : Ω → ℝ) : ℝ := ∑ x, |P x - Q x|

/-- The symbols of a string, as a list of naturals `< σ`. -/
def strCells {σ T : ℕ} (x : Str σ T) : List ℕ := List.ofFn fun i => (x i).val

/-- `x` begins with the history `h`: `|h| ≤ T` and `x_i = h_i` for `i < |h|`. -/
def IsPrefix {σ T : ℕ} (h : List ℕ) (x : Str σ T) : Prop :=
  h.length ≤ T ∧ ∀ i : Fin T, i.val < h.length → h.getD i.val 0 = (x i).val

/-- The prefix mass `P^(t)[h] = Σ_{f ∈ [σ]^{T−t}} P[hf]`, `t = |h|`. -/
def prefMass {σ T : ℕ} (P : Str σ T → ℝ) (h : List ℕ) : ℝ :=
  ∑ x, if IsPrefix h x then P x else 0

/-- The conditional probability `P[f | h] = P^(t+s)[hf] / P^(t)[h]` (meaningful when
`P^(t)[h] > 0`). -/
def condProb {σ T : ℕ} (P : Str σ T → ℝ) (h f : List ℕ) : ℝ :=
  prefMass P (h ++ f) / prefMass P h

/-- The marginal `P_j[a]` of coordinate `j`. -/
def marginal {σ T : ℕ} (P : Str σ T → ℝ) (j : Fin T) (a : Fin σ) : ℝ :=
  ∑ x, if x j = a then P x else 0

/-- `P` is a product distribution: `P[x] = Π_j P_j[x_j]` for every string `x`. -/
def IsProductDist {σ T : ℕ} (P : Str σ T → ℝ) : Prop :=
  ∀ x, P x = ∏ j, marginal P j (x j)

/-- The product law `⊗_t p_t` of rows `p_t` on `[σ]`: `(⊗_t p_t)[x] = Π_t p_t[x_t]`. -/
def prodLaw {σ T : ℕ} (p : Fin T → Fin σ → ℝ) : Str σ T → ℝ :=
  fun x => ∏ t, p t (x t)

end LowRankMisspec.RankOne



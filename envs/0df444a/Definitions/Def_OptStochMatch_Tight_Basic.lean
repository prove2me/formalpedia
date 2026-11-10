-- Prove2me | Definitions.Def_OptStochMatch_Tight_Basic
-- name    : OptStochMatch_Tight_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:52:59.316328+00:00
-- url     : https://prove2.me/theorems/a0140b02-29cc-4ce0-acb1-2acfc8d9670a
-- title:
--   Types, coverage function $\Lambda$, coverage polymatroid $\mathcal P_\lambda$, offline optima and deficiencies
-- statement:
--   Offline vertices (jobs) are $[m]$, written `Fin m`; an online vertex has a type $S\subseteq[m]$ (its neighbourhood), and arrival rates are $\lambda_S\ge 0$.
--
--   - $\Lambda(A)=\sum_{S:\,S\cap A\neq\emptyset}\lambda_S$ and, for type counts $N=(N_S)$, $N(A)=\sum_{S:\,S\cap A\ne\emptyset}N_S$.
--   - The coverage polymatroid $\mathcal P_\lambda=\{x\in\mathbb R^m_+ : x(A)\le\Lambda(A)\ \forall A\subseteq[m]\}$.
--   - A feasible-rate region: a compact, convex, downward-closed $P\subseteq\mathbb R^m_+$ containing $0$.
--   - $\mathrm{OPT}^{\mathrm{Pois}}(N)$: the value of the matching LP $\max\sum_S\sum_{i\in S}x_{i,S}$ over $x_{i,S}\in[0,1]$ with $\sum_{i\in S}x_{i,S}\le N_S$ and $\sum_{S\ni i}x_{i,S}\le 1$ (a supremum of a nonempty set bounded by $m$).
--   - $\mathrm{OPT}^{\mathrm{Exp}}_P(z)=\max\{\sum_i x_i: 0\le x\le z,\ x\in P\}$ and $\mathrm{OPT}^{\mathrm{Exp}}=\mathrm{OPT}^{\mathrm{Exp}}_{\mathcal P_\lambda}$.
--   - Deficiencies $\delta^{\mathrm{Pois}}_N(A)=|A|-N(A)$ (in $\mathbb Z$), $\delta^{\mathrm{Exp}}_z(A)=z(A)-\Lambda(A)$, and their maxima over $A\subseteq[m]$.
--   - The constant $1-e/e^e$ and $\kappa=2^{-18}m^{-3}$.
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), §2.1–§3.1, pp. 5–9 (PDF 6–10); constant from Theorem 1.1, p. 1 (PDF 2); κ from Lemma 6.3, p. 29 (PDF 30)

import Mathlib

/-!
Dütting, Feldman, Molina, *Optimal Online Stochastic Matching*, arXiv:2610.19866
(sha256 0458ce2e…), §2.1–§3.1, pp. 5–9 (PDF 6–10).

Static objects shared by both arrival models and by the scheduling model:
types (neighbourhoods) `S ⊆ [m]`, the coverage function `Λ`, the coverage polymatroid `P_λ`,
the two offline optima `OPT^Pois(N)` (a linear program) and `OPT^Exp_P(z)`, the two
deficiencies, and the constant `1 − e/e^e`.

Conventions. Offline vertices / jobs are `Fin m` (the paper's `[m] = {1,…,m}`, shifted to
`0,…,m-1`). A type is a `Finset (Fin m)`. Arrival rates are `ℝ≥0`-valued (the paper's
`λ_S ≥ 0`).
-/

namespace OptStochMatch.Tight

open scoped NNReal BigOperators

/-- A type (neighbourhood) of an online vertex: a subset `S ⊆ [m]`. -/
abbrev Ty (m : ℕ) := Finset (Fin m)

/-- The constant `1 − e/e^e = 1 − e^{1−e} ≈ 0.8206` of Theorem 1.1. -/
noncomputable def cStar : ℝ := 1 - Real.exp 1 / Real.exp (Real.exp 1)

/-- `κ = 2^{−18} m^{−3}` of Lemma 6.3 (p. 29, PDF 30). -/
noncomputable def kappa (m : ℕ) : ℝ := 1 / ((2 : ℝ) ^ 18 * (m : ℝ) ^ 3)

/-- `Λ(A) := ∑_{S : S ∩ A ≠ ∅} λ_S` (p. 5, PDF 6). -/
noncomputable def coverRate {m : ℕ} (lam : Ty m → ℝ≥0) (A : Finset (Fin m)) : ℝ :=
  ∑ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty), (lam S : ℝ)

/-- `N(A) := ∑_{S : S ∩ A ≠ ∅} N_S` for a vector of type counts `N` (p. 5, PDF 6). -/
def coverCount {m : ℕ} (N : Ty m → ℕ) (A : Finset (Fin m)) : ℕ :=
  ∑ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty), N S

/-- The coverage polymatroid `P_λ := {x ∈ ℝ^m_+ : x(A) ≤ Λ(A) ∀ A ⊆ [m]}` (p. 7, PDF 8). -/
def Plam {m : ℕ} (lam : Ty m → ℝ≥0) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ A : Finset (Fin m), ∑ i ∈ A, x i ≤ coverRate lam A}

/-- A feasible-rate region of the scheduling model (§2.2, p. 6, PDF 7): a compact, convex,
downward-closed set `P ⊆ ℝ^m_+` containing the origin. Downward closed is read inside
`ℝ^m_+`: `0 ≤ y ≤ x ∈ P ⇒ y ∈ P`. -/
def IsRateRegion {m : ℕ} (P : Set (Fin m → ℝ)) : Prop :=
  IsCompact P ∧ Convex ℝ P ∧ (0 : Fin m → ℝ) ∈ P ∧ (∀ x ∈ P, ∀ i, 0 ≤ x i) ∧
    ∀ x ∈ P, ∀ y : Fin m → ℝ, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) → y ∈ P

/-- The offline maximum matching value `OPT^Pois(N)` as the linear program of p. 6 (PDF 7):
the supremum of `∑_S ∑_{i∈S} x_{i,S}` over `x_{i,S} ∈ [0,1]` with
`∑_{i∈S} x_{i,S} ≤ N_S` for every `S` and `∑_{S∋i} x_{i,S} ≤ 1` for every `i`.
The feasible set contains `x = 0` and the objective is at most `m`, so the supremum is the
maximum of the LP. Coordinates `x i S` with `i ∉ S` occur in no constraint and in no
objective term. -/
noncomputable def optPois {m : ℕ} (N : Ty m → ℕ) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin m → Ty m → ℝ,
    (∀ i S, 0 ≤ x i S ∧ x i S ≤ 1) ∧
    (∀ S : Ty m, ∑ i ∈ S, x i S ≤ (N S : ℝ)) ∧
    (∀ i : Fin m, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), x i S ≤ 1) ∧
    v = ∑ S : Ty m, ∑ i ∈ S, x i S}

/-- The offline scheduling optimum `OPT^Exp_P(z) := max {∑_i x_i : 0 ≤ x ≤ z, x ∈ P}`
(p. 7, PDF 8), written as a supremum (attained when `P` is compact and `z ≥ 0`). -/
noncomputable def optExpP {m : ℕ} (P : Set (Fin m → ℝ)) (z : Fin m → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin m → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ z i) ∧ x ∈ P ∧ v = ∑ i, x i}

/-- `OPT^Exp(z) := OPT^Exp_{P_λ}(z)` (p. 7, PDF 8). -/
noncomputable def optExp {m : ℕ} (lam : Ty m → ℝ≥0) (z : Fin m → ℝ) : ℝ :=
  optExpP (Plam lam) z

/-- The Poisson deficiency `δ^Pois_N(A) := |A| − N(A)` (p. 9, PDF 10), in `ℤ`. -/
def defPois {m : ℕ} (N : Ty m → ℕ) (A : Finset (Fin m)) : ℤ :=
  (A.card : ℤ) - (coverCount N A : ℤ)

/-- The exponential deficiency `δ^Exp_Z(A) := Z(A) − Λ(A)` (p. 9, PDF 10). -/
noncomputable def defExp {m : ℕ} (lam : Ty m → ℝ≥0) (z : Fin m → ℝ) (A : Finset (Fin m)) : ℝ :=
  ∑ i ∈ A, z i - coverRate lam A

/-- `max_{A ⊆ [m]} δ^Pois_N(A)`. -/
def maxDefPois {m : ℕ} (N : Ty m → ℕ) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty (defPois N)

/-- `max_{A ⊆ [m]} δ^Exp_Z(A)`. -/
noncomputable def maxDefExp {m : ℕ} (lam : Ty m → ℝ≥0) (z : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (defExp lam z)

/-- The realized type counts `N_S = #{k : s_k = S}` of a finite arrival sequence. -/
def typeCounts {m n : ℕ} (s : Fin n → Ty m) (S : Ty m) : ℕ :=
  (Finset.univ.filter fun k : Fin n => s k = S).card

end OptStochMatch.Tight



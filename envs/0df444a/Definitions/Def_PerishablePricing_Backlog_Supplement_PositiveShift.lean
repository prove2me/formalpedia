-- Prove2me | Definitions.Def_PerishablePricing_Backlog_Supplement_PositiveShift
-- name    : PerishablePricing_Backlog_Supplement_PositiveShift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:58:21.440894+00:00
-- url     : https://prove2.me/theorems/1cdfcde8-7eb7-4fc0-bd3a-17a2a78575e5
-- title:
--   Lemma 4, p. 288 — shifted positive parts and monotonicity of the infinite extension
-- statement:
--   For $1\le k\le n$ and $w=(s_1,\ldots,s_n,s_{n+1})$, define
--
--   $$H_k(w)_i=\begin{cases}(s_i-s_{n+1})^+,&i\le k,\\s_i-s_{n+1},&i>k.\end{cases}$$
--
--   The real and integer versions are both provided. For an effective domain $S$ and finite values $f$ on $S$, nondecreasingness of its $+\infty$ extension in the first $k$ variables means the following: whenever $u,v\in\mathcal V^+_{n,k}$, $u_i\le v_i$ for $i\le k$, and the remaining coordinates agree, $v\in S$ implies $u\in S$ and $f(u)\le f(v)$.
--
--   This is the transformation and the full monotonicity premise of Lemma 4. Testing only pairs already in $S$ would omit the required downward closure of the effective domain.
--
--   **Formalization Note** The first $k$ coordinates are the indices `i < k`. The last $n-k$ coordinates are shifted without truncation; both real and integer carrier cases of the paper are retained.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, https://doi.org/10.1287/opre.2014.1261, Lemma 4, p. 288 (PDF 6), transformation and monotonicity hypothesis

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex
import Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerLNat

namespace PerishablePricing.Backlog.Supplement

/-- Lemma 4: first k shifted coordinates are truncated, the others are not. -/
noncomputable def positiveShift {n : ℕ} (k : ℕ) (w : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < k then max (w i.castSucc - w (Fin.last n)) 0
    else w i.castSucc - w (Fin.last n)

def positiveShiftZ {n : ℕ} (k : ℕ) (w : Fin (n + 1) → ℤ) : Fin n → ℤ :=
  fun i => if (i : ℕ) < k then max (w i.castSucc - w (Fin.last n)) 0
    else w i.castSucc - w (Fin.last n)

/-- Monotonicity of the +∞ extension, including downward closure of its finite domain.
Checking only pairs inside S would miss that closure requirement. -/
def ExtendedMonotoneFirst {n : ℕ} (k : ℕ) (S : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ u ∈ Vplus n k, ∀ v ∈ Vplus n k,
    (∀ i : Fin n, (i : ℕ) < k → u i ≤ v i) →
    (∀ i : Fin n, k ≤ (i : ℕ) → u i = v i) →
    v ∈ S → u ∈ S ∧ f u ≤ f v

def ExtendedMonotoneFirstZ {n : ℕ} (k : ℕ) (S : Set (Fin n → ℤ))
    (f : (Fin n → ℤ) → ℝ) : Prop :=
  ∀ u ∈ VplusZ n k, ∀ v ∈ VplusZ n k,
    (∀ i : Fin n, (i : ℕ) < k → u i ≤ v i) →
    (∀ i : Fin n, k ≤ (i : ℕ) → u i = v i) →
    v ∈ S → u ∈ S ∧ f u ≤ f v

end PerishablePricing.Backlog.Supplement



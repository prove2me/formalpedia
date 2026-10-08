-- Prove2me | Definitions.Def_ResolvingNRM_FRLower_Model
-- name    : ResolvingNRM_FRLower_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:18:34.736446+00:00
-- url     : https://prove2.me/theorems/4f7d5e48-a599-4293-bc04-737410506181
-- title:
--   Section 2 and Algorithm 2 — Poisson network model, hindsight value, and frequent re-solving policy
-- statement:
--   Fix finitely many customer classes and resources. Class $j$ arrives as an independent Poisson process of positive rate $\lambda_j$, earns nonnegative revenue $r_j$ when accepted, and consumes the nonnegative resource vector $A_j$. A **DLP selector** chooses any optimal allocation for each nonnegative average capacity vector.
--
--   The **hindsight value** is the expectation of the linear-program optimum after the total class demands are known. A one-window allocation accepts each ordered arrival independently with its class-specific probability when enough capacity remains. The **frequent re-solving value** applies this allocation in each unit period, recomputing the DLP from the remaining capacity divided by the periods left.
--
--   $$
--   v^{\mathrm{HO}}(T,C)=\mathbb E\bigl[\operatorname{LP}(C,\Lambda(T))\bigr],\qquad
--   v^{\mathrm{FR}}(T,C)=\operatorname{FR}_{T}(C).
--   $$
--
--   These definitions give the two values compared in Proposition 2 and can also support other network revenue-management bounds.
--
--   **Formalization Note** Positive rates and nonnegative revenues and consumption are the standing interpretation of Section 2, p. 7. The independent Poisson streams are represented by their superposition and independent class labels; independent Bernoulli marks implement the fixed acceptance probabilities within each window. The imported `RLPBidPrice.Unbiased.piValue` supplies both LP objectives.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Sec. 2 pp. 7–9; Algorithm 2 p. 11

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open Matrix Finset

namespace ResolvingNRM.FRLower

/-- The Poisson network revenue-management data of Section 2. Class indices are `Fin n`
and resource indices are `Fin m`. Positivity is the standing convention of p. 7. -/
structure Instance (n m : ℕ) where
  lam : Fin n → ℝ
  r : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  lam_pos : ∀ j, 0 < lam j
  r_nonneg : ∀ j, 0 ≤ r j
  A_nonneg : ∀ l j, 0 ≤ A l j

/-- Any optimal DLP selector, including arbitrary choices among ties. It is required only on
nonnegative capacity vectors, which are the states reached by the allocation policy. -/
def IsDLPSelector {n m : ℕ} (I : Instance n m)
    (sel : (Fin m → ℝ) → Fin n → ℝ) : Prop :=
  ∀ b : Fin m → ℝ, 0 ≤ b →
    (I.A *ᵥ sel b ≤ b ∧ 0 ≤ sel b ∧ sel b ≤ I.lam) ∧
      I.r ⬝ᵥ sel b = RLPBidPrice.Unbiased.piValue I.A I.r b I.lam

/-- A feasible optimizer of the deterministic LP at average capacity `b`. -/
def IsDLPOptimal {n m : ℕ} (I : Instance n m) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  I.A *ᵥ x ≤ b ∧ 0 ≤ x ∧ x ≤ I.lam ∧
    I.r ⬝ᵥ x = RLPBidPrice.Unbiased.piValue I.A I.r b I.lam

/-- Sum of the independent arrival rates. -/
def totalRate {n m : ℕ} (I : Instance n m) : ℝ := ∑ j, I.lam j

/-- One fixed-probability window, evaluated on its ordered marked arrivals. The Boolean
marks are the independent acceptance coins. -/
noncomputable def runWindow {n m : ℕ} (I : Instance n m) (c : Fin m → ℝ)
    (arrivals : List (Fin n × Bool)) : ℝ × (Fin m → ℝ) :=
  arrivals.foldl (fun s a =>
    if a.2 && decide (∀ l, I.A l a.1 ≤ s.2 l) then
      (s.1 + I.r a.1, fun l => s.2 l - I.A l a.1)
    else s) (0, c)

/-- Expected revenue in a window plus continuation value `W` at the final capacity.
The independent Poisson class processes are represented by their superposition: a
Poisson number of arrivals, independent class labels, and independent Bernoulli marks.
The zero-rate case is interpreted as an empty arrival sequence. -/
noncomputable def windowValue {n m : ℕ} (I : Instance n m) (ell : ℝ)
    (p : Fin n → ℝ) (c : Fin m → ℝ) (W : (Fin m → ℝ) → ℝ) : ℝ :=
  ∑' N : ℕ, ProbabilityTheory.poissonPMFReal (totalRate I * ell).toNNReal N *
    (∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      (∏ i : Fin N, I.lam (cls i) / totalRate I *
        (if coin i then p (cls i) else 1 - p (cls i))) *
      (let outcome := runWindow I c (List.ofFn (fun i : Fin N => (cls i, coin i)))
       outcome.1 + W outcome.2))

/-- Expected hindsight LP optimum (3) under independent Poisson demand counts. -/
noncomputable def hindsightValue {n m : ℕ} (I : Instance n m) (T : ℝ)
    (C : Fin m → ℝ) : ℝ :=
  ∑' k : Fin n → ℕ,
    (∏ j, ProbabilityTheory.poissonPMFReal (I.lam j * T).toNNReal (k j)) *
      RLPBidPrice.Unbiased.piValue I.A I.r C (fun j => (k j : ℝ))

/-- Algorithm 2, with `k` unit periods remaining. At the start of each period the
capacity is divided by `k`, the DLP is re-solved, and its per-class acceptance
probability is held fixed throughout the period. -/
noncomputable def frTail {n m : ℕ} (I : Instance n m)
    (sel : (Fin m → ℝ) → Fin n → ℝ) : ℕ → (Fin m → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, c =>
      windowValue I 1 (fun j => sel (fun l => c l / ((k + 1 : ℕ) : ℝ)) j / I.lam j)
        c (frTail I sel k)

end ResolvingNRM.FRLower



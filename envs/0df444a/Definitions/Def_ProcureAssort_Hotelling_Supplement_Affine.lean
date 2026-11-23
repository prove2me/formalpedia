-- Prove2me | Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine
-- name    : ProcureAssort_Hotelling_Supplement_Affine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:27:23.077737+00:00
-- url     : https://prove2.me/theorems/d5313dfc-6d9b-4861-ad32-02e1797e9811
-- title:
--   Affine centralized allocation, reduced pricing rows and the five RIOM clauses
-- statement:
--   For an affine market, the centralized allocation is demand at virtual-cost prices: $x^*(\theta)=d(N,v(\theta))$, with active set $Q(\theta)$. Demand coefficients are extended by zero outside the active coordinates. A row dependence in (20) is recorded separately for each active price column, omitting the last active demand row at each profile and retaining every interim-transfer row.
--
--   A **relaxation-is-optimal market (RIOM)** has finite coordinate sets $B_i\subseteq\Theta_i$. Each is a discrete interval, each has at least three members, and every profile in their product has every supplier active. For each supported type between $\max B_i$ and the largest type at which supplier $i$ is ever active, some profile with that type and supplier active is reachable from some profile in the box.
--
--   $$\widetilde\Theta=\prod_i B_i,\qquad Q(\theta)=N\quad(\theta\in\widetilde\Theta),\qquad |B_i|\ge3.$$
--
--   Reachability means that active sets decrease along a finite path and at most one coordinate changes among the next profile's active suppliers. Endpoints are existential, as in G.4. No Hotelling reachability definition is substituted.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Definitions G.1–G.4, (20), pp. 46–53

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Supplement_Types
import Definitions.Def_ProcureAssort_Hotelling_Supplement_QuadraticMarket

open scoped Classical

namespace ProcureAssort.Hotelling.Supplement

variable {n : ℕ}

noncomputable def affX (M : QuadraticMarket (Fin n)) (Θ : Fin n → Finset ℝ)
    (f : Fin n → ℝ → ℝ) (θ : Profile Θ) : Fin n → ℝ :=
  M.demand Finset.univ (vvec Θ f θ)

noncomputable def affQ (M : QuadraticMarket (Fin n)) (Θ : Fin n → Finset ℝ)
    (f : Fin n → ℝ → ℝ) (θ : Profile Θ) : Finset (Fin n) :=
  M.active (vvec Θ f θ)

/-- Lift active coefficients by zero outside the active set. -/
noncomputable def affA (M : QuadraticMarket (Fin n)) (Θ : Fin n → Finset ℝ)
    (f : Fin n → ℝ → ℝ) (θ : Profile Θ) (i j : Fin n) : ℝ :=
  if hi : i ∈ affQ M Θ f θ then
    if hj : j ∈ affQ M Θ f θ then M.faceA (affQ M Θ f θ) ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-- Keep every active demand row except the last in supplier order. -/
def ReducedRow (Q : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ Q ∧ ∃ j ∈ Q, i < j

/-- The coefficient equality (20), column by column. Transfer rows are unchanged,
including rows that happen to be zero. -/
def RowDependence {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (Q : Profile Θ → Finset (Fin n)) (x : Profile Θ → Fin n → ℝ)
    (A : Profile Θ → Fin n → Fin n → ℝ)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ) : Prop :=
  ∀ θ, ∀ j ∈ Q θ,
    (∑ i ∈ (Q θ).filter (fun i => ReducedRow (Q θ) i), a θ i * A θ i j) +
      b j (θ j) * probOthers f j θ * x θ j = 0

/-- Largest supported active type (finite maximum). If never active the value is 0;
RIOM's all-active box rules out this unused case. -/
noncomputable def activeUpper (Θ : Fin n → Finset ℝ)
    (Q : Profile Θ → Finset (Fin n)) (i : Fin n) : ℝ :=
  let S := (Θ i).filter (fun c => ∃ θ : Profile Θ, (θ i : ℝ) = c ∧ i ∈ Q θ)
  if h : S.Nonempty then S.max' h else 0

/-- Reachability for any constructed active set, with exactly the two path conditions
of §G.2. In particular it is not Hotelling Reachable. -/
def ModelReachable {Θ : Fin n → Finset ℝ} (Q : Profile Θ → Finset (Fin n))
    (start finish : Profile Θ) : Prop :=
  ∃ (K : ℕ) (s : ℕ → Profile Θ), s 0 = start ∧ s K = finish ∧
    ∀ k, 1 ≤ k → k ≤ K → Q (s k) ⊆ Q (s (k-1)) ∧
      ∀ i ∈ Q (s k), ∀ j ∈ Q (s k),
        s k i ≠ s (k-1) i → s k j ≠ s (k-1) j → i = j

/-- The five clauses of Definitions G.3–G.4, pp. 52–53. The acceptable set is
represented by its coordinate sets B; requiring their product to be all-active
encodes clauses 1 and 3, and order-convexity encodes clause 2. -/
def RIOM (Θ : Fin n → Finset ℝ) (Q : Profile Θ → Finset (Fin n)) : Prop :=
  ∃ B : Fin n → Finset ℝ,
    (∀ i, B i ⊆ Θ i) ∧
    (∀ i, ∀ a ∈ B i, ∀ b ∈ B i, ∀ c ∈ Θ i, a ≤ c → c ≤ b → c ∈ B i) ∧
    (∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → Q θ = Finset.univ) ∧
    (∀ i, 3 ≤ (B i).card) ∧
    (∀ i, ∀ c ∈ Θ i, (∀ b ∈ B i, b ≤ c) → c ≤ activeUpper Θ Q i →
      ∃ (finish start : Profile Θ), (finish i : ℝ) = c ∧ i ∈ Q finish ∧
        (∀ j, (start j : ℝ) ∈ B j) ∧ ModelReachable Q start finish)

end ProcureAssort.Hotelling.Supplement



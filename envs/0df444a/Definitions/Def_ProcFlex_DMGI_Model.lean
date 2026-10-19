-- Prove2me | Definitions.Def_ProcFlex_DMGI_Model
-- name    : ProcFlex_DMGI_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:36.955482+00:00
-- url     : https://prove2.me/theorems/0de1f03f-c231-442f-9303-ccdf52d8b21f
-- title:
--   Margin-category flexibility model, uncertainty sets, DMGI (4), and long chains
-- statement:
--   A system groups products into occupied categories with strictly increasing positive margins and gives each plant a nonnegative capacity. The profit LP is the finite bipartite program (1). A robust score minimizes $h(g(A,d),(\sum_{i\in S_t}d_i)_t)$ over a demand set $U$, where $h$ is strictly increasing in profit at fixed category totals.
--
--   A part-wise independently symmetric set is the Cartesian product of its category projections and is invariant under permutations that preserve categories. A perturbation set is symmetric around $\mu$ when its residual set $\{d-\mu:d\in U\}$ has that property. The dual margin group index $\delta^K_\mu(A)$ minimizes the objective in (4) over a level assignment and nonnegative plant dual variables with prescribed category counts $K$. The same file defines $P_0=0$, $\beta_{tr}=P_t-P_r$, the feasible count set $Q$, cumulative counts $H_{tr}$, the residual block sum, and cyclic long chains.
--
--   These definitions supply the common model used by every milestone and the goal.
--
--   **Formalization Note** Lean categories are zero-based; all $T$ margin categories are occupied. The positive-margin assumption is made explicit. The paper omits $z\ge0$ from (4) and (5), although its proof uses dual feasibility; the formal program includes it. A level assignment encodes the binary variables $w_{itr}$, and an arbitrary cyclic product order defines a long chain.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), pp. 10–20, §2, Definitions 2.1–2.2, (1)–(5)

import Mathlib
import Definitions.Def_ProcFlex_DMGI_ProfitLP

namespace ProcFlex.DMGI

open Finset

/-- §2: `m` plants, `n` products and `T` ordered margin categories.
Lean category `t` represents paper category `t+1`. -/
structure System (m n T : ℕ) where
  C : Fin m → ℝ
  P : Fin T → ℝ
  cat : Fin n → Fin T

def System.p {m n T : ℕ} (S : System m n T) (i : Fin n) : ℝ :=
  S.P (S.cat i)

def System.s {m n T : ℕ} (S : System m n T) (t : Fin T) : Finset (Fin n) :=
  univ.filter (fun i => S.cat i = t)

/-- The section's positive numbers of plants, products, and occupied margin
categories, nonnegative capacities, and strictly ordered margins. Positive margins
are made explicit as discussed in the mission notes. -/
def System.IsValid {m n T : ℕ} (S : System m n T) : Prop :=
  0 < m ∧ 0 < n ∧ 0 < T ∧
    (∀ j, 0 ≤ S.C j) ∧ StrictMono S.P ∧
    (∀ t, 0 < S.P t) ∧ (∀ t, (S.s t).Nonempty)

/-- Forget category structure to obtain the reusable profit LP (1). -/
def System.lpData {m n T : ℕ} (S : System m n T) : ProfitLPData m n :=
  ⟨S.C, S.p⟩

noncomputable def g {m n T : ℕ} (S : System m n T)
    (A : Design m n) (d : Fin n → ℝ) : ℝ :=
  S.lpData.value A d

def DualFeasible {m n T : ℕ} (S : System m n T)
    (A : Design m n) (y : Fin n → ℝ) (z : Fin m → ℝ) : Prop :=
  S.lpData.DualFeasible A y z

def dualObj {m n T : ℕ} (S : System m n T)
    (d : Fin n → ℝ) (y : Fin n → ℝ) (z : Fin m → ℝ) : ℝ :=
  S.lpData.dualObj d y z

/-- Total demand in category `t`. -/
def catSum {m n T : ℕ} (S : System m n T)
    (d : Fin n → ℝ) (t : Fin T) : ℝ :=
  ∑ i ∈ S.s t, d i

/-- The deterministic measure (2) associated with a function `h` strictly increasing
in its profit argument at every fixed vector of category demand totals. -/
noncomputable def f {m n T : ℕ} (S : System m n T)
    (h : ℝ → (Fin T → ℝ) → ℝ) (A : Design m n) (d : Fin n → ℝ) : ℝ :=
  h (g S A d) (catSum S d)

/-- The robust measure in §2.2. For nonempty compact uncertainty sets and continuous
`f`, the real infimum is attained. -/
noncomputable def Rf {m n T : ℕ} (S : System m n T)
    (h : ℝ → (Fin T → ℝ) → ℝ) (A : Design m n)
    (U : Set (Fin n → ℝ)) : ℝ :=
  sInf (f S h A '' U)

/-- Definition 2.1: independent category projections and closure under every
category-preserving permutation. -/
def IsPartwiseIndepSymmetric {m n T : ℕ} (S : System m n T)
    (E : Set (Fin n → ℝ)) : Prop :=
  (∀ x : Fin n → ℝ,
    (∀ t, ∃ e ∈ E, ∀ i, S.cat i = t → x i = e i) → x ∈ E) ∧
  (∀ e ∈ E, ∀ σ : Equiv.Perm (Fin n),
    (∀ i, S.cat (σ i) = S.cat i) → (e ∘ σ) ∈ E)

/-- Definition 2.2: the residual set about the fixed centre `μ` satisfies Definition 2.1. -/
def IsSymmetricAround {m n T : ℕ} (S : System m n T)
    (U : Set (Fin n → ℝ)) (μ : Fin n → ℝ) : Prop :=
  IsPartwiseIndepSymmetric S ((fun d => d - μ) '' U)

/-- Extended margins, with the paper's `P₀ = 0`. -/
def Pbar {m n T : ℕ} (S : System m n T) (r : Fin (T + 1)) : ℝ :=
  Fin.cases 0 S.P r

/-- `βₜᵣ = Pₜ - Pᵣ`, with Lean category `t` representing paper `t+1`. -/
def beta {m n T : ℕ} (S : System m n T)
    (t : Fin T) (r : Fin (T + 1)) : ℝ :=
  S.P t - Pbar S r

/-- The feasible parameter set `Q` on p. 18. Values `K t r` with `r > t` are unused. -/
def InQ {m n T : ℕ} (S : System m n T)
    (K : Fin T → Fin (T + 1) → ℕ) : Prop :=
  ∀ t, ∑ r ∈ univ.filter (fun r : Fin (T + 1) => r.val ≤ t.val), K t r ≤ (S.s t).card

/-- The binary indicator array `w` of (4) encoded by one level per product. -/
def IsLevelAssignment {m n T : ℕ} (S : System m n T)
    (K : Fin T → Fin (T + 1) → ℕ) (lv : Fin n → Fin (T + 1)) : Prop :=
  (∀ i, (lv i).val ≤ (S.cat i).val + 1) ∧
  (∀ t r, r.val ≤ t.val →
    (univ.filter (fun i => S.cat i = t ∧ lv i = r)).card = K t r)

/-- The integer program (4) with the omitted dual constraint `z ≥ 0` supplied.
Under `K ∈ Q`, `C ≥ 0`, and the model assumptions, this is a finite attained minimum. -/
noncomputable def dmgi {m n T : ℕ} (S : System m n T)
    (μ : Fin n → ℝ) (K : Fin T → Fin (T + 1) → ℕ)
    (A : Design m n) : ℝ :=
  sInf {v | ∃ (lv : Fin n → Fin (T + 1)) (z : Fin m → ℝ),
    IsLevelAssignment S K lv ∧ (∀ j, 0 ≤ z j) ∧
    (∀ a ∈ A, S.p a.2 ≤ beta S (S.cat a.2) (lv a.2) + z a.1) ∧
    v = ∑ i, μ i * beta S (S.cat i) (lv i) + ∑ j, S.C j * z j}

/-- The cumulative count `Hₜᵣ` on p. 18. -/
def H {T : ℕ} (K : Fin T → Fin (T + 1) → ℕ)
    (t : Fin T) (r : Fin (T + 1)) : ℕ :=
  ∑ j ∈ univ.filter (fun j : Fin (T + 1) => j.val ≤ r.val), K t j

/-- The residual block expression in Theorem 1 and Proposition 3. The category
enumeration is by increasing product index and the block bounds are zero-based. -/
noncomputable def blockSum {m n T : ℕ} (S : System m n T)
    (K : Fin T → Fin (T + 1) → ℕ) (ε : Fin n → ℝ) : ℝ :=
  ∑ t, ∑ r ∈ univ.filter (fun r : Fin (T + 1) => r.val ≤ t.val),
    beta S t r *
      ∑ q ∈ univ.filter (fun q : Fin (S.s t).card =>
        H K t r - K t r ≤ q.val ∧ q.val < H K t r),
        ε ((S.s t).orderEmbOfFin rfl q)

/-- A long chain on a fixed product set, with products arranged in cyclic order `π`. -/
def longChain {n : ℕ} (π : Equiv.Perm (Fin n)) : Design n n :=
  univ.image (fun j => (j, π j)) ∪
    univ.image (fun j => (j, π (finRotate n j)))

/-- High and low categories alternate along the cyclic product order. -/
def IsAlternate {n : ℕ} (S : System n n 2)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ j, S.cat (π j) ≠ S.cat (π (finRotate n j))

end ProcFlex.DMGI



-- Prove2me | Definitions.Def_KallenbergLP_AverageLP_Model
-- name    : KallenbergLP_AverageLP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:15:20.206347+00:00
-- url     : https://prove2.me/theorems/3de06a0b-4b46-4ed1-9532-038a2b0faac3
-- title:
--   The AMD-model of Chapter 4: stationary policies, average optimality, Blackwell optimality, the LP pair (4.2.10)/(4.2.11), and the representative (4.3.2)
-- statement:
--   This file fixes the objects of Sections 4.2–4.4 of Kallenberg's tract, on top of the published finite Markov decision model $M$ (state set $E$, nonempty finite action sets $A(i)$, rewards $r_{ia}$, transition probabilities $p_{iaj}\ge0$ with $\sum_j p_{iaj}=1$) and the published general policies $R$ (history-dependent and randomized).
--
--   1. **Stationary policies.** A stationary policy $\pi^\infty$ is given by weights $\pi_{ia}\ge0$ with $\sum_{a\in A(i)}\pi_{ia}=1$; its matrix and reward vector are $P(\pi)_{ij}=\sum_a p_{iaj}\pi_{ia}$ and $r(\pi)_i=\sum_a r_{ia}\pi_{ia}$. For a pure decision rule $f$, $P(f)_{ij}=p_{if(i)j}$ and $r(f)_i=r_{if(i)}$.
--   2. **Criteria.** $\phi_i(R)=\liminf_{T\to\infty}\frac1T\sum_{t=1}^T\sum_j\sum_a\mathbb P_R(X_t=j,Y_t=a\mid X_1=i)\,r_{ja}$, its lim sup version $\hat\phi_i(R)$ (4.2.9), and the AMD-value-vector $\phi_i=\sup_R\phi_i(R)$. A policy $R^*$ is *average optimal* if $\phi(R^*)=\phi$. For $0\leq\alpha<1$, the discounted reward is $v_i^\alpha(R)=\sum_{t\ge1}\alpha^{t-1}\sum_j\sum_a\mathbb P_R(X_t=j,Y_t=a\mid X_1=i)\,r_{ja}$, and $R^*$ is *Blackwell optimal* if for some $\alpha_0\in[0,1)$ it is $\alpha$-discounted optimal for every $\alpha\in[\alpha_0,1)$.
--   3. **Matrices.** $P^*(\pi)$ is the Cesàro limit of the powers of $P(\pi)$, $D(\pi)=(I-P(\pi)+P^*(\pi))^{-1}-P^*(\pi)$ is the deviation matrix, and $u(f^\infty)=D(f)r(f)$.
--   4. **Superharmonicity and the LP pair.** $\tilde\phi$ is AMD-superharmonic if some $\tilde u$ satisfies
--   $$\tilde\phi_i\ge\sum_jp_{iaj}\tilde\phi_j,\qquad \tilde\phi_i+\tilde u_i\ge r_{ia}+\sum_jp_{iaj}\tilde u_j\qquad(a\in A(i),\ i\in E).$$
--   For strictly positive weights $\beta_j$ with $\sum_j\beta_j=1$, the primal program (4.2.10) minimises $\sum_j\beta_j\tilde\phi_j$ over such pairs; the dual program (4.2.11) maximises $\sum_i\sum_a r_{ia}x_{ia}$ subject to $\sum_i\sum_a(\delta_{ij}-p_{iaj})x_{ia}=0$, $\sum_ax_{ja}+\sum_i\sum_a(\delta_{ij}-p_{iaj})y_{ia}=\beta_j$ and $x,y\ge0$. Also $E_x=\{i\mid\sum_ax_{ia}>0\}$, the selection rule of Theorem 4.2.4, and the weights $\pi_{ia}(x,y)$ of (4.3.1).
--   5. **Representatives.** A set $E_0$ is closed under $Q$ if $q_{ij}=0$ for $i\in E_0$, $j\notin E_0$. For a stationary policy, with ergodic sets $E_1,\dots,E_m$ and transient set $F$ of $P(\pi)$, the vector $\gamma$ of (4.3.3) and the vectors $x_{ia}(\pi)=[\beta^TP^*(\pi)]_i\pi_{ia}$, $y_{ia}(\pi)=[\beta^TD(\pi)+\gamma^TP^*(\pi)]_i\pi_{ia}$ of (4.3.2).
--
--   These are the shared vocabulary of every statement in this mission.
--
--   **Formalization Note** LP variables are indexed by the admissible pairs $\{(i,a)\mid a\in A(i)\}$, so extreme points of the feasible set are the book's extreme feasible solutions. Average optimality is the book's lim inf notion, not the stronger Puterman notion `MarkovDecisionProcesses.IsAverageOptimal`. $P^*$ is defined with `limUnder` and $D$ with Mathlib's total matrix inverse; that the Cesàro limit exists and $I-P+P^*$ is nonsingular is Theorem 2.4.1, which no statement assumes. A state is recurrent when every state accessible from it leads back to it (published `IsRecurrent`); the ergodic set of a recurrent state is the set of states accessible from it.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 19–23, Section 2.2; p. 29, Definition 2.4.2; p. 34, Notation 2.5.1; pp. 97–102, Definition 4.2.1, (4.2.9)–(4.2.11); pp. 103, 108–109, (4.3.1)–(4.3.3)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A]

/-! ### Policies, criteria and optimality (§2.2, pp. 19–23)

The model `M : StationaryMDP S A` is the published finite model with stochastic rows
(`Σ_j p_iaj = 1`, the standing assumption of Chapter 4, p. 97). General (history-dependent,
randomized) policies are the published `AvgHRPolicy M`; the pure stationary policy `f^∞` is the
published `stationaryPolicy M f hf`. -/

/-- A **stationary (randomized) policy** `π^∞`: a decision rule `π` with `π_ia ≥ 0`,
`Σ_{a ∈ A(i)} π_ia = 1`, used at every epoch regardless of the history.
Kallenberg (1983), p. 20, §2.2.

**Formalization Note.** Weights outside the admissible set `A(i)` are required to be zero, so two
stationary policies are equal exactly when their weight functions agree. -/
structure StatPolicy (M : StationaryMDP S A) where
  weight : S → A → ℝ
  nonneg : ∀ i a, 0 ≤ weight i a
  supported : ∀ i a, a ∉ M.admissible i → weight i a = 0
  sum_one : ∀ i, ∑ a ∈ M.admissible i, weight i a = 1

/-- The stationary policy `π^∞` viewed as a general policy (it ignores the epoch and history). -/
def StatPolicy.toHR {M : StationaryMDP S A} (π : StatPolicy M) : AvgHRPolicy M where
  q := fun _ _ i a => π.weight i a
  nonneg := fun _ _ i a => π.nonneg i a
  sum_one := fun _ _ i => π.sum_one i

/-- The pure decision rule `f` (with `f(i) ∈ A(i)`) as a stationary randomized policy:
`π_ia = 1` if `a = f(i)` and `0` otherwise. -/
noncomputable def pureStat (M : StationaryMDP S A) [DecidableEq A] (f : S → A)
    (hf : ∀ i, f i ∈ M.admissible i) : StatPolicy M where
  weight := fun i a => if a = f i then 1 else 0
  nonneg := by intro i a; split_ifs <;> norm_num
  supported := by
    intro i a ha
    have : a ≠ f i := fun h => ha (h ▸ hf i)
    simp [this]
  sum_one := by
    intro i
    rw [Finset.sum_ite_eq' (M.admissible i) (f i) (fun _ => (1 : ℝ))]
    simp [hf i]

/-- The matrix `P(π)_ij = Σ_{a ∈ A(i)} p_iaj π_ia` of a weight function `π`. Kallenberg (1983),
p. 21. -/
noncomputable def weightMatrix (M : StationaryMDP S A) (w : S → A → ℝ) : Matrix S S ℝ :=
  Matrix.of fun i j => ∑ a ∈ M.admissible i, w i a * M.trans i a j

/-- `P(π)` of a stationary policy, p. 21. -/
noncomputable def P (M : StationaryMDP S A) (π : StatPolicy M) : Matrix S S ℝ :=
  weightMatrix M π.weight

/-- `r(π)_i = Σ_{a ∈ A(i)} r_ia π_ia`, p. 21. -/
noncomputable def r (M : StationaryMDP S A) (π : StatPolicy M) : S → ℝ :=
  fun i => ∑ a ∈ M.admissible i, π.weight i a * M.reward i a

/-- `P(f)_ij = p_{i f(i) j}` of a pure decision rule `f`, p. 21. -/
def Pf (M : StationaryMDP S A) (f : S → A) : Matrix S S ℝ :=
  Matrix.of fun i j => M.trans i (f i) j

/-- `r(f)_i = r_{i f(i)}` of a pure decision rule `f`, p. 21. -/
def rf (M : StationaryMDP S A) (f : S → A) : S → ℝ := fun i => M.reward i (f i)

/-- The **average reward** `φ_i(R) = liminf_{T→∞} (1/T) Σ_{t=1}^T Σ_j Σ_a P_R(X_t=j, Y_t=a | X_1=i) r_ja`
(p. 22): the published `gainInf`. -/
noncomputable abbrev phi {M : StationaryMDP S A} (R : AvgHRPolicy M) (i : S) : ℝ := gainInf R i

/-- The **lim sup average reward** `φ̂_i(R)` of (4.2.9), p. 101: the published `gainSup`. -/
noncomputable abbrev phiHat {M : StationaryMDP S A} (R : AvgHRPolicy M) (i : S) : ℝ := gainSup R i

/-- The **AMD-value-vector** `φ_i = sup_R φ_i(R)`, the supremum over all policies (p. 23): the
published `optGainInf`. It is a supremum of a nonempty family bounded by `max |r_ia|`. -/
noncomputable abbrev value (M : StationaryMDP S A) (i : S) : ℝ := optGainInf M i

/-- `R*` is **average optimal** if `φ(R*) = φ`, i.e. `φ_i(R*) = sup_R φ_i(R)` for every `i ∈ E`
(p. 23).

**Formalization Note.** This is the book's definition with the lim inf criterion; it is weaker
than the published `MarkovDecisionProcesses.IsAverageOptimal` (Puterman's (8.1.7)). -/
def IsAvgOptimal (M : StationaryMDP S A) (R : AvgHRPolicy M) : Prop :=
  ∀ i : S, gainInf R i = optGainInf M i

/-- The expected **discounted reward over the first `N` epochs**
`Σ_{t=1}^{N} α^{t−1} Σ_j Σ_a P_R(X_t=j, Y_t=a | X_1=i) r_ja`, for the policy `R` started at epoch
`t` after history `h` in state `s`; the same backward recursion as the published `totalReward`
with a factor `α` on the continuation. -/
noncomputable def discReward {M : StationaryMDP S A} (R : AvgHRPolicy M) (α : ℝ) :
    ℕ → ℕ → List (S × A) → S → ℝ
  | 0, _, _, _ => 0
  | (k + 1), t, h, s =>
      ∑ a ∈ M.admissible s, R.q t h s a *
        (M.reward s a + α * ∑ j, M.trans s a j * discReward R α k (t + 1) (h ++ [(s, a)]) j)

/-- The **expected discounted reward** `v_i^α(R) = Σ_{t=1}^∞ α^{t−1} Σ_j Σ_a P_R(X_t=j, Y_t=a | X_1=i) r_ja`
(p. 22), the limit of the `N`-epoch discounted rewards.

**Formalization Note.** `limUnder` is junk if the limit fails to exist; for `0 ≤ α < 1` the series
converges absolutely, and it is only used for such `α`. -/
noncomputable def discValue {M : StationaryMDP S A} (R : AvgHRPolicy M) (α : ℝ) (i : S) : ℝ :=
  limUnder atTop (fun N : ℕ => discReward R α N 0 [] i)

/-- `R*` is **α-discounted optimal**: `v^α(R*) = v^α = sup_R v^α(R)` (p. 22), stated as
`v_i^α(R) ≤ v_i^α(R*)` for every policy `R` and every state `i`. -/
def IsDiscOptimal (M : StationaryMDP S A) (α : ℝ) (R : AvgHRPolicy M) : Prop :=
  ∀ (R' : AvgHRPolicy M) (i : S), discValue R' α i ≤ discValue R α i

/-- `R*` is **Blackwell optimal** if for some `α₀ ∈ [0,1)` it is α-discounted optimal for every
`α ∈ [α₀, 1)` (p. 22). -/
def IsBlackwellOptimal (M : StationaryMDP S A) (R : AvgHRPolicy M) : Prop :=
  ∃ α₀ : ℝ, 0 ≤ α₀ ∧ α₀ < 1 ∧ ∀ α : ℝ, α₀ ≤ α → α < 1 → IsDiscOptimal M α R

/-! ### Stationary and deviation matrices (Definition 2.4.2, p. 29; Notation 2.5.1, p. 34) -/

section Matrices
variable [DecidableEq S]

/-- The **stationary matrix** `P*(π) = (c) lim_{n→∞} P(π)^n` (Cesàro limit), the published
`limitMatrix`. Its existence is Theorem 2.4.1(i). -/
noncomputable def Pstar (M : StationaryMDP S A) (π : StatPolicy M) : Matrix S S ℝ :=
  limitMatrix (P M π)

/-- The **deviation matrix** `D(π) = (I − P(π) + P*(π))^{-1} − P*(π)`, the published
`deviationMatrix`. Nonsingularity of `I − P + P*` is Theorem 2.4.1(iii). -/
noncomputable def Dev (M : StationaryMDP S A) (π : StatPolicy M) : Matrix S S ℝ :=
  deviationMatrix (P M π)

/-- `u(f^∞) := D(f) r(f)` of a pure decision rule `f`, (2.5.5), p. 34. -/
noncomputable def uPure (M : StationaryMDP S A) (f : S → A) : S → ℝ :=
  deviationMatrix (Pf M f) *ᵥ rf M f

end Matrices

/-! ### Superharmonicity and the pair of linear programs (§4.2, pp. 98–102) -/

/-- The set `Ā(i) = {a ∈ A(i) | φ̃_i = Σ_j p_iaj φ̃_j}` of (4.2.2), p. 97. -/
noncomputable def Abar (M : StationaryMDP S A) (φ : S → ℝ) (i : S) : Finset A := by
  classical
  exact (M.admissible i).filter (fun a => φ i = ∑ j, M.trans i a j * φ j)

/-- The pair `(φ̃, ũ)` satisfies (4.2.4) and (4.2.5):
`φ̃_i ≥ Σ_j p_iaj φ̃_j` and `φ̃_i + ũ_i ≥ r_ia + Σ_j p_iaj ũ_j` for all `a ∈ A(i)`, `i ∈ E`.
This is also the feasible set of the primal program (4.2.10). -/
def SuperharmonicPair (M : StationaryMDP S A) (φ u : S → ℝ) : Prop :=
  ∀ i : S, ∀ a ∈ M.admissible i,
    ∑ j, M.trans i a j * φ j ≤ φ i ∧ M.reward i a + ∑ j, M.trans i a j * u j ≤ φ i + u i

/-- **Definition 4.2.1** (p. 98): `φ̃ ∈ ℝ^N` is **AMD-superharmonic** if there is `ũ ∈ ℝ^N` with
(4.2.4) and (4.2.5). -/
def IsAMDSuperharmonic (M : StationaryMDP S A) (φ : S → ℝ) : Prop :=
  ∃ u : S → ℝ, SuperharmonicPair M φ u

/-- `(φ, u)` is an **optimal solution of the primal program (4.2.10)**,
`min {Σ_j β_j φ̃_j | (4.2.4), (4.2.5)}`: it is feasible and its objective is at most that of every
feasible pair. -/
def IsPrimalOptimal (M : StationaryMDP S A) (β : S → ℝ) (φ u : S → ℝ) : Prop :=
  SuperharmonicPair M φ u ∧
    ∀ φ' u' : S → ℝ, SuperharmonicPair M φ' u' → ∑ j, β j * φ j ≤ ∑ j, β j * φ' j

section LP
variable [DecidableEq A]

/-- The admissible state–action pairs `{(i, a) | i ∈ E, a ∈ A(i)}`, which index the variables
`x_ia`, `y_ia` of (4.2.11). -/
abbrev Pair (M : StationaryMDP S A) := {p : S × A // p.2 ∈ M.admissible p.1}

/-- `Σ_{a ∈ A(j)} x_ja` for a vector `x` indexed by the admissible pairs. -/
noncomputable def stateSum (M : StationaryMDP S A) [DecidableEq S] (x : Pair M → ℝ) (j : S) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Pair M => p.1.1 = j), x p

/-- The **feasible set of the dual program (4.2.11)** (p. 102): pairs `(x, y)` with
* `Σ_i Σ_a (δ_ij − p_iaj) x_ia = 0`, `j ∈ E`;
* `Σ_a x_ja + Σ_i Σ_a (δ_ij − p_iaj) y_ia = β_j`, `j ∈ E`;
* `x_ia, y_ia ≥ 0`, `a ∈ A(i)`, `i ∈ E`.

**Formalization Note.** Variables exist only for admissible pairs, so `Set.extremePoints` of this
set is the book's set of extreme feasible solutions. -/
def dualFeasible (M : StationaryMDP S A) [DecidableEq S] (β : S → ℝ) :
    Set ((Pair M → ℝ) × (Pair M → ℝ)) :=
  {z | (∀ j : S, ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.1 p = 0) ∧
       (∀ j : S, stateSum M z.1 j + ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.2 p = β j) ∧
       (∀ p : Pair M, 0 ≤ z.1 p ∧ 0 ≤ z.2 p)}

/-- The objective `Σ_i Σ_a r_ia x_ia` of (4.2.11). -/
def dualObjective (M : StationaryMDP S A) (x : Pair M → ℝ) : ℝ :=
  ∑ p : Pair M, M.reward p.1.1 p.1.2 * x p

/-- `(x, y)` is an **optimal solution of (4.2.11)**: feasible, and its objective is at least that of
every feasible pair. -/
def IsDualOptimal (M : StationaryMDP S A) [DecidableEq S] (β : S → ℝ)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) : Prop :=
  z ∈ dualFeasible M β ∧ ∀ z' ∈ dualFeasible M β, dualObjective M z'.1 ≤ dualObjective M z.1

/-- `E_x = {i ∈ E | Σ_a x_ia > 0}` (Notation 3.1.1, p. 36). -/
def Ex (M : StationaryMDP S A) [DecidableEq S] (x : Pair M → ℝ) : Set S :=
  {i | 0 < stateSum M x i}

/-- The **selection rule of Theorem 4.2.4** (p. 103): `f(i) = a_i` with `x_{i a_i} > 0` for
`i ∈ E_x` and `y_{i a_i} > 0` for `i ∈ E ∖ E_x`. -/
def IsSelection (M : StationaryMDP S A) [DecidableEq S] (x y : Pair M → ℝ)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) : Prop :=
  ∀ i : S, (i ∈ Ex M x → 0 < x ⟨(i, f i), hf i⟩) ∧ (i ∉ Ex M x → 0 < y ⟨(i, f i), hf i⟩)

/-- The weights `π_ia(x, y)` of (4.3.1), p. 108: `x_ia / Σ_a x_ia` for `i ∈ E_x` and
`y_ia / Σ_a y_ia` for `i ∈ E ∖ E_x` (and `0` for `a ∉ A(i)`). -/
noncomputable def dualPolicyWeight (M : StationaryMDP S A) [DecidableEq S]
    (x y : Pair M → ℝ) (i : S) (a : A) : ℝ := by
  classical
  exact if h : a ∈ M.admissible i then
    (if 0 < stateSum M x i then x ⟨(i, a), h⟩ / stateSum M x i
     else y ⟨(i, a), h⟩ / stateSum M y i)
  else 0

end LP

/-! ### Closed sets, ergodic sets and the representative (4.3.2)–(4.3.3) (pp. 25, 109) -/

/-- `E₀ ⊆ E` is **closed under** the matrix `Q` if `q_ij = 0` for `i ∈ E₀`, `j ∉ E₀` (p. 25). -/
def IsClosedUnder (Q : Matrix S S ℝ) (E₀ : Set S) : Prop :=
  ∀ i ∈ E₀, ∀ j ∉ E₀, Q i j = 0

/-- The **ergodic set containing** a state `i`: the states accessible from `i` under `Q`. For a
recurrent `i` (published `IsRecurrent`) this is the closed communicating class of `i`, one of the
ergodic sets `E₁, …, E_m` of p. 109. -/
noncomputable def ergodicClass (Q : Matrix S S ℝ) (i : S) : Finset S := by
  classical
  exact Finset.univ.filter (fun ℓ => Accessible Q i ℓ)

lemma mem_ergodicClass_self (Q : Matrix S S ℝ) (i : S) : i ∈ ergodicClass Q i := by
  classical
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩

section Representative
variable [DecidableEq S] [DecidableEq A]

/-- The vector `γ` of (4.3.3), p. 109: `γ_i = 0` for a transient state `i ∈ F` of `P(π)`, and for
`i` in the ergodic set `E_j`,
`γ_i = max_{ℓ ∈ E_j} { −Σ_k β_k d_kℓ(π) / Σ_{k ∈ E_j} p*_kℓ(π) }`. -/
noncomputable def gammaVec (M : StationaryMDP S A) (β : S → ℝ) (π : StatPolicy M) (i : S) : ℝ := by
  classical
  exact if IsRecurrent (P M π) i then
    (ergodicClass (P M π) i).sup' ⟨i, mem_ergodicClass_self _ i⟩
      (fun ℓ => -(∑ k, β k * Dev M π k ℓ) / ∑ k ∈ ergodicClass (P M π) i, Pstar M π k ℓ)
  else 0

/-- `x_ia(π) = [βᵀ P*(π)]_i · π_ia`, (4.3.2), p. 109. -/
noncomputable def xRep (M : StationaryMDP S A) (β : S → ℝ) (π : StatPolicy M) : Pair M → ℝ :=
  fun p => (Pstar M π).vecMul β p.1.1 * π.weight p.1.1 p.1.2

/-- `y_ia(π) = [βᵀ D(π) + γᵀ P*(π)]_i · π_ia`, (4.3.2), p. 109, with `γ` of (4.3.3). -/
noncomputable def yRep (M : StationaryMDP S A) (β : S → ℝ) (π : StatPolicy M) : Pair M → ℝ :=
  fun p => ((Dev M π).vecMul β p.1.1 + (Pstar M π).vecMul (gammaVec M β π) p.1.1) *
    π.weight p.1.1 p.1.2

end Representative

end KallenbergLP.AverageLP



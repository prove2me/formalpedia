-- Prove2me | Definitions.Def_BudgetedAffine_Disjoint_Construction
-- name    : BudgetedAffine_Disjoint_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:17:32.556975+00:00
-- url     : https://prove2.me/theorems/bf780972-9aaf-4007-91a9-c938d206818a
-- title:
--   Sec. 4.1–4.2, Algorithm 1, (4.5)–(4.7) — B̃, greedy scenario, thresholds I_ℓ, linear and static parts
-- statement:
--   Fix an instance of (1.1) over a disjoint constrained budgeted set with blocks $S_1,\dots,S_L$ and weights $w_{\ell i}$, and a first-stage decision $x^*$.
--
--   1. $\alpha_i=1-(Ax^*)_i$, and $\beta=\dfrac{8\log n}{\log\log n}$ (natural logarithm).
--   2. $\tilde B$ has $i$-th row $B_i/\alpha_i$ if $\alpha_i>0$ and $B_i$ otherwise; $\Theta$ denotes the covering value with $\tilde B$.
--   3. $\mathcal T=\{i:\alpha_i\le0\}$ and $\hat S_\ell=S_\ell\setminus\mathcal T$; $\mathcal U_\ell$ is the set of indicator vectors $\mathbb 1(b)$ with $b\subseteq\hat S_\ell$ and $\sum_{i\in b}w_{\ell i}\le1$.
--   4. **Algorithm 1 (greedy scenario).** Given an online covering algorithm $\mathcal A$ for $\tilde B$, a run chooses at step $\ell=1,\dots,L$ a block $\sigma(\ell)$ not chosen before and $a_\ell\in\mathcal U_{\sigma(\ell)}$ so that
--   $$\mathcal A(a_\ell\mid a_1,\dots,a_{\ell-1})\ \ge\ \mathcal A(b\mid a_1,\dots,a_{\ell-1})$$
--   for every block $s$ not chosen before step $\ell$ and every $b\in\mathcal U_s$. Here $\sigma$ is a bijection of the blocks; ties are arbitrary. Write $\nu_\ell=\mathcal A(a_1,\dots,a_\ell)$, so $\nu_0=0$.
--   5. **Thresholds.** For the block $\sigma(\ell)$ chosen at step $\ell$,
--   $$\mathcal I_\ell=\Big\{i\in S_{\sigma(\ell)}\ :\ \alpha_i>0\ \text{ and }\ \alpha_i z(e_i)\le w_{\sigma(\ell) i}\,\beta\,(\nu_\ell-\nu_{\ell-1})\Big\},\qquad \mathcal I=\bigcup_\ell\mathcal I_\ell,$$
--   where $z(e_i)$ is the covering value (3.2) with $B$.
--   6. **Linear part (4.5).** $y_{Lin}(h)=\sum_{i\in\mathcal I}\alpha_ih_iv_i$ for optimal covers $v_i$ of $e_i$; it equals $Ph$ for the matrix $P$ whose column $i$ is $\alpha_iv_i$ on $\mathcal I$ and $0$ elsewhere.
--   7. **Static part (4.6).** The static problem is $\min_{x\in\mathcal X,\,y\ge0}\{c^Tx+d^Ty : Ax+By\ge r\}$ with $r=\sum_{i\in\mathcal I^c}e_i+\sum_{i\in\mathcal I}(1-\alpha_i)^+e_i$; $z_{Sta}$ is its value and $(x_{Sta},y_{Sta})$ an optimal solution. The affine solution (4.7) is $x=x_{Sta}$, $y(h)=y_{Lin}(h)+y_{Sta}$.
--
--   These objects make up the affine policy whose cost Theorem 4.1 bounds.
--
--   **Formalization Note** The paper relabels the blocks "wlog" so that $a_\ell\in\mathcal U_\ell$ (p. 17); the Lean keeps the relabelling explicit as the bijection $\sigma$ and indexes steps from $0$. The threshold is written in the multiplied form $\alpha_iz(e_i)\le w\,\beta\,(\nu_\ell-\nu_{\ell-1})$ instead of dividing by $w_{\sigma(\ell)i}$, which may be $0$; for $w>0$ the two agree. The increments $\nu_\ell-\nu_{\ell-1}$ enter `Iset` as a function argument, instantiated with `nuInc alg a` in the theorems. The paper's sum $\sum_{i\in S_\ell}w_{\ell i}h_i$ in $\mathcal U_\ell$ equals $\sum_{i\in b}w_{\ell i}$ for $h=\mathbb 1(b)$ with $b\subseteq S_\ell$. $z_{Sta}$ is an extended-real infimum.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 4.1 p. 15, Sec. 4.2, Algorithm 1, (4.5), (4.6), (4.7), pp. 16–18

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Budget_Construction

namespace BudgetedAffine.Disjoint

open Matrix

/-- `β = 8 log n / log log n` (natural logarithm) of Sec. 4.2. -/
noncomputable def beta8 (n : ℕ) : ℝ :=
  8 * Real.log n / Real.log (Real.log n)

/-- `B̃` of Sec. 4.1: row `i` is `Bᵢ / αᵢ` if `αᵢ > 0` and `Bᵢ` otherwise. -/
noncomputable def Btil {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => if 0 < BudgetedAffine.Budget.alpha A x i then B i j / BudgetedAffine.Budget.alpha A x i else B i j

/-- `Ŝ_ℓ = S_ℓ ∩ Tᶜ` with `T = {i | αᵢ ≤ 0}`. -/
noncomputable def hatS {m n L : ℕ} (S : Fin L → Finset (Fin m)) (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (ℓ : Fin L) : Finset (Fin m) :=
  (S ℓ).filter fun i => 0 < BudgetedAffine.Budget.alpha A x i

/-- The prefix `(a₁, …, a_k)` of a sequence `a : Fin L → Finset (Fin m)`, as a list. -/
def seqPrefix {m L : ℕ} (a : Fin L → Finset (Fin m)) (k : ℕ) : List (Finset (Fin m)) :=
  (List.ofFn a).take k

/-- `ν_k = A(a₁, …, a_k)`, the online cost of the first `k` greedy scenarios (`ν₀ = A() = 0`). -/
def nu {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ} {ρ : ℝ}
    (alg : OnlineCover M d ρ) (a : Fin L → Finset (Fin m)) (k : ℕ) : ℝ :=
  alg.cost (seqPrefix a k)

/-- The increment `ν_ℓ − ν_{ℓ−1} = A(a_ℓ | a₁, …, a_{ℓ−1})` at (0-based) step `ℓ`. -/
def nuInc {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ} {ρ : ℝ}
    (alg : OnlineCover M d ρ) (a : Fin L → Finset (Fin m)) (ℓ : Fin L) : ℝ :=
  nu alg a (ℓ.val + 1) - nu alg a ℓ.val

/-- A run of Algorithm 1 (computing a greedy scenario `a`): at step `ℓ` the block `σ ℓ` is chosen
together with `a_ℓ = 𝟙(a ℓ) ∈ 𝒰_{σ ℓ}`, i.e. `a ℓ ⊆ Ŝ_{σ ℓ}` with `∑_{i ∈ a ℓ} w_{σ ℓ, i} ≤ 1`, and
the pair maximizes the online augmenting cost `A(b | a₁, …, a_{ℓ−1})` over every block `s` not
chosen at an earlier step and every `b ∈ 𝒰_s`. Here `Ŝ` is the family of sets `Ŝ_ℓ` (ties in
the arg max are arbitrary). -/
def IsGreedyRun {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ} {ρ : ℝ}
    (alg : OnlineCover M d ρ) (w : Fin L → Fin m → ℝ) (Shat : Fin L → Finset (Fin m))
    (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m)) : Prop :=
  (∀ ℓ, a ℓ ⊆ Shat (σ ℓ) ∧ ∑ i ∈ a ℓ, w (σ ℓ) i ≤ 1) ∧
    ∀ (ℓ s : Fin L), (∀ k : Fin L, k < ℓ → σ k ≠ s) →
      ∀ b ⊆ Shat s, ∑ i ∈ b, w s i ≤ 1 →
        alg.augCost (seqPrefix a ℓ.val) b ≤ alg.augCost (seqPrefix a ℓ.val) (a ℓ)

open Classical in
/-- The set `I = ⋃_ℓ I_ℓ` of Sec. 4.2, where, for the block `σ ℓ` chosen at step `ℓ` with increment
`Δ ℓ = ν_ℓ − ν_{ℓ−1}`, `I_ℓ = {i ∈ S_{σ ℓ} | αᵢ > 0 and αᵢ z(eᵢ) / w_{σ ℓ, i} ≤ β Δ ℓ}`, in the
multiplied form `αᵢ z(eᵢ) ≤ w_{σ ℓ, i} β Δ ℓ` (`z(eᵢ)` the `EReal` covering value with `B`,
`β = beta8 n`, `α` computed from the first-stage decision `x`). -/
noncomputable def Iset {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ) (x : Fin n → ℝ)
    (σ : Fin L ≃ Fin L) (Δ : Fin L → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    ∃ ℓ : Fin L, i ∈ S (σ ℓ) ∧ 0 < BudgetedAffine.Budget.alpha A x i ∧
      ((BudgetedAffine.Budget.alpha A x i : ℝ) : EReal) * BudgetedAffine.Budget.coverCost B d (Pi.single i 1) ≤
        ((w (σ ℓ) i * beta8 n * Δ ℓ : ℝ) : EReal)

end BudgetedAffine.Disjoint



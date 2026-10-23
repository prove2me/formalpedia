-- Prove2me | Definitions.Def_MNatOps_Monotone_Model
-- name    : MNatOps_Monotone_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:03.58647+00:00
-- url     : https://prove2.me/theorems/e69ffd88-d3be-483c-bf20-8b4d1fcb8864
-- title:
--   Definition 1 (p. 8), problem (3) and §2.2 (p. 10) — SSQM♮-concavity on Zᴷ, the box, optimal-solution sets, nonincreasing correspondences
-- statement:
--   This file fixes the objects of Section 2.2 of Chen and Li over the integers ($\mathcal F = \mathbb Z$).
--
--   **Directions.** For a finite index set $K$, let $\mathbf e_i \in \mathbb Z^K$ be the $i$-th unit vector and $\mathbf e_0 = 0$. For $i \in K$ and $j \in K \cup \{0\}$ the direction is $\mathbf e_i - \mathbf e_j$.
--
--   **SSQM♮-concavity (Definition 1, concave form).** A function $G : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$ has effective domain $\operatorname{dom} G = \{x : G(x) > -\infty\}$. It is *semistrictly quasi M♮-concave* if for all $x, y \in \operatorname{dom} G$ and every $i \in \operatorname{supp}^+(x - y)$ there exist $j \in \operatorname{supp}^-(x - y) \cup \{0\}$ and an integer $\alpha_0 > 0$ such that for every integer $\alpha \in [0, \alpha_0]$,
--   $$
--   G(x - \alpha(\mathbf e_i - \mathbf e_j)) > G(x) \ \text{ or } \ G(y + \alpha(\mathbf e_i - \mathbf e_j)) > G(y) \ \text{ or } \ G(x - \alpha(\mathbf e_i - \mathbf e_j)) = G(x) \text{ and } G(y + \alpha(\mathbf e_i - \mathbf e_j)) = G(y).
--   $$
--   This is the statement that $-G$ is SSQM♮-convex in the sense of Definition 1.
--
--   **The box and problem (3).** Given $l \in (\mathbb Z \cup \{-\infty\})^n$ and $u \in (\mathbb Z \cup \{+\infty\})^n$, the box is $B = \{a \in \mathbb Z^n : l_k \le a_k \le u_k \text{ for all } k\}$, and $l \le u$ means that each interval $[l_k, u_k]$ contains an integer. For $G : \mathbb Z^m \times \mathbb Z^n \to \mathbb R \cup \{-\infty\}$ and a parameter $s \in \mathbb Z^m$, $\mathcal A^*_B(s)$ is the set of optimal solutions of $\max\{G(s, a) : a \in B\}$. The set of parameters with a finite optimal value is $\{s : \text{some } a \in \mathcal A^*_B(s) \text{ has } G(s, a) > -\infty\}$.
--
--   **Nonincreasing correspondences (weak induced set ordering).** A correspondence $s \mapsto \mathcal A(s) \subseteq \mathbb Z^n$ is nonincreasing on a parameter set $S$ if for all $s, s' \in S$ with $s \le s'$: every $a \in \mathcal A(s)$ has some $a' \in \mathcal A(s')$ with $a' \le a$, and every $a' \in \mathcal A(s')$ has some $a \in \mathcal A(s)$ with $a' \le a$.
--
--   **Lower orthants.** For $a \in \mathbb Z^n$ and $0 \le i \le n$, $I_{\le, i}(a) = \{a' : a'_k \le a_k,\ k = 1, \dots, i\}$, with $I_{\le, 0}(a) = \mathbb Z^n$.
--
--   These are the objects of Theorem 3 and its proof.
--
--   **Formalization Note** The real case $\mathcal F = \mathbb R$ is not covered. The index $j = 0$ is `none : Option K`, the third alternative of Definition 1 ("both differences are $0$") is stated as two equalities, which is equivalent because $x, y \in \operatorname{dom} G$. Box ends are `WithBot ℤ` (lower) and `WithTop ℤ` (upper). The joint point $(s, a)$ is `Sum.elim s a : Fin m ⊕ Fin n → ℤ`, and the paper's coordinate $k$ is the `Fin n` index $k - 1$.
-- source:
--   Chen & Li, M♮-Convexity and Its Applications in Operations, SSRN 3431474 (PDF sha256 ea81b5d5…), pp. 5–11, notation (pp. 5–6), Definition 1 (p. 8), problem (3) and §2.2 (p. 10), proof of Theorem 3 (p. 11)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom

namespace MNatOps.Monotone

open DiscreteConvex.MConvexFunctions DiscreteConvex.EconomicEquilibrium

/-- The direction `e_i − e_j` in `Zᴷ` (Chen & Li, p. 6), where `j = none` stands for the zero
vector `e_0 = 0`, so that `dir i none = e_i`. -/
def dir {K : Type*} [DecidableEq K] (i : K) (j : Option K) : K → ℤ :=
  fun k => CharVec i k - j.elim 0 (fun j' => CharVec j' k)

/-- Definition 1 (Chen & Li, p. 8) in concave form over `F = Z`: `G : Zᴷ → R ∪ {−∞}` is
SSQM♮-concave (i.e. `−G` is SSQM♮-convex) if for all `x, y ∈ dom G` and every
`i ∈ supp⁺(x − y)` there are `j ∈ supp⁻(x − y) ∪ {0}` (`none` is `0`) and an integer `α₀ > 0`
such that for every integer `α ∈ [0, α₀]`, `G(x − α(e_i − e_j)) > G(x)`, or
`G(y + α(e_i − e_j)) > G(y)`, or both values are unchanged. -/
def SSQMNatConcave {K : Type*} [Fintype K] [DecidableEq K] (G : (K → ℤ) → WithBot ℝ) : Prop :=
  ∀ x ∈ UDom G, ∀ y ∈ UDom G, ∀ i ∈ SuppPos x y,
    ∃ j : Option K, (j = none ∨ ∃ j', j = some j' ∧ j' ∈ SuppNeg x y) ∧
      ∃ α₀ : ℤ, 0 < α₀ ∧ ∀ α : ℤ, 0 ≤ α → α ≤ α₀ →
        G x < G (x - α • dir i j) ∨ G y < G (y + α • dir i j) ∨
          (G (x - α • dir i j) = G x ∧ G (y + α • dir i j) = G y)

/-- Membership in the integer box `B = [l, u] ∩ Zⁿ` with `l, u ∈ [−∞, +∞]ⁿ` (p. 10): lower ends
in `WithBot ℤ` (`⊥ = −∞`), upper ends in `WithTop ℤ` (`⊤ = +∞`). -/
def inBox {n : ℕ} (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (a : Fin n → ℤ) : Prop :=
  ∀ k, l k ≤ (a k : WithBot ℤ) ∧ (a k : WithTop ℤ) ≤ u k

/-- The condition `l ≤ u` of p. 10 for an integer box: every coordinate interval
`[l_k, u_k]` contains an integer. -/
def BoxNonempty {n : ℕ} (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) : Prop :=
  ∀ k, ∃ z : ℤ, l k ≤ (z : WithBot ℤ) ∧ (z : WithTop ℤ) ≤ u k

/-- `A*_B(s)`: the set of optimal solutions of problem (3), `max G(s, a)` s.t. `a ∈ B` (p. 10).
The joint point `(s, a) ∈ Zᵐ × Zⁿ` is `Sum.elim s a`. -/
def optSet {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (l : Fin n → WithBot ℤ)
    (u : Fin n → WithTop ℤ) (s : Fin m → ℤ) : Set (Fin n → ℤ) :=
  {a | inBox l u a ∧ ∀ a', inBox l u a' → G (Sum.elim s a') ≤ G (Sum.elim s a)}

/-- The parameters `s` for which problem (3) has an optimal solution with a finite optimal value
`G(s, a) > −∞`. -/
def finiteParams {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (l : Fin n → WithBot ℤ)
    (u : Fin n → WithTop ℤ) : Set (Fin m → ℤ) :=
  {s | ∃ a ∈ optSet G l u s, G (Sum.elim s a) ≠ ⊥}

/-- "`A(s)` is nonincreasing in `s ∈ S`" in the weak induced set ordering (p. 10): for
`s ≤ s'` in `S`, every `a ∈ A(s)` has some `a' ∈ A(s')` with `a' ≤ a`, and every `a' ∈ A(s')`
has some `a ∈ A(s)` with `a' ≤ a`. -/
def IsNonincreasingOn {m n : ℕ} (A : (Fin m → ℤ) → Set (Fin n → ℤ)) (S : Set (Fin m → ℤ)) :
    Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≤ s' →
    (∀ a ∈ A s, ∃ a' ∈ A s', a' ≤ a) ∧ (∀ a' ∈ A s', ∃ a ∈ A s, a' ≤ a)

/-- `I_{≤,i}(a) = {a' : a'_k ≤ a_k, k = 1, …, i}` (proof of Theorem 3, p. 11). The paper's
coordinate `k` is the `Fin n` index with value `k − 1`, so `lowerOrthant a 0 = Zⁿ` and
`lowerOrthant a n = {a' | a' ≤ a}`. -/
def lowerOrthant {n : ℕ} (a : Fin n → ℤ) (i : ℕ) : Set (Fin n → ℤ) :=
  {a' | ∀ k : Fin n, k.val < i → a' k ≤ a k}

end MNatOps.Monotone



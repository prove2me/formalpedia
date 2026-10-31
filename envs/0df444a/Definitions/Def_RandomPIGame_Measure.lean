-- Prove2me | Definitions.Def_RandomPIGame_Measure
-- name    : RandomPIGame_Measure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:41.75906+00:00
-- url     : https://prove2.me/theorems/39a29d7a-a989-4670-8cc3-d859c5794708
-- title:
--   The map $g:\Pi\to\Omega$, the measure $\mathbb P_p$, and the conditions (2.4)–(2.5) and [1]–[2]
-- statement:
--   Let $\Pi=S^H$, and write $\pi=(\xi_\pi,\iota_\pi,\gamma_\pi)$ for an element of $\Pi$. The tree $T_\pi$ is defined recursively: $\oslash\in T_\pi$, and if $h\in T_\pi$ then $(h,j)\in T_\pi$ if and only if $1\le j\le\xi_\pi(h)$. The map $g:\Pi\to\Omega$ is
--   $$
--   g(\pi)=(T_\pi,\ \iota_\pi|_{T_\pi},\ \gamma_\pi|_{T_\pi}),
--   $$
--   and $\mathbb P_p$ is the distribution of $g$ under the product measure $\bigotimes_H p$: the triple at each node is drawn from $p$, independently across nodes.
--
--   The same definition records two predicates on a measure $\mathbb P$ on $\Omega$.
--
--   1. **(2.4)–(2.5).** $\mathbb P(E(i,k,0))=p_i(k,0)$, and
--   $$
--   \mathbb P\Big(E(i,k,n)\cap\bigcap_{j=1}^n\{\omega(j)\in B_j\}\Big)=p_i(k,n)\prod_{j=1}^n\mathbb P(B_j)
--   $$
--   for $i\in\{\mathrm I,\mathrm{II}\}$, $k\ge0$, $n\ge1$ and Borel $B_1,\dots,B_n\subseteq\Omega$.
--   2. **[1]–[2].** $(\iota(\oslash),\gamma(\oslash),\xi(\oslash))$ has law $p$; and for each $(i,k,n)\in S$ with $n\ge1$ and $p_i(k,n)>0$, the games $\omega(1),\dots,\omega(n)$ are independent under $\mathbb P(\cdot\mid E(i,k,n))$, each with law $\mathbb P$.
--
--   $\mathbb P_p$ generalizes the Galton-Watson measure on ordered trees to trees marked by players and capacities.
--
--   **Formalization Note** `Measure.infinitePi` is the product measure. `Measure.map` returns $0$ on a non-measurable map; $g$ is measurable, and this is the first clause of `RandomPIGame.section2_measure`. An index `j : Fin n` stands for $j+1\in\{1,\dots,n\}$.
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, p.8, (2.4)–(2.5), [1]–[2]

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RandomPIGame

noncomputable section

/-- The recursive definition of the tree `T_π` of `π ∈ Π = S^H`: `⊘ ∈ T_π`, and if `h ∈ T_π` then
`(h, j) ∈ T_π` if and only if `1 ≤ j ≤ ξ_π(h)`. arXiv:2104.10528v1, §2, p.8. -/
inductive InTree (π : H → S) : H → Prop
  | nil : InTree π []
  | snoc {h : H} {j : ℕ+} : InTree π h → (j : ℕ) ≤ (π h).2.2 → InTree π (h ++ [j])

theorem InTree.of_snoc {π : H → S} {l : H} (hl : InTree π l) :
    ∀ (h : H) (j : ℕ+), l = h ++ [j] → InTree π h ∧ (j : ℕ) ≤ (π h).2.2 := by
  cases hl with
  | nil =>
      intro h j hnil
      simp at hnil
  | @snoc h' j' hh' hj' =>
      intro h j he
      obtain ⟨rfl, hj⟩ := List.append_inj' he (by simp)
      have : j' = j := by simpa using hj
      subst this
      exact ⟨hh', hj'⟩

theorem InTree.prefix {π : H → S} {h : H} : ∀ {h' : H}, InTree π (h ++ h') → InTree π h := by
  intro h'
  induction h' using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
      intro hl
      have : InTree π ((h ++ l) ++ [a]) := by simpa [List.append_assoc] using hl
      exact ih (this.of_snoc _ _ rfl).1

/-- `T_π` is an ordered tree with `ξ(h) = ξ_π(h)`. arXiv:2104.10528v1, §2, p.8. -/
theorem isOrderedTree_inTree (π : H → S) : IsOrderedTree {h | InTree π h} :=
  ⟨⟨InTree.nil, fun _ _ hh => InTree.prefix hh⟩, fun h hh =>
    ⟨(π h).2.2, fun _ => ⟨fun hj => (InTree.of_snoc hj _ _ rfl).2, fun hj => InTree.snoc hh hj⟩⟩⟩

/-- The map `g : Π → Ω`, `g(π) = (T_π, ι_π|T_π, γ_π|T_π)`, where `Π = S^H`.
arXiv:2104.10528v1, §2, p.8. -/
def g (π : H → S) : Game where
  T := {h | InTree π h}
  isOrderedTree := isOrderedTree_inTree π
  ι h := (π h.1).1
  γ h := (π h.1).2.1

/-- The measure `P_p` on `Ω`: the distribution of `g` under the product measure `⊗_H p` on `Π`.
arXiv:2104.10528v1, §2, p.8.

**Formalization Note.** `Measure.map` returns `0` on a map that is not measurable. The map `g` is
Borel measurable; this is the first clause of `RandomPIGame.section2_measure`. -/
def gameMeasure (p : Measure S) [IsProbabilityMeasure p] : Measure Game :=
  (Measure.infinitePi fun _ : H => p).map g

/-- The equalities (2.4) and (2.5) for a measure `P` on `Ω`:
`P(E(i, k, 0)) = p_i(k, 0)`, and
`P(E(i, k, n) ∩ ⋂_{j=1}^n {ω(j) ∈ B_j}) = p_i(k, n) ∏_{j=1}^n P(B_j)`
for `i ∈ {I, II}`, `k ≥ 0`, `n ≥ 1` and Borel `B₁, …, Bₙ`. arXiv:2104.10528v1, §2, p.8, (2.4)–(2.5).

**Formalization Note.** The index `j : Fin n` stands for `j + 1 ∈ {1, …, n}`, and `B j` for
`B_{j+1}`. The equalities are between real numbers (`Measure.real`), which is faithful for the
finite measures to which this is applied. -/
def SatisfiesEquations (p : Measure S) (P : Measure Game) : Prop :=
  (∀ (i : Player) (k : ℝ≥0), P.real (E i k 0) = pMass p i k 0) ∧
    ∀ (i : Player) (k : ℝ≥0) (n : ℕ), 1 ≤ n → ∀ B : Fin n → Set Game,
      (∀ j, MeasurableSet (B j)) →
        P.real (E i k n ∩ ⋂ j : Fin n, {ω | ω.child j.val.succPNat ∈ B j}) =
          pMass p i k n * ∏ j : Fin n, P.real (B j)

/-- The conditions [1] and [2] for a measure `P` on `Ω`: the random variable `(ι(⊘), γ(⊘), ξ(⊘))` is
distributed according to `p`; and for each `(i, k, n) ∈ S` with `n ∈ ℕ₊`, if `p_i(k, n) > 0`, then
`ω(1), …, ω(n)` are independent under `P(· | E(i, k, n))`, and each is distributed according to `P`.
arXiv:2104.10528v1, §2, p.8, [1]–[2].

**Formalization Note.** The index `j : Fin n` stands for `j + 1 ∈ {1, …, n}`. `P[|E i k n]` is
Mathlib's conditional measure. -/
def SatisfiesConditions (p : Measure S) (P : Measure Game) : Prop :=
  P.map rootData = p ∧
    ∀ (i : Player) (k : ℝ≥0) (n : ℕ), 1 ≤ n → 0 < pMass p i k n →
      iIndepFun (fun (j : Fin n) (ω : Game) => ω.child j.val.succPNat) (P[|E i k n]) ∧
        ∀ j : Fin n, (P[|E i k n]).map (fun ω : Game => ω.child j.val.succPNat) = P

end

end RandomPIGame



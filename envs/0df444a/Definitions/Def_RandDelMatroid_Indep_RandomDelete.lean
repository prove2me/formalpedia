-- Prove2me | Definitions.Def_RandDelMatroid_Indep_RandomDelete
-- name    : RandDelMatroid_Indep_RandomDelete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:28:26.289617+00:00
-- url     : https://prove2.me/theorems/0eb6fafb-6214-4733-9a2b-ab2e412499d5
-- title:
--   Algorithm 1 (Random-Delete): law of the returned set
-- statement:
--   Algorithm 1 receives a matroid $M=(E,\mathcal I)$ with $m=|E|$ elements and a positive integer $g$. It sets $p=1-m^{-40/g}$, deletes every element of $E$ independently with probability $p$, and returns the set $R$ of remaining elements. Thus every element is **kept** independently with probability
--
--   $$q=m^{-40/g},$$
--
--   and for every $S\subseteq E$,
--
--   $$\Pr[R=S]=q^{|S|}(1-q)^{m-|S|}.$$
--
--   For a family $\mathcal A$ of subsets, $\Pr[R\in\mathcal A]=\sum_{S\subseteq E,\ S\in\mathcal A} q^{|S|}(1-q)^{m-|S|}$. This is the probability space of Theorem 1 and of Lemmas 17 and 19.
--
--   **Formalization Note** `keepProb m g` is the real power `(m : ℝ) ^ (-(40 : ℝ) / g)`; for $m\ge2$ and $g\ge1$ it lies in $(0,1)$. `randomDeleteProb E g A` is the exact finite sum above over the subsets of the finset `E`; `alg1Prob M g A` applies it to the (finite) ground set of `M`. No conditioning or renormalisation is involved. (For $g=0$, which never occurs since circuits are nonempty, Lean's `x / 0 = 0` would give $q=1$.)
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 3, Algorithm 1; p. 2

import Mathlib

set_option autoImplicit false

namespace RandDelMatroid.Indep

open Finset

noncomputable section

/-- Algorithm 1 (p. 3): the probability with which each element is **kept**, `q = m^(-40/g)`
(the algorithm deletes each element with probability `p = 1 - m^(-40/g)`). Real power. -/
def keepProb (m g : ℕ) : ℝ := (m : ℝ) ^ (-(40 : ℝ) / (g : ℝ))

/-- Algorithm 1 (p. 3) on a finite ground set `E` with parameter `g`: every element of `E` is kept
independently with probability `q = keepProb |E| g`, and `R` is the set of kept elements. This is
`Pr[R ∈ A]` for an event `A` (a family of subsets), computed exactly from the product law:
`Pr[R = S] = q^|S| (1-q)^(|E|-|S|)` for every `S ⊆ E`. -/
def randomDeleteProb {β : Type} (E : Finset β) (g : ℕ) (A : Set (Set β)) : ℝ := by
  classical
  exact ∑ S ∈ E.powerset.filter (fun T : Finset β => ((T : Set β) ∈ A)),
    keepProb E.card g ^ (Finset.card S) * (1 - keepProb E.card g) ^ (E.card - Finset.card S)

/-- `Pr[R ∈ A]` for the set `R` returned by Algorithm 1 run on the finite matroid `M` with
parameter `g` (ground set `E = M.E`, `m = |E|`). -/
def alg1Prob {β : Type} (M : Matroid β) [M.Finite] (g : ℕ) (A : Set (Set β)) : ℝ :=
  randomDeleteProb M.ground_finite.toFinset g A

end

end RandDelMatroid.Indep



-- Prove2me | Definitions.Def_SubmodMFG_Supplement_ConstrainedFlows
-- name    : SubmodMFG_Supplement_ConstrainedFlows
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:20:12.837824+00:00
-- url     : https://prove2.me/theorems/fb290af5-3584-5ce5-8f57-954c4833140c
-- title:
--   Measurable flows $L^0_{st}$ and the constrained lattice $\mathcal L$ of §3
-- statement:
--   Let $(S,\mathcal S,\pi)$ be a measure space.
--
--   1. $L^0_{st}$ is the set of measurable maps $\mu=(\mu_t)_{t\in S}:S\to\mathcal M_{\le1}$, ordered by $\mu\le\nu$ if and only if $\mu_t\le_{st}\nu_t$ for $\pi$-a.e. $t$.
--   2. A set $K\subseteq\mathcal M_{\le1}$ is a **Dedekind σ-complete sublattice** if it is closed under the lattice operations $\vee_{st},\wedge_{st}$ of $\mathcal M_{\le1}$ and contains the $\mathcal M_{\le1}$-supremum (infimum) of every nonempty countable subset of $K$ having an upper (lower) bound in $K$.
--   3. Given sets $L_n\subseteq\mathcal M_{\le1}$ and $B_n\in\mathcal S$, $n\in\mathbb N$, the **constrained lattice** is
--   $$\mathcal L=\{\mu\in L^0_{st}:\ \pi(\{t\in S:\mu_t\notin L_n\}\cap B_n)=0\ \text{for all }n\},$$
--   the flows with $\mu_t\in L_n$ for $\pi$-a.e. $t\in B_n$, with the order of $L^0_{st}$.
--
--   **Formalization Note** Elements are representatives and the order is a preorder; its antisymmetrization is the paper's space of $\pi$-a.e. classes. The reading of "Dedekind σ-complete sublattice" (bounds within $K$, suprema and infima in $\mathcal M_{\le1}$) follows Example 3.2 b), p.10; it covers every example listed there, including $K=\mathcal P(\mathbb R)$. The measure of a possibly non-measurable set is its outer measure.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §3, pp.9–10 (L⁰_st, Example 3.2 b), the set 𝓛)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb

open MeasureTheory

namespace SubmodMFG.Supplement

/-- **Measurable flows `L⁰_st`.** Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for
Submodular Mean Field Games*, arXiv:2201.07850v1, §3, p.9: "Let (S, 𝒮, π) be a σ-finite measure
space. We denote … the lattice of all equivalence classes of 𝒮-B(M≤1)-measurable functions
S → M≤1 by L⁰_st = L⁰(S, 𝒮, π; M≤1). … On L⁰_st we consider the order relation ≤_{L⁰_st},
given by µ ≤ ν if and only if µ_t ≤st ν_t for π-a.a. t ∈ S."

**Formalization Note.** An element is a measurable representative `µ : S → M≤1`; the order is
the preorder "`µ_t ≤st ν_t` for `π`-a.e. `t`", whose antisymmetrization is the quotient by
`π`-a.e. equality. The type depends on `π` only through its order. -/
def L0st {S : Type*} [MeasurableSpace S] (_π : Measure S) : Type _ :=
  {μ : S → SubProb // Measurable μ}

/-- The order `≤_{L⁰_st}` (p.9): `µ_t ≤st ν_t` for `π`-a.e. `t`. -/
instance {S : Type*} [MeasurableSpace S] (π : Measure S) : Preorder (L0st π) where
  le μ ν := ∀ᵐ t ∂π, μ.1 t ≤ ν.1 t
  le_refl μ := Filter.Eventually.of_forall fun t => le_refl _
  le_trans μ ν ρ h₁ h₂ := by
    filter_upwards [h₁, h₂] with t ht₁ ht₂ using ht₁.trans ht₂

/-- **Dedekind σ-complete sublattice of `M≤1`**, §3, p.9 ("a family (Lₙ)ₙ∈ℕ of Dedekind
σ-complete sublattices of M≤1"), read as in Example 3.2 b), p.10 ("a property that carries over
to suprema and infima of countably many elements of L"): `K` is closed under the lattice
operations `∨st`, `∧st` of `M≤1`, and contains the `M≤1`-supremum (infimum) of every nonempty
countable subset of `K` that has an upper (lower) bound in `K`.

**Formalization Note.** Suprema and infima are taken in `M≤1` (`IsLUB`/`IsGLB` for `≤st`). The
bound is required to lie in `K`: this is the reading under which every example of Example 3.2 b)
qualifies (for `K = P(ℝ)`, a countable family of probability measures bounded below by a
probability measure has a probability measure as infimum). -/
def IsSigmaSublattice (K : Set SubProb) : Prop :=
  (∀ a ∈ K, ∀ b ∈ K, ∀ c : SubProb, IsLUB {a, b} c → c ∈ K) ∧
  (∀ a ∈ K, ∀ b ∈ K, ∀ c : SubProb, IsGLB {a, b} c → c ∈ K) ∧
  (∀ C ⊆ K, C.Countable → C.Nonempty → (∃ u ∈ K, u ∈ upperBounds C) →
      ∀ c : SubProb, IsLUB C c → c ∈ K) ∧
  (∀ C ⊆ K, C.Countable → C.Nonempty → (∃ l ∈ K, l ∈ lowerBounds C) →
      ∀ c : SubProb, IsGLB C c → c ∈ K)

/-- **The lattice `𝓛` of constrained flows**, §3, p.10: "𝓛 := {µ ∈ L⁰_st | ∀n ∈ ℕ:
π({t ∈ S | µ_t ∉ Lₙ} ∩ Bₙ) = 0}. That is, the set of all measurable flows (µ_t)_{t∈S} of
sub-probability measures such that, for all n ∈ ℕ, µ_t ∈ Lₙ for π-a.a. t ∈ Bₙ."

**Formalization Note.** A subset of `L0st π`; as a type it carries the induced preorder. The
measure of the possibly non-measurable set `{t | µ_t ∉ Lₙ} ∩ Bₙ` is its outer measure. -/
def constrainedFlows {S : Type*} [MeasurableSpace S] (π : Measure S)
    (Ln : ℕ → Set SubProb) (Bn : ℕ → Set S) : Set (L0st π) :=
  {μ | ∀ n : ℕ, π ({t | μ.1 t ∉ Ln n} ∩ Bn n) = 0}

end SubmodMFG.Supplement



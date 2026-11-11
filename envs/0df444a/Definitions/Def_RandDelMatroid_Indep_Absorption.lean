-- Prove2me | Definitions.Def_RandDelMatroid_Indep_Absorption
-- name    : RandDelMatroid_Indep_Absorption
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:30:12.7669+00:00
-- url     : https://prove2.me/theorems/669fd810-6e62-471d-93bf-513de0902573
-- title:
--   Matroid absorption data (the conclusion of Lemma 11)
-- statement:
--   Fix a clean unordered decomposition tree, a node $u$, components $Q_1,\dots,Q_k$ attached to $u$ through 2- or 3-sums with boundary sets $S_1,\dots,S_k$, the subtree $Q$ formed by $u$, these components and their connecting edges, and completions $P_{Q_i,s}$. An **absorption** at $u$ is a matroid $\hat M_u=(\hat E_u,\hat{\mathcal I}_u)$ with nonnegative weights $w:\hat E_u\to\mathbb R_{\ge0}$ and a map $D\mapsto\hat D$ such that
--
--   1. $E_u\cap E_Q\subseteq \hat E_u$ and $|\hat E_u|=|E_u|$;
--   2. $D\mapsto\hat D$ is a bijection from the circuits $D$ of $M_u$ with $|D\cap S_i|\le1$ for all $i$ onto the circuits of $\hat M_u$, and corresponding circuits satisfy $D\cap(E_u\cap E_Q)=\hat D\cap(E_u\cap E_Q)$ and $w(\hat D)=|D^+\setminus Z|$;
--   3. $\hat M_u$ is graphic if $M_u$ is graphic, cographic if $M_u$ is cographic but not graphic, and isomorphic to $R_{10}$ if $M_u$ is.
--
--   Here $Z$ is a set of elements whose contribution is not counted: Lemma 11 is the case $Z=\emptyset$, where $w(\hat D)=|D^+|$; §5.2 uses $Z=S_u$ (the parent boundary), where $w_u(\hat D)=|D^+\setminus S_u|$ counts exactly the elements of $E$ in the expansion.
--
--   **Formalization Note** $\hat M_u$ is a matroid on `β ⊕ ℕ`: an element `x` of $M_u$ appears as `Sum.inl x`, and `Sum.inr` provides the fresh labels the construction introduces (the new vertex edges of the graphic and cographic cases). $\hat E_u$ is required to be finite, so that $|\hat E_u|$ is a genuine cardinality. Weights are `ℝ≥0` (the Δ–Y weights are half-integers). `w(D̂)` is the finite sum `setWeight w D̂`.
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 18, §4.1; p. 20, Lemma 11; p. 26, §5.2

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_DecompTree

set_option autoImplicit false

namespace RandDelMatroid.Indep

open scoped NNReal

variable {β ι : Type}

/-- §4.1 (p. 18): the subtree `Q` formed by the node `u`, the components attached to `u` through
the neighbours `v ∈ K`, and their connecting edges. -/
noncomputable def absorbedSubtree (T : SimpleGraph ι) [Fintype ι] [DecidableEq ι] (u : ι)
    (K : Finset ι) : Finset ι :=
  insert u (K.biUnion (attachedComp T u))

/-- The union `S₁ ∪ ⋯ ∪ S_k` of the boundary sets of the selected components (neighbours in `K`). -/
def selBoundary (Mn : ι → Matroid β) (u : ι) (K : Finset ι) : Set β :=
  ⋃ v ∈ K, edgeBoundary Mn u v

/-- The conclusion of Lemma 11 (p. 20), with an extra set `Z` of elements whose weight is not
counted (Lemma 11 itself uses `Z = ∅`; §5.2 uses `Z = S_u`). The absorbed matroid
`M̂_u = (Ê_u, Î_u)` is `Mh` on `β ⊕ ℕ`: an element `x ∈ β` of `M_u` is `Sum.inl x`, and `Sum.inr`
supplies fresh labels for the new elements. With `X = E_u ∩ E_Q` and `B = S₁ ∪ ⋯ ∪ S_k`:
1. `X ⊆ Ê_u` and `|Ê_u| = |E_u|` (and `Ê_u` is finite);
2. `corr` is a bijection from the circuits `D` of `M_u` with `|D ∩ Sᵢ| ≤ 1` for all selected `i`
   onto the circuits `D̂` of `M̂_u`, with `D̂ ∩ X = D ∩ X` and `w(D̂) = |D⁺ \ Z|`;
3. `M̂_u` is graphic if `M_u` is graphic, cographic if `M_u` is cographic but not graphic, and
   isomorphic to `R10` if `M_u` is. -/
def IsAbsorptionData (T : SimpleGraph ι) [Fintype ι] [DecidableEq ι] (Mn : ι → Matroid β)
    (u : ι) (K : Finset ι) (P : β → Set β) (Z : Set β) (Mh : Matroid (β ⊕ ℕ))
    (w : β ⊕ ℕ → ℝ≥0) (corr : Set β → Set (β ⊕ ℕ)) : Prop :=
  Mh.E.Finite ∧
    Sum.inl '' ((Mn u).E ∩ groundOf Mn (absorbedSubtree T u K)) ⊆ Mh.E ∧
    Mh.E.ncard = (Mn u).E.ncard ∧
    Set.BijOn corr
      {D | (Mn u).IsCircuit D ∧ ∀ v ∈ K, (D ∩ edgeBoundary Mn u v).ncard ≤ 1}
      {Dh | Mh.IsCircuit Dh} ∧
    (∀ D : Set β, (Mn u).IsCircuit D → (∀ v ∈ K, (D ∩ edgeBoundary Mn u v).ncard ≤ 1) →
      corr D ∩ Sum.inl '' ((Mn u).E ∩ groundOf Mn (absorbedSubtree T u K)) =
          Sum.inl '' (D ∩ ((Mn u).E ∩ groundOf Mn (absorbedSubtree T u K))) ∧
        setWeight w (corr D) = ((expansion D (selBoundary Mn u K) P \ Z).ncard : ℝ)) ∧
    (IsGraphic (Mn u) → IsGraphic Mh) ∧
    (IsCographic (Mn u) → ¬ IsGraphic (Mn u) → IsCographic Mh) ∧
    (IsR10 (Mn u) → IsR10 Mh)

end RandDelMatroid.Indep



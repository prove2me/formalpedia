-- Prove2me | Definitions.Def_LiftSAParity_blocks
-- name    : LiftSAParity_blocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:49.127825+00:00
-- url     : https://prove2.me/theorems/625e0225-7f89-473a-a760-3e6f98d80975
-- title:
--   The block-selection procedure $I(J,A)$ and its pivots $I^\star(J,A)$
-- statement:
--   Fix $n,\ell,d$, a nonempty affine space $A\subseteq\mathbb F_2^{n\times\ell}$ and $J=(J_1,\dots,J_n)\in[\ell]^n$ ($J_i$ is the stifled coordinate of block $i$). Let $A_{\mathrm{hom}}$ be the direction space of $A$. Start with $I=\emptyset$; while $|I|<d$ and $A_{\mathrm{hom}}$ is not the whole space on its remaining coordinates:
--
--   1. let $i$ be the smallest block containing a variable with nonzero coefficient in a defining homogeneous equation for $A_{\mathrm{hom}}$;
--   2. replace $A_{\mathrm{hom}}$ by the projection of $A_{\mathrm{hom}}\cap\{y:y_{i,k}=0\text{ for every }k\neq J_i\}$ onto the coordinates outside block $i$, and add $i$ to $I$.
--
--   The final $I$ is $I(J,A)$; it has at most $d$ blocks, and $|I(J,A)|=d$ is the cutoff event. Block $i$ is a **pivot** when $y_{i,J_i}$ appears in a defining constraint of the current $A_{\mathrm{hom}}$ at the moment $i$ is processed; $I^\star(J,A)$ is the set of pivots.
--
--   **Formalization Note** The procedure is run on the space $U$ of coefficient vectors of linear forms constant on $A$ (the annihilator of $A_{\mathrm{hom}}$): step 1 takes the least block $i$ on which some $u\in U$ is nonzero, step 2 replaces $U$ by $\{u$ with block $i$ zeroed $: u\in U,\ u_{i,J_i}=0\}$, and the loop stops when $U\subseteq\{0\}$. So $I(J,A)$ depends on $A$ only through $A_{\mathrm{hom}}$. The loop is iterated $d$ times, enough to reach its final state.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.1, p.13, steps (1)–(2); §4.2, p.14 (pivots)

import Mathlib
import Definitions.Def_LiftSAParity_IsAffineSpace

namespace LiftSAParity

open Classical

/-- The **constraint space** of a set `A ⊆ 𝔽₂^{n×ℓ}`: the coefficient vectors `w` of the linear
forms `y ↦ ∑_v w_v y_v` that are constant on `A`. For a nonempty affine space this is the
annihilator of the direction space `A_hom` (§2, p.7: "the linear forms that are constant on A
form a subspace of dimension cd A, which depends only on A"), i.e. the span of the homogeneous
defining equations of `A_hom`. -/
def constSpace {n ℓ : ℕ} (A : Set (Fin n × Fin ℓ → ZMod 2)) : Set (Fin n × Fin ℓ → ZMod 2) :=
  {w | ∀ x ∈ A, ∀ y ∈ A, ∑ v, w v * x v = ∑ v, w v * y v}

/-- Block `i` is constrained by `U`: some vector of `U` has a nonzero coefficient on a variable
of block `i`. -/
def BlockConstrained {n ℓ : ℕ} (U : Set (Fin n × Fin ℓ → ZMod 2)) (i : Fin n) : Prop :=
  ∃ u ∈ U, ∃ k, u (i, k) ≠ 0

/-- Step (1) of the block-selection procedure (de Rezende–Engström–Shekhovtsov, *Lifting
Sherali-Adams Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…),
§4.1, p.13): "Let i be the smallest block containing a variable with nonzero coefficient in a
defining homogeneous equation for A_hom." `none` when no block is constrained, i.e. "A_hom is the
whole space on its remaining coordinates". -/
noncomputable def firstBlock {n ℓ : ℕ} (U : Set (Fin n × Fin ℓ → ZMod 2)) : Option (Fin n) :=
  if h : (Finset.univ.filter (BlockConstrained U)).Nonempty then
    some ((Finset.univ.filter (BlockConstrained U)).min' h) else none

/-- Step (2) (§4.1, p.13): "Replace A_hom by the projection of A_hom ∩ {y : y_{i,k} = 0 for every
k ≠ J_i} onto the coordinates outside block i." On constraint spaces, the annihilator of that
projection is `{u with block i zeroed : u ∈ U, u_{i,J_i} = 0}` (a vector of the new space is
indexed by all of `[n] × [ℓ]` and vanishes on block `i`). -/
def stepSpace {n ℓ : ℕ} (J : Fin n → Fin ℓ) (i : Fin n) (U : Set (Fin n × Fin ℓ → ZMod 2)) :
    Set (Fin n × Fin ℓ → ZMod 2) :=
  (fun u => fun v => if v.1 = i then 0 else u v) '' {u | u ∈ U ∧ u (i, J i) = 0}

/-- The state of the block-selection procedure: the current constraint space, the processed
blocks `I`, and the pivot blocks `I⋆`. -/
structure SelState (n ℓ : ℕ) where
  /-- the current constraint space (annihilator of the current `A_hom`) -/
  U : Set (Fin n × Fin ℓ → ZMod 2)
  /-- the processed blocks -/
  I : Finset (Fin n)
  /-- the pivot blocks: processed blocks `i` whose stifled variable `y_{i,J_i}` appears in a
  defining constraint of the current `A_hom` when `i` is processed -/
  piv : Finset (Fin n)

/-- One iteration of the procedure (§4.1, p.13): "while |I| < d and A_hom is not the whole space
on its remaining coordinates perform the following two steps"; otherwise the state is final. -/
noncomputable def selStep {n ℓ : ℕ} (d : ℕ) (J : Fin n → Fin ℓ) (s : SelState n ℓ) :
    SelState n ℓ :=
  if s.I.card < d then
    match firstBlock s.U with
    | none => s
    | some i =>
      { U := stepSpace J i s.U
        I := insert i s.I
        piv := if ∃ u ∈ s.U, u (i, J i) ≠ 0 then insert i s.piv else s.piv }
  else s

/-- The final state of the block-selection procedure started from the constraint space of `A`.
At most `d` iterations change the state (each adds a block and the loop stops at `|I| = d`), so
`d` iterations reach the final state. -/
noncomputable def selRun {n ℓ : ℕ} (d : ℕ) (J : Fin n → Fin ℓ) (A : Set (Fin n × Fin ℓ → ZMod 2)) :
    SelState n ℓ :=
  (selStep d J)^[d] ⟨constSpace A, ∅, ∅⟩

/-- **The selected blocks `I(J, A)`** (§4.1, p.13): "Denote the final set I of processed blocks
by I(J, A)." It depends on `A` only through its constraint space, i.e. through `A_hom` (p.14:
"I(J, A) depends only on J and A_hom").

**Formalization Note** "Smallest block" is the order of `Fin n`. The procedure is run on the
annihilator `U` of `A_hom` instead of on `A_hom`: a variable has a nonzero coefficient in some
defining homogeneous equation iff some `u ∈ U` is nonzero there, and `A_hom` is the whole space
on the remaining coordinates iff `U ⊆ {0}`. The cutoff `d` is part of the definition. -/
noncomputable def blocks {n ℓ : ℕ} (d : ℕ) (J : Fin n → Fin ℓ) (A : Set (Fin n × Fin ℓ → ZMod 2)) :
    Finset (Fin n) :=
  (selRun d J A).I

/-- **The pivot blocks `I⋆(J, A)`** (§4.2, p.14): "let I⋆(J, A) be the set of blocks i such that
y_{i,J_i} appears in any of the defining constraints of A_hom. We call these pivot iterations."
Here `A_hom` is the current space at the moment block `i` is processed. -/
noncomputable def pivots {n ℓ : ℕ} (d : ℕ) (J : Fin n → Fin ℓ) (A : Set (Fin n × Fin ℓ → ZMod 2)) :
    Finset (Fin n) :=
  (selRun d J A).piv

end LiftSAParity



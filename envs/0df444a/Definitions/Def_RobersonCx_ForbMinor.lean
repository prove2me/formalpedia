-- Prove2me | Definitions.Def_RobersonCx_ForbMinor
-- name    : RobersonCx_ForbMinor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:16.990365+00:00
-- url     : https://prove2.me/theorems/6ab26cbe-ba7f-44bb-bfd8-3e7b8b43cb93
-- title:
--   $\mathrm{Forb}_{\mathrm m}(H)$, $\mathrm{Forb}_{\mathrm{imm}}(H)$, and closure under minors, immersions and disjoint unions
-- statement:
--   For a graph $H$,
--   $$\mathrm{Forb}_{\mathrm m}(H)=\{F : H\text{ is not a minor of }F\},\qquad \mathrm{Forb}_{\mathrm{imm}}(H)=\{F : H\text{ does not immerse in }F\}.$$
--   Here $H$ is a **minor** of $F$ (Definition 12) if there are pairwise disjoint nonempty vertex sets $M_h\subseteq V(F)$ ($h\in V(H)$), each inducing a connected subgraph, with an edge of $F$ between $M_h$ and $M_{h'}$ for every edge $hh'$ of $H$; immersion is the weak immersion of Definition 3.
--
--   A class $\mathcal F$ is **closed under minors** (resp. **immersions**) if every graph that is a minor of (resp. immerses in) a member of $\mathcal F$ is itself in $\mathcal F$, and **closed under disjoint unions** if $F_1\sqcup F_2\in\mathcal F$ whenever $F_1,F_2\in\mathcal F$.
--
--   These are the classes and closure properties of the Strong Roberson Conjecture and its immersion analogue, which Theorems 2 and 11 refute.
--
--   **Formalization Note** Minor is the published `HadwigerConj.IsMinor`, which is Definition 12 word for word (Mathlib's `Connected` includes nonemptiness). The disjoint union is Mathlib's `G ⊕g F` on `V ⊕ U`. Closure is quantified over all simple graphs on finite types in `Type`.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §1.1 p.3 (PDF p.5); Theorem 11 p.10 (PDF p.12); Definition 12 p.13 (PDF p.15)

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_RobersonCx_InCl
import Definitions.Def_RobersonCx_IsImmersion

set_option autoImplicit false

namespace RobersonCx

/-- `Forb_m(H) = {F : H is not a minor of F}` (§1.1, p.3 (PDF p.5)), as a graph class.

**Formalization Note** "Minor" is the published `HadwigerConj.IsMinor` (branch sets: pairwise disjoint sets
inducing connected, hence nonempty, subgraphs, with an edge between the branch sets of every edge of `H`),
which is Definition 12 (p.13) verbatim. -/
def ForbMinor {W : Type*} (H : SimpleGraph W) : GraphClass :=
  fun _ _ F => ¬ HadwigerConj.IsMinor H F

/-- `Forb_imm(H) = {F : H does not immerse in F}` (§1.1, p.3 (PDF p.5)), with the weak immersion of
Definition 3. -/
def ForbImm {W : Type*} (H : SimpleGraph W) : GraphClass :=
  fun _ _ F => ¬ IsImmersion H F

/-- `𝓕` is closed under minors: every minor of a member is a member (Theorem 11, p.10 (PDF p.12)). -/
def MinorClosed (𝓕 : GraphClass) : Prop :=
  ∀ (V U : Type) [Finite V] [Finite U] (G : SimpleGraph V) (F : SimpleGraph U),
    𝓕 V G → HadwigerConj.IsMinor F G → 𝓕 U F

/-- `𝓕` is closed under immersions: every graph immersing in a member is a member (Theorem 11, p.10
(PDF p.12)). -/
def ImmersionClosed (𝓕 : GraphClass) : Prop :=
  ∀ (V U : Type) [Finite V] [Finite U] (G : SimpleGraph V) (F : SimpleGraph U),
    𝓕 V G → IsImmersion F G → 𝓕 U F

/-- `𝓕` is closed under disjoint unions: `F₁ ⊔ F₂ ∈ 𝓕` whenever `F₁, F₂ ∈ 𝓕` (Theorem 11, p.10 (PDF p.12)).

**Formalization Note** The disjoint union is Mathlib's `G ⊕g F` on `V ⊕ U`. -/
def DisjUnionClosed (𝓕 : GraphClass) : Prop :=
  ∀ (V U : Type) [Finite V] [Finite U] (G : SimpleGraph V) (F : SimpleGraph U),
    𝓕 V G → 𝓕 U F → 𝓕 (V ⊕ U) (G ⊕g F)

end RobersonCx



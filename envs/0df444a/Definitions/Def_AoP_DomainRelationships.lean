-- Prove2me | Definitions.Def_AoP_DomainRelationships
-- name    : AoP_DomainRelationships
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T09:18:18.829805+00:00
-- url     : https://prove2.me/theorems/d52c5498-2630-4769-8433-3a5a21cd43ed
-- title:
--   Assumptions of Physics II.2: dependence, equivalence, causal relationships, combined domains
-- statement:
--   Definitions for Part II, Chapter 2 of *Assumptions of Physics* (Carcassi–Aidala, v3.0), on top of the Chapter 1 vocabulary (statements as truth sets $s\subseteq\Omega$; equivalence of statements is equality of truth sets).
--
--   **Inference relationship and dependence (Definitions 2.1, 2.2).** An inference relationship between $\mathcal D_X$ and $\mathcal D_Y$ is a map $r:\mathcal D_Y\to\mathcal D_X$ with $r(s_Y)\equiv s_Y$; $\mathcal D_Y$ *depends on* $\mathcal D_X$, written $\mathcal D_Y\subseteq\mathcal D_X$, if such a map exists.
--
--   **Domain equivalence (Definition 2.4).** $\mathcal D_X\equiv\mathcal D_Y$ if each depends on the other.
--
--   **Causal relationship (Definition 2.7).** A function $f: X\to Y$ between the possibilities with $x\preccurlyeq f(x)$ for all $x\in X$.
--
--   **Combined domain (Definition 2.13).** For a countable family $\{\mathcal D_{X_i}\}$, the experimental domain generated from all their statements by finite conjunction and countable disjunction; the definition carries the proof (as in the source) that it has a countable basis. The family is indexed by an arbitrary countable type, so finite families are included.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 2 (pp. 149–168), Definitions 2.1, 2.2, 2.4, 2.7, 2.13 (pp. 150–156)

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

/-!
# Assumptions of Physics, Part II, Chapter 2: relationships between experimental domains

Source: G. Carcassi, C. A. Aidala, *Assumptions of Physics*, Ver. 3.0 (December 31, 2025),
Part II, Chapter 2 "Domain combination and relationships", Sections 2.1–2.2.

Statements are truth sets `s : Set Ω` over the possible assignments `Ω` of a fixed logical
context, as in the Chapter 1 definitions (`Def_AoP_ExperimentalDomains`); in particular two
statements are equivalent exactly when they are equal as sets.
-/

namespace AssumptionsOfPhysics

universe u

namespace ExperimentalDomain

variable {Ω : Type u}

/-- Definitions 2.1 and 2.2: `DY` depends on `DX` (`DY ⊆ DX`) if there is an inference
relationship `r : DY → DX`, i.e. a map with `r(s) ≡ s` for every `s ∈ DY`. -/
def DependsOn (DY DX : ExperimentalDomain Ω) : Prop :=
  ∃ r : DY.stmts → DX.stmts, ∀ s : DY.stmts, (r s : Set Ω) = s

/-- Definition 2.4: two experimental domains are equivalent if each depends on the other. -/
def DomainEquiv (DX DY : ExperimentalDomain Ω) : Prop :=
  DependsOn DX DY ∧ DependsOn DY DX

/-- Definition 2.7: a causal relationship between `DX` and `DY` is a function `f : X → Y`
between the possibilities such that `x ≼ f(x)` for every `x ∈ X`. -/
def IsCausalRel (DX DY : ExperimentalDomain Ω) (f : DX.Possibility → DY.Possibility) : Prop :=
  ∀ x : DX.Possibility, x.val ⊆ (f x).val

lemma finConjCountDisj_mono {B C : Set (Set Ω)} (h : ∀ s ∈ B, FinConjCountDisj C s)
    {s : Set Ω} (hs : FinConjCountDisj B s) : FinConjCountDisj C s := by
  induction hs with
  | basic hb => exact h _ hb
  | univ => exact .univ
  | empty => exact .empty
  | inter _ _ ih₁ ih₂ => exact .inter ih₁ ih₂
  | iUnion f _ ih => exact .iUnion f ih

/-- Definition 2.13: the combined experimental domain of a countable family of experimental
domains (on the same logical context): the statements generated from all statements of all
the domains by finite conjunction and countable disjunction. -/
noncomputable def combined {ι : Type*} [Countable ι] (Dfam : ι → ExperimentalDomain Ω) :
    ExperimentalDomain Ω where
  stmts := {s | FinConjCountDisj (⋃ i, (Dfam i).stmts) s}
  univ_mem := FinConjCountDisj.univ
  empty_mem := FinConjCountDisj.empty
  inter_mem _ _ hs ht := FinConjCountDisj.inter hs ht
  iUnion_mem f hf := FinConjCountDisj.iUnion f hf
  exists_countable_basis := by
    choose B hBc hB using fun i => (Dfam i).exists_countable_basis
    refine ⟨⋃ i, B i, Set.countable_iUnion hBc, ?_, ?_⟩
    · intro s hs
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
      exact FinConjCountDisj.basic (Set.mem_iUnion.mpr ⟨i, (hB i).1 hi⟩)
    · intro s hs
      refine finConjCountDisj_mono (fun t ht => ?_) hs
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      exact finConjCountDisj_mono
        (fun b hb => FinConjCountDisj.basic (Set.mem_iUnion.mpr ⟨i, hb⟩)) ((hB i).2 t hi)

end ExperimentalDomain

end AssumptionsOfPhysics



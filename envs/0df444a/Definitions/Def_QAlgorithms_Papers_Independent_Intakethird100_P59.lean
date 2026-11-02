-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P59
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P59
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:25:45.383122+00:00
-- url     : https://prove2.me/theorems/5caed185-8f50-4962-98ca-0f7f6e738c4d
-- title:
--   Definitions for Mapping stacks of topological stacks
-- statement:
--   The objects the formalized statements of *Mapping stacks of topological stacks* (arXiv:0809.2373) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `KProduct`: Compactly generated product, as required by the conventions on PDF pp.3,7.
--   - `KSubspace`: Subspace in CGTop: compact generation of the ordinary induced topology.
--   - `RightAction`: A right action; PDF p.12 explicitly uses right, rather than left, torsors.
--   - `IsRightPrincipal`: A locally trivial right principal bundle over a CGTop base (PDF p.12). Local charts are equivariant homeomorphisms over an open subset of the base; no global section, nonempty base, connectedness, or Hausdorffness is required.
--   - `CylinderPullback`: The pullback of a bundle along [0,1] × T → T, with its CGTop topology (PDF p.12, Lemma 7.1). The action is on the last coordinate.
--   - `singletonRightAction`: Sanity check: the singleton group acts on the singleton from the right.
--   - `twistedLoopSet`: Continuous twisted loops, using the conjugation direction printed on PDF p.13. The domain is the whole real line, not merely [0,1].
--   - `basedTwistedLoopSet`: Based twisted loops have value 1 at time zero (PDF p.14).
--   - `identityBasedTwistedLoopSet`: Twisted loops into the identity path component, with the restriction of Ad(alpha). Alpha itself need not lie in that component (PDF p.14). Equality is checked in G, so no ill-typed alpha : G0 is introduced.
--   - `includeIdentityLoop`: Inclusion of continuous loops in the identity path component into G. Only the map of underlying continuous functions is needed for the equality.
-- source:
--   Mapping stacks of topological stacks, arXiv:0809.2373v2, https://arxiv.org/abs/0809.2373v2

import Mathlib

/-!
Local ordinary-space interfaces for Noohi, Mapping stacks of topological stacks,
arXiv:0809.2373v2. Stack-valued results with missing interfaces are inventoried
in this unit's HARD.md and GAPS.json. Compilation is pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P59

universe u v

/-- Compactly generated product, as required by the conventions on PDF pp.3,7. -/
def KProduct (X : Type u) (Y : Type v) := X × Y

/-- The product carries the compact generation of its ordinary product topology. -/
instance (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (KProduct X Y) :=
  TopologicalSpace.compactlyGenerated.{max u v} (X × Y)

/-- Subspace in CGTop: compact generation of the ordinary induced topology. -/
def KSubspace (X : Type u) (s : Set X) := s

/-- Compactly generated subspace topology, without a separation assumption. -/
instance (X : Type u) [TopologicalSpace X] (s : Set X) :
    TopologicalSpace (KSubspace X s) :=
  TopologicalSpace.compactlyGenerated.{u} s

/-- A right action; PDF p.12 explicitly uses right, rather than left, torsors. -/
structure RightAction (G : Type u) (E : Type v) [Group G] where
  act : E → G → E
  act_one : ∀ e, act e 1 = e
  act_mul : ∀ e g h, act (act e g) h = act e (g * h)

/-- A locally trivial right principal bundle over a CGTop base (PDF p.12).
Local charts are equivariant homeomorphisms over an open subset of the base;
no global section, nonempty base, connectedness, or Hausdorffness is required. -/
def IsRightPrincipal {G E B : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (a : RightAction G E) : Prop :=
  Continuous (fun z : KProduct E G => a.act z.1 z.2) ∧
  (∀ e g, p (a.act e g) = p e) ∧
  ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
    ∃ chart : KSubspace E (p ⁻¹' U) ≃ₜ KProduct (KSubspace B U) G,
      (∀ z, (chart z).1.1 = p z.1) ∧
      ∀ (z : KSubspace E (p ⁻¹' U)) (g : G),
        ∃ hz : a.act z.1 g ∈ KSubspace E (p ⁻¹' U),
          chart (⟨a.act z.1 g, hz⟩ : KSubspace E (p ⁻¹' U)) =
            ((chart z).1, (chart z).2 * g)

/-- The pullback of a bundle along [0,1] × T → T, with its CGTop topology
(PDF p.12, Lemma 7.1). The action is on the last coordinate. -/
abbrev CylinderPullback {Q T : Type u} [TopologicalSpace Q] [TopologicalSpace T]
    (q : C(Q, T)) :=
  KSubspace (KProduct ((Set.Icc (0 : ℝ) 1) × T) Q)
    {z | z.1.2 = q z.2}

/-- Sanity check: the singleton group acts on the singleton from the right. -/
def singletonRightAction : RightAction PUnit PUnit where
  act := fun _ _ => PUnit.unit
  act_one := fun _ => Subsingleton.elim _ _
  act_mul := fun _ _ _ => rfl

/-- Sanity check: the point over the point is a principal bundle, including
its local trivialization and equivariance. -/
example : IsRightPrincipal (ContinuousMap.const PUnit PUnit.unit)
    singletonRightAction := by
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_const
  · intro e g
    rfl
  · intro b
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ b, ?_⟩
    letI : Unique (KSubspace PUnit (Set.univ : Set PUnit)) :=
      { default := ⟨PUnit.unit, Set.mem_univ _⟩
        uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
    letI : Unique (KProduct (KSubspace PUnit (Set.univ : Set PUnit)) PUnit) :=
      { default := (default, PUnit.unit)
        uniq := fun z => by
          apply Prod.ext
          · exact Subsingleton.elim _ _
          · exact Subsingleton.elim _ _ }
    let chart : KSubspace PUnit (Set.univ : Set PUnit) ≃ₜ
        KProduct (KSubspace PUnit (Set.univ : Set PUnit)) PUnit :=
      Homeomorph.homeomorphOfUnique _ _
    refine ⟨chart, ?_, ?_⟩
    · intro z
      exact Subsingleton.elim _ _
    · intro z g
      exact ⟨Set.mem_univ _, Subsingleton.elim _ _⟩

/-- Continuous twisted loops, using the conjugation direction printed on
PDF p.13. The domain is the whole real line, not merely [0,1]. -/
def twistedLoopSet {G : Type u} [Group G] [TopologicalSpace G] (alpha : G) :
    Set C(ℝ, G) :=
  {gamma | ∀ t : ℝ, gamma (t + 1) = alpha * gamma t * alpha⁻¹}

/-- Based twisted loops have value 1 at time zero (PDF p.14). -/
def basedTwistedLoopSet {G : Type u} [Group G] [TopologicalSpace G] (alpha : G) :
    Set C(ℝ, G) :=
  {gamma | gamma ∈ twistedLoopSet alpha ∧ gamma 0 = 1}

/-- Twisted loops into the identity path component, with the restriction of
Ad(alpha). Alpha itself need not lie in that component (PDF p.14).
Equality is checked in G, so no ill-typed alpha : G0 is introduced. -/
def identityBasedTwistedLoopSet {G : Type u} [Group G] [TopologicalSpace G]
    (alpha : G) : Set C(ℝ, pathComponent (1 : G)) :=
  {gamma | (∀ t : ℝ,
    (gamma (t + 1)).1 = alpha * (gamma t).1 * alpha⁻¹) ∧ (gamma 0).1 = 1}

/-- Inclusion of continuous loops in the identity path component into G.
Only the map of underlying continuous functions is needed for the equality. -/
def includeIdentityLoop {G : Type u} [Group G] [TopologicalSpace G]
    (gamma : C(ℝ, pathComponent (1 : G))) : C(ℝ, G) :=
  ⟨fun t => (gamma t).1, continuous_subtype_val.comp gamma.continuous⟩

/-- Sanity check: the constant identity is a based twisted loop for every twist. -/
example {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (alpha : G) : (1 : C(ℝ, G)) ∈ basedTwistedLoopSet alpha := by
  change (∀ t : ℝ, (1 : C(ℝ, G)) (t + 1) =
    alpha * (1 : C(ℝ, G)) t * alpha⁻¹) ∧ (1 : C(ℝ, G)) 0 = 1
  constructor
  · intro t
    simp
  · rfl

/-- Sanity check: the unique real-to-singleton function satisfies every twist. -/
example (alpha : PUnit) : basedTwistedLoopSet alpha = Set.univ := by
  ext gamma
  simp only [Set.mem_univ, iff_true]
  exact ⟨fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end QAlgorithms.Papers.Independent.Intakethird100.P59



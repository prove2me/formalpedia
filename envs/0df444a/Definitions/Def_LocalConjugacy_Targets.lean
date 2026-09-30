-- Prove2me | Definitions.Def_LocalConjugacy_Targets
-- name    : LocalConjugacy_Targets
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T03:47:49.526216+00:00
-- url     : https://prove2.me/theorems/e5cc0fa2-a9f6-4919-8fda-63c8a447ee30
-- title:
--   Full statement of the paper-completion goal
-- statement:
--   The proposition `PaperResults` has one independently quantified field for each of Theorem 1.1, Lemma 1.2, Corollaries 1.3–1.4, Propositions 2.1–2.3, 3.1–3.2, and 4.1–4.2, plus both counterexamples. Constructing it proves all thirteen assertions. It supplies no field as an assumption of another field.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1, https://arxiv.org/pdf/2609.37678v1, §§1–4, pp. 1–8. Adapted in part from the author’s local Apache-2.0 Lean development.

import Definitions.Def_LocalConjugacy_Examples

/-!
# Complete scope of the paper

Every field is one independently quantified assertion. No field assumes another
field, so this record asserts all results and both counterexamples together.
The fields repeat the public milestone statements exactly. This record is a goal
specification, not an axiom or a supplied proof of any of its components.
-/
universe u v
namespace LocalConjugacy

/-- The eleven numbered results and two unnumbered counterexamples. -/
structure PaperResults : Prop where
  /-- Theorem 1.1: no finiteness or bounded nilpotency-class hypothesis is imposed on N. The supplements and the normal pronilpotent subgroup are closed. -/
  theorem_1_1 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal]
      (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
      (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
      (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
      (hHN : Supplements N H) (hKN : Supplements N K) :
      Conjugate H K ↔ LocallyConjugate H K

  /-- Lemma 1.2: the simultaneous restriction map on actual H¹ classes is a pointed bijection to the full product of stable classes. N is finite and nilpotent. -/
  lemma_1_2 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
      [TopologicalSpace N] [MulDistribMulAction J N] [DiscreteTopology N] [Finite N] [Group.IsNilpotent N]
      [ContinuousSMul J N]
      (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
      (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
      Function.Bijective (primaryRestriction (N := N) P) ∧
        (primaryRestriction (N := N) P) default = default

  /-- Corollary 1.3: an internal complement models the profinite semidirect product. Normality of N ∩ H is required inside N, and local witnesses may vary with p. -/
  corollary_1_3 {G : ProfiniteGrp.{u}} (N J H : Subgroup G)
      (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
      (hH : IsClosed (H : Set G)) (hsplit : Splits N J)
      (hpron : Pronilpotent N) (hcase : Prosupersolvable G ∨ Pronilpotent J)
      (hnormal : IntersectionNormal N H) (hlocal : LocallyContains H J) :
      ∃ g : G, conjugate g J ≤ H

  /-- Corollary 1.4: Ω is nonempty and carries no topology. The action is transitive and its point stabilizers are closed; the local fixed points may depend on p. -/
  corollary_1_4 {G : ProfiniteGrp.{u}} {Ω : Type v} [MulAction G Ω] [Nonempty Ω]
      (N J : Subgroup G) (hN : IsClosed (N : Set G)) (hJ : IsClosed (J : Set G))
      (hsplit : Splits N J) (hpron : Pronilpotent N)
      (hcase : Prosupersolvable G ∨ Pronilpotent J)
      (htrans : MulAction.IsPretransitive G Ω)
      (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
      (hnormal : ∃ x : Ω, IntersectionNormal N (MulAction.stabilizer G x))
      (hlocal : SylowFixedPoints (Ω := Ω) J) : HasFixedPoint (Ω := Ω) J

  /-- Proposition 2.1: discrete coefficients may be infinite but are locally finite. The new cocycle is fixed literally by Q and is trivial on J₀ ∩ Q. -/
  proposition_2_1 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
      [TopologicalSpace N] [MulDistribMulAction J N] [IsTopologicalGroup N] [DiscreteTopology N]
      [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N) (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
      (hN : IsPGroup p N) (J₀ Q : Subgroup J) [J₀.Normal]
      (hJ₀ : IsClosed (J₀ : Set J)) (hQ : IsClosed (Q : Set J))
      (hcyclic : Procyclic Q) (hpro : IsProP p₀ Q)
      (f : Cocycle (N := N) J₀) (hinv : InvariantUnder Q J₀ f) :
      ∃ g : Cocycle (N := N) J₀, Cohomologous f g ∧
        (∀ (q : J) (hq : q ∈ Q) (x : J) (hx : x ∈ J₀)
          (hqx : q⁻¹ * x * q ∈ J₀),
          q • g.toFun ⟨q⁻¹ * x * q, hqx⟩ = g.toFun ⟨x, hx⟩) ∧
        ∀ (q : J) (hq : q ∈ Q) (hq₀ : q ∈ J₀), g.toFun ⟨q, hq₀⟩ = 1

  /-- Proposition 2.2: restriction at a closed normal subgroup of prime index is a pointed bijection onto stable classes, with locally finite coefficients. -/
  proposition_2_2 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
      [TopologicalSpace N] [MulDistribMulAction J N] [IsTopologicalGroup N] [DiscreteTopology N]
      [ContinuousSMul J N] (hfinite : LocallyFiniteGroup N) (p p₀ : ℕ) (hp : p.Prime) (hp₀ : p₀.Prime) (hne : p₀ ≠ p)
      (hJ : Prosolvable J) (hN : IsPGroup p N) (J₀ : Subgroup J) [J₀.Normal]
      (hJ₀ : IsClosed (J₀ : Set J)) (hindex : J₀.index = p₀) :
      Function.Bijective (stableRestriction (N := N) J₀) ∧
        (stableRestriction (N := N) J₀) default = default

  /-- Proposition 2.3: the arXiv version assumes profinite J and prosupersolvable NJ. There is no additional prosolvability hypothesis. Q is any Hall subgroup for the primes at most p, and the codomain is all H¹(Q,N), not just stable classes. -/
  proposition_2_3 {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
      [TopologicalSpace N] [MulDistribMulAction J N] [DiscreteTopology N] [Finite N]
      [ContinuousSMul J N] (p : ℕ) (hp : p.Prime) (hN : IsPGroup p N)
      (hG : Prosupersolvable (ActionProduct J N))
      (Q : Subgroup J) (hQ : IsHallPro {r | r ≤ p} Q) :
      Function.Bijective (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) ∧
        (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) default = default

  /-- Proposition 3.1: in the arXiv version N is finite. Both H and K are actual complements, expressed with Mathlib’s standard subgroup complement predicate. -/
  proposition_3_1 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal] [Finite N]
      (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
      (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
      (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
      (hNH : N.IsComplement' H) (hNK : N.IsComplement' K) :
      Conjugate H K ↔ LocallyConjugate H K

  /-- Proposition 3.2: the complete statement of Theorem 1.1 with finite N. The ambient profinite group G is not assumed finite. -/
  proposition_3_2 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal] [Finite N]
      (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
      (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
      (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
      (hHN : Supplements N H) (hKN : Supplements N K) :
      Conjugate H K ↔ LocallyConjugate H K

  /-- Proposition 4.1: the abelian subgroup N and both supplements are closed. No solvability assumption is made on G. -/
  proposition_4_1 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal]
      (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
      (hK : IsClosed (K : Set G)) [IsMulCommutative N]
      (hHN : Supplements N H) (hKN : Supplements N K)
      (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H

  /-- Proposition 4.2: an arbitrary transitive action on a nonempty set, with closed stabilizers. The abelian normal subgroup need not act transitively. -/
  proposition_4_2 {G : ProfiniteGrp.{u}} {Ω : Type v} [MulAction G Ω] [Nonempty Ω]
      (N H : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
      (hH : IsClosed (H : Set G)) [IsMulCommutative N]
      (hHN : Supplements N H) (htrans : MulAction.IsPretransitive G Ω)
      (hclosed : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
      (hlocal : SylowFixedPoints (Ω := Ω) H) : HasFixedPoint (Ω := Ω) H

  /-- First unnumbered counterexample, §1, p. 2. The matrix-group identification, cohomology cardinalities, and failure of conjugacy are all asserted together. -/
  counterexample_quaternion :
      ∃ a : S3 →* MulAut Q8,
        -- The action is realized in the matrix group named in the source.
        Nonempty ((Q8 ⋊[a] S3) ≃* GL (Fin 2) (ZMod 3)) ∧
        -- There are exactly two global cohomology classes.
        Nat.card (FiniteH1 a) = 2 ∧
        -- Every Sylow restriction has trivial first cohomology.
        (∀ (p : ℕ) (hp : p.Prime),
          letI : Fact p.Prime := ⟨hp⟩
          ∀ P : Sylow p S3, Subsingleton (FiniteH1 (a.comp P.toSubgroup.subtype))) ∧
        -- The same action gives the locally conjugate, nonconjugate complements.
        ∃ J' : Subgroup (Q8 ⋊[a] S3),
          (quaternionKernel a).IsComplement' J' ∧
          FiniteLocallyConjugate (quaternionComplement a) J' ∧
          ¬ Conjugate (quaternionComplement a) J'

  /-- Second unnumbered counterexample, §1, p. 2. The Heisenberg and wreath-product identifications are included explicitly, along with every stated local/global property. -/
  counterexample_heisenberg :
      ∃ (G : ProfiniteGrp.{0}) (N J H : Subgroup G),
        -- All concrete group identifications in the source are part of the target.
        Finite G ∧ Nonempty (G ≃* WreathC3S3) ∧
        Nonempty (N ≃* Heisenberg3) ∧
        Nonempty (J ≃* Multiplicative (ZMod 6)) ∧
        Nonempty (H ≃* C3 × S3) ∧
        Nat.card G = 162 ∧ Nat.card N = 27 ∧ Nat.card J = 6 ∧ Nat.card H = 18 ∧
        -- N and J form the specified internal semidirect product.
        Splits N J ∧ Group.IsNilpotent N ∧ Group.IsNilpotent J ∧ Supersolvable G ∧
        IsClosed (N : Set G) ∧ IsClosed (J : Set G) ∧ IsClosed (H : Set G) ∧
        -- The local inclusion test succeeds, but global inclusion fails.
        LocallyContains H J ∧ (¬ ∃ g : G, conjugate g J ≤ H) ∧
        ¬ IntersectionNormal N H

end LocalConjugacy



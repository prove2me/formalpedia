-- Prove2me | Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
-- name    : ExtCitation_LocalLevelSubgroupsPD
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/c4e3cf36-8e1c-5f03-bb43-1a47ab883420
-- title:
--   Level subgroups and inertia pull-backs at a local place
-- statement:
--   Fix a prime $q$. Here $G_q$ denotes `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the chosen algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$; $\mathfrak q$ denotes `primeLocalPlace q`, the valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` obtained by pulling back the unit ball of `PadicAlgCl q` along a fixed $\mathbb Q$-embedding $\overline{\mathbb Q}\hookrightarrow$ `PadicAlgCl q`; and $r_q =$ `primeLocalToGlobal q` is the monoid homomorphism $G_q \to \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ given by restricting scalars to $\mathbb Q$ and then restricting to the normal subextension $\overline{\mathbb Q}$. The first statement records that $r_q$ lands in the decomposition subgroup of $\mathfrak q$, i.e. in the stabiliser of the valuation subring $\mathfrak q$ under the action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on valuation subrings.
--
--   For an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ that is normal over $\mathbb Q$, `levelSubgroup_eq_ker` identifies the level subgroup $r_q^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F)) \le G_q$ — the comap along $r_q$ of the fixing subgroup of $F$ — with the kernel of the composite of $r_q$ with the restriction map $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{Gal}(F/\mathbb Q)$. Two instances follow: this subgroup is normal in $G_q$, and it has finite index when moreover $F/\mathbb Q$ is finite. A further lemma states antitonicity: $F \le F'$ implies that the level subgroup of $F'$ is contained in that of $F$ (here no normality of $F$, $F'$ is assumed).
--
--   Finally, `mem_inertiaPullback_iff` characterises membership of $g \in G_q$ in the comap along $r_q$ of `inertiaSubgroupIn ℚ` of $\mathfrak q$ — the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup sitting inside the decomposition subgroup — as the condition that the element $r_q(g)$, viewed in the decomposition subgroup, fixes every element of the residue field of $\mathfrak q$; an accompanying instance records that this inertia pull-back is normal in $G_q$.
--
--   **Relation to Mathlib.** The decomposition subgroup, the inertia subgroup of a valuation subring and the residue field of a local ring are Mathlib notions; [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21) is the project's variant, the image of Mathlib's inertia subgroup under the inclusion of the decomposition subgroup into the full automorphism group.
--
--   **Where it is used.** The level subgroups form a system of normal, finite-index subgroups of the local Galois group at $q$ cut out by finite normal extensions of $\mathbb Q$, and the inertia pull-back is the corresponding inertia at the chosen place above $q$; both are used in the local bookkeeping of the Selmer and Greenberg–Wiles dimension counts carried out over the index set of places in the project's arithmetic datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtCitation_LocalLevelSubgroupsPD.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ExtCitation

namespace ExtCitation

theorem primeLocalToGlobal_mem_decompositionSubgroup (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    primeLocalToGlobal q g ∈ (primeLocalPlace q).decompositionSubgroup ℚ := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g

theorem levelSubgroup_eq_ker (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup).comap (primeLocalToGlobal q)
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp (primeLocalToGlobal q)).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›, MonoidHom.comap_ker]
  rfl

instance levelSubgroup_normal (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).Normal := by
  rw [levelSubgroup_eq_ker]; exact MonoidHom.normal_ker _

instance levelSubgroup_finiteIndex (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).FiniteIndex := by
  rw [levelSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

theorem levelSubgroup_antitone (q : Nat.Primes) {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') :
    (F'.fixingSubgroup).comap (primeLocalToGlobal q) ≤ (F.fixingSubgroup).comap (primeLocalToGlobal q) :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h)

theorem mem_inertiaPullback_iff (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    g ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ↔
      ∀ x : IsLocalRing.ResidueField (primeLocalPlace q),
        (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ :
          (primeLocalPlace q).decompositionSubgroup ℚ) • x = x := by
  rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτg⟩
    intro x
    have hmem : (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ : (primeLocalPlace q).decompositionSubgroup ℚ) = τ := by
      apply Subtype.ext; exact hτg.symm
    rw [hmem]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun φ => (φ : IsLocalRing.ResidueField (primeLocalPlace q) ≃+* _) x) hτ
    simpa using this
  · intro h
    refine ⟨⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    simpa using h x

instance inertiaPullback_normal (q : Nat.Primes) :
    (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)).Normal := by

  let D := (primeLocalPlace q).decompositionSubgroup ℚ
  have hD : ∀ g : primeLocalGaloisGroup q, primeLocalToGlobal q g ∈ D := primeLocalToGlobal_mem_decompositionSubgroup q
  let r' : primeLocalGaloisGroup q →* D := (primeLocalToGlobal q).codRestrict D hD
  have : ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
      = (((primeLocalPlace q).inertiaSubgroup ℚ)).comap r' := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
    constructor
    · rintro ⟨τ, hτ, hτg⟩
      have : r' g = τ := Subtype.ext hτg.symm
      rwa [this]
    · intro h; exact ⟨r' g, h, rfl⟩
  rw [this, ValuationSubring.inertiaSubgroup, MonoidHom.comap_ker]
  exact MonoidHom.normal_ker _

end ExtCitation



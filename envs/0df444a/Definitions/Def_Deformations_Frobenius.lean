-- Prove2me | Definitions.Def_Deformations_Frobenius
-- name    : Deformations_Frobenius
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/c5ff2bad-75a6-5697-905a-412ebe5dc66b
-- title:
--   Frobenius elements for profinite group actions on rings
-- statement:
--   The standing setting is a commutative ring $S$ over a commutative ring $R$, together with a group $G$ acting on $S$ by ring automorphisms commuting with the $R$-action, such that $G$ is a profinite group (compact, totally disconnected topological group), the action is invariant in the sense of `Algebra.IsInvariant R S G` (the $G$-fixed part of $S$ is the image of $R$), and the action satisfies [`ContinuousSMulDiscrete G S`](../def/Deformations_ContinuousSMulDiscrete.html#L7), i.e. for all $x,y \in S$ the set $\{g \in G : g \cdot x = y\}$ is open in $G$ — equivalently all point stabilisers are open, which is continuity of the action for the discrete topology on $S$. Throughout, `Q.under R` denotes the contraction of an ideal $Q \subseteq S$ to $R$, and `IsArithFrobAt R σ Q` is the congruence condition $\sigma \cdot x \equiv x^{q} \pmod Q$ for all $x \in S$, where $q$ is the cardinality of the residue ring $R/(Q \cap R)$.
--
--   Two existence results are proved. First, if $Q$ is a maximal ideal of $S$ whose contraction has finite residue ring, then some $\sigma \in G$ is an arithmetic Frobenius at $Q$. Second, for a prime $P$ of $R$ with $R/P$ finite there is a function on the set `Ideal.primesOver P S` of primes of $S$ lying over $P$ which assigns to each such $Q$ an arithmetic Frobenius at $Q$, with all values conjugate in $G$. Using a choice of such a function, [`arithFrobAt' R G Q`](../def/Deformations_Frobenius.html#L68) is defined for every prime $Q$ of $S$ with $R/(Q \cap R)$ finite; it is characterised only by the two accompanying lemmas, namely that it is an arithmetic Frobenius at $Q$, and that $\mathrm{arithFrobAt}'(Q)$ and $\mathrm{arithFrobAt}'(Q')$ are conjugate in $G$ whenever $Q$ and $Q'$ have the same contraction to $R$.
--
--   **Relation to Mathlib.** The predicate `IsArithFrobAt` and the profinite infrastructure used here (integrality and transitivity of the $G$-action on primes over a fixed prime under `Algebra.IsInvariant`, surjectivity of the map from a stabiliser to the residue-extension automorphisms) are Mathlib's; what this module adds is the existence of Frobenius elements in the profinite situation, their conjugacy along the primes over a fixed prime, and the chosen element [`arithFrobAt'`](../def/Deformations_Frobenius.html#L68). The class [`ContinuousSMulDiscrete`](../def/Deformations_ContinuousSMulDiscrete.html#L7), asserting openness of the sets $\{g : g \cdot x = y\}$, is the project's own, with the comparison to `ContinuousSMul` for a discrete action proved alongside it.
--
--   **Where it is used.** Frobenius elements attached to primes, determined up to conjugacy by the prime of the base ring they lie over, are what allows characteristic polynomials of a Galois representation to be evaluated at unramified primes; this module supplies them for the absolute Galois group acting on a ring of integers, in the form used in the deformation-theoretic part of the argument.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Deformations/RepresentationTheory/Frobenius.lean` — © 2025 Andrew Yang; authors: Andrew Yang). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_Frobenius.lean

import Mathlib
import Definitions.Def_Deformations_ContinuousSMulDiscrete

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {Q : Ideal S} {σ σ' : G}

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [Algebra.IsInvariant R S G]
variable [ContinuousSMulDiscrete G S]

variable (R G Q) in
attribute [local instance] Ideal.Quotient.field in

lemma exists_of_isInvariant_of_profinite
    [Q.IsMaximal] [Finite (R ⧸ Q.under R)] : ∃ σ : G, IsArithFrobAt R σ Q := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  let P := Q.under R
  have : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  have : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  cases nonempty_fintype (R ⧸ P)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (R ⧸ P) p
  have := CharP.of_ringHom_of_ne_zero (algebraMap (R ⧸ P) (S ⧸ Q)) p hp.ne_zero
  have : ExpChar (S ⧸ Q) p := .prime hp
  have : PerfectField (S ⧸ Q) := Algebra.IsAlgebraic.perfectField (K := (R ⧸ P))
  let l : (S ⧸ Q) ≃ₐ[R ⧸ P] S ⧸ Q :=
    { __ := iterateFrobeniusEquiv (S ⧸ Q) p k,
      commutes' r := by
        dsimp [iterateFrobenius_def]
        rw [← map_pow, ← hk, FiniteField.pow_card] }
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) P Q l
  refine ⟨σ, fun x ↦ ?_⟩
  rw [← Ideal.Quotient.eq, Nat.card_eq_fintype_card, hk]
  exact DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)

variable (S G) in
lemma exists_primesOver_isConj_of_profinite (P : Ideal R) [Finite (R ⧸ P)] [P.IsPrime] :
    ∃ σ : Ideal.primesOver P S → G, (∀ Q, IsArithFrobAt R (σ Q) Q.1) ∧
      (∀ Q₁ Q₂, IsConj (σ Q₁) (σ Q₂)) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  have hP : P.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R ⧸ P))
  have : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  obtain hs | ⟨Q, hQ, hQ₂⟩ := Set.eq_empty_or_nonempty (Ideal.primesOver P S)
  · simp [hs]
  have (Q' : Ideal.primesOver P S) : ∃ σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  have : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) Q
    (by rwa [← Ideal.under, ← hQ₂.over])
  have : Finite (R ⧸ Q.under R) := by rwa [← hQ₂.over]
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant_of_profinite R G Q
  refine ⟨fun Q' ↦ τ Q' * σ * (τ Q')⁻¹, fun Q' ↦ hτ Q' ▸ hσ.conj (τ Q'), fun Q₁ Q₂ ↦
    .trans (.symm (isConj_iff.mpr ⟨τ Q₁, rfl⟩)) (isConj_iff.mpr ⟨τ Q₂, rfl⟩)⟩

variable (R G Q)

noncomputable
def _root_.arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] : G :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

protected lemma arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] :
    IsArithFrobAt R (arithFrobAt' R G Q) Q :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩

lemma _root_.isConj_arithFrobAt'
    [Q.IsPrime] [Finite (R ⧸ Q.under R)] (Q' : Ideal S) [Q'.IsPrime] [Finite (R ⧸ Q'.under R)]
    (H : Q.under R = Q'.under R) : IsConj (arithFrobAt' R G Q) (arithFrobAt' R G Q') := by
  obtain ⟨P, hP, h₁, h₂, h₃⟩ :
      ∃ P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R ∧ Finite (R ⧸ P) :=
    ⟨Q.under R, inferInstance, rfl, H, ‹_›⟩
  convert (exists_primesOver_isConj_of_profinite S G P).choose_spec.2
    ⟨Q, ‹_›, ⟨h₁⟩⟩ ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂; rfl

end IsArithFrobAt

end



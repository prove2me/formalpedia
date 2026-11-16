-- Prove2me | Definitions.Def_ConstGapCircuits_Supplement_orthogonalGroups
-- name    : ConstGapCircuits_Supplement_orthogonalGroups
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:28:04.203442+00:00
-- url     : https://prove2.me/theorems/739ce6d0-53c0-4201-8f0f-3b74b779c1ac
-- title:
--   Special orthogonal, orthogonal Pauli and Clifford groups, and their local subgroups
-- statement:
--   For $n$ qubits, let $U$ be a matrix in $\mathrm{SU}(2^n)$, indexed by the computational basis. The real-entry subgroup is
--   $$
--   \mathrm{SO}(2^n)=\{U\in\mathrm{SU}(2^n):\operatorname{Im}U_{xy}=0\text{ for every }x,y\}.
--   $$
--   Let $\mathcal P(n;\mathbb R)$ be the special Pauli matrices in this subgroup: the real determinant-one matrices among $i^kP$, where $k\in\{0,1,2,3\}$ and $P$ is a tensor product of $I,X,Y,Z$. Define $\mathrm{Cl}(n;\mathbb R)$ as the normalizer of this set inside $\mathrm{SO}(2^n)$.
--
--   For a qubit set $S$, $\mathrm{LO}(S,n)$ consists of all elements of $\mathrm{SO}(2^n)$ supported on $S$, and $\mathrm{LCl}(S,n;\mathbb R)$ is its inverse image in $\mathrm{Cl}(n;\mathbb R)$. These local groups retain the central signs. The determinant is tested in the full space: on two qubits the local block lies in $\mathrm O(4)$ when $n\ge3$, and in $\mathrm{SO}(4)$ when $n=2$.
--
--   These compact groups supply the Haar probability measures used by the orthogonal walks. The helper `withinLocal S T` views the intersection with the group on $T$ as a subgroup of the group on $S$; when $T\subseteq S$ it is exactly the smaller local group. The published commutant definition of support, equivalent to the published `supportedMatrix`, is reused.
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), pp. 2–3, 15, 17, 28, Definition 1.2 and §§2.2, 4; PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_quantumGroups

noncomputable section

namespace ConstGapCircuits.Supplement

/-- The real-entry closed subgroup of SU(2^n), hence SO(2^n), §2.2. -/
def orthogonal (n : ℕ) : ClosedSubgroup (SU n) where
  carrier := {U | ∀ x y, ((U : Mat n) x y).im = 0}
  one_mem' := by
    intro x y
    change ((1 : Mat n) x y).im = 0
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  mul_mem' := by
    intro U V hU hV x y
    change ∀ x y, ((U : Mat n) x y).im = 0 at hU
    change ∀ x y, ((V : Mat n) x y).im = 0 at hV
    change (∑ z, (U : Mat n) x z * (V : Mat n) z y).im = 0
    simp [Complex.mul_im, hU, hV]
  inv_mem' := by
    intro U hU x y
    change (star ((U : Mat n) y x)).im = 0
    simpa using hU y x
  isClosed' := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (Complex.continuous_im.comp
        ((continuous_apply y).comp ((continuous_apply x).comp continuous_subtype_val)))
        continuous_const

abbrev SO (n : ℕ) := ↥(orthogonal n)

instance soCompact (n : ℕ) : CompactSpace (SO n) :=
  isCompact_iff_compactSpace.mp (orthogonal n).isClosed'.isCompact

/-- Inclusion keeps the determinant-one condition in the full 2^n-dimensional space. -/
def soInclusion (n : ℕ) : SO n →* SU n := (orthogonal n).toSubgroup.subtype

/-- The special Pauli matrices lying in SO(2^n), including the central signs. -/
def orthogonalPauliSet (n : ℕ) : Set (SO n) :=
  soInclusion n ⁻¹' specialPauliSet n

lemma orthogonalPauliSet_finite (n : ℕ) : (orthogonalPauliSet n).Finite :=
  (specialPauliSet_finite n).preimage Subtype.val_injective.injOn

/-- Normalizer in SO itself, rather than the unitary Clifford group. -/
def orthogonalClifford (n : ℕ) : ClosedSubgroup (SO n) :=
  closedNormalizer (orthogonalPauliSet n) (orthogonalPauliSet_finite n).isClosed

abbrev OCl (n : ℕ) := ↥(orthogonalClifford n)

instance orthogonalCliffordCompact (n : ℕ) : CompactSpace (OCl n) :=
  isCompact_iff_compactSpace.mp (orthogonalClifford n).isClosed'.isCompact

/-- Forget only membership in the normalizer. -/
def orthogonalCliffordInclusion (n : ℕ) : OCl n →* SO n :=
  (orthogonalClifford n).toSubgroup.subtype

/-- All real determinant-one matrices supported on S; includes both local determinant
components whenever the complementary tensor factor makes their full determinant one. -/
def localOrthogonal {n : ℕ} (S : Finset (Fin n)) : ClosedSubgroup (SO n) where
  toSubgroup := (localUnitary S).toSubgroup.comap (soInclusion n)
  isClosed' := (localUnitary S).isClosed'.preimage continuous_subtype_val

/-- Local orthogonal Cliffords retain the full center {±1}. -/
def localOrthogonalClifford {n : ℕ} (S : Finset (Fin n)) : ClosedSubgroup (OCl n) where
  toSubgroup := (localOrthogonal S).toSubgroup.comap (orthogonalCliffordInclusion n)
  isClosed' := (localOrthogonal S).isClosed'.preimage continuous_subtype_val

/-- A local subgroup viewed inside a larger local group; when T⊆S this is exactly LCl_T. -/
def withinLocal {n : ℕ} (S T : Finset (Fin n)) :
    ClosedSubgroup (localOrthogonalClifford S) where
  toSubgroup := (localOrthogonalClifford T).toSubgroup.comap
    (localOrthogonalClifford S).toSubgroup.subtype
  isClosed' := (localOrthogonalClifford T).isClosed'.preimage continuous_subtype_val

end ConstGapCircuits.Supplement



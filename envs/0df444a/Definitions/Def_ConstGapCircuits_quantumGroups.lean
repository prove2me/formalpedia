-- Prove2me | Definitions.Def_ConstGapCircuits_quantumGroups
-- name    : ConstGapCircuits_quantumGroups
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:47:46.701755+00:00
-- url     : https://prove2.me/theorems/04c8bc9d-9573-41d3-879b-323ba4b1dbb0
-- title:
--   Hermitian Pauli strings, the special Clifford normalizer, and local groups (Definition 1.2)
-- statement:
--   Write $I,X,Y,Z$ for the standard two-dimensional Hermitian Pauli matrices. A Pauli string is $P_p=\bigotimes_{j=0}^{n-1}p_j$, with $p_j\in\{I,X,Y,Z\}$. The index set $\mathcal P_n$ excludes the all-identity string. The special Pauli set is
--   $$\{i^kP_p:k\in\{0,1,2,3\},\ \det(i^kP_p)=1\},$$
--   and $\mathrm{Cl}(n)$ is its normalizer inside $\mathrm{SU}(2^n)$. Phases are retained. For $n=1$ the special Pauli set is the quaternion group.
--
--   For a qubit subset $S$, $\mathrm{LU}(S,n)$ consists of matrices supported on $S$, and $\mathrm{LCl}(S,n)=\mathrm{LU}(S,n)\cap\mathrm{Cl}(n)$. The local unitary group is encoded equivalently as the commutant of the full matrix algebra supported on $S^c$. The full-space determinant-one condition is retained, so scalar matrices in the centre belong even when $S=\varnothing$.
--
--   These groups supply the common model for every circuit theorem. Closedness, compactness and the topological group instances are proved structurally. The finite special Pauli set is given explicitly, rather than requiring generators of determinant minus one to lie in the special unitary group.
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 2–3, Definition 1.2

import Definitions.Def_ConstGapCircuits_compactGroups

noncomputable section

namespace ConstGapCircuits
open scoped BigOperators

/-- The standard Hermitian matrices I, X, Y, Z, with no phase quotient. -/
def pauliSingle (p : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if p = 0 then 1 else if p = 1 then !![0, 1; 1, 0]
  else if p = 2 then !![0, -Complex.I; Complex.I, 0] else !![1, 0; 0, -1]

/-- Tensor product in the computational basis, including the identity string. -/
def pauli {n : ℕ} (p : Fin n → Fin 4) : Mat n :=
  fun x y => ∏ i, pauliSingle (p i) (x i) (y i)

abbrev PauliIndex (n : ℕ) := {p : Fin n → Fin 4 // p ≠ 0}

/-- Exact special Pauli set: phase ±1, ±i, followed by the determinant-one restriction.
At n=1 this is Q8, rather than the determinant-minus-one Pauli matrices. -/
def specialPauliSet (n : ℕ) : Set (SU n) :=
  {U | ∃ k : Fin 4, ∃ p : Fin n → Fin 4,
    (U : Mat n) = Complex.I ^ (k : ℕ) • pauli p}

lemma specialPauliSet_finite (n : ℕ) : (specialPauliSet n).Finite := by
  let f : Fin 4 × (Fin n → Fin 4) → Mat n := fun z => Complex.I ^ (z.1 : ℕ) • pauli z.2
  have h : specialPauliSet n = Subtype.val ⁻¹' Set.range f := by
    ext U
    simp [specialPauliSet, f, eq_comm]
  rw [h]
  exact (Set.finite_range f).preimage Subtype.val_injective.injOn

/-- A closed-set normalizer, as a closed subgroup. -/
def closedNormalizer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Set G) (hS : IsClosed S) : ClosedSubgroup G where
  toSubgroup := Subgroup.normalizer S
  isClosed' := by
    have heq : (Subgroup.normalizer S : Set G) =
        {g | (∀ x ∈ S, g * x * g⁻¹ ∈ S) ∧ (∀ x ∈ S, g⁻¹ * x * g ∈ S)} := by
      ext g
      constructor
      · intro h
        exact ⟨fun x hx => (Subgroup.mem_set_normalizer_iff.mp h x).mp hx,
          fun x hx => (Subgroup.mem_set_normalizer_iff''.mp h x).mp hx⟩
      · rintro ⟨hf, hb⟩
        apply Subgroup.mem_set_normalizer_iff.mpr
        intro x
        constructor
        · exact hf x
        · intro hx
          have := hb (g * x * g⁻¹) hx
          simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    change IsClosed (Subgroup.normalizer S : Set G)
    rw [heq]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun x => isClosed_iInter fun _ =>
      hS.preimage (by fun_prop)).inter (isClosed_iInter fun x => isClosed_iInter fun _ =>
      hS.preimage (by fun_prop))

/-- Definition 1.2: the normalizer of the special Pauli group inside SU, including its centre. -/
def clifford (n : ℕ) : ClosedSubgroup (SU n) :=
  closedNormalizer (specialPauliSet n) (specialPauliSet_finite n).isClosed

abbrev Cl (n : ℕ) : Type := {U : SU n // U ∈ clifford n}

instance cliffordCompact (n : ℕ) : CompactSpace (Cl n) :=
  isCompact_iff_compactSpace.mp (clifford n).isClosed'.isCompact

instance cliffordTopologicalGroup (n : ℕ) : IsTopologicalGroup (Cl n) where
  continuous_mul := continuous_induced_rng.mpr ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.inv

def cliffordInclusion (n : ℕ) : Cl n →* SU n := (clifford n).toSubgroup.subtype

/-- Full matrix algebra on a set of qubits, tensored with identity on its complement. -/
def supportedMatrix {n : ℕ} (S : Finset (Fin n)) (A : Mat n) : Prop :=
  ∃ B : Matrix (S → Fin 2) (S → Fin 2) ℂ, ∀ x y,
    A x y = if (∀ i, i ∉ S → x i = y i) then
      B (fun i => x i) (fun i => y i) else 0

/-- Commuting with every complementary matrix is exactly acting on S and as identity outside S.
This commutant encoding includes scalar matrices, with determinant tested in the full space. -/
def localUnitary {n : ℕ} (S : Finset (Fin n)) : ClosedSubgroup (SU n) where
  carrier := {U | ∀ A : Mat n, supportedMatrix Sᶜ A → (U : Mat n) * A = A * U}
  one_mem' := by intro A hA; simp
  mul_mem' := by
    intro U V hU hV A hA
    change ((U : Mat n) * V) * A = A * ((U : Mat n) * V)
    rw [mul_assoc, hV A hA, ← mul_assoc, hU A hA, mul_assoc]
  inv_mem' := by
    intro U hU A hA
    have h := hU A hA
    have hleft : (U⁻¹ : SU n).val * U.val = 1 := U.prop.1.1
    have hright : U.val * (U⁻¹ : SU n).val = 1 := U.prop.1.2
    calc
      (U⁻¹ : SU n).val * A = (U⁻¹ : SU n).val * A * (U.val * (U⁻¹ : SU n).val) := by rw [hright, mul_one]
      _ = (U⁻¹ : SU n).val * (A * U.val) * (U⁻¹ : SU n).val := by simp only [mul_assoc]
      _ = (U⁻¹ : SU n).val * (U.val * A) * (U⁻¹ : SU n).val := by rw [h]
      _ = A * (U⁻¹ : SU n).val := by rw [← mul_assoc, hleft, one_mul]
  isClosed' := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun A => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) (by fun_prop)

/-- Local Clifford groups as closed subgroups of Cl(n). -/
def localClifford {n : ℕ} (S : Finset (Fin n)) : ClosedSubgroup (Cl n) where
  toSubgroup := (localUnitary S).toSubgroup.comap (cliffordInclusion n)
  isClosed' := (localUnitary S).isClosed'.preimage continuous_subtype_val

end ConstGapCircuits



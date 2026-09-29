-- Prove2me | Definitions.Def_DifferentFiltrationFormula
-- name    : DifferentFiltrationFormula
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/3acea8c0-92ee-5087-ac40-d001e7664d2b
-- title:
--   Truncated lower ramification sums and the different formula
-- statement:
--   Throughout, $B$ is a commutative local ring and $G$ a group acting on $B$ by ring automorphisms, so that the lower ramification groups $G_i =$ [`IsLocalRing.lowerRamificationGroup B G i`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) are available: $G_i$ is the inertia subgroup of $\mathfrak{m}_B^{i+1}$, i.e. the subgroup of those $\sigma$ with $\sigma \cdot x - x \in \mathfrak{m}_B^{i+1}$ for all $x \in B$, a chain antitone in $i$. Two numerical invariants are defined. First, [`lowerRamificationFiltrationSum B G N`](../def/DifferentFiltrationFormula.html#L15) is the truncated sum $\sum_{i < N} (\#G_i - 1)$, formed with `Nat.card` and truncated natural subtraction. Second, [`lowerRamificationDepthCount B G N σ`](../def/DifferentFiltrationFormula.html#L18) is the number of indices $i < N$ with $\sigma \in G_i$, that is the truncation at $N$ of Serre's function $i_G(\sigma)$. Two structural facts accompany them: if $G_N = 1$ then $G_M = 1$ for all $M \ge N$, and consequently the truncated sum takes the same value at any two cut-offs $N, M$ at which the chain is trivial, so the sum is independent of the cut-off once the filtration has died; and, for $G$ finite, $\sum_{\sigma \neq 1} \#\{i < N : \sigma \in G_i\} = \sum_{i<N} (\#G_i - 1)$, the double-counting identity underlying Serre's proof.
--
--   In the second part, $A$ is a commutative domain, $B$ a local Dedekind domain that is a torsion-free $A$-module with an $A$-algebra structure, and $G$ acts on $B$ as above. The predicate [`DifferentEqPowFiltrationSum A B G`](../def/DifferentFiltrationFormula.html#L76) asserts: for every $N$ with $G_N = 1$, the different ideal $\mathfrak{d}_{B/A}$ equals $\mathfrak{m}_B^{\,\sum_{i<N}(\#G_i-1)}$. By cut-off independence, verifying this equality for a single such $N$ yields the predicate in full, which is the content of the final theorem.
--
--   **Relation to Mathlib.** Mathlib supplies `differentIdeal` and `Ideal.inertia`; the lower-numbering ramification groups of a local ring with a group action, and the filtration sums and the different formula stated here, are the project's own.
--
--   **Where it is used.** The equality $\mathfrak{d}_{B/A} = \mathfrak{m}_B^{\sum_i (\#G_i - 1)}$ is the local form of Hilbert's different formula, from which the unramified case $\mathfrak{d} = (1)$ and the tame case $\mathfrak{d} = \mathfrak{m}^{e-1}$ are obtained; these feed the discriminant and conductor computations for local Galois extensions used in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DifferentFiltrationFormula.lean

import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import Mathlib.RingTheory.DedekindDomain.Different

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

attribute [local instance] FractionRing.liftAlgebra

section FiltrationSum

variable (B : Type*) [CommRing B] [IsLocalRing B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

noncomputable def lowerRamificationFiltrationSum (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, (Nat.card (IsLocalRing.lowerRamificationGroup B G i) - 1)

noncomputable def lowerRamificationDepthCount (N : ℕ) (σ : G) : ℕ :=
  letI : DecidablePred fun i => σ ∈ IsLocalRing.lowerRamificationGroup B G i :=
    fun _ => Classical.propDecidable _
  ((Finset.range N).filter fun i => σ ∈ IsLocalRing.lowerRamificationGroup B G i).card

variable {B G}

theorem lowerRamificationGroup_eq_bot_of_le {N M : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥) (hNM : N ≤ M) :
    IsLocalRing.lowerRamificationGroup B G M = ⊥ :=
  le_bot_iff.mp (hN ▸ IsLocalRing.lowerRamificationGroup_antitone hNM)

theorem lowerRamificationFiltrationSum_eq_of_le {N M : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥) (hNM : N ≤ M) :
    lowerRamificationFiltrationSum B G M = lowerRamificationFiltrationSum B G N := by
  unfold lowerRamificationFiltrationSum
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM,
    ← Finset.range_eq_Ico]
  have h0 : ∀ i ∈ Finset.Ico N M,
      Nat.card (IsLocalRing.lowerRamificationGroup B G i) - 1 = 0 := by
    intro i hi
    rw [lowerRamificationGroup_eq_bot_of_le hN (Finset.mem_Ico.mp hi).1, Subgroup.card_bot]
  rw [Finset.sum_eq_zero h0, add_zero]

theorem lowerRamificationFiltrationSum_eq_of_eq_bot {N M : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥)
    (hM : IsLocalRing.lowerRamificationGroup B G M = ⊥) :
    lowerRamificationFiltrationSum B G N = lowerRamificationFiltrationSum B G M := by
  rcases le_total N M with h | h
  · exact (lowerRamificationFiltrationSum_eq_of_le hN h).symm
  · exact lowerRamificationFiltrationSum_eq_of_le hM h

private theorem sum_erase_one_ite_mem [Fintype G] [DecidableEq G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] :
    (∑ σ ∈ Finset.univ.erase (1 : G), if σ ∈ H then 1 else 0) = Nat.card H - 1 := by
  classical
  rw [← Finset.card_filter, Finset.filter_erase,
    Finset.card_erase_of_mem (by simp [H.one_mem]), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem sum_lowerRamificationDepthCount_erase_one [Fintype G] [DecidableEq G] (N : ℕ) :
    (∑ σ ∈ Finset.univ.erase (1 : G), lowerRamificationDepthCount B G N σ)
      = lowerRamificationFiltrationSum B G N := by
  classical
  simp only [lowerRamificationDepthCount, lowerRamificationFiltrationSum, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    sum_erase_one_ite_mem (IsLocalRing.lowerRamificationGroup B G i)

end FiltrationSum

section StatementLayer

variable (A : Type*) [CommRing A] [IsDomain A]
variable (B : Type*) [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
variable [Algebra A B] [Module.IsTorsionFree A B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

def DifferentEqPowFiltrationSum : Prop :=
  ∀ N : ℕ, IsLocalRing.lowerRamificationGroup B G N = ⊥ →
    differentIdeal A B
      = IsLocalRing.maximalIdeal B ^ lowerRamificationFiltrationSum B G N

variable {A B G}

theorem differentEqPowFiltrationSum_of_cutoff {N : ℕ}
    (hN : IsLocalRing.lowerRamificationGroup B G N = ⊥)
    (h : differentIdeal A B
      = IsLocalRing.maximalIdeal B ^ lowerRamificationFiltrationSum B G N) :
    DifferentEqPowFiltrationSum A B G := by
  intro M hM
  rw [h, lowerRamificationFiltrationSum_eq_of_eq_bot hN hM]

end StatementLayer



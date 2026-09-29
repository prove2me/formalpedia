-- Prove2me | Definitions.Def_ValuationSubring_ResidueValuationSubring
-- name    : ValuationSubring_ResidueValuationSubring
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/e250c55b-fd0b-5928-9bba-3e6dbc56342c
-- title:
--   Residue valuation subring of a pair of comparable valuation subrings
-- statement:
--   Let $L$ be a field and let $A \le S$ be valuation subrings of $L$. Write $\mathrm{ResidueField}\,S = S/\mathfrak m_S$ and let $\mathrm{residue}\,S \colon S \to \mathrm{ResidueField}\,S$ be the quotient map. [`ValuationSubring.residueValuationSubring A S h`](../def/ValuationSubring_ResidueValuationSubring.html#L11) is the valuation subring of $\mathrm{ResidueField}\,S$ whose underlying subring is the range of the composite of the inclusion $A \hookrightarrow S$ (supplied by `h : A ≤ S`) with $\mathrm{residue}\,S$, i.e. the image $\bar A$ of $A$ in the residue field of $S$. That this subring is a valuation subring, namely that every $x \in \mathrm{ResidueField}\,S$ satisfies $x \in \bar A$ or $x^{-1} \in \bar A$, is verified by lifting $x$ to some $s \in S$ and distinguishing the cases $s \in A$, $s$ a unit of $S$ with $s^{-1} \in A$ (so that $x^{-1}$ is the class of $s^{-1}$), and $s$ a non-unit of $S$ (so that $x = 0$). Classically $\bar A$ is the valuation ring of the residue valuation in the decomposition of the valuation of $A$ as a composite of the valuation of $S$ with a valuation of $\kappa(S)$.
--
--   Alongside it, [`ValuationSubring.toResidueValuationSubring A S h`](../def/ValuationSubring_ResidueValuationSubring.html#L29) is the ring homomorphism $A \to \bar A$ obtained by restricting the codomain of $A \hookrightarrow S \to \mathrm{ResidueField}\,S$, so it sends $a$ to the class of $a$ modulo $\mathfrak m_S$. The remaining declarations record its basic properties: `mem_residueValuationSubring_iff` characterises the elements of $\bar A$ as the residues of elements of $A$; `coe_toResidueValuationSubring` identifies the value of the map in $\mathrm{ResidueField}\,S$ with $\mathrm{residue}\,S$ applied to the image of $a$ in $S$; `toResidueValuationSubring_surjective` states surjectivity; and `ker_toResidueValuationSubring` identifies its kernel with `A.idealOfLE S h`, the prime $\mathfrak m_S \cap A$ of $A$ attached to the coarsening $S$. Consequently $\bar A \cong A/(\mathfrak m_S \cap A)$ as rings.
--
--   **Relation to Mathlib.** Built on Mathlib's `ValuationSubring`, `ValuationSubring.ofSubring`, `ValuationSubring.inclusion`, `ValuationSubring.idealOfLE` and `IsLocalRing.residue`; the passage from a pair $A \le S$ to the induced valuation subring of the residue field of $S$, together with the surjection from $A$ onto it, is added here.
--
--   **Where it is used.** These constructions make the decomposition of a valuation into a coarsening and a residue valuation available, so that a valuation ring with a finite chain of primes can be studied inductively through the rank-one valuation rings arising in the residue fields of its coarsenings; the module is used by the valuation-theoretic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ValuationSubring_ResidueValuationSubring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ValuationSubring

open IsLocalRing

variable {L : Type*} [Field L]

noncomputable def residueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    ValuationSubring (ResidueField S) :=
  ValuationSubring.ofSubring ((residue S).comp (A.inclusion S h)).range <| by
    intro x
    obtain ⟨s, rfl⟩ := residue_surjective x
    rcases A.mem_or_inv_mem (s : L) with hs | hs
    · exact Or.inl ⟨⟨s, hs⟩, rfl⟩
    · by_cases hu : IsUnit s
      · obtain ⟨u, rfl⟩ := hu
        have hinv : (((u⁻¹ : Sˣ) : S) : L) = ((u : S) : L)⁻¹ := map_units_inv S.subtype u
        refine Or.inr ⟨⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩, ?_⟩
        change residue S (A.inclusion S h ⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩) = (residue S u)⁻¹
        rw [← map_units_inv]
        rfl
      · refine Or.inl ⟨0, ?_⟩
        rw [map_zero, eq_comm, residue_eq_zero_iff]
        exact (_root_.mem_nonunits_iff.mpr hu)

noncomputable def toResidueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    A →+* A.residueValuationSubring S h :=
  ((residue S).comp (A.inclusion S h)).codRestrict (A.residueValuationSubring S h) fun a => ⟨a, rfl⟩

variable (A S : ValuationSubring L) (h : A ≤ S)

theorem mem_residueValuationSubring_iff {x : ResidueField S} :
    x ∈ A.residueValuationSubring S h ↔ ∃ a : A, residue S (A.inclusion S h a) = x :=
  Iff.rfl

@[simp]
theorem coe_toResidueValuationSubring (a : A) :
    (A.toResidueValuationSubring S h a : ResidueField S) = residue S (A.inclusion S h a) :=
  rfl

theorem toResidueValuationSubring_surjective :
    Function.Surjective (A.toResidueValuationSubring S h) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

theorem ker_toResidueValuationSubring :
    RingHom.ker (A.toResidueValuationSubring S h) = A.idealOfLE S h := by
  ext a
  rw [RingHom.mem_ker, ← Subtype.coe_inj, coe_toResidueValuationSubring, ZeroMemClass.coe_zero,
    residue_eq_zero_iff]
  rfl

end ValuationSubring



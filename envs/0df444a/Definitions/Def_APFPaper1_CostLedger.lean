-- Prove2me | Definitions.Def_APFPaper1_CostLedger
-- name    : APFPaper1_CostLedger
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-08T14:01:18.257978+00:00
-- url     : https://prove2.me/theorems/c6fe6009-916e-40a2-9422-38e57f96e751
-- title:
--   Original protocol bills, service and infimal family cost
-- statement:
--   Ledger D P Record exposes the unchanged original admitted protocols, tested distinctions, record support and complete non-null calibrated bills. The same original empty protocol has the explicit source-convention zero bill. Full-domain restrict/reconstruct correspondence is proved under that convention. Service is realization of every family member from the same protocol's own maintained sufficient support. Carriage retains unrequested sufficient support. Nonnegativity, subfamily service, served-member carriage and an empty-family witness are theorems, not Ledger-law fields. Feasible and infimal cost retain their original nonempty-domain scope. The provider represents the original nonnegative complete calibrated bills on the unchanged admitted protocol domain, with the original empty protocol's zero bill fixed by Supplement2880–2883; it proves no new physical zero-cost law or calibration property.
-- source:
--   Paper1 Supplement v9.27:1754–1757,1778–1787,2188–2221,2615–2617,2767–2773,2880–2883,7092; inputs revision2026-10-04.1. Selected source-projection correction of the historical Ledger/costs/Feasible/cost facet. Original P,D,Record,complete bills and fixed resolution/perturbation/duration meanings are required source correspondence, not automatically established for arbitrary data. No resource or calibration law is asserted. The provider represents the original nonnegative complete calibrated bills on the unchanged admitted protocol domain, with the original empty protocol's zero bill fixed by Supplement2880–2883; it proves no new physical zero-cost law or calibration property.

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false
open Classical

namespace APFPaper1.Foundation

/-- Reconstruct the full bill from its restriction away from the SAME original
empty protocol. The zero branch represents Supplement v9.27:2880–2883; it is
not a theorem that an arbitrary original bill vanishes there. -/
noncomputable def billFromNonNull {P : Type*} (p0 : P)
    (g : {p : P // p ≠ p0} → NNReal) (p : P) : NNReal :=
  if h : p = p0 then 0 else g ⟨p, h⟩

/-- Full-domain bill preservation under the explicitly stated original
empty-protocol zero-bill convention. No original protocol is added or removed. -/
theorem billFromNonNull_restrict {P : Type*} (p0 : P) (b : P → NNReal)
    (hzero : b p0 = 0) (p : P) :
    billFromNonNull p0 (fun q => b q.val) p = b p := by
  by_cases h : p = p0
  · subst p
    simp [billFromNonNull, hzero]
  · simp [billFromNonNull, h]

/-- Restricting reconstruction recovers every original non-null bill value. -/
theorem billFromNonNull_nonNull {P : Type*} (p0 : P)
    (g : {p : P // p ≠ p0} → NNReal) (p : {p : P // p ≠ p0}) :
    billFromNonNull p0 g p.val = g p := by
  simp [billFromNonNull, p.property]

/-- Cost-only source projection on the unchanged original admitted P, tested D,
and Record domains, at the fixed resolution, perturbations and duration.
nonNullBill is the COMPLETE original calibrated bill, including all resource
charges, on each non-null original p. nullProtocol denotes the original empty
protocol. Its zero bill is the visible source convention, not a new input.
The three support predicates retain their original source meanings. Arbitrary
values of this structure are not thereby certified as physical source data.
No calibration, resource-equality, action, or composition law is asserted. -/
structure Ledger (D P Record : Type*) where
  nullProtocol : P
  nonNullBill : {p : P // p ≠ nullProtocol} → NNReal
  maintained : P → Set Record
  sufficient : P → Set Record → D → Prop
  usesToRealize : P → D → Set Record → Prop

namespace Ledger
variable {D P Record : Type*}

noncomputable def price (L : Ledger D P Record) (p : P) : ℝ :=
  (billFromNonNull L.nullProtocol L.nonNullBill p : ℝ)

/-- Same original realized-member certificate, using this p's own support. -/
def RealizesMember (L : Ledger D P Record) (p : P) (d : D) : Prop :=
  ∃ σ : Set Record,
    σ ⊆ L.maintained p ∧ L.sufficient p σ d ∧ L.usesToRealize p d σ

/-- One and the same originally admitted protocol realizes every member. -/
def serves (L : Ledger D P Record) (p : P) (S : Finset D) : Prop :=
  ∀ d ∈ S, L.RealizesMember p d

/-- Retains sufficient unrequested support; no converse to realization. -/
def carries (L : Ledger D P Record) (p : P) (d : D) : Prop :=
  ∃ σ : Set Record, σ ⊆ L.maintained p ∧ L.sufficient p σ d

theorem price_nonneg (L : Ledger D P Record) (p : P) : 0 ≤ L.price p := by
  exact (billFromNonNull L.nullProtocol L.nonNullBill p).property

theorem serves_mono (L : Ledger D P Record) (p : P) (S T : Finset D)
    (hST : S ⊆ T) (hT : L.serves p T) : L.serves p S := by
  intro d hd
  exact hT d (hST hd)

theorem carries_of_serves (L : Ledger D P Record) (p : P) (S : Finset D)
    (d : D) (hS : L.serves p S) (hd : d ∈ S) : L.carries p d := by
  obtain ⟨σ, hmaintained, hsufficient, _huse⟩ := hS d hd
  exact ⟨σ, hmaintained, hsufficient⟩

theorem empty_protocol (L : Ledger D P Record) :
    ∃ p, L.serves p ∅ ∧ L.price p = 0 := by
  refine ⟨L.nullProtocol, ?_, ?_⟩
  · intro d hd
    exact False.elim (Finset.notMem_empty d hd)
  · simp [price, billFromNonNull]

end Ledger

def costs {D P Record : Type*} (L : Ledger D P Record) (S : Finset D) : Set ℝ :=
  {c | ∃ p, L.serves p S ∧ L.price p = c}

def Feasible {D P Record : Type*} (L : Ledger D P Record) (S : Finset D) : Prop :=
  ∃ p, L.serves p S

/-- Physical cost claims retain Feasible; the totalized real infimum outside
that domain is not the source's positive-infinity cost of an empty class. -/
noncomputable def cost {D P Record : Type*} (L : Ledger D P Record) (S : Finset D) : ℝ :=
  sInf (costs L S)

end APFPaper1.Foundation



-- Prove2me | solution 1 for APFB07b.unique_minimum_determined_by_records
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T01:54:03.944202+00:00
-- url     : https://prove2.me/submissions/11f26ad9-5c0e-46d1-9bef-bbab9c9154cd

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFB07b_no_side_without_a_record
title: Where admissibility and cost depend only on the records kept, the unique minimum is the only configuration keeping its records, so it has a side on a distinction only where its records fix one
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B07b in its declared Lean form APFB07b.BWUniqueMinimum.
 Thm_APFB07b_unique_minimum_symmetry_and_variation (this seat, pass 20). The archive's
 APFLoFStrengthening.recorded_coordinate_iff (read as a statement, not imported): a coordinate is recoverable
 from a protocol exactly when recorded; its unavailable direction is "two states with identical records and
 different d outputs". FOUNDATION_INPUTS B02, second sentence (every combination of sides is held), is the
 reason such pairs exist; it is not consumed here. The author, 2026-11-14 18:31 HST: "I think what is
 realized has no side - this is the superposition part of the occupant?"
consumes_inputs: B07b, in the last theorem, as a hypothesis in its declared Lean form.
named_hypotheses: kept (each configuration keeps a set of records); hadm (a configuration keeping the same
 records as an admissible one is admissible); hcost (configurations keeping the same records cost the
 same). hcost is the bill as a sum over the records kept, said of A2's candidates. hadm needs "having its
 records is enough", which is named and NOT adopted. Neither is a declared input.
statement: (unique_minimum_determined_by_records) under hadm and hcost the unique minimum is the only
 configuration keeping its records. (no_side_without_a_record) so no configuration keeps the same records
 as the unique minimum and reads a two-valued distinction the other way. (no_unique_minimum_with_a_free_side)
 if every configuration has a partner keeping the same records and reading d the other way, there is no
 unique minimum. (B07b_excludes_a_free_side) the same with B07b in its declared form at one interface.
not_claimed: that A2's candidates are potential states, or that they are protocols; that what is realized
 has no side. The theorems say only that a unique minimum and a side not fixed by the records cannot both
 be had under hadm and hcost. No lane. No claim that the transfer is forced, that the carrier gap is closed
 or narrowed, or that Born is derived.
-/
import Theorems.Thm_APFB07b_unique_minimum_fixed_by_symmetry
import Theorems.Thm_APFB07b_no_unique_minimum_of_moving_symmetry
import Theorems.Thm_APFB07b_unique_minimum_has_no_side
import Theorems.Thm_APFB07b_B07b_excludes_turnover_symmetry
import Theorems.Thm_APFB07b_unique_minimum_locally_constant_explicit
import Theorems.Thm_APFB07b_unique_minimum_constant_of_finite_explicit
import Theorems.Thm_APFB07b_infinite_of_unique_minimum_changes_explicit
import Theorems.Thm_APFB07b_B07_realized_constant_of_finite_explicit

set_option autoImplicit false
namespace APFB07b

variable {Configuration Record : Type*}

/-- Where admissibility and cost depend only on the records kept, the unique minimum is the only
configuration keeping its records. -/
theorem unique_minimum_determined_by_records (adm : Configuration → Prop)
    (cost : Configuration → ℝ) (kept : Configuration → Set Record)
    (hadm : ∀ G H, kept G = kept H → adm G → adm H)
    (hcost : ∀ G H, kept G = kept H → cost G = cost H)
    (G : Configuration) (hmin : IsMinimum adm cost G)
    (huniq : ∀ H, IsMinimum adm cost H → H = G) (H : Configuration) (hk : kept H = kept G) :
    H = G :=
  huniq H ⟨hadm G H hk.symm hmin.1, fun K hK => by rw [hcost H G hk]; exact hmin.2 K hK⟩

/-- No configuration keeps the same records as the unique minimum and reads a two-valued
distinction the other way. -/
theorem no_side_without_a_record (adm : Configuration → Prop)
    (cost : Configuration → ℝ) (kept : Configuration → Set Record)
    (hadm : ∀ G H, kept G = kept H → adm G → adm H)
    (hcost : ∀ G H, kept G = kept H → cost G = cost H)
    (reads : Configuration → Bool)
    (G : Configuration) (hmin : IsMinimum adm cost G)
    (huniq : ∀ H, IsMinimum adm cost H → H = G) :
    ¬ ∃ H, kept H = kept G ∧ reads H = !reads G := by
  rintro ⟨H, hk, hr⟩
  rw [unique_minimum_determined_by_records adm cost kept hadm hcost G hmin huniq H hk] at hr
  cases hd : reads G <;> rw [hd] at hr <;> exact absurd hr (by decide)

/-- If every configuration has a partner keeping the same records and reading `d` the other way,
there is no unique minimum. -/
theorem no_unique_minimum_with_a_free_side (adm : Configuration → Prop)
    (cost : Configuration → ℝ) (kept : Configuration → Set Record)
    (hadm : ∀ G H, kept G = kept H → adm G → adm H)
    (hcost : ∀ G H, kept G = kept H → cost G = cost H)
    (reads : Configuration → Bool)
    (hfree : ∀ G, ∃ H, kept H = kept G ∧ reads H = !reads G) :
    ¬ ∃ G, IsMinimum adm cost G ∧ ∀ H, IsMinimum adm cost H → H = G := by
  rintro ⟨G, hmin, huniq⟩
  exact no_side_without_a_record adm cost kept hadm hcost reads G hmin huniq (hfree G)

/-- B07b in its declared form, at one interface: it excludes a two-valued distinction that the
records kept leave free. -/
theorem B07b_excludes_a_free_side {Interface : Type*} {Config : Interface → Type*}
    (originalAdmissible : (i : Interface) → Config i → Prop)
    (totalCost : (i : Interface) → Config i → ℝ)
    (hB : BWUniqueMinimum originalAdmissible totalCost) (i : Interface)
    (kept : Config i → Set Record)
    (hadm : ∀ G H, kept G = kept H → originalAdmissible i G → originalAdmissible i H)
    (hcost : ∀ G H, kept G = kept H → totalCost i G = totalCost i H)
    (reads : Config i → Bool)
    (hfree : ∀ G, ∃ H, kept H = kept G ∧ reads H = !reads G) : False :=
  no_unique_minimum_with_a_free_side (originalAdmissible i) (totalCost i) kept hadm hcost reads
    hfree (hB i)

end APFB07b

#print axioms APFB07b.unique_minimum_determined_by_records
#print axioms APFB07b.no_side_without_a_record
#print axioms APFB07b.no_unique_minimum_with_a_free_side
#print axioms APFB07b.B07b_excludes_a_free_side


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {Configuration : Type apfNative_u_1} {Record : Type apfNative_u_2} (adm : Configuration → Prop)
  (cost : Configuration → Real) (kept : Configuration → Set.{apfNative_u_2} Record)
  (hadm :
    ∀ (G H : Configuration), @Eq.{apfNative_u_2 + 1} (Set.{apfNative_u_2} Record) (kept G) (kept H) → adm G → adm H)
  (hcost :
    ∀ (G H : Configuration),
      @Eq.{apfNative_u_2 + 1} (Set.{apfNative_u_2} Record) (kept G) (kept H) → @Eq.{1} Real (cost G) (cost H))
  (G : Configuration) (hmin : @APFB07b.IsMinimum.{apfNative_u_1} Configuration adm cost G)
  (huniq :
    ∀ (H : Configuration),
      @APFB07b.IsMinimum.{apfNative_u_1} Configuration adm cost H → @Eq.{apfNative_u_1 + 1} Configuration H G)
  (H : Configuration) (hk : @Eq.{apfNative_u_2 + 1} (Set.{apfNative_u_2} Record) (kept H) (kept G)),
  @Eq.{apfNative_u_1 + 1} Configuration H G := by
  exact @APFB07b.unique_minimum_determined_by_records

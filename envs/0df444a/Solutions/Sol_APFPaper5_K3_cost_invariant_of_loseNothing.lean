-- Prove2me | solution 1 for APFPaper5.K3.cost_invariant_of_loseNothing
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:20:30.389552+00:00
-- url     : https://prove2.me/submissions/d758d161-b98e-4ccc-b34a-62c1829fb5f2

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_cost_invariant
title: Turns that lose nothing and never raise cost leave cost unchanged, and two realized configurations of one admissible set cost the same
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper5_K3_Continuity (TurnsLoseNothing, adopted 2026-11-12). FOUNDATION_INPUTS B07a (A2), in
 the written-out form of its formal reference A2Selection: the realized configuration is admissible and no
 admissible configuration is cheaper. Fidelity of that form is NOT certified.
consumes_inputs: (realized_cost_eq) A2, as two hypotheses in the written-out form. The first theorem consumes
 none.
statement: (cost_invariant_of_loseNothing) if every admissible turn is undone by an admissible turn and no
 admissible turn raises cost, every admissible turn leaves cost unchanged. (realized_cost_eq) if s and t are
 both realized in the sense of A2 for one admissible set and one price, they have the same price.
not_claimed: that an admissible turn never raises cost; that turns carry realized configurations to realized
 configurations; that the price in A2 is the cost on combinations used in the plane theorem.
-/
import Definitions.Def_APFPaper5_K3_Continuity

set_option autoImplicit false
namespace APFPaper5.K3

universe u
variable {S : Type u}

theorem cost_invariant_of_loseNothing (Adm : Set (S → S)) (h : TurnsLoseNothing Adm)
    (cost : S → ℝ) (hnoraise : ∀ f ∈ Adm, ∀ s : S, cost (f s) ≤ cost s) :
    ∀ f ∈ Adm, ∀ s : S, cost (f s) = cost s := by
  intro f hf s
  obtain ⟨g, hg, hgf⟩ := h f hf
  have h1 := hnoraise f hf s
  have h2 := hnoraise g hg (f s)
  rw [hgf s] at h2
  exact le_antisymm h1 h2

theorem realized_cost_eq (admissible : Set S) (price : S → ℝ) (s t : S)
    (hs : s ∈ admissible ∧ ∀ a ∈ admissible, price s ≤ price a)
    (ht : t ∈ admissible ∧ ∀ a ∈ admissible, price t ≤ price a) : price s = price t :=
  le_antisymm (hs.2 t ht.1) (ht.2 s hs.1)

end APFPaper5.K3


universe apfNative_u
theorem solution :
∀ {S : Type apfNative_u} (Adm : Set.{apfNative_u} (S → S)) (h : @APFPaper5.K3.TurnsLoseNothing.{apfNative_u} S Adm)
  (cost : S → Real)
  (hnoraise :
    ∀ (f : S → S),
      @Membership.mem.{apfNative_u, apfNative_u} (S → S) (Set.{apfNative_u} (S → S))
          (@Set.instMembership.{apfNative_u} (S → S)) Adm f →
        ∀ (s : S), @LE.le.{0} Real Real.instLE (cost (f s)) (cost s))
  (f : S → S),
  @Membership.mem.{apfNative_u, apfNative_u} (S → S) (Set.{apfNative_u} (S → S))
      (@Set.instMembership.{apfNative_u} (S → S)) Adm f →
    ∀ (s : S), @Eq.{1} Real (cost (f s)) (cost s) := by
  exact @APFPaper5.K3.cost_invariant_of_loseNothing

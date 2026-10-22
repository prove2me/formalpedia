-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
-- name    : LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:19:03.962989+00:00
-- url     : https://prove2.me/theorems/51e6b426-02ce-46c0-91d3-f479fc6ccfac
-- title:
--   Coordinate Power Cofinality for localized persistent commutative algebra
-- statement:
--   This bundle supplies coordinate Power Cofinality for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Diagonal powers of the selected coordinates. The exponent is positive, including at diagram index zero. These ideals live in the ambient polynomial ring.
--   - Every ideal whose radical contains the coordinate support contains one of the diagonal power ideals. Only finite generation of that support is needed.
--   - Replacing ordinary ideal powers by coordinate powers preserves the actual Ext-colimit local-cohomology functor. No Cech or Koszul comparison is assumed.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CoordinatePowerCofinality.lean, selected declarations in lines 16–89; source SHA-256 cc47e03ebe267821bbda40efaf11869292a7d8c09df42f67a4c64f86b4df8506; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA

set_option autoImplicit false

namespace LPCA

open Opposite CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

/-- Diagonal powers of the selected coordinates. The exponent is positive,
including at diagram index zero. These ideals live in the ambient polynomial ring. -/
noncomputable def coordinatePowerIdeal (T : Finset V) (n : ℕ) : Ideal (MvPolynomial V k) :=
  Ideal.span ((fun j => (MvPolynomial.X j : MvPolynomial V k) ^ (n + 1)) '' (T : Set V))

theorem coordinateIdeal_fg (T : Finset V) : (coordinateIdeal k T).FG := by
  exact Submodule.fg_span (T.finite_toSet.image MvPolynomial.X)

theorem coordinatePowerIdeal_le_power (T : Finset V) (n : ℕ) :
    coordinatePowerIdeal k T n ≤ coordinateIdeal k T ^ (n + 1) := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, hj, rfl⟩
  have hjI : (MvPolynomial.X j : MvPolynomial V k) ∈ coordinateIdeal k T :=
    Ideal.subset_span ⟨j, hj, rfl⟩
  exact Ideal.pow_mem_pow hjI (n + 1)

theorem coordinateIdeal_le_radical_power (T : Finset V) (n : ℕ) :
    coordinateIdeal k T ≤ (coordinatePowerIdeal k T n).radical := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, hj, rfl⟩
  exact ⟨n + 1, Ideal.subset_span ⟨j, hj, rfl⟩⟩

theorem coordinatePowerIdeal_antitone (T : Finset V) :
    Antitone (coordinatePowerIdeal k T) := by
  intro n m hnm
  apply Ideal.span_le.mpr
  rintro p ⟨j, hj, rfl⟩
  exact (coordinatePowerIdeal k T n).pow_mem_of_pow_mem
    (Ideal.subset_span ⟨j, hj, rfl⟩) (Nat.add_le_add_right hnm 1)

/-- Every ideal whose radical contains the coordinate support contains one
of the diagonal power ideals. Only finite generation of that support is needed. -/
theorem exists_coordinatePowerIdeal_le
    (T : Finset V) (J : Ideal (MvPolynomial V k))
    (hJ : coordinateIdeal k T ≤ J.radical) :
    ∃ n, coordinatePowerIdeal k T n ≤ J := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ (coordinateIdeal_fg k T)
  exact ⟨n, (coordinatePowerIdeal_le_power k T n).trans
    ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn)⟩

noncomputable def coordinatePowersDiagram (T : Finset V) : ℕᵒᵖ ⥤ Ideal (MvPolynomial V k) where
  obj n := coordinatePowerIdeal k T (unop n)
  map f := ⟨⟨coordinatePowerIdeal_antitone k T f.unop.down.down⟩⟩

noncomputable def coordinatePowersToSelfLERadical (T : Finset V) :
    ℕᵒᵖ ⥤ localCohomology.SelfLERadical (coordinateIdeal k T) :=
  ObjectProperty.lift _ (coordinatePowersDiagram k T)
    (fun n => coordinateIdeal_le_radical_power k T (unop n))

noncomputable instance coordinatePowers_initial (T : Finset V) :
    Functor.Initial (coordinatePowersToSelfLERadical k T) where
  out J := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨n, hn⟩ := exists_coordinatePowerIdeal_le k T J.1 J.2
      exact ⟨CostructuredArrow.mk
        (⟨⟨⟨hn⟩⟩⟩ : (coordinatePowersToSelfLERadical k T).obj (op n) ⟶ J)⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right
        exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left
        exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

variable [Fintype V]

/-- Replacing ordinary ideal powers by coordinate powers preserves the actual
Ext-colimit local-cohomology functor. No Cech or Koszul comparison is assumed. -/
noncomputable def coordinatePowersLocalCohomologyIso (T : Finset V) (q : ℕ) :
    localCohomology.ofDiagram (coordinatePowersDiagram k T) q ≅
      localCohomology (coordinateIdeal k T) q :=
  localCohomology.isoOfFinal.{u, u, 0} (coordinatePowersToSelfLERadical k T)
    (localCohomology.selfLERadicalDiagram (coordinateIdeal k T)) q ≪≫
      localCohomology.isoSelfLERadical (coordinateIdeal k T) q

end LPCA



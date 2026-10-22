-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:28:49.8874+00:00
-- url     : https://prove2.me/theorems/1e312105-46e4-4127-af95-35cd32d82762
-- title:
--   Simplicial face families and Koszul support indices
-- statement:
--   This bundle supplies simplicial face families and Koszul support indices. These are declarations about finite downward-closed face families and their selected index predicates, including the distinct void and {empty face} complexes. The Koszul-family predicate is combinatorial support data; it does not itself construct a polynomial resolution or assert exactness.
--
--   The included constructions and necessary compatibility results are:
--
--   - A simplicial complex on the vertex set `V`: a finite family of finsets closed under taking subsets. The empty set may be a face: `faces = {∅}` is the complex `{∅}` and `faces = ∅` is the void complex.
--   - `K ≤ L` iff every face of `K` is a face of `L` (`K` is a subcomplex of `L`).
--   - The indicator vector `1_J ∈ ℤ^V`.
--   - The support `{v : a v ≠ 0}` of a multidegree `a ∈ ℤ^V`.
--   - Index family of the Koszul cochain complex `K^•(k[Γ])_b`: the `J ⊆ V` with `k[Γ]_{b + 1_J} ≠ 0`, i.e. `b + 1_J ≥ 0` and `supp(b + 1_J) ∈ Γ`.
--   - Index family of the reduced cochain complex of `K`: the faces of `K`.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SrFamily/Common.lean, selected declarations in lines 10–53; source SHA-256 16a883955946d7e9bdd038e60012394fcb7677b3656c0e7afc040fd2ce62e6d6; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs

namespace Proofs.BassLyubeznik.SrFamily

open Finset Proofs.BassLyubeznik.SignedCore

universe u

/-- A simplicial complex on the vertex set `V`: a finite family of finsets closed under taking
subsets. The empty set may be a face: `faces = {∅}` is the complex `{∅}` and `faces = ∅` is the
void complex (the paper's convention; Mathlib's `PreAbstractSimplicialComplex` excludes `∅`). -/
structure SComplex (V : Type u) [DecidableEq V] where
  faces : Finset (Finset V)
  down_closed : ∀ ⦃s t : Finset V⦄, s ∈ faces → t ⊆ s → t ∈ faces

variable {V : Type u} [LinearOrder V] [Fintype V]

namespace SComplex

/-- `K ≤ L` iff every face of `K` is a face of `L` (`K` is a subcomplex of `L`). -/
instance : LE (SComplex V) := ⟨fun K L => K.faces ⊆ L.faces⟩

theorem le_def {K L : SComplex V} : K ≤ L ↔ K.faces ⊆ L.faces := Iff.rfl



end SComplex

/-- The indicator vector `1_J ∈ ℤ^V`. -/
def indic (J : Finset V) : V → ℤ := fun v => if v ∈ J then 1 else 0

/-- The support `{v : a v ≠ 0}` of a multidegree `a ∈ ℤ^V`. -/
def supp (a : V → ℤ) : Finset V := univ.filter (fun v => a v ≠ 0)

/-- Index family of the Koszul cochain complex `K^•(k[Γ])_b`: the `J ⊆ V` with `k[Γ]_{b + 1_J} ≠ 0`,
i.e. `b + 1_J ≥ 0` and `supp(b + 1_J) ∈ Γ`. -/
def koszulFamily (Γ : SComplex V) (b : V → ℤ) (J : Finset V) : Prop :=
  (∀ v, 0 ≤ b v + indic J v) ∧ supp (b + indic J) ∈ Γ.faces

instance (Γ : SComplex V) (b : V → ℤ) : DecidablePred (koszulFamily Γ b) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Index family of the reduced cochain complex of `K`: the faces of `K`. -/
def faceFamily (K : SComplex V) (τ : Finset V) : Prop := τ ∈ K.faces

instance (K : SComplex V) : DecidablePred (faceFamily K) :=
  fun τ => inferInstanceAs (Decidable (τ ∈ K.faces))

end Proofs.BassLyubeznik.SrFamily



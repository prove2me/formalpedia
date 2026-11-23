-- Prove2me | Definitions.Def_SimpleRbrFri_State
-- name    : SimpleRbrFri_State
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:54:12.289282+00:00
-- url     : https://prove2.me/theorems/31c2c449-0b8a-41bf-9f6f-ced62a64705e
-- title:
--   State
-- statement:
--   Definitions and structural lemmas for State, from zksecurity/simple-rbr-fri contributors (see pinned LICENSE and source headers)'s pinned Round-by-round soundness and completeness of FRI development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean

import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
noncomputable def FRI_distance_star (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) : ℝ :=
  let dist := relDistanceToSet f_0 (FRI_code P 0).carrier
  min dist (1 - bound - 1 / P.D_0.card)
def FRI_Is_Large_Subset (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : ℕ) (hi : i < P.num_foldings) (S : Finset F) : Prop :=
  S ⊆ FRI_domain P i ∧
  (pow_domain S (P.m ⟨i, hi⟩)).card ≥
    (1 - FRI_distance_star P f_0 bound) * (FRI_domain P (i + 1)).card
def FRI_BadEvent (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) (alpha : F) : Prop :=
  ∃ (S : Finset F),
    FRI_Is_Large_Subset P f_0 bound i i.isLt S ∧
    let m := P.m i
    let D_next := FRI_domain P ((i : ℕ) + 1)
    let S_next := pow_domain S m
    (∃ (u : FRI_domain P ((i : ℕ) + 1) → F), u ∈ FRI_code P ((i : ℕ) + 1) ∧
      ∀ z, z ∈ S_next →
        Fold (FRI_domain P i) m (extend_by_zero (FRI_domain P i) f_prev) alpha z =
          extend_by_zero D_next u z) ∧
    (∀ (v : FRI_domain P i → F), v ∈ FRI_code P i →
      ¬ ∀ x, x ∈ S → extend_by_zero (FRI_domain P i) f_prev x = extend_by_zero (FRI_domain P i) v x)
open scoped Classical in
/-- The probability of the bad event for round i (using FRI_BadEvent) -/
noncomputable def FRI_BadEvent_Prob [Fintype F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) : ℝ :=
  let bad_set := Finset.univ.filter (fun alpha => FRI_BadEvent P f_0 bound i f_prev alpha)
  (bad_set.card : ℝ) / Fintype.card F
def FRI_oracle_at_round (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (hi : i < P.num_foldings) : FRI_domain P i → F :=
  if h0 : i = 0 then
    fun x ↦ f_0 ⟨x.val, by simpa only [FRI_domain, h0] using x.property⟩
  else
    have hi' : i - 1 < P.num_foldings := by grind
    fun x ↦ T.f ⟨i - 1, hi'⟩ ⟨x.val, by grind⟩
def FRI_State (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P) : ℕ → Prop
  | 0 => f_0 ∈ (FRI_code P 0).carrier
  | i + 1 =>
    if h : i < P.num_foldings then
      FRI_State P f_0 bound T i ∨
      FRI_BadEvent P f_0 bound ⟨i, h⟩ (FRI_oracle_at_round P f_0 T i h) (T.alpha ⟨i, h⟩)
    else if i = P.num_foldings then
      FRI_State P f_0 bound T i ∨ FRI_verifier_accepts P f_0 T
    else
      FRI_State P f_0 bound T i
noncomputable def poly_component {F : Type*} [Semiring F]
    (P : Polynomial F) (m : ℕ) (j : Fin m) : Polynomial F :=
  ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff (k * m + j)) * Polynomial.X ^ k
def domain_congr_map {F : Type*} [Field F] {A B : Type*} (e : A ≃ B) : (B → F) →ₗ[F] (A → F) where
  toFun f := f ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
section FRI_MCA_And_Query_Analysis
def FRI_MCA_Hypothesis [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F)
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ) : Prop :=
  ∀ (i : Fin P.num_foldings),
    MutualCorrelatedAgreement powersGenerator
      (FRI_code P i.succ)
      bound errorstar
open scoped Classical in
/-- Bad query points: points in D_0 that pass all local checks -/
noncomputable def FRI_BadQuery_Points (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) : Finset {x // x ∈ P.D_0} :=
  P.D_0.attach.filter (fun s => ∀ i, FRI_local_check P f_0 T s i)
noncomputable def FRI_W (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) : ℕ → Finset F
  | 0 => (FRI_BadQuery_Points P f_0 T).image Subtype.val
  | i + 1 => if h : i < P.num_foldings then pow_domain (FRI_W P f_0 T i) (P.m ⟨i, h⟩) else ∅
def FRI_Domain_Size_Property (P : FRIParameters F) : Prop :=
  ∀ i (h : i < P.num_foldings), (FRI_domain P i).card = P.m ⟨i, h⟩ * (FRI_domain P (i + 1)).card
open scoped Classical in
/-- Query phase acceptance probability -/
noncomputable def FRI_query_prob [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P) : ENNReal :=
  if _ : Nonempty {x // x ∈ P.D_0} then
    have : Nonempty (Fin P.q_rep → {x // x ∈ P.D_0}) := instNonemptyForall
    (PMF.uniformOfFintype (Fin P.q_rep → {x // x ∈ P.D_0})).toMeasure {s |
      let T' := {T with s := s}
      FRI_State P f_0 bound T' (P.num_foldings + 1)}
  else 0
end FRI_MCA_And_Query_Analysis



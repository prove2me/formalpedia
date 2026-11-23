-- Prove2me | Definitions.Def_SimpleRbrFri_Core
-- name    : SimpleRbrFri_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:52:30.544746+00:00
-- url     : https://prove2.me/theorems/5a4afecd-e4bb-4f77-9c18-2865db121d46
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from zksecurity/simple-rbr-fri contributors (see pinned LICENSE and source headers)'s pinned Round-by-round soundness and completeness of FRI development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean

import Mathlib
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
noncomputable def relDistance {D S : Type*} [Fintype D] [DecidableEq S] (f g : D → S) : ℝ :=
  (hammingDist f g : ℝ) / Fintype.card D
noncomputable def relDistanceToSet {D S : Type*} [Fintype D] [DecidableEq S]
    (f : D → S) (C : Set (D → S)) : ℝ :=
  sInf (relDistance f '' C)
def IsFoldable {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) : Prop :=
  ∃ (H : Subgroup Fˣ) (a : Fˣ),
    (D : Set F) = (a • (H : Set Fˣ)).image (fun (x : Fˣ) => (x : F)) ∧
    m ∣ D.card
def pow_domain {F : Type*} [CommMonoid F] [DecidableEq F] (D : Finset F) (m : ℕ) : Finset F :=
  D.image (fun x => x ^ m)
def evalOn {F : Type*} [Field F] (D : Finset F) : Polynomial F →ₗ[F] (D → F) where
  toFun p := fun x ↦ p.eval x
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
noncomputable def reedSolomon {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (d : ℕ) :
    Submodule F (D → F) :=
  (Polynomial.degreeLT F d).map (evalOn D)
def Block {F : Type*} [CommMonoid F] [DecidableEq F] (D : Finset F) (m : ℕ) (z : F) : Finset F :=
  D.filter (fun y => y ^ m = z)
noncomputable def Fold {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (f : F → F) (alpha : F) (z : F) : F :=
  (Lagrange.interpolate (Block D m z) id f).eval alpha
structure FRIParameters (F : Type*) [Field F] [DecidableEq F] where
  D_0 : Finset F
  d_0 : ℕ
  num_foldings : ℕ
  m : Fin num_foldings → ℕ
  q_rep : ℕ
  h_D0_foldable : IsFoldable D_0 (∏ i, m i)
  h_d0_le_D0 : d_0 ≤ D_0.card / 2
  h_m_pos : ∀ i, m i > 0
  h_m_dvd_d : (∏ i, m i) ∣ d_0
  h_d0_pos : 0 < d_0
def FRI_domain {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) : ℕ → Finset F
  | 0 => P.D_0
  | i + 1 => if h : i < P.num_foldings then pow_domain (FRI_domain P i) (P.m ⟨i, h⟩) else ∅
def FRI_prod_tail {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (i : ℕ) : ℕ :=
  ∏ j ∈ (Finset.univ : Finset (Fin P.num_foldings)).filter
    (fun j : Fin P.num_foldings => i ≤ (j : ℕ)), P.m j
def FRI_degree {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) : ℕ → ℕ
  | 0 => P.d_0
  | i + 1 => if h : i < P.num_foldings then FRI_degree P i / (P.m ⟨i, h⟩) else 0
noncomputable def FRI_code {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (i : ℕ) :
    Submodule F (FRI_domain P i → F) :=
  reedSolomon (FRI_domain P i) (FRI_degree P i)
def folded_query {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (z : F) : ℕ → F
  | 0 => z
  | i + 1 => if h : i < P.num_foldings then (folded_query P z i) ^ (P.m ⟨i, h⟩) else 0
structure FRITranscript {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) where
  /-- Prover's folded functions. `f i` is the function at round i+1, defined on domain L_{i+1}. -/
  f : (i : Fin P.num_foldings) → FRI_domain P (i.val + 1) → F
  /-- Verifier's folding challenges α₁, ..., αₖ (0-indexed: `alpha i` = α_{i+1}) -/
  alpha : Fin P.num_foldings → F
  /-- Query points s₁, ..., sₜ -/
  s : Fin P.q_rep → P.D_0
structure FRIVerifierChallenges {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) where
  alpha : Fin P.num_foldings → F
  s : Fin P.q_rep → P.D_0
def FRI_get_val {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (i : Fin (P.num_foldings + 1)) (x : F) : F :=
  if h0 : i.val = 0 then
    if hx : x ∈ P.D_0 then f_0 ⟨x, hx⟩ else 0
  else
    have hi : i.val - 1 < P.num_foldings := by grind
    -- The domain at round i is FRI_domain P (i-1+1), which equals FRI_domain P i
    -- T.f ⟨i-1, hi⟩ expects an element of FRI_domain P ((i-1)+1) = FRI_domain P i
    if hx : x ∈ FRI_domain P i then
      have hx' : x ∈ FRI_domain P ((i.val - 1) + 1) := by grind
      T.f ⟨i.val - 1, hi⟩ ⟨x, hx'⟩
    else 0
def FRI_local_check {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (s : F) (i : Fin P.num_foldings) : Prop :=
  let f_prev := fun x => FRI_get_val P f_0 T i.castSucc x
  let f_next := fun x => FRI_get_val P f_0 T i.succ x
  let m := P.m i
  let alpha := T.alpha i
  let z := folded_query P s (i : ℕ).succ
  Fold (FRI_domain P i) m f_prev alpha z = f_next z
def FRI_fold_check {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (i : Fin P.num_foldings) (y : F) : Prop :=
  let f_prev := fun x => FRI_get_val P f_0 T i.castSucc x
  let f_next := fun x => FRI_get_val P f_0 T i.succ x
  let m := P.m i
  let alpha := T.alpha i
  Fold (FRI_domain P i) m f_prev alpha y = f_next y
def FRI_is_green {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (i : ℕ) (x : F) : Prop :=
  if h : i < P.num_foldings then
    let y := x ^ (P.m ⟨i, h⟩)
    FRI_is_green P f_0 T (i + 1) y ∧ FRI_fold_check P f_0 T ⟨i, h⟩ y
  else
    true
termination_by P.num_foldings - i
decreasing_by
  simp_wf
  omega
open scoped Classical in
/-- The set of Green nodes at layer i.

G_i := {x ∈ D_i : FRI_is_green(i, x)}

This is the set of nodes where all verifier checks pass along paths from the root.

**Reference:** Used in soundness proof on page 11 (Section 5.1). -/
noncomputable def FRI_green_set {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (i : ℕ) : Finset F :=
  (FRI_domain P i).filter (FRI_is_green P f_0 T i)
def FRI_final_oracle {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) : FRI_domain P P.num_foldings → F :=
  if h : P.num_foldings = 0 then
    fun x ↦
      have hx : x.val ∈ P.D_0 := by grind [FRI_domain]
      f_0 ⟨x.val, hx⟩
  else
    fun x ↦
      have hx' : x.val ∈ FRI_domain P ((P.num_foldings - 1) + 1) := by grind
      T.f ⟨P.num_foldings - 1, Nat.sub_one_lt h⟩ ⟨x.val, hx'⟩
def FRI_f {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (i : Fin (P.num_foldings + 1)) : FRI_domain P i → F :=
  if h0 : i.val = 0 then
    fun x ↦
      have hx : x.val ∈ P.D_0 := by simpa only [FRI_domain, h0] using x.property
      f_0 ⟨x.val, hx⟩
  else
    have hi : i.val - 1 < P.num_foldings := by grind
    fun x ↦
      have h_idx : i.val = (i.val - 1) + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)).symm
      have hx' : x.val ∈ FRI_domain P ((i.val - 1) + 1) := h_idx ▸ x.property
      T.f ⟨i.val - 1, hi⟩ ⟨x.val, hx'⟩
def FRI_verifier_accepts {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) : Prop :=
  let final_check := FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings
  let local_checks := ∀ (j : Fin P.q_rep) (i : Fin P.num_foldings),
    FRI_local_check P f_0 T (T.s j) i
  final_check ∧ local_checks
lemma FRI_domain_succ_eq {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (h : i < P.num_foldings) :
    FRI_domain P (i + 1) = pow_domain (FRI_domain P i) (P.m ⟨i, h⟩) := by
  simp only [FRI_domain, dif_pos h]
noncomputable def PowersBound (ρ : ℝ) : ℝ := (1 + ρ) / 2
def FRI_delta_star (bound : ℝ) (delta : ℝ) : ℝ :=
  min delta (1 - bound)
def FRI_error_fold (P : FRIParameters F) (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (i : Fin P.num_foldings) (delta : ℝ) : ℝ :=
  errorstar (P.m i) (FRI_delta_star bound delta)
def FRI_error_query (P : FRIParameters F) (bound : ℝ) (delta : ℝ) : ℝ :=
  (1 - FRI_delta_star bound delta) ^ P.q_rep
noncomputable def PowersError {F : Type*} [Fintype F] (m : ℕ) (d : ℕ) (ρ : ℝ) : ℝ :=
  ((m - 1 : ℝ) * d) / (ρ * Fintype.card F)
noncomputable def FRI_code_cast {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) (i : ℕ)
    (h : i < P.num_foldings) :
    Submodule F ({ x // x ∈ pow_domain (FRI_domain P i) (P.m ⟨i, h⟩) } → F) :=
  (FRI_code P (i + 1)).map <|
    (LinearEquiv.funCongrLeft F F <|
      (Equiv.refl F).subtypeEquiv (p := (· ∈ pow_domain (FRI_domain P i) (P.m ⟨i, h⟩)))
        (q := (· ∈ FRI_domain P (i + 1))) (fun _ ↦ by simp [FRI_domain_succ_eq P i h])).toLinearMap
def extend_by_zero {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (f : D → F) : F → F :=
  fun x => if h : x ∈ D then f ⟨x, h⟩ else 0
def Folding_Bad_Event {F : Type*} [Field F] [DecidableEq F]
  (D : Finset F) (m : ℕ) (d : ℕ) (f : D → F) (alpha : F) (delta : ℝ) : Prop :=
  ∃ (S : Finset F),
    S ⊆ D ∧
    let D_next := pow_domain D m
    let S_next := pow_domain S m
    (S_next.card : ℝ) ≥ (1 - delta) * (D_next.card : ℝ) ∧
    (∃ (u : D_next → F), u ∈ reedSolomon D_next (d / m) ∧
      ∀ z, z ∈ S_next →
        Fold D m (extend_by_zero D f) alpha z =
          extend_by_zero D_next u z) ∧
    (∀ (v : D → F), v ∈ reedSolomon D d →
      ¬ ∀ x, x ∈ S → extend_by_zero D f x = extend_by_zero D v x)
def ProximityGenerator (F : Type*) [Field F] [DecidableEq F] := (m : ℕ) → PMF (Fin m → F)
def BadEvent {F : Type*} [Field F] [DecidableEq F] {L : Type*} [Fintype L]
    (C : Submodule F (L → F)) (m : ℕ) (f : Fin m → (L → F)) (δ : ℝ) (r : Fin m → F) : Prop :=
  ∃ S : Finset L, (S.card : ℝ) ≥ (1 - δ) * (Fintype.card L : ℝ) ∧
    (∃ u ∈ C, ∀ x ∈ S, u x = ∑ j, r j * f j x) ∧
    (∃ i : Fin m, ∀ u' ∈ C, ∃ x ∈ S, u' x ≠ f i x)
noncomputable def powersGenerator {F : Type*} [Field F] [DecidableEq F]
    [Fintype F] [Nonempty F] : ProximityGenerator F :=
  fun _m => (PMF.uniformOfFintype F).map (fun r i => r ^ (i : ℕ))
def MutualCorrelatedAgreement {F : Type*} [Field F] [DecidableEq F]
    [MeasurableSpace F] [DiscreteMeasurableSpace F] {L : Type*} [Fintype L]
    (Gen : ProximityGenerator F)
    (C : Submodule F (L → F))
    (bound : ℝ)
    (errorstar : ℕ → ℝ → ℝ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → (L → F)) (δ : ℝ),
    0 ≤ δ → δ < 1 - bound →
    (Gen m).toMeasure {r | BadEvent C m f δ r} ≤ ENNReal.ofReal (errorstar m δ)
noncomputable def folding_component {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (f : F → F) (i : Fin m) (z : F) : F :=
  (Lagrange.interpolate (Block D m z) id f).coeff i
noncomputable def folding_components {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (f : F → F) : Fin m → (pow_domain D m → F) :=
  fun i z => folding_component D m f i (z : F)
def FoldingBadEvent {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (C0 : Submodule F (D → F)) (C1 : Submodule F (pow_domain D m → F))
    (f : F → F) (delta : ℝ) (r : F) : Prop :=
  ∃ S : Finset F, S ⊆ D ∧
    let S_next := pow_domain S m
    (S_next.card : ℝ) ≥ (1 - delta) * (pow_domain D m).card ∧
    (∃ u' ∈ C1, ∀ z ∈ S_next, Fold D m f r z = if h : z ∈ pow_domain D m then u' ⟨z, h⟩ else 0) ∧
    (∀ u ∈ C0, ¬ ∀ x ∈ S, (if h : x ∈ D then u ⟨x, h⟩ else 0) = f x)
noncomputable def poly_from_components {F : Type*} [Semiring F]
    (m : ℕ) (P_i : Fin m → Polynomial F) : Polynomial F :=
  ∑ i : Fin m, (P_i i).comp (Polynomial.X ^ m) * Polynomial.X ^ (i : ℕ)
def reconstruct_func {F : Type*} [Field F] [DecidableEq F]
    (m : ℕ) (u : Fin m → F → F) (x : F) : F :=
  ∑ i : Fin m, u i (x ^ m) * x ^ (i : ℕ)



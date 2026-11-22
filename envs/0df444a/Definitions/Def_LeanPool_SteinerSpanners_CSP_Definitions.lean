-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_CSP_Definitions
-- name    : LeanPool_SteinerSpanners_CSP_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:17.489059+00:00
-- url     : https://prove2.me/theorems/e178a28a-7c4c-497b-9cd5-036bc30788ee
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Definitions.lean

module
public import Mathlib.Data.FinEnum
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
abbrev diffCoords {N q : ℕ} (x y : Fin N → Fin q) : Finset (Fin N) :=
  disagreeSet x y
abbrev dHam {N q : ℕ} (x y : Fin N → Fin q) : ℕ :=
  (disagreeSet x y).card
abbrev d3Coords {N q : ℕ} (x y z : Fin N → Fin q) : Finset (Fin N) :=
  threeWayDisagree x y z
def cspKMax (C₁ : ℕ) : ℕ := 8 * C₁
def cspKCh (C₁ : ℕ) : ℕ := 20 * C₁ ^ 2
def cspKMom (C₁ : ℕ) : ℕ := 20 * C₁ ^ 2
def cspInvEta0 (_C₁ : ℕ) : ℕ := 80
def cspLam0 (C₁ : ℕ) : ℕ := 100 * C₁ * (2 * Nat.clog 2 C₁ + 6)
def cspBeta0 (C₁ : ℕ) : ℕ := 6 * cspLam0 C₁
def cspGamma0 (C₁ : ℕ) : ℕ := 5 * cspLam0 C₁
def cspL (C₁ : ℕ) : ℕ := 20 + 20 * C₁ ^ 2 * cspInvEta0 C₁ * cspLam0 C₁
def cspEq (C₁ : ℕ) : ℕ := 2 * cspBeta0 C₁ * 2 ^ cspL C₁
def cspQ (C₁ : ℕ) : ℕ := 2 ^ cspEq C₁ + 1
abbrev cspIota (N q : ℕ) : Type :=
  (Fin N × Fin N × Fin q × Fin q) ⊕ (Fin N → Fin q)
def homQueries {N q : ℕ} (z : Fin N → Fin q) : Finset (Fin N × Fin N × Fin q × Fin q) :=
  (Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).image
    (fun uv => (uv.1, uv.2, z uv.1, z uv.2))
noncomputable def bernWeight {ι : Type*} [Fintype ι] (p : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i : ι, if ω i = true then p i else 1 - p i
noncomputable def cspSigmaEdge (C₁ r_star : ℕ) : ℝ :=
  ((cspEq C₁ + cspL C₁ + cspGamma0 C₁ + 2 : ℕ) : ℝ) / ((2 ^ cspL C₁ * r_star - 1 : ℕ) : ℝ)
noncomputable def cspPEdge (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ (- cspSigmaEdge C₁ r_star)
noncomputable def cspDOmega (C₁ r_star s : ℕ) : ℝ :=
  ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
    (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1) - s.choose 2)
noncomputable def cspDStar (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ ((1 / 4 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
noncomputable def cspPKeep (C₁ r_star : ℕ) : ℝ :=
  cspDStar C₁ r_star / cspDOmega C₁ r_star r_star
noncomputable def cspN0 (C₁ r_star : ℕ) : ℝ :=
  cspPKeep C₁ r_star * ((cspQ C₁ : ℝ) ^ (2 ^ cspL C₁ * r_star)) *
    (cspPEdge C₁ r_star) ^ ((2 ^ cspL C₁ * r_star).choose 2)
noncomputable def cspPIota (C₁ r_star : ℕ) : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → ℝ :=
  Sum.elim (fun _ => cspPEdge C₁ r_star) (fun _ => cspPKeep C₁ r_star)
noncomputable def cspGamma (r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ ((r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))
noncomputable def cspDeltaBad (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
def cspPoolCand {N q : ℕ} (C₁ r_star : ℕ) (a b : Fin N → Fin q) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun x : Fin N → Fin q =>
    x ≠ a ∧ x ≠ b ∧ dHam x a ≤ C₁ * r_star ∧ dHam x b ≤ C₁ * r_star)
def cspRvc {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) : Finset (Fin N × Fin q) :=
  Finset.univ.image (fun v : Fin N => (v, a v)) ∪
    Finset.univ.image (fun v : Fin N => (v, b v)) ∪
    Finset.univ.biUnion (fun t : Fin m => Finset.univ.image (fun v : Fin N => (v, z_prev t v)))
def cspUCand {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) : Finset (cspIota N q) :=
  ({a, b} : Finset (Fin N → Fin q)).image Sum.inr ∪
    Finset.univ.image (fun t : Fin m => (Sum.inr (z_prev t) : cspIota N q)) ∪
    (Finset.univ.filter (fun t : Fin N × Fin N × Fin q × Fin q =>
      t.1 < t.2.1 ∧ (t.1, t.2.2.1) ∈ cspRvc a b m z_prev ∧
      (t.2.1, t.2.2.2) ∈ cspRvc a b m z_prev)).image Sum.inl
def cspPoolCh {N q : ℕ} (C₁ r_star : ℕ) (x w₀ : Fin N → Fin q) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun y : Fin N → Fin q =>
    y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
    r_star < 4 * (disagreeSet x w₀ ∩ disagreeSet x y).card ∧
    cspInvEta0 C₁ * (threeWayDisagree x w₀ y).card ≤ r_star)
def cspUCh {N q : ℕ} (x w₀ : Fin N → Fin q) (m : ℕ)
    (y_prev : Fin m → (Fin N → Fin q)) : Finset (cspIota N q) :=
  ({x, w₀} : Finset (Fin N → Fin q)).image Sum.inr ∪
    Finset.univ.image (fun t : Fin m => (Sum.inr (y_prev t) : cspIota N q)) ∪
    (homQueries x ∪ homQueries w₀ ∪
      Finset.univ.biUnion (fun t : Fin m => homQueries (y_prev t))).image Sum.inl
def symROf {N q : ℕ} (ω : cspIota N q → Bool) : Fin N → Fin N → Fin q → Fin q → Prop :=
  fun u v c₁ c₂ =>
    if u < v then ω (Sum.inl (u, v, c₁, c₂)) = true
    else if v < u then ω (Sum.inl (v, u, c₂, c₁)) = true
    else False
def cspPRaw {N q : ℕ} (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun x : Fin N → Fin q =>
    ω (Sum.inr x) = true ∧ ∀ t ∈ homQueries x, ω (Sum.inl t) = true)
open Classical in
/-- Raw assignments admitting a nearby satisfying triple with excessive three-way disagreement. -/
def cspBD3 {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ u ∈ cspPRaw ω, ∃ z : Fin N → Fin q,
      (∀ t ∈ homQueries z, ω (Sum.inl t) = true) ∧
      dHam x u ≤ C₁ * r_star ∧ dHam x z ≤ C₁ * r_star ∧
      r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card)
def cspBCh {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ w₀ ∈ cspPRaw ω, x ≠ w₀ ∧ dHam x w₀ ≤ C₁ * r_star ∧
      cspKCh C₁ ≤ ((cspPoolCh C₁ r_star x w₀).filter (fun y => y ∈ cspPRaw ω)).card)
noncomputable def cspBCand {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) :
    Finset (Fin N → Fin q) :=
  by
    classical
    exact
      (cspPRaw ω).filter (fun a =>
        ∃ b ∈ cspPRaw ω, a ≠ b ∧ dHam a b ≤ C₁ * r_star ∧
          cspKMom C₁ ≤
          ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b)).card)
def cspBDist {N q : ℕ} (r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ y ∈ cspPRaw ω, x ≠ y ∧ 2 * dHam x y < r_star)
noncomputable def cspBBad {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) :
    Finset (Fin N → Fin q) :=
  cspBD3 C₁ r_star ω ∪ cspBCh C₁ r_star ω ∪ cspBCand C₁ r_star ω ∪ cspBDist r_star ω
abbrev candCStar {N q : ℕ} (a b x : Fin N → Fin q) (v : Fin N) : Fin q :=
  activeColor x a b v
def candMFresh {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v : Fin N => (v, x v) ∉ cspRvc a b m z_prev)
def candA1 {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2 ∧ (uv.1 ∈ S ∨ uv.2 ∈ S))
abbrev candWitType (N C₁ : ℕ) : Type :=
  Fin (cspKMax C₁ + 1) ×
  (Fin N → Fin (cspKMax C₁ + 1)) ×
  (Fin (cspKMax C₁) → Finset (Fin N)) ×
  Finset (Fin (cspKMax C₁) × Fin N)
def candA2 {N q : ℕ} (C₁ : ℕ) (a b x : Fin N → Fin q) (M : Finset (Fin N))
    (w : candWitType N C₁) : Finset (Fin N × Fin N) :=
  (M ×ˢ (disagreeSet x a ∪ disagreeSet x b)).filter
    (fun uv => ∃ r : Fin (cspKMax C₁),
      r.1 < w.1.1 ∧ w.2.1 uv.1 = r.succ ∧ (uv.2 ∈ w.2.2.1 r ∨ (r, uv.2) ∈ w.2.2.2))
def candPhi1 {N q : ℕ} (x : Fin N → Fin q) (uv : Fin N × Fin N) :
    Fin N × Fin N × Fin q × Fin q :=
  (uv.1, uv.2, x uv.1, x uv.2)
def candPhi2 {N q : ℕ} (a b x : Fin N → Fin q) (uv : Fin N × Fin N) :
    Fin N × Fin N × Fin q × Fin q :=
  if uv.1 < uv.2 then (uv.1, uv.2, x uv.1, activeColor x a b uv.2)
  else (uv.2, uv.1, activeColor x a b uv.2, x uv.1)
def candMWit {N q : ℕ} (C₁ r_star : ℕ) (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    Finset (candWitType N C₁) :=
  let K_max := cspKMax C₁
  let M := candMFresh a b m z_prev x
  let W_ab := disagreeSet x a ∪ disagreeSet x b
  let base := (Finset.univ : Finset (Fin (K_max + 1))) ×ˢ
    (Fintype.piFinset (fun u : Fin N =>
      if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))) ×ˢ
      Fintype.piFinset (fun _ : Fin K_max => M.powerset))
  let s_hat := fun (k : Fin (K_max + 1)) (τ : Fin N → Fin (K_max + 1)) (r : Fin K_max) =>
    if r.1 < k.1 then (M.filter (fun u => τ u = r.succ)).card - (11 * r_star) / 40 else 0
  (base.biUnion (fun ktB =>
    (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).powersetCard
      (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r)).image
      (fun U_out => (ktB.1, ktB.2.1, ktB.2.2, U_out)))).filter
    (fun w =>
      let k := w.1
      let τ := w.2.1
      let B_fut := w.2.2.1
      let U_out := w.2.2.2
      (∀ u ∈ M, (τ u).1 ≤ k.1) ∧
      2 * (M.filter (fun u => τ u = 0)).card ≤ r_star ∧
      ∀ r : Fin K_max, r.1 < k.1 →
        let M_r := M.filter (fun u => τ u = r.succ)
        let I_t := M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1)
        let B_o := W_ab.filter (fun v => (r, v) ∈ U_out)
        B_fut r ⊆ I_t ∧
        80 * (I_t \ B_fut r).card ≤ r_star ∧
        Disjoint B_o (M_r ∪ I_t) ∧
        B_o.card = M_r.card - (11 * r_star) / 40)
def candQCand {N q : ℕ} (C₁ : ℕ) (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (w : candWitType N C₁) : Finset (cspIota N q) :=
  ({x} : Finset (Fin N → Fin q)).image Sum.inr ∪
    ((candA1 (candMFresh a b m z_prev x)).image (candPhi1 x) ∪
      (candA2 C₁ a b x (candMFresh a b m z_prev x) w).image (candPhi2 a b x)).image Sum.inl
end Helpers
end HighDimSteinerSpanners.Proofs.CSP



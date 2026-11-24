-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GeometricAbelianConnected
-- name    : Development_AutomorphicSpectrum_Definitions_MetricPeriods_GeometricAbelianConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:59.253356+00:00
-- url     : https://prove2.me/theorems/ffa4e968-c8bc-4d07-9652-a2a12e80be0c
-- title:
--   Geometric Abelian Connected
-- statement:
--   Definitions and structural lemmas for Geometric Abelian Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GeometricAbelianConnected.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Inputs_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open MvPolynomial Filter Topology
open scoped ComplexOrder ContDiff
structure AnSq {d : ℕ} {σ : Type} [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) where
  eps_a₀ : ε a₀ = -2

  SW : AnSys (d + 2) (Option σ)

  q : Fin 2 → SW.X → SY.X
  holo : ∀ j, HoloMap SW.A SY.A (q j)
  bdry_eq : ∀ j, SW.open' = q j ⁻¹' SY.open'
  t₀_le : SW.t₀ ≤ SY.t₀
  th0 : ∀ a, SamePot SW.A Set.univ (SW.th (some a)) ((SY.th a).pullback (q 0) (holo 0).1)
  th1 : SamePot SW.A Set.univ (SW.th none) ((SY.th a₀).pullback (q 1) (holo 1).1)
  ph0 : ∀ a, SW.ph (some a) = SY.ph a ∘ q 0
  ph1 : SW.ph none = SY.ph a₀ ∘ q 1
  phase_some_eq_comp_first_projection : ∀ a t, SW.phT (some a) t = SY.phT a t ∘ q 0
  phase_none_eq_comp_second_projection : ∀ t, SW.phT none t = SY.phT a₀ t ∘ q 1
  base_ph : ∀ a, a ≠ a₀ → SY.ph a ∘ q 0 = SY.ph a ∘ q 1
  base_phT : ∀ a, a ≠ a₀ → ∀ t, SY.phT a t ∘ q 0 = SY.phT a t ∘ q 1

  L' : LocPot SW.X

  v : SW.X → SW.X → ℂ

  Dg : Set SW.X

  cst : ℝ
  potL' : IsPotential SW.A L'
  secv : IsSection SW.A L' v
  sncv : IsSNC SW.A L' v ![1] ![Dg]
  sncsv : IsSNC SW.A (SW.L + L') (fun x y => SW.s x y * v x y) (Fin.snoc SW.m 1) (Fin.snoc SW.W Dg)
  normv : ∀ y, logNormSec L' v y ≤ 0

  U : ℕ → Set (Fin d → ℂ)

  B : ℕ → Set (Fin d → ℂ)

  G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ

  α : ℕ → σ → (Fin d → ℂ) → ℝ

  ΦY : ℕ → (Fin (d + 1) → ℂ) → SY.X

  ΦW : ℕ → (Fin (d + 2) → ℂ) → SW.X
  U_open : ∀ n, IsOpen (U n)
  B_meas : ∀ n, MeasurableSet (B n) ∧ B n ⊆ U n
  G_pos : ∀ n, ∀ y ∈ U n, (G n y).PosDef
  G_smooth : ∀ n p r, ContDiffOn ℝ ∞ (fun y => G n y p r) (U n)
  α_smooth : ∀ n a, ContDiffOn ℝ ∞ (α n a) (U n)
  coverY : IsParamCover SY.A (fun n => {z | Fin.tail z ∈ U n}) (fun n => {z | Fin.tail z ∈ B n}) ΦY
  coverW : IsParamCover SW.A (fun n => {z | Fin.tail (Fin.tail z) ∈ U n})
    (fun n => {z | Fin.tail (Fin.tail z) ∈ B n}) ΦW
  ΦY_open : ∀ n (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U n → ΦY n z ∈ SY.open'
  first_projection_chart_compat : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U n → q 0 (ΦW n z) = ΦY n (Fin.cons (z 0) (Fin.tail (Fin.tail z)))
  second_projection_chart_compat : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U n → q 1 (ΦW n z) = ΦY n (Fin.tail z)
  xi_pot : ∀ n (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U n → ∃ H : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H z ∧ ∀ᶠ z' in 𝓝 z,
    ∑ a, (ε a : ℝ) * (SY.potH a).φ (ΦY n z) (ΦY n z') = xiPot (G n (Fin.tail z')) (z' 0) + (H z').re
  base_pot : ∀ n a, a ≠ a₀ → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U n → ∃ H : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H z ∧
    ∀ᶠ z' in 𝓝 z, (SY.potH a).φ (ΦY n z) (ΦY n z') = α n a (Fin.tail z') + (H z').re
  norm_hom : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U n → z 0 ≠ z 1 →
    logNormSec L' v (ΦW n z) + cst +
        (1 / 2) * ∑ a, (ε a : ℝ) * (SY.ph a (q 0 (ΦW n z)) + SY.ph a (q 1 (ΦW n z))) =
      logSin (G n (Fin.tail (Fin.tail z))) (z 0) (z 1)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
structure AlgSq (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) where
  arithY : IsArithVar P (d + 2)
  xi_two_base_eq_neg_two : xi2 k₀ = -2

  KW : Type
  [finKW : Fintype KW]

  ιW : KW → Type
  [finιW : ∀ k, Fintype (ιW k)]

  PW : Ideal (MRing ιW)
  arithW : IsArithVar PW (d + 3)

  κ : Fin 2 → K → KW

  v : Fin 2 → (Σ k, ι k) → (Σ k, ιW k)
  block : ∀ j, IsBlockMap (κ j) (v j)
  image : ∀ j, imageZ (v j) PW = P
  same : ∀ p : Σ k, ι k, p.1 ≠ k₀ → v 0 p = v 1 p
  new : κ 1 k₀ ∉ Set.range (κ 0)
  all : ∀ k', k' ∈ Set.range (κ 0) ∨ k' = κ 1 k₀
  fibre_line : ∀ G : GenFibre (v 0) PW, ∃ T : Set (MRingOver G.Φ (fibreIdx ιW (κ 0))),
    (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (κ 0) G = Ideal.span T

  Δ : Ideal (MRing ιW)
  arithΔ : IsArithVar Δ (d + 2)
  PW_le : PW ≤ Δ
  diag : ∀ i i' : ι k₀, X (v 0 ⟨k₀, i⟩) * X (v 1 ⟨k₀, i'⟩) - X (v 0 ⟨k₀, i'⟩) * X (v 1 ⟨k₀, i⟩) ∈ Δ

  g : MRing ιW

  h : MRing ιW

  dg : KW → ℕ

  dh : KW → ℕ
  g_deg : IsMultiHomog g dg
  h_deg : IsMultiHomog h dh
  g_nmem : g ∉ PW
  h_nmem : h ∉ PW
  deg_eq : ∀ k', 2 * ((dg k' : ℤ) - dh k') = -(pullDeg (κ 0) xi2 k' + pullDeg (κ 1) xi2 k')
  div_eq : divCycle PW g = divCycle PW h + Finsupp.single Δ 1
attribute [instance] AlgSq.finKW AlgSq.finιW
def AlgSq.logNormT {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K} {xi2 : K → ℤ} (Q : AlgSq P d k₀ xi2)
    (Xi : HermLine ι) (z : (Σ k, Q.ιW k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) Q.g)‖ / ‖eval z (map (Int.castRingHom ℂ) Q.h)‖) +
    (Real.log (Xi.h fun p => z (Q.v 0 p)) + Real.log (Xi.h fun p => z (Q.v 1 p))) / 2
def FromBase (k₀ : K) (A : HermLine ι) : Prop :=
  A.a k₀ = 0 ∧ ∀ z z' : (Σ k, ι k) → ℂ, (∀ p : Σ k, ι k, p.1 ≠ k₀ → z p = z' p) → A.h z = A.h z'
structure SqSys {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {P : Ideal (MRing ι)} (Re : Realis SY P)
    (a₀ : σ) (ε : σ → ℤ) where

  k₀ : K

  an : AnSq SY a₀ ε

  alg : AlgSq P d k₀ (combLine Re.ref ε).a

  ReW : Realis an.SW alg.PW
  deg_eq : ReW.deg = Re.deg
  base : ∀ a, a ≠ a₀ → ∀ t, FromBase k₀ (Re.line a t)
  pull0 : ∀ a t, IsPullHerm (alg.κ 0) (alg.v 0) (Re.line a t) (ReW.line (some a) t)
  pull1 : ∀ t, IsPullHerm (alg.κ 1) (alg.v 1) (Re.line a₀ t) (ReW.line none t)
  norm_eq : ∃ N : Set ReW.R.X, IsNull ReW.R.A N ∧ ∀ t, 0 < t → t ≤ an.SW.t₀ → ∀ x ∉ N,
    alg.logNormT (combLine (fun a => Re.line a t) ε) (ReW.R.lift x x) =
      logNormSec an.L' an.v (ReW.π x) + an.cst +
        (1 / 2) * ∑ a, (ε a : ℝ) * (SY.phT a t (an.q 0 (ReW.π x)) + SY.phT a t (an.q 1 (ReW.π x)))
end GlobalTheory.CompanionTheory.Ar.PB



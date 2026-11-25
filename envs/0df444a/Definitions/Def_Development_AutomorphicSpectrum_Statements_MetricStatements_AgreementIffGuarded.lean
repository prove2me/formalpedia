-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
-- name    : Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:07.249863+00:00
-- url     : https://prove2.me/theorems/3904aa77-3eaa-5fbb-b8b5-d2727c8539b3
-- title:
--   Agreement Iff Guarded
-- statement:
--   Definitions and structural lemmas for Agreement Iff Guarded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/AgreementIffGuarded.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagIndices_InstFintypeFlIdx
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GeometricAbelianConnected
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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
section Fl
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
def hFlPoly (II : IntersectionSystem) : MvPolynomial (Ψ × Fin N) ℝ :=
  formPoly (antisymDegree Ψ N + 1) fun w =>
    II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => xLine Ψ N (w r)
def degFlPoly : MvPolynomial (Ψ × Fin N) ℝ :=
  formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) fun _ => 1
def yLineFl (p : Ψ × Fin N) : HermLine (FlIdx Ψ N) :=
  fsHerm (FlIdx Ψ N) fun q => if q.1 = p.1 ∧ (q.2 : ℕ) = p.2 then 1 else 0
end Fl
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}
def volOf {D : ℕ} (S : AnSys D (Ψ × Fin N)) : ℝ :=
  eval (rhoWt Ψ N) (toWt S.degPoly) / eval (rhoWt Ψ N) (degFlPoly Ψ N)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
structure FlagSys {d : ℕ} {S : AnSys (d + 1) (Ψ × Fin N)} {P : Ideal (MRing ι)} (Re : Realis S P) (j : ℕ) where
  j_le : j ≤ N
  dim : d + 1 = antisymDegree Ψ N
  unif : IsUniformised S.A S.open' j S.potH

  sq : ∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → SqSys Re (τ, a) (xiCoef τ a)
def Agreement : Prop :=
  Inputs → ∀ (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (abelian₂ : ℝ) (_ : 0 < S.t₀ := by assumption),
    ∃ C₃ s₀ : ℝ, 0 < s₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P),
      (∀ w, Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w))) ∧
      ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, ∑ a, |c a| ≤ abelian₂ →
        |eval c (Re.FT II (Real.exp (-(s ^ 2)⁻¹))) - eval c (Re.PB II)| ≤ C₃ * s
def Coefficients : Prop :=
  Inputs → ∀ (D N : ℕ) (Ψ : Type) [Fintype Ψ] (S : AnSys D (Option (Ψ × Fin N))) (thH : LocPot S.X),
    IsPotential S.A thH → ∃ C₂ : ℝ,
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P),
      ((Re.PBs II).IsHomogeneous (D + 1) ∧ (Re.PBwt II).IsHomogeneous (D + 1) ∧
        aeval (fun o : Option (Ψ × Fin N) => o.elim 0 X) (Re.PBs II) = Re.PBwt II) ∧
      ∀ (Re' : Realis S P) (T : Finset ℕ) (α : ℕ → ℝ) (H : HermLine ι), Re'.deg = Re.deg →
        (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) → IsSmoothHerm H →
        SamePot Re.R.A Set.univ (potOf Re.R H) (thH.pullback Re.π Re.holo.1) →
        (∀ a t, 0 < t → t ≤ S.t₀ → VertClose P T α (Re.line a t) (Re'.line a t)) →
        (∀ p ∈ T, NefAt P p H.a ∧ ∀ a, NefAt P p ((Re.ref a).a + H.a) ∧ NefAt P p ((Re'.ref a).a + H.a)) →
        (∀ m, |coeff m (Re.PBs II) - coeff m (Re'.PBs II)| ≤ C₂ * ∑ p ∈ T, α p * Real.log p) ∧
          ∀ m, |coeff m (Re.PBwt II) - coeff m (Re'.PBwt II)| ≤ C₂ * ∑ p ∈ T, α p * Real.log p
def Proportional : Prop :=
  Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ), 2 ≤ N → j ≤ N →
    (∃ c : ℝ, 0 < c ∧ degFlPoly Ψ N = C c * antisymDelta Ψ N) ∧
    ∀ (D : ℕ) (S : AnSys D (Ψ × Fin N)), D = antisymDegree Ψ N → IsUniformised S.A S.open' j S.potH →
      0 < volOf S ∧ toWt S.degPoly = C (volOf S) * degFlPoly Ψ N
def Antisymmetry : Prop :=
  Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j d : ℕ), 2 ≤ N →
    ∀ (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι)) (Re : Realis S P), FlagSys Re j →
      toWt (Re.PB II) - volOf S • hFlPoly Ψ N II ∈ antisymSpace Ψ N j
def FlagHeight : Prop :=
  Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
      (hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) ∧
      (∀ (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N), (p.2 : ℕ) + 1 < N → gap lam p = 0 →
        eval lam (hFlPoly Ψ N II) = 0) ∧
      ∀ lam : Ψ × Fin N → ℝ, Dominant lam → 0 ≤ eval lam (hFlPoly Ψ N II)
def NefPol : Prop :=
  Inputs → ∀ (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (Fl : Set σ),
    (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (Re : Realis S (mCoordIdeal y)), Re.J = ⊤ → Birational y →
    ∀ (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily ℚ ι), ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I →
    ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.NefOnF I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) (combLine Re.ref n).a ∧
      (0 < eval (fun a => (n a : ℝ)) S.degPoly →
        ∀ (β : MRing ι) (dβ : K → ℕ), IsMultiHomog β dβ → β ∉ mCoordIdeal y →
          ∃ k : ℕ, 1 ≤ k ∧
            ∃ e ∈ chartLat y (fun κ => (k : ℤ) * (combLine Re.ref n).a κ - 1 - dβ κ) 1, e ≠ 0)
end GlobalTheory.CompanionTheory.Ar.PB



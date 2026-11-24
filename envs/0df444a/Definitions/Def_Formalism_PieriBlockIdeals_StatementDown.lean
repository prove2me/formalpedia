-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementDown
-- name    : Formalism_PieriBlockIdeals_StatementDown
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:35:30.991933+00:00
-- url     : https://prove2.me/theorems/827807b8-6495-4888-bc14-221bf092dccc
-- title:
--   Statement Down
-- statement:
--   Definitions and structural lemmas for Statement Down, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementDown.lean

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CohomologicalDescent.Down
section SLD
open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD
def PeelBound : Prop :=
  ∀ (l q w m : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ μ : Fin (1 + q) → ℕ, ExpLe l (1 + q) (blockWt 1 q w lam2) μ (eL + (w + q - m - 1) / (l - 1))
end SLD
section SLD2
open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD
def PeelBoundLast : Prop :=
  ∀ (l q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + 1) → ℤ), l.Prime → Antitone lam2 →
    (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) → Antitone ξ →
    ∀ (i' : ℤ) (eL : ℕ),
      (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWtLast 1 q w lam2) (blockWtLast 1 q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
      ∀ μ : Fin (q + 1) → ℕ, depth2 ξ (blockWtLast 1 q w lam2) μ ≤ i' →
        ExpLe l (q + 1) (blockWtLast 1 q w lam2) μ (eL + (M + q - w - 1) / (l - 1))
def PeelRows : Prop :=
  ∀ (l n s h : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ), l.Prime →
    (∀ a b, a ≤ b → b < n + s → lam b ≤ lam a) → lam 0 + (n + s) ≤ h + lam (n + s - 1) + 1 → Antitone ξ →
    ∀ (I : ℤ) (e : ℕ), ExpUpTo l n lam ξ I e → ExpUpTo l (n + s) lam ξ I (e + s * ((h - 1) / (l - 1)))
def BlockStep : Prop :=
  ∀ (l n t : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < n + t → lam b ≤ lam a) → (∀ a, n ≤ a → a < n + t → lam a = lam n) →
    ∀ eL : ℕ, (∀ μ2 : Fin n → ℕ, ExpLe l n (res n lam) μ2 eL) →
      ∀ I : ℕ, ExpUpTo l (n + t) lam (varpi n) (I : ℤ) (eL + blockCost l n t I lam)
def ApplicationSteps : Prop :=
  ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        (q * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + j * ((h - 1) / (l - 1)) + ecl)
end SLD2
section SF06
open CategoryTheory CategoryTheory.Limits
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
def Step2Real : Prop :=
  ∀ (l k j t w M h : ℕ) (I : ℝ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Antitone lam →
    Rows k j t w M lam xm xp → xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 →
    ∀ eL : ℕ, (∀ μ2 : Fin (k + j) → ℕ, ExpLe l (k + j) lam μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (k + j + t) → ℕ), IsDepthLast t (k + j) w μ i → (i : ℝ) ≤ I →
        ExpLe l (k + j + t) (blockWtLast t (k + j) w lam) μ
          (eL + ⌊(j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + labelSumBoundPos l k t h I xm xp (maxB t w)⌋₊)
def Application : Prop :=
  ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ k → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cPrime l k j t q h ecl (UN (k + j + t + q) lam (k - 1)) (UN (k + j + t + q) lam 0)
          (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊
def ApplicationCoarse : Prop :=
  ∀ (l k j t q h N' : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ k → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cCoarse l k j t q h N' ecl (UN (k + j + t + q) lam (k - 1)) (UN (k + j + t + q) lam 0)
          (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊
end SF06
section SF07
open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative
def ApplicationWindow : Prop :=
  ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    (∀ a, a < k → xm ≤ UN (k + j + t + q) lam a ∧ UN (k + j + t + q) lam a ≤ xp) →
    (∀ a, k ≤ a → a < k + j → UN (k + j + t + q) lam a < xm) →
    UN (k + j + t + q) lam (k + j) < xm → xm ≤ xp → xp - UN (k + j + t + q) lam (k + j) ≤ (h : ℤ) →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cPrime l k j t q h ecl xm xp (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊
def TheoremWTop : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ) ∧
    sInf {J : ℕ | TopIncl O Γ jK l N lam S J} ≤
      ∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ
open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealAt : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (l : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O D.Nr lam)] [IsScalarTower O A (NablaT O D.Nr lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O D.Nr lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin D.Nr → ℕ),
    D.Params →
    TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
      (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt →
    (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) →
    D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J} →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ))
def WeightSpacePrimePowerBoundOverDomain : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (l N k j t q h : ℕ) (lam : ℕ → ℕ)
    (xm xp : ℤ) (ecl : ℕ), l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) → h < l ^ 2 → 1 ≤ t →
    Shape N k j t q h lam xm xp → (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
    ∀ (I : ℕ) (w : Fin N → ℕ), depth2 (res N (varpi (k + j))) (res N lam) w ≤ (I : ℤ) →
      ∀ x ∈ nablaWtR R N (res N lam) w,
        (l : R) ^ ⌊cPrime l k j t q h ecl xm xp (UN N lam (k + j)) (I : ℝ)⌋₊ • x ∈
          weyl R N N le_rfl (res N lam)
def TheoremWTopCoarse : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloorCoarse l N k t h lam j q xm xp ecl i) τ)
open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealBound5Derived : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Params →
    (∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
      D.t + 2 * D.kap l < l →
      ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (A : Type) (_ : Ring A)
        (_ : Algebra O A) (G : Type) (_ : Group G) (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
        (_ : Module A (NablaT O D.Nr lam)) (_ : IsScalarTower O A (NablaT O D.Nr lam)) (T : Type)
        (_ : CommRing T) (_ : Algebra O T) (_ : Module T (Forms O Γ jK (NablaT O D.Nr lam)))
        (_ : IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))) (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
        (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) (_ : ∀ μ, AddCommGroup (L μ))
        (_ : ∀ μ, Module O (L μ)) (_ : ∀ μ, Module A (L μ)) (_ : ∀ μ, IsScalarTower O A (L μ))
        (_ : ∀ μ, Module T (Forms O Γ jK (L μ))) (hwt : Λ → ι → Fin D.Nr → ℕ),
        TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
          (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt ∧
        (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) ∧
        D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J}) →
    Cor.BlockIdealBound5 D
end SF07
section SF09
open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
def TheoremWTopShort6 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloorShort6 l N k t h lam j q xm xp ecl i) τ) ∧
    sInf {J : ℕ | TopIncl O Γ jK l N lam S J} ≤
      ∑ τ, cTau T2 ex (cFloorShort6 l N k t h lam j q xm xp ecl i) τ
def InclWReal : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ (l : ℕ) (X : HidaSetting ι P.Nr W.lam), l.Prime → ¬ IsUnit ((l : ℕ) : X.O) →
    P.lJ < (l : ℝ) → X.WInputs l (kc P) W.j W.T2 (W.iW P l) →
    X.Incl l (W.JW P l) ∧ X.Jmin l ≤ W.JW P l
def RecIncl : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    ∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec P l) ∧ (X l).Jmin l ≤ W.Jrec P l
def BoundWReal : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (W.sizeData₂ P (fun l => (X l).Jmin l)).BoundW P
def InputsReal : Prop :=
  LA.LemmaAZ → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (W.sizeData₂ P (fun l => (X l).Jmin l)).Inputs P
def CorollaryOfRecord : Prop :=
  LA.LemmaAZ → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def CorollaryOfRecordLink : Prop :=
  LA.LemmaAZ → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → WInputsLink P W (X l) l) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
end SF09
end Formalism.CohomologicalDescent.Down



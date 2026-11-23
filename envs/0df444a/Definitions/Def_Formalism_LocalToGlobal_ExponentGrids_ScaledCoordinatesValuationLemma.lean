-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
-- name    : Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:41.422029+00:00
-- url     : https://prove2.me/theorems/26d32b3e-ecd2-464c-8604-f8079424deb7
-- title:
--   Scaled Coordinates Valuation Lemma
-- statement:
--   Definitions and structural lemmas for Scaled Coordinates Valuation Lemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/ScaledCoordinatesValuationLemma.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_HarderNarasimhan_StatementMod
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_PairingDivisors_StatementX
import Definitions.Def_Formalism_TowerValuationBounds_HermitianSumValuationBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)
noncomputable section
namespace Formalism.AtG
def denIdeal {K : Type} [Field K] [NumberField K] (T : Finset (Pl K)) (a : Pl K → ℤ) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  ∏ w ∈ T, (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a w))
def rhoAt {K : Type} [Field K] (x y E : ℤ → K) (s : ℤ) : K :=
  if 1 ≤ s then y s / x s else E s * (y (1 - s) / x (1 - s))
def gridBudget {Sq : Type} (m N : ℕ) (B BN0 Bδ : ℝ) (S0 : Finset Sq) (ee qq : Sq → ℕ) : ℝ :=
  (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * (BN0 + 1) + 6 * Bδ +
    4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))
def NormalisedPrimeUnitWeight : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ell : Pl K → ℕ),
    (∀ w, (ell w).Prime ∧ PlOver (ell w) w) →
    ∀ (S : Finset ℕ) (c : ℕ → ℝ), (∀ l ∈ S, l.Prime) → ∀ w : Pl K,
      wt S c w = (if ell w ∈ S then c (ell w) else 0) * (vw w (ell w : K) : ℝ)
def SquareAtPlaceBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K)
    (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    ∀ (x xd y E : ℤ → K) (g : ℤ → ℤ) (S Se : Finset ℕ) (N0 : ℕ → ℝ) (δ σ : ℝ),
    (∀ l ∈ S, 0 ≤ N0 l) →
    (∀ s, x s ≠ 0 ∧ xd s ≠ 0 ∧ y s ≠ 0 ∧ E s ≠ 0) →

    (∀ s : ℤ, 1 ≤ s → s ≤ h → - wt S N0 w ≤ ((vw w (y s) + g s : ℤ) : ℝ) ∧
      ((vw w (y s) + g s : ℤ) : ℝ) ≤
        ((vw w (xd s) + g s : ℤ) : ℝ) + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) →

    (∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 → vw w (E s) = 0) →

    ∀ (c0 c00 A A0 A0' : K), c0 ≠ 0 → c00 ≠ 0 → A ≠ 0 → A0 ≠ 0 → A0' ≠ 0 →
    (vw w c0 : ℝ) ≤ (vw w A : ℝ) + 3 * δ → -(vw w c00 : ℝ) ≤ (vw w A0' : ℝ) + 3 * δ →
    A / A0 = ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), rhoAt x y E s →

    ∀ (ub ua : ℕ → K), (∀ j, ub j ≠ 0 ∧ ua j ≠ 0) →
    (∀ j, j < q → (vw w (ub j) : ℝ) ≤ σ) → (∀ i, i < p → (vw w (ua i) : ℝ) ≤ σ) →
    ∀ r : K, r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) *
        (∏ k ∈ Icc 1 p, rhoAt x y E ((e : ℤ) + q - k + 1)) *
        (∏ k ∈ Icc 1 q, rhoAt x y E ((e : ℤ) + k))⁻¹ →
    (vw w r : ℝ) ≤ |(vw w A0 : ℝ)| + |(vw w A0' : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) h,
        (|((vw w (x s) + g s : ℤ) : ℝ)| + |((vw w (xd s) + g s : ℤ) : ℝ)|)) +
      d * (wt S N0 w + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) + 6 * δ + (p + q : ℕ) * σ
def DisjointUnionFactorProduct : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (x : K) (dl : Pl K → ℝ)
    (Bδ : ℝ), x ≠ 0 → (∀ w, 0 ≤ dl w) → (∀ w, -(3 * dl w) ≤ (vw w x : ℝ)) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    HtLe (fun _ => 0) x (meanInf K (fun v => Real.posLog ‖v.embedding x‖) + 6 * Bδ)
def GridHeightBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
      (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool) (dd hh yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ) (W0 : Finset (Pl K)),
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime ∧ 0 ≤ N0 l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ij, rr w ij ≠ 0) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →

    (∀ w ∈ W0, ∀ ij, (vw w (rr w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      dd ij * (wt S N0 w + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →

    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →

    ∑ l ∈ S, N0 l * Real.log l ≤ BN0 →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    ∑ w ∈ W0, lw w * (vw w (∏ ij, rr w ij) : ℝ) ≤ gridBudget m N B BN0 Bδ S0 ee qq
def SlopeInequalityDenominators : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W) (T : Finset (Pl K))
      (a : Pl K → ℤ), A.FG → A ≠ ⊥ → B.FG → B ≠ ⊥ → Function.Injective φ →
      A.map (φ.restrictScalars (𝓞 K)) ≤
        Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) B →
      muMaxDef b X A ≤
        muMaxDef b' X' B + (htMap b X b' X' φ + 2 * ∑ w ∈ T, lw w * (a w : ℝ))
def LargestSlopeFunctionSpace : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (R : Submodule (𝓞 K) V) (M : Submodule (𝓞 K) W) (Ψ : V →ₗ[K] W)
      (T : Finset (Pl K)) (a : Pl K → ℤ) (r : Pl K → K) (dF : Pl K → ℝ) (EM hInf Gr BF : ℝ),
    R.FG → R ≠ ⊥ → M.FG → M ≠ ⊥ → Function.Injective Ψ →
    R.map (Ψ.restrictScalars (𝓞 K)) ≤ Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) M →
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (r w) : ℝ) + dF w) →
    muMaxDef b' X' M ≤ EM → htMap b X b' X' Ψ ≤ hInf →
    ∑ w ∈ T, lw w * (vw w (r w) : ℝ) ≤ Gr → ∑ w ∈ T, lw w * dF w ≤ BF →
    muMaxDef b X R ≤ EM + hInf + 2 * (Gr + BF)
def LargestSlopeLatticeFrames : Prop :=
  ∀ (K W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (D : ℕ), 0 < D →
    ∀ (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (kap : InfinitePlace K → ℝ)
      (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (XE v).det) → (∀ v, 0 < kap v) → (∀ v, IsUnit (X' v).det) →
    ∀ (R : Submodule (𝓞 K) (Fin D → K)) (M : Submodule (𝓞 K) W) (Ψ : (Fin D → K) →ₗ[K] W)
      (T : Finset (Pl K)) (a : Pl K → ℤ) (r : Pl K → K) (dF : Pl K → ℝ) (EM hInf Gr BF : ℝ),
    Submodule.IsLattice K R → M.FG → M ≠ ⊥ → Function.Injective Ψ →
    R.map (Ψ.restrictScalars (𝓞 K)) ≤ Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) M →
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (r w) : ℝ) + dF w) →
    muMaxDef b' X' M ≤ EM →
    htMap (Pi.basisFun K (Fin D)) (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' Ψ ≤ hInf →
    ∑ w ∈ T, lw w * (vw w (r w) : ℝ) ≤ Gr → ∑ w ∈ T, lw w * dF w ≤ BF →
    muMaxDef (Pi.basisFun K (Fin D)) XE R ≤ -meanLog kap + (EM + hInf + 2 * (Gr + BF))
def PassageSizeHypothesis : Prop :=
  ∀ (K W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (D : ℕ), 0 < D →
    ∀ (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (kap : InfinitePlace K → ℝ)
      (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (XE v).det) → (∀ v, 0 < kap v) → (∀ v, IsUnit (X' v).det) →
    ∀ (R : Submodule (𝓞 K) (Fin D → K)) (M : Submodule (𝓞 K) W) (Ψ : (Fin D → K) →ₗ[K] W)
      (T : Finset (Pl K)) (a : Pl K → ℤ) (dF : Pl K → ℝ) (EM hInf BF p2 bb : ℝ),

    Submodule.IsLattice K R → M.FG → M ≠ ⊥ → Function.Injective Ψ →
    R.map (Ψ.restrictScalars (𝓞 K)) ≤ Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) M →
    muMaxDef b' X' M ≤ EM →
    htMap (Pi.basisFun K (Fin D)) (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' Ψ ≤ hInf →
    ∑ w ∈ T, lw w * dF w ≤ BF →

    ∀ (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool) (dd hh yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ),
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (∏ ij, rr w ij) : ℝ) + dF w) →
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime ∧ 0 ≤ N0 l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ij, rr w ij ≠ 0) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ T, ∀ ij, (vw w (rr w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      dd ij * (wt S N0 w + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →
    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →
    ∑ l ∈ S, N0 l * Real.log l ≤ BN0 →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →

    EM + hInf + 2 * (gridBudget m N B BN0 Bδ S0 ee qq + BF) ≤ p2 * bb →
    muMaxDef (Pi.basisFun K (Fin D)) XE R ≤ -meanLog kap + p2 * bb
def DualLatticeMinimalSlope : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      muMinDef b.dualBasis (dualFrame X) (dualLat A) = -muMaxDef b X A
def FrameTheoremHeightNumber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (R1 : Submodule (𝓞 K) (Fin D → K)) (HH0 sF logκ lam0 c p2 ps bb : ℝ),
    Submodule.IsLattice K R1 →
    HH0 ≤ -logκ + p2 * bb →
    muMaxDef (Pi.basisFun K (Fin D)) XE R1 ≤ HH0 + c * lam0 →
    sF ≤ logκ + ps * bb → 0 ≤ c → lam0 ≤ bb → 0 ≤ bb → 1 ≤ ps + p2 + c →
    sF - muMinDef (Pi.basisFun K (Fin D)).dualBasis (dualFrame XE) (dualLat R1) ≤
        max bb (sF + muMaxDef (Pi.basisFun K (Fin D)) XE R1) ∧
      0 ≤ max bb (sF + muMaxDef (Pi.basisFun K (Fin D)) XE R1) ∧
      max bb (sF + muMaxDef (Pi.basisFun K (Fin D)) XE R1) ≤ (ps + p2 + c) * bb
def FinitePlaceLiesOverPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ ell : Pl K → ℕ, ∀ w, (ell w).Prime ∧ PlOver (ell w) w
def SquareAtPlaceRatiosCM : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (δ σ : ℝ) (p q : ℕ)
    (c0 c00 A A0 A0' P0 P1 P2 : K), c0 ≠ 0 → c00 ≠ 0 → A ≠ 0 → A0 ≠ 0 → A0' ≠ 0 → P0 ≠ 0 → P1 ≠ 0 →
    P2 ≠ 0 →
    (vw w c0 : ℝ) ≤ (vw w A : ℝ) + 3 * δ → -(vw w c00 : ℝ) ≤ (vw w A0' : ℝ) + 3 * δ →
    A / A0 = P0 →
    ∀ (ub ua : ℕ → K), (∀ j, ub j ≠ 0 ∧ ua j ≠ 0) →
    (∀ j, j < q → (vw w (ub j) : ℝ) ≤ σ) → (∀ i, i < p → (vw w (ua i) : ℝ) ≤ σ) →
    ∀ r : K, r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) * P1 * P2⁻¹ →
    (vw w r : ℝ) ≤ (vw w A0 : ℝ) + (vw w A0' : ℝ) + 6 * δ + (p + q : ℕ) * σ +
      (vw w (P0 * P1 * P2⁻¹) : ℝ)
def reflArg (s : ℤ) : ℤ := if 1 ≤ s then s else 1 - s
def sqArg (lo hi e : ℤ) (p q : ℕ) :
    (↥(Icc lo hi) ⊕ (↥(Icc 1 p) ⊕ ↥(Icc 1 q))) → ℤ :=
  Sum.elim (fun s => (s : ℤ))
    (Sum.elim (fun k => e + q - ((k : ℕ) : ℤ) + 1) (fun k => e + ((k : ℕ) : ℤ)))
def SquareRatioProductFactor : Prop :=
  ∀ (K : Type) [Field K] (x y E : ℤ → K) (lo hi e : ℤ) (p q : ℕ),
    Formalism.PairingDivisionLocalBalance.cmFactor (Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (fun _ => false)))
      (fun i => x (reflArg (sqArg lo hi e p q i)))
      (fun i => if 1 ≤ sqArg lo hi e p q i then 1 else E (sqArg lo hi e p q i))
      (fun i => y (reflArg (sqArg lo hi e p q i))) =
    (∏ s ∈ Icc lo hi, rhoAt x y E s) * (∏ k ∈ Icc 1 p, rhoAt x y E (e + q - k + 1)) *
      (∏ k ∈ Icc 1 q, rhoAt x y E (e + k))⁻¹
def ExplicitSizeInequality : Prop :=
  ∀ (K : Type) [Field K] (J : Type) [Fintype J] (I : J → Type) [∀ j, Fintype (I j)]
    (al : (Σ j, I j) → Bool) (x u y : (Σ j, I j) → K),
    Formalism.PairingDivisionLocalBalance.cmFactor al x u y =
      ∏ j, Formalism.PairingDivisionLocalBalance.cmFactor (fun i => al ⟨j, i⟩) (fun i => x ⟨j, i⟩) (fun i => u ⟨j, i⟩)
        (fun i => y ⟨j, i⟩)
def UntwistedPlacesVanish : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (T Tw : Finset (Pl K)) (r : Pl K → K), Tw ⊆ T →
    (∀ w ∈ T, w ∉ Tw → r w = 1) →
    ∑ w ∈ T, lw w * (vw w (r w) : ℝ) = ∑ w ∈ Tw, lw w * (vw w (r w) : ℝ)
def GridHeightBoundCM : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (Sq : Type) (m : ℕ) (dl : Pl K → ℝ) (rr cf : Pl K → Fin m × Fin m → K)
    (zA zA' : Fin m × Fin m → K) (yy : Fin m × Fin m → ℕ)
    (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B Bδ Ex : ℝ) (T : Finset (Pl K))
    (I : Type) [Fintype I] (al : I → Bool) (x : I → K) (u y : Pl K → I → K),
    (∀ w ij, rr w ij ≠ 0 ∧ cf w ij ≠ 0) → (∀ ij, yy ij ≤ m) → (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ T, ∀ ij, (vw w (rr w ij) : ℝ) ≤ (vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) + (vw w (cf w ij) : ℝ)) →
    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    (∀ w ∈ T, ∏ ij, cf w ij = Formalism.PairingDivisionLocalBalance.cmFactor al x (u w) (y w)) →
    ∑ w ∈ T, lw w * (vw w (Formalism.PairingDivisionLocalBalance.cmFactor al x (u w) (y w)) : ℝ) ≤ Ex →
    ∑ w ∈ T, lw w * (vw w (∏ ij, rr w ij) : ℝ) ≤
      (m : ℝ) ^ 2 * (2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) + Ex
def PassageSizeHypothesisCM : Prop :=
  ∀ (K W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (D : ℕ), 0 < D →
    ∀ (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (kap : InfinitePlace K → ℝ)
      (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (XE v).det) → (∀ v, 0 < kap v) → (∀ v, IsUnit (X' v).det) →
    ∀ (R : Submodule (𝓞 K) (Fin D → K)) (M : Submodule (𝓞 K) W) (Ψ : (Fin D → K) →ₗ[K] W)
      (T : Finset (Pl K)) (a : Pl K → ℤ) (dF : Pl K → ℝ) (EM hInf BF p2 bb : ℝ),
    Submodule.IsLattice K R → M.FG → M ≠ ⊥ → Function.Injective Ψ →
    R.map (Ψ.restrictScalars (𝓞 K)) ≤ Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) M →
    muMaxDef b' X' M ≤ EM →
    htMap (Pi.basisFun K (Fin D)) (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' Ψ ≤ hInf →
    ∑ w ∈ T, lw w * dF w ≤ BF →
    ∀ (Tw : Finset (Pl K)) (Sq : Type) (m : ℕ) (dl : Pl K → ℝ) (rr cf : Pl K → Fin m × Fin m → K)
      (zA zA' : Fin m × Fin m → K) (yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B Bδ Ex : ℝ)
      (I : Type) [Fintype I] (al : I → Bool) (x : I → K) (u y : Pl K → I → K),
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (∏ ij, rr w ij) : ℝ) + dF w) →

    Tw ⊆ T → (∀ w ∈ T, w ∉ Tw → ∀ ij, rr w ij = 1) →
    (∀ w ij, rr w ij ≠ 0 ∧ cf w ij ≠ 0) → (∀ ij, yy ij ≤ m) → (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ Tw, ∀ ij, (vw w (rr w ij) : ℝ) ≤ (vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) + (vw w (cf w ij) : ℝ)) →
    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    (∀ w ∈ Tw, ∏ ij, cf w ij = Formalism.PairingDivisionLocalBalance.cmFactor al x (u w) (y w)) →
    ∑ w ∈ Tw, lw w * (vw w (Formalism.PairingDivisionLocalBalance.cmFactor al x (u w) (y w)) : ℝ) ≤ Ex →
    EM + hInf + 2 * ((m : ℝ) ^ 2 * (2 * B + 6 * Bδ +
      2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) + Ex + BF) ≤ p2 * bb →
    muMaxDef (Pi.basisFun K (Fin D)) XE R ≤ -meanLog kap + p2 * bb
def UnitRatioAtPlace : Prop :=
  ∀ (Sq : Type) (m N : ℕ) (S0 : Finset Sq) (ee qq : Sq → ℕ)
    (B BN0 Bδ BF EM hInf f bb LL CB CN Cδ Sg pM pI pB : ℝ),
    1 ≤ bb → 1 ≤ f * bb * LL →
    B ≤ CB * f * bb * LL → BN0 ≤ CN * f * bb * LL → Bδ ≤ Cδ * f * bb * LL →
    ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) ≤ Sg → 0 ≤ Sg →
    EM ≤ pM * bb → hInf ≤ pI * bb → BF ≤ pB * bb →
    EM + hInf + 2 * (gridBudget m N B BN0 Bδ S0 ee qq + BF) ≤
      (pM + pI + 2 * ((m : ℝ) ^ 2 * ((2 * (2 + 8 * N) * CB + 2 * N * (CN + 1) + 6 * Cδ) * f * LL +
        4 * m * Sg) + pB)) * bb
def GridSquaresHeightBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
      (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool)
      (aa aa' dd hh pp qp ep : Fin m × Fin m → ℕ)
      (yT EE : Pl K → Fin m × Fin m → ℤ → K) (c0 c00 AA : Pl K → Fin m × Fin m → K)
      (ub ua : Pl K → Fin m × Fin m → ℕ → K)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ) (W0 : Finset (Pl K)),
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime ∧ 0 ≤ N0 l) → (∀ l ∈ Se, l.Prime) →

    (∀ ij, aa ij + aa' ij = dd ij ∧ aa ij = aa' ij + 2 * ep ij ∧ dd ij = 2 * hh ij ∧
      2 * (pp ij + qp ij) + 1 < ep ij ∧ 2 * (pp ij + qp ij) + 1 < aa' ij) →
    (∀ ij, dd ij ≤ 2 * N) → (∀ ij, pp ij + qp ij ≤ m) → (∀ s ∈ S0, cc s ≤ ee s) →

    (∀ w ij, rr w ij ≠ 0) → (∀ ij s, zT ij s ≠ 0) → (∀ ij b s, zTd ij b s ≠ 0) →
    (∀ w ij s, yT w ij s ≠ 0 ∧ EE w ij s ≠ 0) → (∀ ij, zA ij ≠ 0 ∧ zA' ij ≠ 0) →
    (∀ w ij, c0 w ij ≠ 0 ∧ c00 w ij ≠ 0 ∧ AA w ij ≠ 0) → (∀ w ij j, ub w ij j ≠ 0 ∧ ua w ij j ≠ 0) →

    (∀ w ∈ W0, ∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij →
      - wt S N0 w ≤ ((vw w (yT w ij s) + gT ij s w : ℤ) : ℝ) ∧
      ((vw w (yT w ij s) + gT ij s w : ℤ) : ℝ) ≤
        ((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ) + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) →

    (∀ w ∈ W0, ∀ ij, ∀ s : ℤ, 1 - ((ep ij : ℤ) + qp ij - pp ij) ≤ s → s ≤ 0 →
      vw w (EE w ij s) = 0) →

    (∀ w ∈ W0, ∀ ij, (vw w (c0 w ij) : ℝ) ≤ (vw w (AA w ij) : ℝ) + 3 * dl w ∧
      -(vw w (c00 w ij) : ℝ) ≤ (vw w (zA' ij) : ℝ) + 3 * dl w) →
    (∀ w ∈ W0, ∀ ij, AA w ij / zA ij =
      ∏ s ∈ Icc (1 - ((ep ij : ℤ) + qp ij - pp ij)) ((hh ij : ℤ) - (pp ij + qp ij)),
        rhoAt (zT ij) (yT w ij) (EE w ij) s) →

    (∀ w ∈ W0, ∀ ij j,
      (j < qp ij → (vw w (ub w ij j) : ℝ) ≤ 2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) ∧
      (j < pp ij → (vw w (ua w ij j) : ℝ) ≤ 2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →

    (∀ w ∈ W0, ∀ ij, rr w ij =
      ((∏ j ∈ range (qp ij), ub w ij j) * ∏ i ∈ range (pp ij), ua w ij i) * (c0 w ij / c00 w ij) *
        (∏ k ∈ Icc 1 (pp ij), rhoAt (zT ij) (yT w ij) (EE w ij) ((ep ij : ℤ) + qp ij - k + 1)) *
        (∏ k ∈ Icc 1 (qp ij), rhoAt (zT ij) (yT w ij) (EE w ij) ((ep ij : ℤ) + k))⁻¹) →

    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →
    ∑ l ∈ S, N0 l * Real.log l ≤ BN0 →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    ∑ w ∈ W0, lw w * (vw w (∏ ij, rr w ij) : ℝ) ≤ gridBudget m N B BN0 Bδ S0 ee qq
def CoefficientRatioTowerFormula : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (ι : K →+* F) (L L0 : ℤ → F) (c u cb u0 : ℕ → ℕ → F) (p q : ℕ)
    (e : ℤ) (Ω Ω' : F), Ω ≠ 0 → Ω' ≠ 0 →
    (∀ k : ℕ, 1 ≤ k → k ≤ q → L (e + k) ≠ 0 ∧ L0 (e + k) ≠ 0) →
    (∀ j, j < q → c 0 j * L (e + j + 1) = u 0 j * c 0 (j + 1)) →
    (∀ i, i < p → c i q = u i q * L (e - i + q) * c (i + 1) q) →
    (∀ j, j < q → cb 0 j * L0 (e + j + 1) = u0 0 j * cb 0 (j + 1)) →
    (∀ i, i < p → cb i q = u0 i q * L0 (e - i + q) * cb (i + 1) q) →
    ∀ (x y E : ℤ → K) (r c0 c00 : K) (ub ua : ℕ → K),
    ι r = c 0 0 / cb 0 0 → ι c0 = c p q * Ω' / Ω → ι c00 = cb p q * Ω' / Ω →
    (∀ j, j < q → ι (ub j) = u 0 j / u0 0 j) → (∀ i, i < p → ι (ua i) = u i q / u0 i q) →
    (∀ k : ℕ, 1 ≤ k → k ≤ p →
      ι (rhoAt x y E (e + q - k + 1)) = L (e + q - k + 1) / L0 (e + q - k + 1)) →
    (∀ k : ℕ, 1 ≤ k → k ≤ q → ι (rhoAt x y E (e + k)) = L (e + k) / L0 (e + k)) →
    r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) *
        (∏ k ∈ Icc 1 p, rhoAt x y E (e + q - k + 1)) * (∏ k ∈ Icc 1 q, rhoAt x y E (e + k))⁻¹
def CoefficientFieldNormRatio : Prop :=
  ∀ (K F : Type) [Field K] [Field F] (ι : K →+* F) (Ac Ω2 : F) (L L0 : ℤ → F) (lo hi : ℤ),
    Ac ≠ 0 → Ω2 ≠ 0 →
    ∀ (x y E : ℤ → K) (A A0 : K),
    ι A = Ac * (∏ s ∈ Icc lo hi, L s) / Ω2 → ι A0 = Ac * (∏ s ∈ Icc lo hi, L0 s) / Ω2 →
    (∀ s ∈ Icc lo hi, ι (rhoAt x y E s) = L s / L0 s) →
    A / A0 = ∏ s ∈ Icc lo hi, rhoAt x y E s
def HeightBoundedDenominators : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (Sq : Type) (S0 : Finset Sq) (ζ : K)
    (Ga Ga' Gb Gb' : Sq → K) (cc qq : Sq → ℕ), ζ ≠ 0 → vw w ζ = 0 → (∀ s ∈ S0, 0 < qq s) →
    (∀ s ∈ S0, 0 ≤ vw w (Ga s) ∧ 0 ≤ vw w (Ga' s) ∧ Ga s * Ga' s = (qq s : K) ^ cc s) →
    (∀ s ∈ S0, 0 ≤ vw w (Gb s) ∧ 0 ≤ vw w (Gb' s) ∧ Gb s * Gb' s = (qq s : K) ^ cc s) →
    |(vw w (ζ * ∏ s ∈ S0, Ga s / Gb s) : ℝ)| ≤ 2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)
def ScaledCoordinatesValuationLemma : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K)
    (ι κ : Type) [Fintype κ] (X : Finset ι) (z z' : ι → κ → K) (gm : ι → κ → κ → K) (c0 : K) (δ : ℝ),
    c0 ≠ 0 → (∀ x ∈ X, ∀ k, z x k = c0 * z' x k) →
    (∀ x ∈ X, ∀ k, z x k = 0 ∨
      (-δ ≤ (vw w (z x k) : ℝ) ∧ -δ ≤ (vw (Formalism.DivisionValues.conjPl w) (z x k) : ℝ))) →
    (∀ x ∈ X, ∀ k, z' x k = 0 ∨
      (-δ ≤ (vw w (z' x k) : ℝ) ∧ -δ ≤ (vw (Formalism.DivisionValues.conjPl w) (z' x k) : ℝ))) →
    (∀ x ∈ X, ∀ k l, gm x k l = 0 ∨ -δ ≤ (vw w (gm x k l) : ℝ)) →
    ∀ A A' : K, A = ∑ x ∈ X, ∑ k, ∑ l, z x k * star (z x l) * gm x k l →
    A' = ∑ x ∈ X, ∑ k, ∑ l, z' x k * star (z' x l) * gm x k l → A ≠ 0 → A' ≠ 0 →
    (vw w c0 : ℝ) ≤ (vw w A : ℝ) + 3 * δ ∧ -(vw w c0 : ℝ) ≤ (vw w A' : ℝ) + 3 * δ ∧
      -(3 * δ) ≤ (vw w A : ℝ) ∧ -(3 * δ) ≤ (vw w A' : ℝ)
end Formalism.AtG



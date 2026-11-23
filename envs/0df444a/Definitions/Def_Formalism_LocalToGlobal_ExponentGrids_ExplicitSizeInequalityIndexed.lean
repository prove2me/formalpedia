-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExplicitSizeInequalityIndexed
-- name    : Formalism_LocalToGlobal_ExponentGrids_ExplicitSizeInequalityIndexed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:07.660685+00:00
-- url     : https://prove2.me/theorems/7b6251ed-85b0-4a0b-a3f4-01bacbd5320a
-- title:
--   Explicit Size Inequality Indexed
-- statement:
--   Definitions and structural lemmas for Explicit Size Inequality Indexed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/ExplicitSizeInequalityIndexed.lean

import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationBoundIndexed
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
def gridBudgetIdx {Sq : Type} (m N : ℕ) (B BN0 Bδ : ℝ) (S0 : Finset Sq) (ee qq : Sq → ℕ) : ℝ :=
  (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 10 * N * BN0 + 2 * N + 6 * Bδ +
    4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))
def explicitSizeConstant (m N : ℕ) (f LL CB CN Cδ Sg pM pI pB : ℝ) : ℝ :=
  pM + pI + 2 * ((m : ℝ) ^ 2 * ((2 * (2 + 8 * N) * CB + 10 * N * CN + 2 * N + 6 * Cδ) * f * LL +
    4 * m * Sg) + pB)
def SquareAtPlaceIndexed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K)
    (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    ∀ (x xd y E : ℤ → K) (g : ℤ → ℤ) (S Se : Finset ℕ) (N0 : ℤ → ℕ → ℝ) (δ σ : ℝ),
    (∀ s : ℤ, 1 ≤ s → s ≤ h → ∀ l ∈ S, 0 ≤ N0 s l) →
    (∀ s, x s ≠ 0 ∧ xd s ≠ 0 ∧ y s ≠ 0 ∧ E s ≠ 0) →

    (∀ s : ℤ, 1 ≤ s → s ≤ h → - wt S (N0 s) w ≤ ((vw w (y s) + g s : ℤ) : ℝ) ∧
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
      5 * (∑ s ∈ Icc (1 : ℤ) h, wt S (N0 s) w) + d * wt Se (fun l => 1 / (l : ℝ) ^ 2) w +
      6 * δ + (p + q : ℕ) * σ
def GridHeightBoundIndexed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
      (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool) (dd hh yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ) (W0 : Finset (Pl K)),
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime) →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∀ l ∈ S, 0 ≤ N0 ij s l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ij, rr w ij ≠ 0) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →

    (∀ w ∈ W0, ∀ ij, (vw w (rr w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), wt S (N0 ij s) w) +
      dd ij * wt Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →

    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →

    0 ≤ BN0 →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∑ l ∈ S, N0 ij s l * Real.log l ≤ BN0) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    ∑ w ∈ W0, lw w * (vw w (∏ ij, rr w ij) : ℝ) ≤ gridBudgetIdx m N B BN0 Bδ S0 ee qq
def GridSquaresBoundIndexed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
      (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool)
      (aa aa' dd hh pp qp ep : Fin m × Fin m → ℕ)
      (yT EE : Pl K → Fin m × Fin m → ℤ → K) (c0 c00 AA : Pl K → Fin m × Fin m → K)
      (ub ua : Pl K → Fin m × Fin m → ℕ → K)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ) (W0 : Finset (Pl K)),
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime) →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∀ l ∈ S, 0 ≤ N0 ij s l) → (∀ l ∈ Se, l.Prime) →

    (∀ ij, aa ij + aa' ij = dd ij ∧ aa ij = aa' ij + 2 * ep ij ∧ dd ij = 2 * hh ij ∧
      2 * (pp ij + qp ij) + 1 < ep ij ∧ 2 * (pp ij + qp ij) + 1 < aa' ij) →
    (∀ ij, dd ij ≤ 2 * N) → (∀ ij, pp ij + qp ij ≤ m) → (∀ s ∈ S0, cc s ≤ ee s) →

    (∀ w ij, rr w ij ≠ 0) → (∀ ij s, zT ij s ≠ 0) → (∀ ij b s, zTd ij b s ≠ 0) →
    (∀ w ij s, yT w ij s ≠ 0 ∧ EE w ij s ≠ 0) → (∀ ij, zA ij ≠ 0 ∧ zA' ij ≠ 0) →
    (∀ w ij, c0 w ij ≠ 0 ∧ c00 w ij ≠ 0 ∧ AA w ij ≠ 0) → (∀ w ij j, ub w ij j ≠ 0 ∧ ua w ij j ≠ 0) →

    (∀ w ∈ W0, ∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij →
      - wt S (N0 ij s) w ≤ ((vw w (yT w ij s) + gT ij s w : ℤ) : ℝ) ∧
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
    0 ≤ BN0 →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∑ l ∈ S, N0 ij s l * Real.log l ≤ BN0) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    ∑ w ∈ W0, lw w * (vw w (∏ ij, rr w ij) : ℝ) ≤ gridBudgetIdx m N B BN0 Bδ S0 ee qq
def PassageSizeIndexed : Prop :=
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

    ∀ (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool) (dd hh yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ),
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (∏ ij, rr w ij) : ℝ) + dF w) →
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime) →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∀ l ∈ S, 0 ≤ N0 ij s l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ij, rr w ij ≠ 0) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ T, ∀ ij, (vw w (rr w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), wt S (N0 ij s) w) +
      dd ij * wt Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →
    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →
    0 ≤ BN0 →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∑ l ∈ S, N0 ij s l * Real.log l ≤ BN0) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →

    EM + hInf + 2 * (gridBudgetIdx m N B BN0 Bδ S0 ee qq + BF) ≤ p2 * bb →
    muMaxDef (Pi.basisFun K (Fin D)) XE R ≤ -meanLog kap + p2 * bb
def ExplicitSizeInequalityIndexed : Prop :=
  ∀ (Sq : Type) (m N : ℕ) (S0 : Finset Sq) (ee qq : Sq → ℕ)
    (B BN0 Bδ BF EM hInf f bb LL CB CN Cδ Sg pM pI pB : ℝ),
    1 ≤ bb → 1 ≤ f * bb * LL →
    B ≤ CB * f * bb * LL → BN0 ≤ CN * f * bb * LL → Bδ ≤ Cδ * f * bb * LL →
    ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) ≤ Sg → 0 ≤ Sg →
    EM ≤ pM * bb → hInf ≤ pI * bb → BF ≤ pB * bb →
    EM + hInf + 2 * (gridBudgetIdx m N B BN0 Bδ S0 ee qq + BF) ≤
      explicitSizeConstant m N f LL CB CN Cδ Sg pM pI pB * bb
def PassageSizeExplicitIndexed : Prop :=
  ∀ (K W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (D : ℕ), 0 < D →
    ∀ (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (kap : InfinitePlace K → ℝ)
      (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (XE v).det) → (∀ v, 0 < kap v) → (∀ v, IsUnit (X' v).det) →
    ∀ (R : Submodule (𝓞 K) (Fin D → K)) (M : Submodule (𝓞 K) W) (Ψ : (Fin D → K) →ₗ[K] W)
      (T : Finset (Pl K)) (a : Pl K → ℤ) (dF : Pl K → ℝ) (EM hInf BF bb : ℝ),

    Submodule.IsLattice K R → M.FG → M ≠ ⊥ → Function.Injective Ψ →
    R.map (Ψ.restrictScalars (𝓞 K)) ≤ Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) M →
    muMaxDef b' X' M ≤ EM →
    htMap (Pi.basisFun K (Fin D)) (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' Ψ ≤ hInf →
    ∑ w ∈ T, lw w * dF w ≤ BF →

    ∀ (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool) (dd hh yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ),
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (∏ ij, rr w ij) : ℝ) + dF w) →
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime) →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∀ l ∈ S, 0 ≤ N0 ij s l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ij, rr w ij ≠ 0) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ T, ∀ ij, (vw w (rr w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), wt S (N0 ij s) w) +
      dd ij * wt Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →
    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →
    0 ≤ BN0 →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∑ l ∈ S, N0 ij s l * Real.log l ≤ BN0) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →

    ∀ (f LL CB CN Cδ Sg pM pI pB : ℝ), 1 ≤ bb → 1 ≤ f * bb * LL →
    B ≤ CB * f * bb * LL → BN0 ≤ CN * f * bb * LL → Bδ ≤ Cδ * f * bb * LL →
    ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) ≤ Sg → 0 ≤ Sg →
    EM ≤ pM * bb → hInf ≤ pI * bb → BF ≤ pB * bb →
    muMaxDef (Pi.basisFun K (Fin D)) XE R ≤
      -meanLog kap + explicitSizeConstant m N f LL CB CN Cδ Sg pM pI pB * bb
def GridBudgetIndexedFormula : Prop :=
  ∀ (Sq : Type) (m N : ℕ) (B BN0 Bδ : ℝ) (S0 : Finset Sq) (ee qq : Sq → ℕ),
    gridBudgetIdx m N B BN0 Bδ S0 ee qq =
      gridBudget m N B BN0 Bδ S0 ee qq + (m : ℝ) ^ 2 * (8 * N * BN0)
def UniformDenominatorConstant : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (S : Finset ℕ) (N0 : ℕ → ℝ) (d h : ℕ),
    (∀ l ∈ S, 0 ≤ N0 l) → d = 2 * h →
    (d : ℝ) * wt S N0 w ≤ 5 * ∑ _s ∈ Icc (1 : ℤ) h, wt S N0 w
end Formalism.AtG



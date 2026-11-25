-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:23.860556+00:00
-- url     : https://prove2.me/theorems/4a8049f2-62d3-5a6d-b443-380cf42b2d5d
-- title:
--   Is Pluecker Coord
-- statement:
--   Definitions and structural lemmas for Is Pluecker Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PlueckerCoordinates/IsPlueckerCoord.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_DataHodge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Twist
variable {Ω : Type} [Field Ω]
def twistFactor (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (b : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ (-b k)
def IsTwValueAt (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (b : K → ℤ) (s : Ω) (z : (Σ k, ι k) → ℂ)
    (v : ℂ) : Prop :=
  (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∃ v0, IsValueAt y (s * twistFactor y c b) z v0 ∧ v = v0 * ∏ k, z ⟨k, c k⟩ ^ b k
variable {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}
def IsDualSectionOver (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E) (c : (k : K) → ι k)
    (b : K → ℤ) {r : ℕ} (φ : E [⋀^Fin r]→ₗ[Ω] Ω) : Prop :=
  ∀ e : Fin r → E, (∀ a, e a ∈ W.lat c) → φ e * twistFactor y c b ∈ chartRing ℤ (segreCoord y) c
def firstCols (g : Matrix (Fin N) (Fin N) ℂ) (r : ℕ) (h : r ≤ N) : Matrix (Fin N) (Fin r) ℂ :=
  fun p a => g p (Fin.castLE h a)
def IsPlueckerCoord (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (b : K → ℤ) {r : ℕ}
    (φ : E [⋀^Fin r]→ₗ[Ω] Ω) (bfr : Fin N → E) (z : (Σ k, ι k) → ℂ) (g : Matrix (Fin N) (Fin r) ℂ)
    (v : ℂ) : Prop :=
  ∃ V : (Fin r → Fin N) → ℂ, (∀ q, IsTwValueAt y c b (φ (bfr ∘ q)) z (V q)) ∧
    v = ∑ q, (∏ a, g (q a) a) * V q
end Twist
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
structure PlueckerData (D : ComponentDataHodge II Ψ K ι Ω E) where

  b : K → ℤ

  M : Ψ → Fin D.N → ℕ
  M_ge : ∀ τ (i : Fin D.N), D.N.choose ((i : ℕ) + 1) ≤ M τ i

  gen : ∀ τ (i : Fin D.N), Fin (M τ i) → (E τ [⋀^Fin ((i : ℕ) + 1)]→ₗ[Ω] Ω)
  global : ∀ τ (i : Fin D.N) m (c : (k : K) → ι k), segreCoord D.y c ≠ 0 →
    IsDualSectionOver D.y (D.W τ) c b (gen τ i m)
  generates : ∀ τ (i : Fin D.N) (c : (k : K) → ι k), segreCoord D.y c ≠ 0 →
    ∀ φ : E τ [⋀^Fin ((i : ℕ) + 1)]→ₗ[Ω] Ω, IsDualSectionOver D.y (D.W τ) c b φ →
      ∃ a : Fin (M τ i) → Ω, (∀ m, a m ∈ chartRing ℤ (segreCoord D.y) c) ∧ φ = ∑ m, a m • gen τ i m
variable {D : ComponentDataHodge II Ψ K ι Ω E}
abbrev YBlk (D : ComponentDataHodge II Ψ K ι Ω E) : Type := K ⊕ (Ψ × Fin D.N)
def ιY (P : PlueckerData D) : YBlk D → Type
  | Sum.inl k => ι k
  | Sum.inr q => Fin (P.M q.1 q.2)
instance instFintypeιY (P : PlueckerData D) : ∀ k, Fintype (ιY P k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr q => inferInstanceAs (Fintype (Fin (P.M q.1 q.2)))
def yJoin (P : PlueckerData D) (z : (Σ k, ι k) → ℂ) (w : ∀ q : Ψ × Fin D.N, Fin (P.M q.1 q.2) → ℂ) :
    (Σ k : YBlk D, ιY P k) → ℂ
  | ⟨Sum.inl k, i⟩ => z ⟨k, i⟩
  | ⟨Sum.inr q, m⟩ => w q m
def zPart (P : PlueckerData D) (u : (Σ k : YBlk D, ιY P k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => u ⟨Sum.inl p.1, p.2⟩
def wPart (P : PlueckerData D) (u : (Σ k : YBlk D, ιY P k) → ℂ) (q : Ψ × Fin D.N) :
    Fin (P.M q.1 q.2) → ℂ :=
  fun m => u ⟨Sum.inr q, m⟩
def IsFlagFibrePt (P : PlueckerData D) (τ : Ψ) (z : (Σ k, ι k) → ℂ)
    (wτ : ∀ i : Fin D.N, Fin (P.M τ i) → ℂ) : Prop :=
  ∃ (c : (k : K) → ι k) (f : Ω) (bfr : Fin D.N → E τ) (g : Matrix (Fin D.N) (Fin D.N) ℂ)
    (lam : Fin D.N → ℂ),
    IsFrameOver D.y (D.W τ) c f bfr ∧ InFrameDomain D.y c f z ∧ g.det ≠ 0 ∧ (∀ i, lam i ≠ 0) ∧
    ∀ i m, ∃ v, IsPlueckerCoord D.y c P.b (P.gen τ i m) bfr z (firstCols g ((i : ℕ) + 1) i.isLt) v ∧
      wτ i m = lam i * v
def flagPts (P : PlueckerData D) : Set ((Σ k : YBlk D, ιY P k) → ℂ) :=
  {u | zPart P u ∈ mcPts (mCoordIdeal D.y) ∧
    ∀ τ, IsFlagFibrePt P τ (zPart P u) (fun i => wPart P u (τ, i))}
def PY (P : PlueckerData D) : Ideal (MRing (ιY P)) :=
  ⨅ u ∈ flagPts P, RingHom.ker ((MvPolynomial.eval u).comp (MvPolynomial.map (Int.castRingHom ℂ)))
def BdY (P : PlueckerData D) : Set ((Σ k : YBlk D, ιY P k) → ℂ) := {u | zPart P u ∈ D.Bd}
def detDeg (P : PlueckerData D) (τ : Ψ) (i : Fin D.N) : YBlk D → ℤ
  | Sum.inl k => -P.b k
  | Sum.inr q => if q = (τ, i) then 1 else 0
def IsDetNormAt (P : PlueckerData D) (τ : Ψ) (i : Fin D.N) (z : (Σ k, ι k) → ℂ)
    (w : Fin (P.M τ i) → ℂ) (r : ℝ) : Prop :=
  z ∈ ComponentData.Xo D.toComponentData ∧
    ∃ (l : Fin (D.h τ).m) (g : Matrix (Fin D.N) (Fin D.N) ℂ) (lam : ℂ),
      InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z ∧ g.det ≠ 0 ∧ lam ≠ 0 ∧
      (∀ m, ∃ v, IsPlueckerCoord D.y ((D.h τ).chart l) P.b (P.gen τ i m) ((D.h τ).b l) z
        (firstCols g ((i : ℕ) + 1) i.isLt) v ∧ w m = lam * v) ∧
      r = ‖lam‖ * Real.sqrt ((firstCols g ((i : ℕ) + 1) i.isLt)ᴴ * (D.h τ).gram l z *
        firstCols g ((i : ℕ) + 1) i.isLt).det.re
open Classical in

def detNorm (P : PlueckerData D) (τ : Ψ) (i : Fin D.N) (z : (Σ k, ι k) → ℂ)
    (w : Fin (P.M τ i) → ℂ) : ℝ :=
  if h : ∃ r, IsDetNormAt P τ i z w r then h.choose else 1
def phDet (P : PlueckerData D) (τ : Ψ) (i : Fin D.N) (u : (Σ k : YBlk D, ιY P k) → ℂ) : ℝ :=
  Real.log (detNorm P τ i (zPart P u) (wPart P u (τ, i)))
def refLine (P : PlueckerData D) (a : YBlk D → ℤ) : HermLine (ιY P) :=
  HermLine.ofMetrics (fun k => fsMetric (ιY P k)) a
def phRef (P : PlueckerData D) (a : YBlk D → ℤ) (u : (Σ k : YBlk D, ιY P k) → ℂ) : ℝ :=
  Real.log ((refLine P a).h u)
def plCoeff {N : ℕ} (la : Ψ × Fin N → ℤ) (q : Ψ × Fin N) : ℤ :=
  if h : (q.2 : ℕ) + 1 < N then la (q.1, ⟨(q.2 : ℕ) + 1, h⟩) - la q else -la q
def laDeg (P : PlueckerData D) (la : Ψ × Fin D.N → ℤ) : YBlk D → ℤ :=
  ∑ q, plCoeff la q • detDeg P q.1 q.2
def phLa (P : PlueckerData D) (la : Ψ × Fin D.N → ℤ) (u : (Σ k : YBlk D, ιY P k) → ℂ) : ℝ :=
  ∑ q, (plCoeff la q : ℝ) * phDet P q.1 q.2 u
def phLaAsWritten (P : PlueckerData D) (la : Ψ × Fin D.N → ℤ) (u : (Σ k : YBlk D, ιY P k) → ℂ) : ℝ :=
  ∑ q, (la q : ℝ) * phDet P q.1 q.2 u
def grDeg (P : PlueckerData D) (τ : Ψ) (i : Fin D.N) : YBlk D → ℤ :=
  laDeg P (Pi.single (τ, i) 1)
def grPh (P : PlueckerData D) (τ : Ψ) (i : Fin D.N) (u : (Σ k : YBlk D, ιY P k) → ℂ) : ℝ :=
  phLa P (Pi.single (τ, i) 1) u
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree



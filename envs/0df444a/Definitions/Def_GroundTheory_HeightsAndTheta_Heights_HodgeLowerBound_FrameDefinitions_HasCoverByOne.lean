-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:03.986952+00:00
-- url     : https://prove2.me/theorems/172901e3-f281-4429-90a1-6687b1376aad
-- title:
--   Has Cover By One
-- statement:
--   Definitions and structural lemmas for Has Cover By One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/HasCoverByOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
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
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Cover
variable {Ω : Type} [Field Ω]
def HasCoverBy (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (Pr : Ω → Prop) : Prop :=
  ∃ (m : ℕ) (f cc : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord y) c) ∧
    (∀ l, cc l ∈ chartRing ℤ (segreCoord y) c) ∧ ∑ l, cc l * f l = 1 ∧ ∀ l, Pr (f l)
def zMono (z : (Σ k, ι k) → ℂ) (c : (k : K) → ι k) (a : K → ℤ) : ℂ := ∏ k, z ⟨k, c k⟩ ^ a k
end Cover
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
theorem step_le {N : ℕ} (i : Fin (N - 1)) : (i : ℕ) + 1 ≤ N := by have := i.isLt; omega
structure PlueckerData (D : ComponentData II Ψ K ι Ω E) where

  e : ∀ τ, Fin D.N → E τ
  e_indep : ∀ τ, LinearIndependent Ω (e τ)
  e_span : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤

  M : Ψ → Fin (D.N - 1) → ℕ
  M_ge : ∀ τ (i : Fin (D.N - 1)), Nat.choose D.N ((i : ℕ) + 1) ≤ M τ i

  bdeg : Ψ → Fin (D.N - 1) → K → ℤ

  gen : ∀ τ (i : Fin (D.N - 1)), Fin (M τ i) → Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ))
  global : ∀ τ (i : Fin (D.N - 1)) m (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → ∀ v : Fin ((i : ℕ) + 1) → E τ,
    (∀ a, v a ∈ (D.W τ).lat c) →
      gen τ i m (exteriorPower.ιMulti Ω _ v) * chartMono D.y c (-bdeg τ i) ∈ chartRing ℤ (segreCoord D.y) c
  generates : ∀ τ (i : Fin (D.N - 1)) (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → HasCoverBy D.y c fun f =>
    ∃ b : Fin D.N → E τ, IsFrameOver D.y (D.W τ) c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ A : Fin ((i : ℕ) + 1) → Fin D.N, StrictMono A → ∃ a : Fin (M τ i) → Ω,
        (∀ m, ∃ n : ℕ, f ^ n * a m ∈ chartRing ℤ (segreCoord D.y) c) ∧
        ∀ A' : Fin ((i : ℕ) + 1) → Fin D.N, StrictMono A' →
          ∑ m, a m * (gen τ i m (exteriorPower.ιMulti Ω _ (b ∘ A')) * chartMono D.y c (-bdeg τ i)) =
            if A' = A then 1 else 0

  wdeg : Ψ → K → ℤ

  ω : ∀ τ, ⋀[Ω]^D.N (E τ)
  detW : ∀ τ (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → HasCoverBy D.y c fun f =>
    ∃ b : Fin D.N → E τ, IsFrameOver D.y (D.W τ) c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∃ u : Ω, IsUnitOn D.y c f u ∧ ω τ = (u * chartMono D.y c (-wdeg τ)) • exteriorPower.ιMulti Ω D.N b
namespace PlueckerData
variable {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)
def ιY : K ⊕ (Ψ × Fin (D.N - 1)) → Type := Sum.elim ι fun q => Fin (Pl.M q.1 q.2)
instance instFintypeιY : ∀ k, Fintype (Pl.ιY k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr q => inferInstanceAs (Fintype (Fin (Pl.M q.1 q.2)))
abbrev ΩY (_Pl : PlueckerData D) : Type := FractionRing (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω)
def ofΩ (x : Ω) : Pl.ΩY := algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (C x)
def gvar (τ : Ψ) (a b : Fin D.N) : Pl.ΩY :=
  algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (X (τ, a, b))
def pluecker (τ : Ψ) (i : Fin (D.N - 1)) (m : Fin (Pl.M τ i)) : Pl.ΩY :=
  ∑ c : Fin ((i : ℕ) + 1) → Fin D.N, (∏ a, Pl.gvar τ (headIdx (step_le i) a) (c a)) *
    Pl.ofΩ (Pl.gen τ i m (exteriorPower.ιMulti Ω _ (Pl.e τ ∘ c)))
def yY : (Σ k, Pl.ιY k) → Pl.ΩY
  | ⟨Sum.inl k, t⟩ => Pl.ofΩ (D.y ⟨k, t⟩)
  | ⟨Sum.inr q, m⟩ => Pl.pluecker q.1 q.2 m
def PY : Ideal (MRing Pl.ιY) := mCoordIdeal Pl.yY
def detFDeg (τ : Ψ) (i : Fin (D.N - 1)) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  Sum.elim (Pl.bdeg τ i) fun q => if q = (τ, i) then -1 else 0
def detStepDeg (τ : Ψ) (s : ℕ) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  if hs : s = 0 then 0 else if h : s < D.N then Pl.detFDeg τ ⟨s - 1, by omega⟩ else Sum.elim (Pl.wdeg τ) 0
def grDeg (τ : Ψ) (a : Fin D.N) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  Pl.detStepDeg τ ((a : ℕ) + 1) - Pl.detStepDeg τ a
def LDeg (la : Ψ × Fin D.N → ℤ) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  ∑ p, la p • Pl.grDeg p.1 p.2
def xPart (p : (Σ k, Pl.ιY k) → ℂ) : (Σ k, ι k) → ℂ := fun q => p ⟨Sum.inl q.1, q.2⟩
open Classical in

def solveLin {I : Type} [Fintype I] {M : ℕ} (Φ : Fin M → I → ℂ) (w : Fin M → ℂ) : I → ℂ :=
  if h : ∃ ω : I → ℂ, ∀ m, ∑ A, Φ m A * ω A = w m then h.choose else 0
abbrev Incr (s N : ℕ) : Type := {A : Fin s → Fin N // StrictMono A}
open Classical in

def detFNormSq (τ : Ψ) (i : Fin (D.N - 1)) (p : (Σ k, Pl.ιY k) → ℂ) : ℝ :=
  let z := Pl.xPart p
  if hl : ∃ l, InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z then
    let l := hl.choose
    let c := (D.h τ).chart l
    let Φ : Fin (Pl.M τ i) → Incr ((i : ℕ) + 1) D.N → ℂ := fun m A =>
      valAt D.y (Pl.gen τ i m (exteriorPower.ιMulti Ω _ ((D.h τ).b l ∘ A.1)) *
        chartMono D.y c (-Pl.bdeg τ i)) z * zMono z c (Pl.bdeg τ i)
    let w : Fin (Pl.M τ i) → ℂ := fun m => p ⟨Sum.inr (τ, i), m⟩
    let ω := solveLin Φ w
    (∑ A, ∑ A', starRingEnd ℂ (ω A) *
      (Matrix.of fun a b => (D.h τ).gram l z (A.1 a) (A'.1 b)).det * ω A').re
  else 0
def detFMetric (τ : Ψ) (i : Fin (D.N - 1)) (p : (Σ k, Pl.ιY k) → ℂ) : ℝ :=
  1 / Real.sqrt (Pl.detFNormSq τ i p)
structure DetWFrameAt (τ : Ψ) (z : (Σ k, ι k) → ℂ) where
  c : (k : K) → ι k
  f : Ω
  inDom : InFrameDomain D.y c f z
  b : Fin D.N → E τ
  frame : IsFrameOver D.y (D.W τ) c f b
  span : Submodule.span Ω (Set.range b) = ⊤
  u : Ω
  unit : IsUnitOn D.y c f u
  eq : Pl.ω τ = (u * chartMono D.y c (-Pl.wdeg τ)) • exteriorPower.ιMulti Ω D.N b
open Classical in

def detWMetric (τ : Ψ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if h : Nonempty (Pl.DetWFrameAt τ z) then
    ‖zMono z h.some.c (Pl.wdeg τ)‖ /
      (‖valAt D.y h.some.u z‖ * Real.sqrt (gramAt (D.h τ) h.some.b z).det.re)
  else 0
def detStepMetric (τ : Ψ) (s : ℕ) (p : (Σ k, Pl.ιY k) → ℂ) : ℝ :=
  if hs : s = 0 then 1 else if h : s < D.N then Pl.detFMetric τ ⟨s - 1, by omega⟩ p
  else Pl.detWMetric τ (Pl.xPart p)
def grMetric (τ : Ψ) (a : Fin D.N) (p : (Σ k, Pl.ιY k) → ℂ) : ℝ :=
  Pl.detStepMetric τ ((a : ℕ) + 1) p / Pl.detStepMetric τ a p
def grLine (τ : Ψ) (a : Fin D.N) : HermLine Pl.ιY := hermOfFun Pl.ιY (Pl.grDeg τ a) (Pl.grMetric τ a)
def phGr (τ : Ψ) (a : Fin D.N) (p : (Σ k, Pl.ιY k) → ℂ) : ℝ := Real.log ((Pl.grLine τ a).h p)
def LLine (la : Ψ × Fin D.N → ℤ) : HermLine Pl.ιY :=
  hermOfFun Pl.ιY (Pl.LDeg la) fun p => ∏ q, Pl.grMetric q.1 q.2 p ^ la q
def phLa (la : Ψ × Fin D.N → ℤ) (p : (Σ k, Pl.ιY k) → ℂ) : ℝ := Real.log ((Pl.LLine la).h p)
end PlueckerData
end GroundTheory.Heights₂.Heights.LowerBoundFree



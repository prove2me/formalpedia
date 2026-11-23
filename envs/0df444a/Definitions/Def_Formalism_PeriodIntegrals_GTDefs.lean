-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GTDefs
-- name    : Formalism_PeriodIntegrals_GTDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:14.267915+00:00
-- url     : https://prove2.me/theorems/cab86492-1d2b-4913-a2f2-408338315c30
-- title:
--   GTDefs
-- statement:
--   Definitions and structural lemmas for GTDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GTDefs.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open Formalism.BasicNotions MvPolynomial
def lastGL (R : Type) [CommRing R] (N : ℕ) (a : Rˣ) : GL (Fin N) R :=
  diagGL R N (fun i => if i.1 + 1 = N then a else 1)
def wsum {k : ℕ} (l : DomWeight k) : ℤ := ∑ i, l.w i
def aa {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  sg.w i - lam.w ⟨i.1 + 1, by omega⟩
def bb {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  lam.w ⟨i.1, by omega⟩ - sg.w i
def D0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, (sg.w i - lam.w ⟨i.1 + 1, by omega⟩)
def D1 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg)
def degZ {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n) : ℤ := wsum lam - wsum sg
def Rset {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w ⟨i.1 + 1, by omega⟩) (min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg))
def cBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - sg.w j + (j.1 : ℤ))
def rowsZ {n N : ℕ} (h : n + 1 = N) (i : Fin n) : Fin (i.1 + 1) → Fin N :=
  fun p => if p.1 = i.1 then ⟨N - 1, by omega⟩ else ⟨p.1, by omega⟩
def xi (R : Type) [CommRing R] {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) R :=
  ∏ i : Fin n, (Formalism.GradedWeylDivisibility.lpMinor R (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat *
    (Formalism.GradedWeylDivisibility.initMinor R (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat
def cBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  (((2 * lam.spread : ℤ) : ℝ)) ^ ((((N : ℤ) * D1 h lam sg : ℤ) : ℝ))
def brBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  cBd h lam sg * Real.sqrt (Module.finrank ℂ (delSq ℂ N lam))
def IsIota {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
    io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) ∧
  (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
    io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s)) ∧
  io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg ∧
  (∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (io s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • io s) ∧
  (∀ s ∈ nablaSq ℂ n sg,
    (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re)
def IsBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
    br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)
def IsTranspose {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  ∀ s ∈ nablaSq ℂ n sg, ∀ f ∈ delSq ℂ N lam, normFock lam (io s) f = normFock sg s (br f)
def Branch {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧ xi ℂ h lam sg ≠ 0 ∧
  degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg ∧
  ∃ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io ∧ IsBr h lam sg br ∧ IsTranspose lam sg io br
end PI



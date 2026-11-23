-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:07.216257+00:00
-- url     : https://prove2.me/theorems/99f2f328-017f-4600-99c1-9cf437ea207e
-- title:
--   Cm Lattice Commutator Pairing Pow Eq One Of Good Lift
-- statement:
--   Definitions and structural lemmas for Cm Lattice Commutator Pairing Pow Eq One Of Good Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
namespace GlobalTheory.MomOne
def wK (d : ℕ) : ℂ := (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2
def InOK (d : ℕ) (z : ℂ) : Prop := ∃ u v : ℤ, z = (u : ℂ) + (v : ℂ) * wK d
def Split (d q : ℕ) : Prop := (q = 2 ∧ d % 8 = 7) ∨ (q ≠ 2 ∧ jacobiSym (-(d : ℤ)) q = 1)
def eis (d k : ℕ) : ℂ := ∑' w : {w : ℂ // InOK d w ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)
def discr (d : ℕ) : ℂ := (60 * eis d 2) ^ 3 - 27 * (140 * eis d 3) ^ 2
def IsOK (d : ℕ) (L : PeriodPair) : Prop := ∀ z : ℂ, z ∈ L.lattice ↔ InOK d z
def h1 (d : ℕ) (z w : ℂ) : ℂ := ((2 / Real.sqrt d : ℝ) : ℂ) * (z * conj w)
def U1 (d : ℕ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => F (z + x) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)
def W1 (d : ℕ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * U1 d x F z
def kap1 (d : ℕ) (x y : ℂ) : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((h1 d x y).im : ℝ) : ℂ))
def IsTh (d : ℕ) (θ : ℂ → ℂ) : Prop :=
  Differentiable ℂ θ ∧ θ 0 = 1 ∧ (∀ z, θ (-z) = θ z) ∧ (∀ x, InOK d x → W1 d x θ = θ) ∧
    ∀ z, θ z = 0 → InOK d (z - 1 / 2)
def PrimeTo (d q : ℕ) (t : ℂ) : Prop := ∃ s : ℕ, 0 < s ∧ Nat.Coprime s q ∧ InOK d ((s : ℂ) * t)
def tay (G : ℂ → ℂ) : ℂ⟦X⟧ := PowerSeries.mk fun n => iteratedDeriv n G 0 / (n.factorial : ℂ)
def Ell (L : PeriodPair) (φ : ℂ → ℂ) : Prop := Meromorphic φ ∧ ∀ l ∈ L.lattice, ∀ z, φ (z + l) = φ z
variable {q : ℕ} [Fact q.Prime]
def zc (a : ℤ_[q]) : ℂ_[q] := algebraMap ℚ_[q] ℂ_[q] (a : ℚ_[q])
def logS : ℂ_[q]⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) / (n : ℂ_[q])
def mulS (a : ℤ_[q]) : ℂ_[q]⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else zc (Ring.choose a n)
def DT (f : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧ := (1 + X) * derivative ℂ_[q] f
def Bd (C : ℝ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ C
def Bdd (f : ℂ_[q]⟦X⟧) : Prop := ∃ C, Bd C f
def ev (f : ℂ_[q]⟦X⟧) (x : ℂ_[q]) : ℂ_[q] := ∑' n, coeff n f * x ^ n
def shiftS (ζ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧ :=
  PowerSeries.mk fun n => ∑' m, coeff m f * ((m.choose n : ℂ_[q]) * ζ ^ n * (ζ - 1) ^ (m - n))
def hat (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (G : ℂ → ℂ) : ℂ_[q]⟦X⟧ :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay G)).subst ℓ
structure Mdl (q : ℕ) [Fact q.Prime] where

  ι : ℂ ≃+* ℂ_[q]

  L : PeriodPair

  c : ℂ

  W : WeierstrassCurve ℂ_[q]
namespace Mdl
variable (M : Mdl q)
def Ok : Prop :=
  M.c ≠ 0 ∧ ‖M.W.a₁‖ ≤ 1 ∧ ‖M.W.a₂‖ ≤ 1 ∧ ‖M.W.a₃‖ ≤ 1 ∧ ‖M.W.a₄‖ ≤ 1 ∧ ‖M.W.a₆‖ ≤ 1 ∧ ‖M.W.Δ‖ = 1 ∧
    M.W.c₄ / 12 = M.ι (M.L.g₂ / M.c ^ 4) ∧ M.W.c₆ / 216 = M.ι (M.L.g₃ / M.c ^ 6)
def x (z : ℂ) : ℂ := M.L.weierstrassP z / M.c ^ 2 - M.ι.symm (M.W.b₂ / 12)
def y (z : ℂ) : ℂ :=
  (M.L.derivWeierstrassP z / M.c ^ 3 - M.ι.symm M.W.a₁ * M.x z - M.ι.symm M.W.a₃) / 2
open Classical in

def u (z : ℂ) : ℂ := if z ∈ M.L.lattice then 0 else -M.x z / M.y z
open Classical in

def w (z : ℂ) : ℂ := if z ∈ M.L.lattice then 0 else -1 / M.y z
def Small (z : ℂ) : Prop := z ∈ M.L.lattice ∨ 1 < ‖M.ι (M.x z)‖
def Chart (ℓ : ℂ_[q]⟦X⟧) : Prop :=
  M.Ok ∧ constantCoeff ℓ = 0 ∧ Bd 1 (hat M.ι ℓ M.u) ∧ ‖coeff 1 (hat M.ι ℓ M.u)‖ = 1
def MChart (ω : ℂ_[q]) : Prop := M.Chart (C ω * logS)
def At (ω ζ : ℂ_[q]) (z : ℂ) : Prop :=
  M.Small z ∧ ‖ζ - 1‖ < 1 ∧ ev (hat M.ι (C ω * logS) M.u) (ζ - 1) = M.ι (M.u z)
end Mdl
def Good (ι : ℂ ≃+* ℂ_[q]) (d n s : ℕ) (y : ℂ) : Prop :=
  ∃ v : ℂ, InOK d v ∧ ‖ι (conj v)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ y = (s : ℂ) * v / (q : ℂ) ^ n
def ThetaLaws (ι : ℂ ≃+* ℂ_[q]) (d : ℕ) (ω : ℂ_[q]) (θ : ℂ → ℂ) : Prop :=
  (∀ t, PrimeTo d q t → Bd 1 (hat ι (C ω * logS) (U1 d t θ))) ∧
  (∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y →
    ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧
    hat ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (ι (kap1 d 1 y)) (hat ι (C ω * logS) (U1 d t θ))) ∧
  ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t →
    Bd B (∑ j, C (c j) * hat ι (C ω * logS) (U1 d (s j) θ) ^ a) →
    Bd B (∑ j, C (c j) * hat ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a)
namespace Basic
open Filter Topology
def okPair (d : ℕ) (hd : 0 < d) : PeriodPair := ⟨1, wK d, LinearIndependent.pair_iff.2 fun s t h => by
  have hs : Real.sqrt d ≠ 0 := by positivity
  have h2 := congrArg Complex.im h
  have h1 := congrArg Complex.re h
  simp [wK, hs] at h1 h2
  subst h2
  exact ⟨by simpa using h1, rfl⟩⟩
example : Split 7 2 := Or.inl ⟨rfl, rfl⟩
example : Split 7 11 := Or.inr ⟨by norm_num, by norm_num⟩
example : ¬ Split 7 3 := by norm_num [Split]
end Basic
end GlobalTheory.MomOne



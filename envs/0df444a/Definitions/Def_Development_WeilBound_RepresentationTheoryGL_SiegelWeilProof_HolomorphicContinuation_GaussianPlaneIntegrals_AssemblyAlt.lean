-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:33.08983+00:00
-- url     : https://prove2.me/theorems/c4dd4f07-9785-4888-992c-296e45236e25
-- title:
--   Assembly Alt
-- statement:
--   Definitions and structural lemmas for Assembly Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyAlt.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
namespace PositivityTheory.Rg.Sw.FFTSteps
abbrev PV (ι A B : Type) := MvPolynomial ((ι × A) ⊕ (ι × B)) ℂ
def sub {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) : PV ι A B →ₐ[ℂ] PV ι A B :=
  aeval (Sum.elim (fun x : ι × A => ∑ j, C (g x.1 j) * X (Sum.inl (j, x.2)))
    (fun y : ι × B => ∑ j, C (h y.1 j) * X (Sum.inr (j, y.2))))
def IsInv {ι A B : Type} [Fintype ι] [DecidableEq ι] (p : PV ι A B) : Prop :=
  ∀ u ∈ Matrix.unitaryGroup ι ℂ, sub u (u.map star) p = p
def pairAlg (ι A B : Type) [Fintype ι] : Subalgebra ℂ (PV ι A B) :=
  Algebra.adjoin ℂ (Set.range fun ab : A × B => ∑ i, (X (Sum.inl (i, ab.1)) : PV ι A B) * X (Sum.inr (i, ab.2)))
def Stable : Prop :=
  ∀ (ι A B : Type) [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B], Fintype.card A ≤ Fintype.card ι →
    Fintype.card B ≤ Fintype.card ι → ∀ p : PV ι A B, IsInv p → p ∈ pairAlg ι A B
def Ext : Prop :=
  ∀ (ι A B : Type) [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] (p : PV ι A B), IsInv p →
    ∀ g h : Matrix ι ι ℂ, g * h.transpose = 1 → sub g h p = p
def Avg : Prop :=
  ∀ (N : ℕ) (A B : Type) [Fintype A] [Fintype B] (p : PV (Fin N) A B), ∃ P : PV (Fin N) A B, IsInv P ∧
    P.totalDegree ≤ p.totalDegree ∧ ∀ z, eval z P =
      ∫ k : Formalism.REAL.KG (fun _ : Fin N => true), eval z (sub (Formalism.REAL.toMK k) ((Formalism.REAL.toMK k).map star) p)
        ∂(Formalism.REAL.muK (fun _ : Fin N => true))
def gip {σ : Type} [Fintype σ] (f g : MvPolynomial σ ℂ) : ℂ :=
  ∫ z : σ → ℂ, eval z f * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))
def Pos : Prop :=
  ∀ (ι A B : Type) [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] (M : Matrix ι ι ℂ), M.PosSemidef →
    ∀ f : PV ι A B, 0 ≤ (gip (sub 1 M f) f).re ∧ (gip (sub 1 M f) f).im = 0 ∧ (M.PosDef → f ≠ 0 → 0 < (gip (sub 1 M f) f).re)
def Assembly : Prop := Stable → Ext → Avg → Pos → FFT
def CycAvg : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ P : PX m n, ∃ Q : PX m n,
    (∀ u : Matrix (Fin m) (Fin m) ℂ, u ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ a b, ε a ≠ ε b → u a b = 0) →
      aeval (fun k : Fin m × Fin n × Bool => if k.2.2 then ∑ b, C (star (u k.1 b)) * X (b, k.2.1, true)
        else ∑ b, C (u k.1 b) * X (b, k.2.1, false)) Q = Q) ∧ NullSec ε c (P - Q)
def CycFFT : Prop :=
  FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (Q : PX m n),
    (∀ u : Matrix (Fin m) (Fin m) ℂ, u ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ a b, ε a ≠ ε b → u a b = 0) →
      aeval (fun k : Fin m × Fin n × Bool => if k.2.2 then ∑ b, C (star (u k.1 b)) * X (b, k.2.1, true)
        else ∑ b, C (u k.1 b) * X (b, k.2.1, false)) Q = Q) →
    Q ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))
def SecLine : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    ∃ δ : ℝ, 0 < δ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x *
        Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)) {z | |z.im| < δ} ∧
      (∀ z : ℂ, (z.im = 0) → (∫ x : Fin m → Fin n → ℂ, evX P x * gs c x *
        Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)) = secN ε c t P (z • b)) ∧
      ∀ k : ℕ, iteratedDeriv k (fun z : ℂ => ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x *
        Complex.exp (Complex.I * t * z * (b * gramX ε x).trace)) 0 =
          (Complex.I * t) ^ k * ∫ x, evX P x * gs c x * ((b * gramX ε x).trace) ^ k
def PowSpan : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool),
    (Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))).toSubmodule =
      Submodule.span ℂ {R | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), b.IsHermitian ∧
        R = (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k}
end PositivityTheory.Rg.Sw.FFTSteps



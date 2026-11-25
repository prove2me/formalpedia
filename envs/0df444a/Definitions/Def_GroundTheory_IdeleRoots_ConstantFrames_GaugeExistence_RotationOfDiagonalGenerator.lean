-- Prove2me | Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
-- name    : GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:22.814863+00:00
-- url     : https://prove2.me/theorems/c699325f-5b14-41b8-a048-19b6dda168cc
-- title:
--   Rotation Of Diagonal Generator
-- statement:
--   Definitions and structural lemmas for Rotation Of Diagonal Generator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/RotationOfDiagonalGenerator.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GenTransferKapCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists
noncomputable section
def dZv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : ℂ → V) (ζ : ℂ) : V :=
  (1 / 2 : ℂ) • (fderiv ℝ φ ζ 1 - Complex.I • fderiv ℝ φ ζ Complex.I)
def dZbv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : ℂ → V) (ζ : ℂ) : V :=
  (1 / 2 : ℂ) • (fderiv ℝ φ ζ 1 + Complex.I • fderiv ℝ φ ζ Complex.I)
def dl (P : M.Par) (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ' => if ρ' = ρ then 1 else 0
def sumRho (P : M.Par) (ρ : M.Ty P) : ℂ := ∑ i ∈ Finset.Icc 1 (P.k - 1), (M.rho P ρ i : ℂ)
def sumU (k : ℕ) (u : ℕ → ℝ) : ℂ := ∑ i ∈ Finset.Icc 1 k, (u i : ℂ)
def iN (k r : ℕ) : Fin (2 * r + k + 1) := wI k r (Fin.last k)
def iP (k r : ℕ) : Fin (2 * r + k + 1) := wI k r 0
def iU {k : ℕ} (r : ℕ) (i : Fin (k - 1)) : Fin (2 * r + k + 1) := wI k r ⟨i.val + 1, by have := i.isLt; omega⟩
def gAm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Q.Mx k r :=
  B2.embWb k r (Formalism.FourierDecayAlt.P.TheSec.gA k (wbPart k r z) (Tz k r z))
def gBm (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Q.Mx k r :=
  B2.embWb k r (Formalism.FourierDecayAlt.P.TheSec.gB k (wbPart k r z') (Tz k r z'))
def Am (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (2 * r + k + 1)) : Q.Mx k r :=
  (gBm k r z')⁻¹ * Matrix.single a b (1 : ℂ) * gBm k r z'
def wLv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := gAm k r z *ᵥ Pi.single (iP k r) 1
def wRv (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  (gBm k r z')⁻¹ *ᵥ Pi.single (iP k r) 1
def frL (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (k - 1)) : Fin (2 * r + k + 1) → ℂ :=
  gAm k r z *ᵥ Pi.single (iU r i) 1
def frR (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (k - 1)) : Fin (2 * r + k + 1) → ℂ :=
  (gBm k r z')⁻¹ *ᵥ Pi.single (iU r i) 1
section ops
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
def Lw (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) : Module.End ℂ Wp :=
  Qr.EB π (fun _ : Fin 1 => wLv k r z) 0 0
def Rw (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) : Module.End ℂ Wq :=
  Qr.EB π' (fun _ : Fin 1 => wRv k r z') 0 0
def Ru (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) : Module.End ℂ Wq :=
  ∑ i, Qr.EB π' (frR k r z') i i
end ops
section sub
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
def ZY (g : Q.Mx k r) : Q.Mx k r :=
  ∑ a, ∑ b, (Q.yv k r z (Fin.last r) g a * Q.xbv k r z' (Fin.last r) b) •
    Matrix.single (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) (1 : ℂ)
def ZX (g : Q.Mx k r) : Q.Mx k r :=
  ∑ a, ∑ b, (Q.xv k r z' (Fin.last r) a * Q.ybv k r z (Fin.last r) g b) •
    Matrix.single (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) (1 : ℂ)
def Ir : Q.Mx k r := ∑ a, Matrix.single (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) a) (1 : ℂ)
def lowerOffDiagonalCoeff (f : Q.Mx k r → E) (g : Q.Mx k r) : E :=
  Q.RZ (Hpk k r) (ZY k r z z' g) f g - star (Q.zetaL k r z z' (Fin.last r) g) • Q.RZ (Hpk k r) (Ir k r) f g -
    (((k : ℂ) / 2) * star (Q.zetaL k r z z' (Fin.last r) g)) • f g
def upperOffDiagonalCoeff (f : Q.Mx k r → E) (g : Q.Mx k r) : E :=
  Q.RZ (Hpk k r) (ZX k r z z' g) f g - Q.zetaL k r z z' (Fin.last r) g • Q.RZ (Hpk k r) (Ir k r) f g +
    (((k : ℂ) / 2) * Q.zetaL k r z z' (Fin.last r) g) • f g
def IsBlockSL2Embedding (Z : Q.Mx k r) : Prop :=
  ∀ p q, (p ∉ Set.range (Q.posL k r (Fin.last r)) ∨ q ∉ Set.range (Q.posL k r (Fin.last r))) → Z p q = 0
end sub
section frame
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def IsTheSec (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Prop :=
  Bs.μsec = Formalism.FourierDecayAlt.P.TheSec.theSection P.k P.r Bs.z Bs.z'
def cF {P : M.Par} (E : M.Ty P → (Wq →L[ℂ] Wp)) : M.Ty P → ℂ → (Wq →L[ℂ] Wp) := fun ρ _ => E ρ
def AtThe (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) : Prop :=
  GTHyp P Bs X d ∧ IsTheSec P Bs
def IsLines (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (Qr : M.Ty P → (Wq →L[ℂ] Wq))
    (E : M.Ty P → (Wq →L[ℂ] Wp)) : Prop :=
  KapPt P Bs d Qr ∧ (∀ ρ, (E ρ).comp (Qr ρ) = E ρ) ∧ IsFrameB P Bs (cF E) ∧ KapF P Bs d (cF E)
def slc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) :
    ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)
end frame
def ConstFrame : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)), IsLines P Bs d Qr E
def ConstFrameOf : Prop := GTKPt → GTKLine → ConstFrame
def QdetSub : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (Eo : Fin n → Fin n → A), 1 ≤ n →
    ∃ C : ℕ → A, ∀ u : ℂ, qdet Eo u = algebraMap ℂ A (u ^ n) +
      algebraMap ℂ A (u ^ (n - 1)) * (∑ i, Eo i i - algebraMap ℂ A (((n : ℂ) * ((n : ℂ) - 1)) / 2)) +
      ∑ j ∈ Finset.range (n - 1), algebraMap ℂ A (u ^ j) * C j
def TSub : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ),
    2 ≤ k → inWb k r z → inWb k r z' →
    ∃ A : Fin 2 → ℕ → (Q.Mx k r → E) → Q.Mx k r → E, ∀ (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), IsOpen D →
      Q.SmoothLev k r (Fin.last r) D f → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ Y : ℂ,
        Q.tL k r z z' (Fin.last r) Y 1 0 f g = -((star (Q.zetaL k r z z' (Fin.last r) g) * Y ^ k) • f g) +
          Y ^ (k - 1) • lowerOffDiagonalCoeff k r z z' f g + ∑ j ∈ Finset.range (k - 1), Y ^ j • A 1 j f g ∧
        Q.tL k r z z' (Fin.last r) Y 0 1 f g = -((Q.zetaL k r z z' (Fin.last r) g * Y ^ k) • f g) +
          Y ^ (k - 1) • upperOffDiagonalCoeff k r z z' f g + ∑ j ∈ Finset.range (k - 1), Y ^ j • A 0 j f g
def NabEq : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r), x ∈ Q.DomR P.k P.r Bs.z Bs.z' →
      ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) • ((d.L.nab.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        -lowerOffDiagonalCoeff P.k P.r Bs.z Bs.z' ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2 -
          star (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2) • (((d.κ (sumRho P)).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 -
          ((1 / 2 : ℂ) * star (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 ∧
      ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) • ((d.L.nabs.1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        -upperOffDiagonalCoeff P.k P.r Bs.z Bs.z' ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2 -
          Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 • (((d.κ (sumRho P)).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 +
          ((1 / 2 : ℂ) * Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2
def NabEqOf : Prop := TSub → NabEq
def RZSum : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), IsOpen D →
    Q.SmoothLev k r (Fin.last r) D f → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ (ι : Type) (s : Finset ι) (c : ι → ℂ)
      (Z : ι → Q.Mx k r), (∀ i ∈ s, IsBlockSL2Embedding k r (Z i)) →
      Q.RZ (Hpk k r) (∑ i ∈ s, c i • Z i) f g = ∑ i ∈ s, c i • Q.RZ (Hpk k r) (Z i) f g
def SecPlane : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      ZY P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec ζ) = (-(((Real.sqrt P.T * Real.sqrt P.T' : ℝ) : ℂ) * star (Formalism.FourierDecayAlt.P.TheSec.wZ P.T P.T' ζ))) • Am P.k P.r Bs.z' (iN P.k P.r) (iN P.k P.r) +
        (((Real.sqrt P.T * Real.sqrt P.T' : ℝ) : ℂ) * (Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ)) • Am P.k P.r Bs.z' (iP P.k P.r) (iN P.k P.r) ∧
      ZX P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec ζ) = (-(((Real.sqrt P.T * Real.sqrt P.T' : ℝ) : ℂ) * (Formalism.FourierDecayAlt.P.TheSec.wZ P.T P.T' ζ))) • Am P.k P.r Bs.z' (iN P.k P.r) (iN P.k P.r) -
        (((Real.sqrt P.T * Real.sqrt P.T' : ℝ) : ℂ) * (Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ)) • Am P.k P.r Bs.z' (iN P.k P.r) (iP P.k P.r) ∧
      Ir P.k P.r = Am P.k P.r Bs.z' (iN P.k P.r) (iN P.k P.r) + Am P.k P.r Bs.z' (iP P.k P.r) (iP P.k P.r) +
        ∑ i : Fin (P.k - 1), Am P.k P.r Bs.z' (iU P.r i) (iU P.r i) ∧
      (∀ a b, IsBlockSL2Embedding P.k P.r (Am P.k P.r Bs.z' (wI P.k P.r a) (wI P.k P.r b)))
def SecR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ v : Wq,
      (Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iP P.k P.r) (iP P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) v = slc P Bs Φ c ζ (Rw P.k P.r Bs.z' Bs.π' v) ∧
      (∑ i : Fin (P.k - 1), Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iU P.r i) (iU P.r i)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) v =
        slc P Bs Φ c ζ (Ru P.k P.r Bs.z' Bs.π' v)
def RotationOfDiagonalGenerator : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ v : Wq,
      (Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iN P.k P.r) (iN P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) v = Lw P.k P.r Bs.z Bs.π (slc P Bs Φ c ζ v) +
        (ζ • dZv (slc P Bs Φ c) ζ - star ζ • dZbv (slc P Bs Φ c) ζ) v
def SecDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      ((Real.sqrt P.T * Real.sqrt P.T' : ℝ) : ℂ) • dZv (slc P Bs Φ c) ζ =
        (-(star (Formalism.FourierDecayAlt.P.TheSec.wZ P.T P.T' ζ) / 2)) • (Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iN P.k P.r) (iN P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ) - Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iP P.k P.r) (iP P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) -
          (star (Formalism.FourierDecayAlt.P.TheSec.wZ P.T P.T' ζ) ^ 2 / (2 * (Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ))) • Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iN P.k P.r) (iP P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ) +
          (((Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ) ^ 2 - 1) / (2 * (Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ))) • Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iP P.k P.r) (iN P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ) ∧
      ((Real.sqrt P.T * Real.sqrt P.T' : ℝ) : ℂ) • dZbv (slc P Bs Φ c) ζ =
        ((Formalism.FourierDecayAlt.P.TheSec.wZ P.T P.T' ζ) / 2) • (Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iN P.k P.r) (iN P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ) - Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iP P.k P.r) (iP P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) +
          (((Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ) ^ 2 - 1) / (2 * (Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ))) • Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iN P.k P.r) (iP P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ) -
          ((Formalism.FourierDecayAlt.P.TheSec.wZ P.T P.T' ζ) ^ 2 / (2 * (Formalism.FourierDecayAlt.P.TheSec.sZ P.T P.T' ζ))) • Q.RZ (Hpk P.k P.r) (Am P.k P.r Bs.z' (iP P.k P.r) (iN P.k P.r)) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)
def SecB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ v : Wq,
      (lowerOffDiagonalCoeff P.k P.r Bs.z Bs.z' ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) v =
        -(((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) • (dZv (slc P Bs Φ c) ζ) v) - star ζ • ((1 / 2 : ℂ) • Lw P.k P.r Bs.z Bs.π (slc P Bs Φ c ζ v) +
          (1 / 2 : ℂ) • slc P Bs Φ c ζ (Rw P.k P.r Bs.z' Bs.π' v) + slc P Bs Φ c ζ (Ru P.k P.r Bs.z' Bs.π' v) +
          ((P.k : ℂ) / 2) • slc P Bs Φ c ζ v) ∧
      (upperOffDiagonalCoeff P.k P.r Bs.z Bs.z' ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) v =
        ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) • (dZbv (slc P Bs Φ c) ζ) v - ζ • ((1 / 2 : ℂ) • Lw P.k P.r Bs.z Bs.π (slc P Bs Φ c ζ v) +
          (1 / 2 : ℂ) • slc P Bs Φ c ζ (Rw P.k P.r Bs.z' Bs.π' v) + slc P Bs Φ c ζ (Ru P.k P.r Bs.z' Bs.π' v) -
          ((P.k : ℂ) / 2) • slc P Bs Φ c ζ v)
def SecBOf : Prop := RZSum → SecPlane → SecR → RotationOfDiagonalGenerator → SecDeriv → SecB
def WRight : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → ∀ (ρ : M.Ty P) (v : Wq),
      E ρ (Ru P.k P.r Bs.z' Bs.π' v) = sumRho P ρ • E ρ v
def WTrace : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), 1 ≤ k → Q.IsType k r z π u →
    ∀ F : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] F → ∀ v : Wp, ∑ a, Qr.EB π F a a v = sumU k u • v
def WInter : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ (i : Fin (P.k - 1)) (v : Wq),
      Qr.EB Bs.π (frL P.k P.r Bs.z) i i (Z v) = Z (Qr.EB Bs.π' (frR P.k P.r Bs.z') i i v)
def Weights : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → ∀ (ρ : M.Ty P) (v : Wq),
      Lw P.k P.r Bs.z Bs.π (E ρ v) = (sumU P.k P.u - sumRho P ρ) • E ρ v ∧
      E ρ (Rw P.k P.r Bs.z' Bs.π' v) = (sumU P.k P.u' - sumRho P ρ) • E ρ v ∧
      E ρ (Ru P.k P.r Bs.z' Bs.π' v) = sumRho P ρ • E ρ v
def WeightsOf : Prop := WRight → WTrace → WInter → Weights
def TrWirt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ E : M.Ty P → (Wq →L[ℂ] Wp), IsFrameB P Bs (cF E) → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((dzQ P (trR P Bs (cF E) (Φ) ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (E ρ)) (B.hsVec (dZv (slc P Bs Φ q.1.1) q.1.2)) +
          ((((P.k : ℂ) - 1) / 2) * star q.1.2 / ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))) *
            ((trR P Bs (cF E) (Φ) ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ∧
      ((dzbQ P (trR P Bs (cF E) (Φ) ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (E ρ)) (B.hsVec (dZbv (slc P Bs Φ q.1.1) q.1.2)) +
          ((((P.k : ℂ) - 1) / 2) * q.1.2 / ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))) *
            ((trR P Bs (cF E) (Φ) ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q
def NabThe : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → NabF P Bs d (cF E)
def NabTheOf : Prop := NabEq → SecB → Weights → TrWirt → NabThe
def SSVia : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, M.Up P l ρ ρ' → ∀ (Y : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      M.xEx P {l} ρ Y • (d.SS l).1 ((d.κ (dl P ρ)).1 Φ) = (d.κ (dl P ρ')).1 (X.t Y 1 0 ((d.κ (dl P ρ)).1 Φ)) ∧
      M.xEx P {l} ρ Y • (star (d.SS l)).1 ((d.κ (dl P ρ')).1 Φ) = (d.κ (dl P ρ)).1 (X.t Y 0 1 ((d.κ (dl P ρ')).1 Φ))
def Ord0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∀ T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
    (∀ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (ζ : ℂ), c ∈ OmX P.r → P.TT < Complex.normSq ζ →
      (∃ V ∈ nhds ζ, ∀ ζ' ∈ V, slc P Bs Φ c ζ' = slc P Bs Ψ c ζ') → slc P Bs (T Φ) c ζ = slc P Bs (T Ψ) c ζ) →
    (∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
      (T Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' id (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))) →
    (∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
      (T Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))) →
    ∀ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (ζ : ℂ), c ∈ OmX P.r → P.TT < Complex.normSq ζ →
      slc P Bs Φ c ζ = slc P Bs Ψ c ζ → slc P Bs (T Φ) c ζ = slc P Bs (T Ψ) c ζ
def SSPoint : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, M.Up P l ρ ρ' →
      ∃ s s' : MA.SmQ P.r P.TT, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs (cF E) ((d.SS l).1 ((d.κ (dl P ρ)).1 Φ)) ρ' = s * trR P Bs (cF E) (Φ) ρ ∧
        trR P Bs (cF E) ((star (d.SS l)).1 ((d.κ (dl P ρ')).1 Φ)) ρ = s' * trR P Bs (cF E) (Φ) ρ'
def SSPointOf : Prop := SSVia → Ord0 → SSPoint
def SSConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, M.Up P l ρ ρ' →
      ∃ s s' : ℂ, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs (cF E) ((d.SS l).1 ((d.κ (dl P ρ)).1 Φ)) ρ' = s • trR P Bs (cF E) (Φ) ρ ∧
        trR P Bs (cF E) ((star (d.SS l)).1 ((d.κ (dl P ρ')).1 Φ)) ρ = s' • trR P Bs (cF E) (Φ) ρ'
def SSConstOf : Prop := SSPoint → NabThe → SSConst
def SSBump : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → ∀ ρ ρ' : M.Ty P, ∃ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (b : MA.SmQ P.r P.TT) (K : Set (Q.Mx P.k P.r)),
      b ≠ 0 ∧ IsCompact K ∧ K ⊆ {g | 0 < Q.GGl P.k P.r Bs.z Bs.z' g} ∧
      (∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (fun _ => 1) g = 0 ∧ (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (fun _ => 1) g = 0) ∧
      (∀ σ, trR P Bs (cF E) Φ σ = if σ = ρ then b else 0) ∧ (∀ σ, trR P Bs (cF E) Ψ σ = if σ = ρ' then b else 0)
def SSAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, M.Up P l ρ ρ' → ∀ s s' : ℂ,
      (∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs (cF E) ((d.SS l).1 ((d.κ (dl P ρ)).1 Φ)) ρ' = s • trR P Bs (cF E) (Φ) ρ ∧
        trR P Bs (cF E) ((star (d.SS l)).1 ((d.κ (dl P ρ')).1 Φ)) ρ = s' • trR P Bs (cF E) (Φ) ρ') → s' = star s
def SSAdjOf : Prop := SSVia → SSBump → SSAdj
def SSSquare : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), P.OK → d.Rel →
    (∀ Y Y', Commute (d.QQ Y 1 0) (d.QQ Y' 1 0)) → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ j ∈ Finset.Icc 1 (P.k - 1), l ≠ j →
    ∀ ρ ρ1 ρ2 ρ3 : M.Ty P, M.Up P l ρ ρ1 → M.Up P j ρ1 ρ2 → M.Up P j ρ ρ3 → M.Up P l ρ3 ρ2 →
      (((M.rho P ρ l - M.rho P ρ j - 1 : ℝ) : ℂ)) • (d.SS l * d.SS j * d.κ (dl P ρ)) =
        (((M.rho P ρ l - M.rho P ρ j + 1 : ℝ) : ℂ)) • (d.SS j * d.SS l * d.κ (dl P ρ))
def PhaseBox : Prop :=
  ∀ (P : M.Par) (θ : ℕ → M.Ty P → ℂ),
    (∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, M.Up P l ρ ρ' → ‖θ l ρ‖ = 1) →
    (∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ j ∈ Finset.Icc 1 (P.k - 1), l ≠ j → ∀ ρ ρ1 ρ2 ρ3 : M.Ty P,
      M.Up P l ρ ρ1 → M.Up P j ρ1 ρ2 → M.Up P j ρ ρ3 → M.Up P l ρ3 ρ2 → θ j ρ1 * θ l ρ = θ l ρ3 * θ j ρ) →
    ∃ v : M.Ty P → ℂ, (∀ ρ, ‖v ρ‖ = 1) ∧
      ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, M.Up P l ρ ρ' → v ρ' = θ l ρ * v ρ
def RhoGap : Prop :=
  ∀ (P : M.Par), P.OK → ∀ (ρ : M.Ty P), ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ j ∈ Finset.Icc 1 (P.k - 1), l < j →
    1 ≤ M.rho P ρ l - M.rho P ρ j
def SSFThe : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp)),
    AtThe P Bs X d → IsLines P Bs d Qr E → ∃ E' : M.Ty P → (Wq →L[ℂ] Wp), IsLines P Bs d Qr E' ∧
      NabF P Bs d (cF E') ∧ SSF P Bs d (cF E')
def SSFOf : Prop := NabThe → SSConst → SSAdj → SSSquare → PhaseBox → RhoGap → SSFThe
def GenThe : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    AtThe P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ FnF P Bs d e ∧ KapF P Bs d e ∧ NabF P Bs d e ∧
      SSF P Bs d e
def GenTheOf : Prop := GTFn → ConstFrame → NabThe → SSFThe → GenThe
def GCoreThe : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → IsTheSec P Bs →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ
def CoreTheOf : Prop := GenThe → GCoreThe
def MoveThe : Prop := GCoreThe → GCore
end
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists



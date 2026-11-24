-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:40:08.996242+00:00
-- url     : https://prove2.me/theorems/45c3a9c9-2097-4ad7-a8f7-946e50e49fdf
-- title:
--   Cut Gauge Cut
-- statement:
--   Definitions and structural lemmas for Cut Gauge Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge
noncomputable section
section defs
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def OmB {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Set (B.Mat k r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g ∧
    ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}
def IsFrameB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ
def rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Bs q.1)))
def trJB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawJ P Bs e J ρ)
def wR (k : ℕ) (TT : ℝ) (ζ : ℂ) : ℝ := Real.sqrt ((Complex.normSq ζ - TT) ^ (k - 1))
def rawR (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
    inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (Φ q.1.1 (NF.muZ P.k P.r μsec q.1.2)))
def FamR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : Prop :=
  IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ x.2 ∈ Dc x.1} ∧
  (∀ c ∈ OmX P.r, Q.IsDom P.k P.r Bs.z Bs.z' (Fin.last P.r) (Dc c)) ∧
  (∀ q : MA.Qp P.r P.TT, NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Dc q.1.1) ∧
  Q.FamFF P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) Dc Φ
end defs
def GTrChain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs),
      FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs}) (Q.resG P.k P.r (Fin.last P.r) J) ∧
      (∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P),
        rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ) ∧
      ∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (Y : ℝ),
        rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ =
          ∑ a : Fin 2, ∑ b : Fin 2, rawR P Bs.μsec e
            (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
              (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
                (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) (Q.resG P.k P.r (Fin.last P.r) J)))) ρ
def GRawSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ ρ, rawR P Bs.μsec e Φ ρ ∈ MA.smSub P.r P.TT
def GQLFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2), FamR P Bs Dc (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ)
def GVTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (b : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ) =
          MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ
def GVsTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ρ) =
          MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a)) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ
def GCore : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ
section act
variable (P : M.Par)
def fstHom : (MA.DQ P).Pr →+ (MA.DQ P).Op where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
def evalHom (g : (MA.DQ P).R) : (MA.DQ P).Op →+ (MA.DQ P).R where
  toFun X := X g
  map_zero' := rfl
  map_add' _ _ := rfl
end act
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge



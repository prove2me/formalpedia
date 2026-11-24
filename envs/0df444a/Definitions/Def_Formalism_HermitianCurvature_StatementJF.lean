-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementJF
-- name    : Formalism_HermitianCurvature_StatementJF
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:27:35.948928+00:00
-- url     : https://prove2.me/theorems/043c7b7c-17c7-4f9c-9509-5d5188df5296
-- title:
--   Statement JF
-- statement:
--   Definitions and structural lemmas for Statement JF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementJF.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.JF
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def Om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) := B.GV k r ∩ Q.OmPlus k r z z'
def QDom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × ℂ) :=
  {q | (∀ a, q.1 a ≠ 0) ∧ Tz k r z * Tz k r z' < Complex.normSq q.2}
def xiP {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) : ℂ :=
  psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2))
def integrand {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) (p : B.SS k r) : Wq →L[ℂ] Wp :=
  xiP D p • B.rho D p F g
def sL {k r : ℕ} (p : B.SS k r) : B.Mat k r := Matrix.of p.1.2 * Matrix.of p.1.1
def sR {k r : ℕ} (p : B.SS k r) : B.Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1
def AdL {k r : ℕ} (p : B.SS k r) (X : B.Mat k r) : B.Mat k r := (sL p)⁻¹ * X * sL p
def AdR {k r : ℕ} (p : B.SS k r) (X : B.Mat k r) : B.Mat k r := (sR p)⁻¹ * X * sR p
def IsEqv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (UU : Set (B.Mat k r))
    (f : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ p, D.inSS p → ∀ g ∈ UU, xiP D p • B.rho D p f g = f g
def castW {k : ℕ} (μ : B.Mat k 0) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.reindex (finCongr (by omega)) (finCongr (by omega)) μ
def sliceR {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) (μ : B.Mat k 0) : Wq →L[ℂ] Wp :=
  ∫ nn : Mt k r × Mt k r, (psi k r D.z cStd (Matrix.of nn.1) * star (psi k r D.z' cStd (Matrix.of nn.2))) •
    F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ∂(D.μN.prod D.μN)
def TransportedAlt (k r : ℕ) (A : ℝ) (m : ℕ) : Prop :=
  ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < (A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))
def JConv : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A 0 → B.InCC A 0 F →
    (∀ g ∈ Om k r D.z D.z', Integrable (integrand D F g) D.μSS) ∧
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧ ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖B.rho D p F g‖ ≤ b p
def JDom : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS) ∧
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p
def JWords : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    Q.CkLev k r 0 m (Q.OmPlus k r D.z D.z') (B.JF D F) ∧
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        Integrable (fun p => xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS ∧
        B.dLR u v (B.JF D F) g =
          ∫ p, xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g ∂D.μSS
def JWordsOfDom : Prop := JDom → JWords
def RwRho : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (p : B.SS k r),
    D.inSS p → B.CkOn (m : ℕ∞) (B.GV k r) f →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.inLie k r X) → (∀ X ∈ v, B.inLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ B.GV k r, B.dLR u v (B.rho D p f) g = B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) f) g
def LastLevelDiagonalSlice : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)) ∧
    (∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) →
      B.InCC (k := k) (r := 0) ((A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))) m (sliceR D F c)) ∧
    ∀ (d : ℕ) (O : Set (Fin d → ℝ)) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0),
      IsOpen O → ContDiffOn ℝ ∞ cx O → ContDiffOn ℝ ∞ μx O → (∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => sliceR D F (cx x) (μx x)) O
def CVLeft : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E),
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ y ∈ B.GV k r, ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => f (y * x)) g = Q.CV k r Y f (y * g)
def CVRight : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E),
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ y ∈ B.GV k r, ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => f (x * y)) g = Q.CV k r Y f (g * y)
def CVPost : Prop :=
  ∀ (k r : ℕ) (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (Y : ℂ) (Φ : E →L[ℂ] E') (f : B.Mat k r → E),
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => Φ (f x)) g = Φ (Q.CV k r Y f g)
def CVRho : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (p : B.SS k r),
    D.inSS p → B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ g ∈ B.GV k r, Q.CV k r Y (B.rho D p f) g = B.rho D p (Q.CV k r Y f) g
def CVRhoOfParts : Prop := CVLeft → CVRight → CVPost → CVRho
def CVWordSum : Prop :=
  ∀ (k r : ℕ) (Y : ℂ), ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        Q.CV k r Y f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum
def CVUnderInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Y : ℂ),
    2 * r + k + 1 ≤ m → TransportedAlt k r A m → B.InCC A m F →
    ∀ g ∈ Om k r D.z D.z', Q.CV k r Y (B.JF D F) g = ∫ p, xiP D p • Q.CV k r Y (B.rho D p F) g ∂D.μSS
def CVUnderIntOfParts : Prop := JWords → CVWordSum → RwRho → CVUnderInt
def GqDom : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ q ∈ QDom k r D.z D.z', B.gq D q ∈ Om k r D.z D.z'
def GqOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ᵐ q ∂(volume.restrict (B.Qset D)), B.gq D q ∈ Om k r D.z D.z'
def GqOmOfDom : Prop := GqDom → GqOm
def BesselCommutesOfParts : Prop :=
  JWords → CVRho → CVUnderInt → GqOm → B2.ConjInvAll → BesselNEquiv → BesselUEquiv → Q.BesselCommutes
def JTheta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Θ : B.DiffOp k r Wp Wq),
    B.opOrder Θ ≤ m → TransportedAlt k r A m → B.InCC A m F → B.Commutes D (Om k r D.z D.z') Θ →
    ∀ g ∈ Om k r D.z D.z', B.opApply Θ (B.JF D F) g = B.JF D (B.opApply Θ F) g
def JThetaOfParts : Prop := JWords → RwRho → JTheta
def RadialPartIntertwines : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Θ : B.DiffOp k r Wp Wq),
    B.opOrder Θ ≤ m → TransportedAlt k r A m → B.InCC A m F → B.Commutes D (Om k r D.z D.z') Θ →
    ∀ᵐ q ∂(volume.restrict (B.Qset D)), B.JF D (B.opApply Θ F) (B.gq D q) = B.opApply Θ (B.JF D F) (B.gq D q)
def RadialPartIntertwinesFromComponents : Prop := JTheta → GqOm → RadialPartIntertwines
def PsiOnto : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ g ∈ Om k r D.z D.z',
      ∃ p, D.inSS p ∧ ∃ q ∈ QDom k r D.z D.z', g = B.sgs p (B.gq D q)
def PsiQUnique : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p₁ p₂ : B.SS k r) (q₁ q₂ : (Fin r → ℂ) × ℂ),
    D.inSS p₁ → D.inSS p₂ → q₁ ∈ QDom k r D.z D.z' → q₂ ∈ QDom k r D.z D.z' →
    B.sgs p₁ (B.gq D q₁) = B.sgs p₂ (B.gq D q₂) → q₁ = q₂
def EquivDet : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)),
    IsEqv D (Om k r D.z D.z') f → IsEqv D (Om k r D.z D.z') f' →
    (∀ q ∈ QDom k r D.z D.z', f (B.gq D q) = f' (B.gq D q)) → ∀ g ∈ Om k r D.z D.z', f g = f' g
def EquivDetOfOnto : Prop := PsiOnto → EquivDet
def ThetaEquiv : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq)
    (f : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.Commutes D (Om k r D.z D.z') Θ → Q.CkLev k r 0 (B.opOrder Θ) (Q.OmPlus k r D.z D.z') f →
    IsEqv D (Om k r D.z D.z') f → IsEqv D (Om k r D.z D.z') (B.opApply Θ f)
def RadAdj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)) (K : Set ((Fin r → ℂ) × ℂ)),
    B.IntFormula D → B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ →
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') f → Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') f' →
    IsEqv D (Om k r D.z D.z') f → IsEqv D (Om k r D.z D.z') f' →
    IsCompact K → K ⊆ QDom k r D.z D.z' →
    (∀ q ∈ QDom k r D.z D.z', q ∉ K → f (B.gq D q) = 0 ∧ f' (B.gq D q) = 0) →
    betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec (fun g => B.hsVec (B.opApply Θ f g)) (fun g => B.hsVec (f' g)) =
      betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec (fun g => B.hsVec (f g)) (fun g => B.hsVec (B.opAdj Θ f' g))
def JqSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ContDiffOn ℝ (m : WithTop ℕ∞) (fun q => B.JF D F (B.gq D q)) (QDom k r D.z D.z')
def JqSmoothOfParts : Prop := JWords → GqDom → JqSmooth
end Formalism.FourierDecayAlt.JF



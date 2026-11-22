-- Prove2me | Definitions.Def_Formalism_MoebiusJetDuality_Statement
-- name    : Formalism_MoebiusJetDuality_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:13.409468+00:00
-- url     : https://prove2.me/theorems/7a4dcce2-3132-4d1e-90de-3fd083ca762a
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MoebiusJetDuality/Statement.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MJ
open MvPolynomial
open scoped Kronecker
universe u v
def linSubst {σ : Type u} {R : Type v} [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (f : MvPolynomial σ R) : MvPolynomial σ R :=
  aeval (fun i => ∑ j, C (g i j) * X j) f
def IsIntegralJet {σ : Type u} {R : Type v} [CommRing R] (A : Subring R)
    (f : MvPolynomial σ R) : Prop :=
  ∀ α, coeff α f ∈ A
def IsIntegralMat {ι κ : Type u} {R : Type v} [CommRing R] (A : Subring R)
    (g : Matrix ι κ R) : Prop :=
  ∀ i j, g i j ∈ A
def mfac {σ : Type u} (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial
def evOp {σ : Type u} {R : Type v} [CommRing R] (P F : MvPolynomial σ R) : R :=
  ∑ α ∈ P.support, (mfac α : R) * coeff α P * coeff α F
def jetTrunc {σ : Type u} {R : Type v} [CommRing R] (N : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
  ∑ n ∈ Finset.range (N + 1), homogeneousComponent n f
def hcMat {R : Type v} [CommRing R] {p q : ℕ} (A : Matrix (Fin p) (Fin p) R)
    (D : Matrix (Fin q) (Fin q) R) : Matrix (Fin p × Fin q) (Fin p × Fin q) R :=
  A ⊗ₖ D.transpose
def actK {R : Type v} [CommRing R] {p q r : ℕ}
    (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (k : GL (Fin p) R × GL (Fin q) R) (F : Fin r → MvPolynomial (Fin p × Fin q) R) :
    Fin r → MvPolynomial (Fin p × Fin q) R :=
  fun i => ∑ j, C ((ρ k : Matrix (Fin r) (Fin r) R) i j) *
    linSubst (hcMat ((k.1⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R)
      ((k.2 : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) (F j)
def LinSubstOne : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [DecidableEq σ] [CommRing R] (f : MvPolynomial σ R),
    linSubst (1 : Matrix σ σ R) f = f
def LinSubstMul : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g h : Matrix σ σ R)
    (f : MvPolynomial σ R),
    linSubst (g * h) f = linSubst h (linSubst g f)
def LinSubstHomog : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (f : MvPolynomial σ R) (n : ℕ),
    homogeneousComponent n (linSubst g f) = linSubst g (homogeneousComponent n f)
def JetTruncSubst : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (f : MvPolynomial σ R) (N : ℕ),
    jetTrunc N (linSubst g f) = linSubst g (jetTrunc N f)
def ScaleHomog : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [DecidableEq σ] [CommRing R] (c : R)
    (f : MvPolynomial σ R) (n : ℕ),
    homogeneousComponent n (linSubst (c • (1 : Matrix σ σ R)) f) =
      c ^ n • homogeneousComponent n f
def IntSubst : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (A : Subring R) (g : Matrix σ σ R)
    (f : MvPolynomial σ R),
    IsIntegralMat A g → IsIntegralJet A f → IsIntegralJet A (linSubst g f)
def IntSubstIff : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [DecidableEq σ] [CommRing R] (A : Subring R)
    (g h : Matrix σ σ R) (f : MvPolynomial σ R),
    IsIntegralMat A g → IsIntegralMat A h → g * h = 1 →
      (IsIntegralJet A (linSubst g f) ↔ IsIntegralJet A f)
def IntMul : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (f f' : MvPolynomial σ R),
    IsIntegralJet A f → IsIntegralJet A f' → IsIntegralJet A (f * f')
def DerivCoeff : Prop :=
  ∀ (σ : Type u) (R : Type v) [DecidableEq σ] [CommRing R] (l : List σ) (f : MvPolynomial σ R),
    constantCoeff (l.foldr (fun i g => pderiv i g) f) =
      (mfac (Multiset.toFinsupp (l : Multiset σ)) : R) * coeff (Multiset.toFinsupp (l : Multiset σ)) f
def EvMonomial : Prop :=
  ∀ (σ : Type u) (R : Type v) [DecidableEq σ] [CommRing R] (l : List σ) (F : MvPolynomial σ R),
    evOp (monomial (Multiset.toFinsupp (l : Multiset σ)) 1) F =
      constantCoeff (l.foldr (fun i g => pderiv i g) F)
def EvIntegral : Prop :=
  ∀ (σ : Type u) (R : Type v) [CommRing R] (A : Subring R) (P F : MvPolynomial σ R),
    IsIntegralJet A P → IsIntegralJet A F → evOp P F ∈ A
def EvSubst : Prop :=
  ∀ (σ : Type u) (R : Type v) [Fintype σ] [CommRing R] (g : Matrix σ σ R)
    (P F : MvPolynomial σ R),
    evOp P (linSubst g F) = evOp (linSubst g.transpose P) F
def EvFock : Prop :=
  ∀ (σ : Type u) (P F : MvPolynomial σ ℂ),
    evOp P F = Formalism.REAL.fockF F (map (starRingEnd ℂ) P)
def HcMatApply : Prop :=
  ∀ (R : Type v) [CommRing R] (p q : ℕ) (A : Matrix (Fin p) (Fin p) R)
    (D : Matrix (Fin q) (Fin q) R) (z : Matrix (Fin p) (Fin q) R) (a : Fin p) (b : Fin q),
    (hcMat A D).mulVec (fun x => z x.1 x.2) (a, b) = (A * z * D) a b
def HcMatMul : Prop :=
  ∀ (R : Type v) [CommRing R] (p q : ℕ) (A A' : Matrix (Fin p) (Fin p) R)
    (D D' : Matrix (Fin q) (Fin q) R),
    hcMat (A * A') (D' * D) = hcMat A D * hcMat A' D'
def HcMatInt : Prop :=
  ∀ (R : Type v) [CommRing R] (A0 : Subring R) (p q : ℕ) (A : Matrix (Fin p) (Fin p) R)
    (D : Matrix (Fin q) (Fin q) R),
    IsIntegralMat A0 A → IsIntegralMat A0 D → IsIntegralMat A0 (hcMat A D)
def ActKMul : Prop :=
  ∀ (R : Type v) [CommRing R] (p q r : ℕ) (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (k k' : GL (Fin p) R × GL (Fin q) R) (F : Fin r → MvPolynomial (Fin p × Fin q) R),
    actK ρ (k * k') F = actK ρ k (actK ρ k' F)
def ActKOne : Prop :=
  ∀ (R : Type v) [CommRing R] (p q r : ℕ) (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (F : Fin r → MvPolynomial (Fin p × Fin q) R),
    actK ρ 1 F = F
def ActKInt : Prop :=
  ∀ (R : Type v) [CommRing R] (A0 : Subring R) (p q r : ℕ)
    (ρ : (GL (Fin p) R × GL (Fin q) R) →* GL (Fin r) R)
    (k : GL (Fin p) R × GL (Fin q) R) (F : Fin r → MvPolynomial (Fin p × Fin q) R),
    IsIntegralMat A0 ((ρ k : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) →
    IsIntegralMat A0 ((k.1⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) →
    IsIntegralMat A0 ((k.2 : GL (Fin q) R) : Matrix (Fin q) (Fin q) R) →
    (∀ j, IsIntegralJet A0 (F j)) → ∀ i, IsIntegralJet A0 (actK ρ k F i)
def HomogRank : Prop :=
  ∀ (σ : Type u) (K : Type v) [Fintype σ] [Field K] (n : ℕ),
    Module.finrank K (homogeneousSubmodule σ K n) = Nat.choose (n + Fintype.card σ - 1) n
def JetRank : Prop :=
  ∀ (σ : Type u) (K : Type v) [Fintype σ] [Field K] (N : ℕ),
    Module.finrank K (restrictTotalDegree σ K N) = Nat.choose (N + Fintype.card σ) N
def JetInjective : Prop :=
  ∀ (E : Type u) (F : Type v) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F) (U : Set E) (x : E),
    IsOpen U → IsPreconnected U → x ∈ U → AnalyticOnNhd ℂ f U →
    (∀ n, iteratedFDeriv ℂ n f x = 0) → Set.EqOn f 0 U
end Formalism.MJ



-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- name    : Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:19.097944+00:00
-- url     : https://prove2.me/theorems/ebbc3c98-806e-4994-ae46-531b10cd9fdd
-- title:
--   Coef Mod Lemmas
-- statement:
--   Definitions and structural lemmas for Coef Mod Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.BasicNotions
def FockSHerm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (σ : Type) (f g : MvPolynomial σ K), fockS g f = star (fockS f g)
def FockSQ : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (σ : Type) (f g : MvPolynomial σ ℚ),
    fockS (map (algebraMap ℚ K) f) (map (algebraMap ℚ K) g) = algebraMap ℚ K (Formalism.GradedWeylDivisibility.fockQ f g)
def FockSAdj : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (U : ι → Matrix (Fin n) (Fin n) K)
    (F F' : Pol K ι n),
    fockS (Formalism.GradedWeylDivisibility.blockAct K U F) F' = fockS F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (U τ)ᴴ) F')
def FockSTen : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ)
    (f g : ι → MvPolynomial (Fin n × Fin n) K), fockS (ten f) (ten g) = ∏ τ, fockS (f τ) (g τ)
def ExtNormPos : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    ∃ q : ℚ, 0 < q ∧ extNorm K lam = algebraMap ℚ K q
def ActTen : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) K)
    (f : ι → MvPolynomial (Fin n × Fin n) K),
    actP lam g (ten f) = ten fun τ => sqAct K n (lam τ) (g τ) (f τ)
def ActRat : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (K0 : Subfield K)
    (g : ι → GL (Fin n) K), (∀ τ a b, (g τ : Matrix (Fin n) (Fin n) K) a b ∈ K0) →
    ∀ i j, (bVV K lam).repr (rhoK lam g (bVV K lam j)) i ∈ K0
def PairTransport : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (g g' : ι → GL (Fin n) K) (F F' : Pol K ι n),
    pairP lam G (actP lam g F) (actP lam g' F') =
      pairP lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g' τ : Matrix (Fin n) (Fin n) K)) F F'
def PairInv : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (g : ι → GL (Fin n) K),
    (∀ τ, (g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g τ : Matrix (Fin n) (Fin n) K) = G τ) →
    ∀ x y : VV K lam, pairK lam G (rhoK lam g x) (rhoK lam g y) = pairK lam G x y
def PairExtremal : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (B : ι → GL (Fin n) K),
    (∀ τ, (B τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (B τ : Matrix (Fin n) (Fin n) K) = 1) →
    pairP lam G (actP lam B (ten fun τ => extremal K n (lam τ))) (actP lam B (ten fun τ => extremal K n (lam τ))) = 1
def PairSymm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) → (pairK lam G).IsSymm
def PairNondeg : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsUnit (G τ).det) → (pairK lam G).Nondegenerate
def PairRat : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (K0 : Subfield K)
    (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ a b, G τ a b ∈ K0) →
    ∀ i j, pairK lam G (bVV K lam i) (bVV K lam j) ∈ K0
def PairPos : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (φ : K →+* ℂ), (∀ τ, ((G τ).map φ).PosDef) →
    (Matrix.of fun i j : VVIdx lam => φ (pairK lam G (bVV K lam i) (bVV K lam j))).PosDef
def BasisAtEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsLattice K M →
    ∀ w : HeightOneSpectrum (𝓞 K), ∃ B : GL (Fin n) K, IsBasisAt w M B
def NabIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K),
    (∀ τ, IsBasisAt w (M τ) (B τ)) → (∀ τ, IsBasisAt w (M τ) (B' τ)) → ∀ F : Pol K ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) ↔
        actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam))
def DelIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K),
    (∀ τ, IsBasisAt w (M τ) (B τ)) → (∀ τ, IsBasisAt w (M τ) (B' τ)) → ∀ F : Pol K ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) ↔
        actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam))
def NabDelFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K),
    nabP lam (fun τ => colLat (B τ)) = (nabStd K lam).map ((actP lam B).restrictScalars (𝓞 K)) ∧
    delP lam (fun τ => colLat (B τ)) = (delStd K lam).map ((actP lam B).restrictScalars (𝓞 K))
def NabDelLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam)).map ((actP lam B).restrictScalars (𝓞 K)) ∧
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delP lam M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam)).map ((actP lam B).restrictScalars (𝓞 K))
def NabRoundFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (m : ℕ) (lam : ι → DomWeight (m + 1))
    (B : ι → GL (Fin (m + 1)) K),
    nabP lam (fun τ => dualFr (colLat (B τ))) =
      Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K fun τ =>
        Formalism.GradedWeylDivisibility.nablaLTw (𝓞 K) K m (lam τ).w (B τ : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
def NabLeVV : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ F ∈ nabP lam M, F ∈ VV K lam
def NabDelLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    Submodule.IsLattice K (nabK lam M) ∧ Submodule.IsLattice K (delK lam M)
def DelLeNab : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), delK lam M ≤ nabK lam M
def NabDelEquiv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K),
    nabP lam (fun τ => gLat (g τ) (M τ)) = (nabP lam M).map ((actP lam g).restrictScalars (𝓞 K)) ∧
    delP lam (fun τ => gLat (g τ) (M τ)) = (delP lam M).map ((actP lam g).restrictScalars (𝓞 K))
def NabDelStable : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K), (∀ τ, gLat (g τ) (M τ) = M τ) →
    (∀ x ∈ nabK lam M, rhoK lam g x ∈ nabK lam M) ∧ (∀ x ∈ delK lam M, rhoK lam g x ∈ delK lam M)
def NabDelDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)),
    (∀ τ, (G τ)ᴴ = G τ) → (∀ τ, IsUnit (G τ).det) → (∀ τ, Submodule.IsLattice K (M τ)) →
    Formalism.HermitianLatticesTheory.dual (pairK lam G) (nabK lam M) = delK lam (fun τ => hdualFr (G τ) (M τ)) ∧
    Formalism.HermitianLatticesTheory.dual (pairK lam G) (delK lam M) = nabK lam (fun τ => hdualFr (G τ) (M τ))
def DualFrHdual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)), Gᴴ = G → IsUnit G.det → Submodule.IsLattice K M →
    hdualFr (G⁻¹)ᵀ (dualFr M) = dualFr (hdualFr G M)
def DualFrLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)), IsUnit G.det → Submodule.IsLattice K M →
    Submodule.IsLattice K (dualFr M) ∧ Submodule.IsLattice K (hdualFr G M)
def TauLatLattice : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → Submodule.IsLattice K (tauLat emb τ L)
def TauLatG : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι)
    (L : Submodule (𝓞 E) (Fin n → E)) (γ : GL (Fin n) E),
    tauLat emb τ (L.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E))) =
      gLat (embGL emb γ τ) (tauLat emb τ L)
def TauLatDual : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ (J : Matrix (Fin n) (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)), IsUnit J.det → Submodule.IsLattice E L →
      (∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE J x y ∈ (algebraMap (𝓞 E) E).range) →
      hdualFr (gramK emb J τ) (tauLat emb τ L) = tauLat emb τ L'
def GramHerm : Prop :=
  ∀ (E K : Type) [Field E] [Field K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ J : Matrix (Fin n) (Fin n) E, Formalism.UG.IsHerm cE J →
      (gramK emb J τ)ᴴ = gramK emb J τ ∧ (gramKd emb J τ)ᴴ = gramKd emb J τ
def UJUnitary : Prop :=
  ∀ (E K : Type) [Field E] [Field K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), γ ∈ Formalism.UG.UJ cE J →
      ((embGL emb γ τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ * gramK emb J τ *
        ((embGL emb γ τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = gramK emb J τ ∧
      (IsUnit J.det →
        ((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ * gramKd emb J τ *
          ((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = gramKd emb J τ)
def RoundGL : Prop :=
  ∀ (E K : Type) [Field E] [Field K] (ι : Type) (n : ℕ) (emb : ι → E →+* K) (cE : E →+* E)
    (Jg γ : GL (Fin n) E), γ ∈ Formalism.UG.UJ cE (Jg : Matrix (Fin n) (Fin n) E) →
    invTrK (embGL emb γ) =
      invTrK (embGL emb Jg⁻¹) * embGL (fun τ => (emb τ).comp cE) γ * (invTrK (embGL emb Jg⁻¹))⁻¹
def RoundLat : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, cE (cE x) = x) →
    ∀ (Jg : GL (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L →
      Formalism.UG.IsHerm cE (Jg : Matrix (Fin n) (Fin n) E) →
      (∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE (Jg : Matrix (Fin n) (Fin n) E) x y ∈ (algebraMap (𝓞 E) E).range) →
      dualFr (tauLat emb τ L) = gLat (invTrK (embGL emb Jg⁻¹) τ) (tauLat (fun τ => (emb τ).comp cE) τ L')
def RoundGram : Prop :=
  ∀ (E K : Type) [Field E] [Field K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ Jg : GL (Fin n) E, Formalism.UG.IsHerm cE (Jg : Matrix (Fin n) (Fin n) E) →
      ((invTrK (embGL emb Jg⁻¹) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ *
          gramKd emb (Jg : Matrix (Fin n) (Fin n) E) τ *
          ((invTrK (embGL emb Jg⁻¹) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        gramK (fun τ => (emb τ).comp cE) (Jg : Matrix (Fin n) (Fin n) E) τ
section Adj
variable {K : Type} [Field K] [StarRing K]
variable {ι : Type} [Fintype ι] {n : ℕ}
end Adj
section Equiv
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
end Equiv
section Checks
variable {K : Type} [Field K]
def lamVec : DomWeight 2 where
  w := ![1, 0]
  anti := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
def vecP (v : Fin 2 → K) : Pol K Unit 2 := ∑ a : Fin 2, C (v a) * X ((), (a, 0))
variable [StarRing K]
def lamChar (e : ℤ) : DomWeight 1 where
  w := fun _ => e
  anti := fun _ _ _ => le_rfl
end Checks
section RankOne
variable {K : Type} [Field K] [NumberField K]
end RankOne
end Formalism.L2.DIV



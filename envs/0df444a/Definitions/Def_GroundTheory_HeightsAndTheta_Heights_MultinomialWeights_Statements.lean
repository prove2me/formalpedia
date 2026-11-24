-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:58.490731+00:00
-- url     : https://prove2.me/theorems/ae61e7f4-1db4-4bd3-9a1a-3a3ce4ff0875
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_add_970f926c8cdd

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
namespace GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
structure IndexData where
  f : ℕ
  N : ℕ
  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N
namespace IndexData
variable (d : IndexData)
def D : ℕ := RestTerms.topDegree d.f d.N
def n0 : ℕ := d.f * d.N
def TextRange : Prop := 2 < d.f * (d.N - 1)
def jIdx : Fin d.N := ⟨d.j - 1, by have := d.j_lt_N; omega⟩
def jSucc : Fin d.N := ⟨d.j, d.j_lt_N⟩
end IndexData
variable (d : IndexData)
abbrev Idx := Fin d.f × Fin d.N
abbrev Weight := Idx d → ℝ
abbrev LamPoly := MvPolynomial (Idx d) ℝ
abbrev XPoly := RestTerms.RootRing d.f d.N
def lamDotX (u : Idx d → ℚ) : XPoly d := ∑ p : Idx d, C (u p) * X p
def lineClass (u : Idx d → ℚ) : XPoly d := -lamDotX d u
def permWeight {R : Type*} (w : Fin d.f → Equiv.Perm (Fin d.N)) (u : Idx d → R) : Idx d → R :=
  fun p => u (p.1, w p.1 p.2)
abbrev weylL : Subgroup (Equiv.Perm (Idx d)) := antisymWeyl (Fin d.f) d.N d.j
def permAct (σ : Equiv.Perm (Idx d)) (lam : Weight d) : Weight d := fun p => lam (σ.symm p)
def gap (τ : Fin d.f) (lam : Weight d) : ℝ := lam (τ, d.jIdx) - lam (τ, d.jSucc)
def IsCompactStep (a b : Fin d.N) : Prop := b.val = a.val + 1 ∧ b.val ≠ d.j
def IsDominant (lam : Weight d) : Prop :=
  ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 → 0 ≤ lam (τ, a) - lam (τ, b)
def IsRegular (lam : Weight d) : Prop :=
  ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 → 0 < lam (τ, a) - lam (τ, b)
def varpi (τ : Fin d.f) : Weight d := fun p => if p.1 = τ ∧ p.2.val < d.j then 1 else 0
def lowerPowerSum (k : ℕ) (τ : Fin d.f) : XPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), X (τ, i) ^ k
def upperPowerSum (k : ℕ) (τ : Fin d.f) : XPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => d.j ≤ i.val), X (τ, i) ^ k
def flagIntegralLin (f N : ℕ) : RestTerms.RootRing f N →ₗ[ℚ] ℚ where
  toFun := RestTerms.flagIntegral f N
  map_add' := RestTerms.Flag.flagIntegral_add f N
  map_smul' c Φ := by
    rw [← C_mul', RestTerms.Flag.flagIntegral_C_mul, RingHom.id_apply, smul_eq_mul]
def flagNormalisation (f N : ℕ) : ℚ :=
  (-1) ^ RestTerms.topDegree f N / (∏ i : Fin N, ((i : ℕ).factorial : ℚ)) ^ f
def intFl : XPoly d →ₗ[ℚ] ℚ := flagNormalisation d.f d.N • flagIntegralLin d.f d.N
def degAt (u : Idx d → ℚ) : ℚ := intFl d (lineClass d u ^ d.D)
def outerDot (σ R : Type*) [CommRing R] [Fintype σ] : MvPolynomial σ (MvPolynomial σ R) :=
  ∑ v : σ, X v * C (X v)
def polarPoly {σ R : Type*} [CommRing R] [Fintype σ] (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) :
    MvPolynomial σ R :=
  ∑ m ∈ ((-outerDot σ R) ^ n).support, monomial m (Φ (coeff m ((-outerDot σ R) ^ n)))
def degPoly : MvPolynomial (Idx d) ℚ := polarPoly (intFl d) d.D
def shiftFl (τ : Fin d.f) (F : XPoly d) : ℚ :=
  intFl d (∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) F)
def totalFl (τ : Fin d.f) (F : XPoly d) : ℚ :=
  intFl d (∑ i : Fin d.N, pderiv (τ, i) F)
abbrev vSpace : Submodule ℝ (LamPoly d) := antisymSpace (Fin d.f) d.N d.j
def lowerSum (τ : Fin d.f) : LamPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), X (τ, i)
def upperSum (τ : Fin d.f) : LamPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => d.j ≤ i.val), X (τ, i)
def invForms : Submodule ℝ (LamPoly d) :=
  Submodule.span ℝ (Set.range (lowerSum d) ∪ Set.range (upperSum d))
def uSpace : Submodule ℝ (LamPoly d) :=
  (invForms d).map (LinearMap.mulLeft ℝ (antisymDelta (Fin d.f) d.N))
abbrev rootHyperplane (τ : Fin d.f) (a b : Fin d.N) : Set (Weight d) :=
  diagHyperplane (Fin d.f) d.N τ a b
def IsCross (a b : Fin d.N) : Prop := a.val < d.j ∧ d.j ≤ b.val
def HasRelInteriorIn (S H : Set (Weight d)) : Prop :=
  ∃ O : Set (Weight d), IsOpen O ∧ (O ∩ H).Nonempty ∧ O ∩ H ⊆ S
def KSet (τ0 : Fin d.f) (c0 : ℝ) : Set (Weight d) :=
  {lam | ‖lam‖ ≤ 1 / 2 ∧ gap d τ0 lam = 0 ∧ (∀ τ, τ ≠ τ0 → c0 ≤ gap d τ lam) ∧
    ∀ (τ : Fin d.f) (a b : Fin d.N), IsCompactStep d a b → c0 ≤ lam (τ, a) - lam (τ, b)}
def quarterInverseN : ℝ := 1 / (4 * (d.N : ℝ))
def supOn (S : Set (Weight d)) (P : LamPoly d) : ℝ := sSup ((fun x => |eval x P|) '' S)
def IsWallFamily (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)) : Prop :=
  ∀ (τ : Fin d.f) (a b : Fin d.N), IsCross d a b →
    IsCompact (Om τ a b) ∧ Om τ a b ⊆ rootHyperplane d τ a b ∧
      HasRelInteriorIn d (Om τ a b) (rootHyperplane d τ a b)
def wallUnion (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)) : Set (Weight d) :=
  {x | ∃ (τ : Fin d.f) (a b : Fin d.N), IsCross d a b ∧ x ∈ Om τ a b}
def DegVanishesOnWall.Statement : Prop :=
  ∀ (d : IndexData) (u : Idx d → ℚ) (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 →
    u (τ, a) = u (τ, b) → degAt d u = 0
def DegAntisym.Statement : Prop :=
  ∀ (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N)) (u : Idx d → ℚ),
    degAt d (permWeight d w u) = RestTerms.blockSign d.f d.N w * degAt d u
def DegPolyEval.Statement : Prop :=
  ∀ (d : IndexData) (u : Idx d → ℚ), eval u (degPoly d) = degAt d u
def DelDividesDeg.Statement : Prop :=
  ∀ d : IndexData, RestTerms.blockVandermonde d.f d.N ∣ degPoly d
def DegEqConstDel.Statement : Prop :=
  ∀ d : IndexData, ∃ c : ℚ, degPoly d = C c * RestTerms.blockVandermonde d.f d.N
def CFlPos.Statement : Prop :=
  ∀ d : IndexData, ∃ c : ℚ, 0 < c ∧ degPoly d = C c * RestTerms.blockVandermonde d.f d.N
def ShFormula.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d),
    F.IsHomogeneous (d.D + 1) →
    (∀ k ∈ Icc 1 d.N, ∀ τ' : Fin d.f, (Q k τ').IsHomogeneous (d.D + 1 - k)) →
    RestTerms.IsPowerSumDecomposition d.f d.N F Q →
    shiftFl d τ F = ∑ k ∈ Icc 1 d.N, (k : ℚ) * intFl d (lowerPowerSum d (k - 1) τ * Q k τ)
def TotFormula.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d),
    F.IsHomogeneous (d.D + 1) →
    (∀ k ∈ Icc 1 d.N, ∀ τ' : Fin d.f, (Q k τ').IsHomogeneous (d.D + 1 - k)) →
    RestTerms.IsPowerSumDecomposition d.f d.N F Q →
    totalFl d τ F = (d.N : ℚ) * intFl d (Q 1 τ)
def ShOfPower.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (u : Idx d → ℚ),
    shiftFl d τ (lineClass d u ^ (d.D + 1)) =
      -((d.D + 1 : ℕ) : ℚ) * degAt d u * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i)
def TotOfPower.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (u : Idx d → ℚ),
    totalFl d τ (lineClass d u ^ (d.D + 1)) = -((d.D + 1 : ℕ) : ℚ) * degAt d u * ∑ i : Fin d.N, u (τ, i)
def PolarisationCoeff.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Φ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (n : ℕ) (m : σ →₀ ℕ),
    (m.sum fun _ e => e) = n →
    Φ (monomial m 1) =
      (-1) ^ n * ((m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ)) * coeff m (polarPoly Φ n)
def PolarisationBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (n : ℕ),
    (∀ Φ Ψ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ, polarPoly Φ n = polarPoly Ψ n →
      ∀ F : MvPolynomial σ ℝ, F.IsHomogeneous n → Φ F = Ψ F) ∧
    ∀ (Φ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (m : σ →₀ ℕ) (M : ℝ), (m.sum fun _ e => e) = n →
      (∀ m' : σ →₀ ℕ, |coeff m' (polarPoly Φ n)| ≤ M) → |Φ (monomial m 1)| ≤ M
def ULiesInV.Statement : Prop :=
  ∀ d : IndexData, uSpace d ≤ vSpace d
def PolyVanishesOnHyperplane.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d) (τ : Fin d.f) (a b : Fin d.N), a ≠ b →
    (∃ O : Set (Weight d), IsOpen O ∧ (O ∩ rootHyperplane d τ a b).Nonempty ∧
      ∀ x ∈ O ∩ rootHyperplane d τ a b, eval x P = 0) →
    ∀ x ∈ rootHyperplane d τ a b, eval x P = 0
def DivisibleByRootForm.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d) (τ : Fin d.f) (a b : Fin d.N), a ≠ b →
    (∀ x ∈ rootHyperplane d τ a b, eval x P = 0) → (X (τ, a) - X (τ, b) : LamPoly d) ∣ P
def CompactRootVanishes.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d), P ∈ vSpace d →
    ∀ (τ : Fin d.f) (a b : Fin d.N), a < b → (a.val < d.j ↔ b.val < d.j) →
      ∀ x ∈ rootHyperplane d τ a b, eval x P = 0
def DelDividesV.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d),
    (∀ (τ : Fin d.f) (a b : Fin d.N), a < b → (X (τ, a) - X (τ, b) : LamPoly d) ∣ P) →
    antisymDelta (Fin d.f) d.N ∣ P
def QuotientLinear.Statement : Prop :=
  ∀ (d : IndexData) (P l : LamPoly d), P ∈ vSpace d → P = antisymDelta (Fin d.f) d.N * l →
    l ∈ antisymInv (Fin d.f) d.N d.j
def InvariantLinearForm.Statement : Prop :=
  ∀ d : IndexData, antisymInv (Fin d.f) d.N d.j = invForms d
def VInUOfVanish.Statement : Prop :=
  ∀ (d : IndexData) (P : LamPoly d), P ∈ vSpace d →
    (∀ (τ : Fin d.f) (a b : Fin d.N), IsCross d a b →
      ∃ O : Set (Weight d), IsOpen O ∧ (O ∩ rootHyperplane d τ a b).Nonempty ∧
        ∀ x ∈ O ∩ rootHyperplane d τ a b, eval x P = 0) →
    P ∈ uSpace d
def SeminormOnV.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∃ s : Seminorm ℝ (vSpace d), ∀ P : vSpace d, s P = supOn d (wallUnion d Om) (P : LamPoly d)
def SeminormKernel.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∀ P ∈ vSpace d, (supOn d (wallUnion d Om) P = 0 ↔ P ∈ uSpace d)
def NormEquivalence.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∀ V' : Submodule ℝ (LamPoly d), V' ≤ vSpace d → Disjoint (uSpace d) V' →
      ∃ C : ℝ, ∀ P ∈ V', ∀ m, |coeff m P| ≤ C * supOn d (wallUnion d Om) P
def DecompositionBound.Statement : Prop :=
  ∀ (d : IndexData) (Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d)), IsWallFamily d Om →
    ∀ V' : Submodule ℝ (LamPoly d), V' ≤ vSpace d → Disjoint (uSpace d) V' →
      uSpace d ⊔ V' = vSpace d →
      ∃ C : ℝ, ∀ P ∈ vSpace d, ∃ l ∈ invForms d, ∃ P' ∈ V',
        P = antisymDelta (Fin d.f) d.N * l + P' ∧
          ∀ m, |coeff m P'| ≤ C * supOn d (wallUnion d Om) P
def KNonemptyInterior.Statement : Prop :=
  ∀ (d : IndexData) (τ0 : Fin d.f),
    HasRelInteriorIn d (KSet d τ0 (quarterInverseN d)) (rootHyperplane d τ0 d.jIdx d.jSucc)
def KRationalDense.Statement : Prop :=
  ∀ (d : IndexData) (τ0 : Fin d.f) (c0 : ℚ), 0 < c0 → c0 ≤ 1 →
    KSet d τ0 c0 ⊆ closure (KSet d τ0 c0 ∩ {lam | ∀ p, ∃ q : ℚ, lam p = q})
def KTransport.Statement : Prop :=
  ∀ (d : IndexData) (τ : Fin d.f) (a b : Fin d.N), IsCross d a b →
    ∃ σ ∈ weylL d, σ (τ, d.jIdx) = (τ, a) ∧ σ (τ, d.jSucc) = (τ, b) ∧
      IsCompact (permAct d σ '' KSet d τ (quarterInverseN d)) ∧
      permAct d σ '' KSet d τ (quarterInverseN d) ⊆ rootHyperplane d τ a b ∧
      HasRelInteriorIn d (permAct d σ '' KSet d τ (quarterInverseN d)) (rootHyperplane d τ a b) ∧
      ∀ R ∈ vSpace d, ∀ lam : Weight d, |eval (permAct d σ lam) R| = |eval lam R|
abbrev d1 : IndexData := ⟨1, 2, 1, le_rfl, le_rfl, by norm_num⟩
abbrev d2 : IndexData := ⟨1, 3, 2, by norm_num, by norm_num, by norm_num⟩
def sampleQ : ℕ → Fin d1.f → XPoly d1 := fun k τ => if k = 1 then X (τ, ⟨0, by norm_num⟩) else 0
def sampleF : XPoly d1 := ∑ k ∈ Icc 1 d1.N, ∑ τ : Fin d1.f, RestTerms.blockPowerSum d1.f d1.N k τ * sampleQ k τ
def unitWallFamily : Fin d.f → Fin d.N → Fin d.N → Set (Weight d) :=
  fun τ a b => Metric.closedBall 0 1 ∩ rootHyperplane d τ a b
end GroundTheory.Heights₂.Heights.TheoremB



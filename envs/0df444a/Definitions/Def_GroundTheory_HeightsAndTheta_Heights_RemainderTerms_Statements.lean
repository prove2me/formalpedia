-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:03.476161+00:00
-- url     : https://prove2.me/theorems/2443f290-21a4-4705-8234-fc7debf1cfa7
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Statements.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
open MvPolynomial Finset
noncomputable section
abbrev RootRing (f N : ℕ) := MvPolynomial (Fin f × Fin N) ℚ
def blockPowerSum (f N k : ℕ) (τ : Fin f) : RootRing f N := ∑ i : Fin N, X (τ, i) ^ k
def vandermondeOf {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) : R :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (v i - v j)
def blockVandermonde (f N : ℕ) : RootRing f N :=
  ∏ τ : Fin f, vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N))
def blockPermute (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : RootRing f N →ₐ[ℚ] RootRing f N :=
  rename (fun p => (p.1, w p.1 p.2))
def blockSign (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : ℚ :=
  ∏ τ : Fin f, (((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℚ)
def antisymmetrize (f N : ℕ) (H : RootRing f N) : RootRing f N :=
  ∑ w : Fin f → Equiv.Perm (Fin N), blockSign f N w • blockPermute f N w H
def dividedDifference (f N : ℕ) (H : RootRing f N) : FractionRing (RootRing f N) :=
  algebraMap (RootRing f N) (FractionRing (RootRing f N)) (antisymmetrize f N H) /
    algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N)
def topDegree (f N : ℕ) : ℕ := f * (N * (N - 1) / 2)
def flagIntegral (f N : ℕ) (Φ : RootRing f N) : ℚ :=
  ∑ α ∈ (blockVandermonde f N).support,
    coeff α Φ * coeff α (blockVandermonde f N) * α.prod (fun _ e => (e.factorial : ℚ))
def restrictToBlock (f N : ℕ) (τ : Fin f) : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (fun p : Fin f × Fin N => if p.1 = τ then X p.2 else 0)
def powerSumHom (N : ℕ) : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (fun i : Fin N => psum (Fin N) ℚ (i.val + 1))
def IsPowerSumDecomposition (f N : ℕ) (F : RootRing f N) (Q : ℕ → Fin f → RootRing f N) : Prop :=
  F = ∑ k ∈ Finset.Icc 1 N, ∑ τ : Fin f, blockPowerSum f N k τ * Q k τ
def restTerm (f N : ℕ) (Q : ℕ → Fin f → RootRing f N) (k : ℕ) (τ : Fin f) (G : RootRing f N) : ℚ :=
  (k : ℚ) * flagIntegral f N (G * Q k τ)
def completeSymmetric (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℤ) : MvPolynomial σ ℚ :=
  if 0 ≤ d then hsymm σ ℚ d.toNat else 0
def schur (σ : Type*) [Fintype σ] [DecidableEq σ] {m : ℕ} (lam : Fin m → ℕ) : MvPolynomial σ ℚ :=
  Matrix.det (Matrix.of fun i j : Fin m =>
    completeSymmetric σ ((lam i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
def youngCells {m : ℕ} (lam : Fin m → ℕ) : Finset (Fin m × ℕ) :=
  (Finset.univ ×ˢ Finset.range (∑ i, lam i)).filter (fun c => c.2 < lam c.1)
def numStandardTable {m : ℕ} (lam : Fin m → ℕ) : ℕ :=
  Nat.card {T : youngCells lam ≃ Fin (youngCells lam).card //
    ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q}
def symmetricGroupCharacter {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) : ℚ :=
  coeff (Finsupp.equivFunOnFinite.symm fun i : Fin m => lam i + (m - 1 - (i : ℕ)))
    (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
      (rho.map fun q => psum (Fin m) ℚ q).prod)
def partitionsOf (m n : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.Nat.antidiagonalTuple m n).filter fun lam => ∀ i j : Fin m, i ≤ j → lam j ≤ lam i
inductive SmallBlock
  | last
  | first
  deriving DecidableEq
def SmallBlock.sign : SmallBlock → ℚ
  | .last => 1
  | .first => -1
def yIndex (f r a : ℕ) : SmallBlock → Fin f → Fin r → Fin f × Fin (r + a)
  | .last, τ, i => (τ, ⟨a + i.val, by have := i.isLt; omega⟩)
  | .first, τ, i => (τ, ⟨i.val, by have := i.isLt; omega⟩)
def zIndex (f r a : ℕ) : SmallBlock → Fin f → Fin a → Fin f × Fin (r + a)
  | .last, τ, i => (τ, ⟨i.val, by have := i.isLt; omega⟩)
  | .first, τ, i => (τ, ⟨r + i.val, by have := i.isLt; omega⟩)
def yRoot (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin r) : RootRing f (r + a) :=
  C c.sign * X (yIndex f r a c τ i)
def zRoot (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin a) : RootRing f (r + a) :=
  X (zIndex f r a c τ i)
def smallBlockMu (f r a : ℕ) (c : SmallBlock) : RootRing f (r + a) :=
  ∑ τ : Fin f, ∑ i : Fin r, yRoot f r a c τ i
def fibreClass (f r a : ℕ) (c : SmallBlock) : RootRing f (r + a) :=
  ∏ τ : Fin f, vandermondeOf (yRoot f r a c τ) * vandermondeOf (zRoot f r a c τ)
def restPolynomial (f r a : ℕ) (c : SmallBlock) : RootRing f (r + a) :=
  smallBlockMu f r a c ^ (f * (r * a) + 1) * fibreClass f r a c
def fibreDegree (f r a : ℕ) (c : SmallBlock) : ℚ :=
  flagIntegral f (r + a) (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c)
def smallPowerSum (f r a : ℕ) (c : SmallBlock) (k : ℕ) (τ : Fin f) : RootRing f (r + a) :=
  ∑ i : Fin r, yRoot f r a c τ i ^ k
def restX (r a : ℕ) : ℚ := 2 * (((r * a : ℕ) : ℚ) + ((r + a : ℕ) : ℚ))
def rectangle (r a : ℕ) : Fin r → ℕ := fun _ => a
def hookShape (r k l : ℕ) : Fin r → ℕ :=
  fun i => if (i : ℕ) = 0 then k - l else if (i : ℕ) ≤ l then 1 else 0
def FlagIntegralKillsPowerSums.Statement : Prop :=
  ∀ (f N k : ℕ) (τ : Fin f) (G : RootRing f N), 1 ≤ k → k ≤ N →
    flagIntegral f N (blockPowerSum f N k τ * G) = 0
def CoinvariantTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), H.IsHomogeneous (topDegree f N) →
    ∃ b : ℚ, H - C b * ∏ τ : Fin f, ∏ i : Fin N, X (τ, i) ^ (i : ℕ) ∈
      Ideal.span {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = blockPowerSum f N k τ}
def DividedDifferenceOfVandermonde.Statement : Prop :=
  ∀ f N : ℕ, dividedDifference f N (blockVandermonde f N) =
    algebraMap ℚ (FractionRing (RootRing f N)) ((N.factorial : ℚ) ^ f)
def IntegralIsDividedDifference.Statement : Prop :=
  ∀ f N : ℕ, ∃ c : ℚ, c ≠ 0 ∧ ∀ H : RootRing f N, H.IsHomogeneous (topDegree f N) →
    algebraMap ℚ (FractionRing (RootRing f N)) (flagIntegral f N H) =
      algebraMap ℚ (FractionRing (RootRing f N)) c * dividedDifference f N H
def LemmaA.Statement : Prop :=
  ∀ f N : ℕ, ∃ c : ℚ, c ≠ 0 ∧
    (∀ H : RootRing f N, H.IsHomogeneous (topDegree f N) →
      algebraMap ℚ (FractionRing (RootRing f N)) (flagIntegral f N H) =
        algebraMap ℚ (FractionRing (RootRing f N)) c * dividedDifference f N H) ∧
    ∀ (F : RootRing f N) (Q : ℕ → Fin f → RootRing f N), IsPowerSumDecomposition f N F Q →
    ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (τ : Fin f) (G : RootRing f N),
      G.IsHomogeneous (k - 1) →
      ∃ P : RootRing f N,
        algebraMap (RootRing f N) (FractionRing (RootRing f N)) P =
          dividedDifference f N (G * F) ∧
        (F.IsHomogeneous (topDegree f N + 1) → (restrictToBlock f N τ P).IsHomogeneous k) ∧
        ∃ S : MvPolynomial (Fin N) ℚ, powerSumHom N S = restrictToBlock f N τ P ∧
          flagIntegral f N (G * Q k τ) =
            c * coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) S
def RestTermWellDefined.Statement : Prop :=
  ∀ (f N : ℕ) (F : RootRing f N) (Q Q' : ℕ → Fin f → RootRing f N),
    IsPowerSumDecomposition f N F Q → IsPowerSumDecomposition f N F Q' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ N → ∀ (τ : Fin f) (G : RootRing f N), G.IsHomogeneous (k - 1) →
      restTerm f N Q k τ G = restTerm f N Q' k τ G
def LemmaB.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ κ : ℚ,
    (κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) ∧
    ∀ lam : Fin r → ℕ, Antitone lam →
      dividedDifference 1 (r + a)
          (aeval (yRoot 1 r a c 0) (schur (Fin r) lam) *
            vandermondeOf (yRoot 1 r a c 0) * vandermondeOf (zRoot 1 r a c 0)) =
        if ∀ i, a ≤ lam i then
          algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
            (C κ * aeval (fun i : Fin (r + a) => C c.sign * X ((0 : Fin 1), i))
              (schur (Fin (r + a)) (fun i => lam i - a)))
        else 0
def LemmaC.Statement : Prop :=
  ∀ (r a : ℕ) (nu : Fin r → ℕ), Antitone nu →
    numStandardTable (fun i => a + nu i) ≤
      Nat.choose (r * a + ∑ i, nu i) (∑ i, nu i) * numStandardTable (rectangle r a) *
        numStandardTable nu
def FrobeniusDimensionFormula.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    (numStandardTable lam : ℚ) =
      ((∑ i, lam i).factorial : ℚ) *
        vandermondeOf (fun i : Fin m => ((lam i + (m - 1 - (i : ℕ)) : ℕ) : ℚ)) /
        ∏ i : Fin m, ((lam i + (m - 1 - (i : ℕ))).factorial : ℚ)
def SchurPowerSumCoefficient.Statement : Prop :=
  ∀ (N r k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (nu : Fin r → ℕ), Antitone nu → ∑ i, nu i = k →
    ∃ S : MvPolynomial (Fin N) ℚ, powerSumHom N S = schur (Fin N) nu ∧
      coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) S =
        if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0
def HookDimensionSum.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∑ l ∈ Finset.range k, numStandardTable (hookShape k k l) = 2 ^ (k - 1)
def FrobeniusCharacterFormula.Statement : Prop :=
  ∀ r q m : ℕ, 1 ≤ q →
    psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m =
      ∑ lam ∈ partitionsOf r (q + m),
        C (symmetricGroupCharacter lam (q :: List.replicate m 1)) * schur (Fin r) lam
def CharacterBound.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (rho : List ℕ), Antitone lam → (∀ q ∈ rho, 1 ≤ q) →
    |symmetricGroupCharacter lam rho| ≤ numStandardTable lam
def CharacterAtIdentity.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    symmetricGroupCharacter lam (List.replicate (∑ i, lam i) 1) = numStandardTable lam
def RestPolynomialDecomposes.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock),
    ∃ Q : ℕ → Fin f → RootRing f (r + a),
      IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q
def SameFactorFormula.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f ∧
      ∀ Q : ℕ → Fin f → RootRing f (r + a),
        IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
        ∀ (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ r + a) (τ : Fin f),
          ∃ S : MvPolynomial (Fin (r + a)) ℚ,
            powerSumHom (r + a) S =
              ∑ nu ∈ partitionsOf r k,
                C (symmetricGroupCharacter (fun i => a + nu i)
                    ((k - 1) :: List.replicate (r * a + 1) 1)) *
                  aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) ∧
            restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ) =
              C₀ * k * (f * (r * a) + 1).factorial /
                  (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1)) *
                (numStandardTable (rectangle r a) : ℚ) ^ (f - 1) *
                coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1) S
def SameFactorBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    fibreDegree f r a c ≠ 0 ∧
    (∃ Q, IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q) ∧
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
      ∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ)| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)
def OtherFactorBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    fibreDegree f r a c ≠ 0 ∧
    (∃ Q, IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q) ∧
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
      ∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f, τ' ≠ τ →
        (r * a < k - 1 → restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ') = 0) ∧
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)
def XBound.Statement : Prop :=
  ∀ r a : ℕ, 2 ≤ r + a →
    (restX r a : ℝ) ≤ ((r + a : ℕ) : ℝ) ^ 2 / 2 + 2 * ((r + a : ℕ) : ℝ) ∧
      ((r + a : ℕ) : ℝ) ^ 2 / 2 + 2 * ((r + a : ℕ) : ℝ) ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2
def XOverPrime.Statement : Prop :=
  ∀ (f r a : ℕ) (B₀ p : ℝ), 1 ≤ f → 2 ≤ r + a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ → B₀ < p → (restX r a : ℝ) / p ≤ 3 / 8
def GeometricTail.Statement : Prop :=
  ∀ (p : ℝ) (k : ℕ), 2 ≤ p → 1 ≤ k →
    Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹) ∧
      ∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ ≤ 2 * (p ^ k)⁻¹
def ExponentialTail.Statement : Prop :=
  ∀ p X : ℝ, 0 < p → 0 ≤ X → X ≤ 3 / 8 * p →
    Summable (fun k : ℕ => 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)) ∧
      ∑' k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) ≤
        Real.exp (3 / 8) * X / p ^ 2 ∧
      Real.exp (3 / 8) * X / p ^ 2 ≤ 1.5 * X / p ^ 2
def ChebyshevThetaBound.Statement : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p ≤ x * Real.log 4
def PrimeLogSquareTail.Statement : Prop :=
  ∀ B : ℝ, 0 < B →
    Summable (fun p : {p : ℕ // p.Prime ∧ B < p} => Real.log p / (p : ℝ) ^ 2) ∧
      ∑' p : {p : ℕ // p.Prime ∧ B < p}, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / B
def RestConstants.Statement : Prop :=
  2 * Real.log 4 ≤ 2.78 ∧
    ∀ f N : ℕ, 1 ≤ f → 2 ≤ N →
      1.5 * (f : ℝ) * (3 / 2 * (N : ℝ) ^ 2) * (2.78 / (4 * f * (N : ℝ) ^ 2)) ≤ 1.6
def IntegerLogSquareTail.Statement : Prop :=
  ∀ (f N : ℕ) (B₀ : ℝ), 1 ≤ f → 2 ≤ N → 4 * (f : ℝ) * (N : ℝ) ^ 2 ≤ B₀ →
    Summable (fun m : {m : ℕ // B₀ < m} => Real.log m / (m : ℝ) ^ 2) ∧
      ∑' m : {m : ℕ // B₀ < m}, Real.log m / (m : ℝ) ^ 2 ≤ 2 * (1 + Real.log B₀) / B₀
def HookCharacterSumIdentity.Statement : Prop :=
  ∀ r a : ℕ, 1 ≤ r → 1 ≤ a →
    (a : ℚ) * numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) =
      ∑ k ∈ Finset.Icc 2 (r + a), ∑ l ∈ Finset.range (min r k),
        (-1 : ℚ) ^ l * symmetricGroupCharacter (fun i => a + hookShape r k l i)
          ((k - 1) :: List.replicate (r * a + 1) 1)
def TotalIdentity.Statement : Prop :=
  ∀ r a : ℕ, 1 ≤ r → 1 ≤ a →
    (r + a) * numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) =
      (r * a + 1) * r * numStandardTable (rectangle r a)
def restPrimeModel (f r a : ℕ) (c : SmallBlock) (Q : ℕ → Fin f → RootRing f (r + a))
    (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ) (p : ℕ) : ℝ :=
  Real.log p * ∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
    ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
      ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
        (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)
def RestPrimeBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    (∃ Q, IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q) ∧
    ∀ (Q : ℕ → Fin f → RootRing f (r + a)),
      IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) →
    ∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|
def RestBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    (∃ Q, IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q) ∧
    ∀ (Q : ℕ → Fin f → RootRing f (r + a)),
      IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) →
    ∀ P : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
        |restPrimeModel f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Q s e p| ≤
        1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|
def SmallBlock.jIndex (r a : ℕ) : SmallBlock → ℕ
  | .last => a
  | .first => r
def shiftFunctional (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (F : RootRing f (r + a)) : ℚ :=
  flagIntegral f (r + a)
    (∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < c.jIndex r a), pderiv (τ, i) F)
def totalFunctional (f N : ℕ) (τ : Fin f) (F : RootRing f N) : ℚ :=
  flagIntegral f N (∑ i : Fin N, pderiv (τ, i) F)
def ShiftTotalValues.Statement : Prop :=
  ∀ (f r a : ℕ) (τ : Fin f),
    (shiftFunctional f r a .last τ (restPolynomial f r a .last) = 0 ∧
      totalFunctional f (r + a) τ (restPolynomial f r a .last) =
        ((f * (r * a) + 1 : ℕ) : ℚ) * r * fibreDegree f r a .last) ∧
    (shiftFunctional f r a .first τ (restPolynomial f r a .first) =
        -(((f * (r * a) + 1 : ℕ) : ℚ) * r * fibreDegree f r a .first) ∧
      totalFunctional f (r + a) τ (restPolynomial f r a .first) =
        -(((f * (r * a) + 1 : ℕ) : ℚ) * r * fibreDegree f r a .first))
def FibreTranslationInvariance.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (τ : Fin f),
    ∑ i : Fin r, pderiv (yIndex f r a c τ i) (fibreClass f r a c) = 0 ∧
      ∑ i : Fin a, pderiv (zIndex f r a c τ i) (fibreClass f r a c) = 0
def PlueckerCauchyBinet.Statement : Prop :=
  ∀ (p q : ℕ) (Z : Matrix (Fin p) (Fin q) ℂ),
    (1 + Z * Z.conjTranspose).det =
      ((∑ S : {s : Finset (Fin p ⊕ Fin q) // s.card = p},
        ‖((Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) Z).submatrix id
          (fun i => ((S.1.equivFinOfCardEq S.2).symm i : Fin p ⊕ Fin q))).det‖ ^ 2 : ℝ) : ℂ)
def PlueckerHadamard.Statement : Prop :=
  ∀ (p q : ℕ) (Z : Matrix (Fin p) (Fin q) ℂ), (∀ i j, ‖Z i j‖ = 1) →
    ((1 + Z * Z.conjTranspose).det).re ≤ ((1 + q : ℕ) : ℝ) ^ p
def SmallRankBound.Statement : Prop :=
  ∀ k m j' N : ℕ, 2 ≤ m → m ^ 4 ≤ k → j' ≤ m → N = k + m - 1 →
    2 * m + 2 ≤ k ∧ 3 * j' ≤ N - 1
def SmallRankWeakHypothesis.Statement : Prop :=
  ¬ ∀ k m j' N : ℕ, 2 ≤ m → m + 3 ≤ k → j' ≤ m → N = k + m - 1 → 3 * j' ≤ N - 1
end
end RestTerms
end GroundTheory.Heights₂.Heights



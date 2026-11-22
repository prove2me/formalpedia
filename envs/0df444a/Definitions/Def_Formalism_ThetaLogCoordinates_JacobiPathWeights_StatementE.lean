-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:14.378474+00:00
-- url     : https://prove2.me/theorems/585a30ad-94d3-4ad4-bf95-2063b7062ecb
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/StatementE.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_DetLetters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
def ValTop : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k),
    (valS isVec S G = ⊤ ↔ G = 0) ∧ (lam1S isVec S G = ⊥ ↔ G = 0)
def PropVa : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G H : MvPolynomial (LVar ι ζ n) k),
    valS isVec S (G * H) = valS isVec S G + valS isVec S H ∧
    min (valS isVec S G) (valS isVec S H) ≤ valS isVec S (G + H) ∧
    lam1S isVec S (G * H) = lam1S isVec S G + lam1S isVec S H ∧
    lam1S isVec S (G + H) ≤ max (lam1S isVec S G) (lam1S isVec S H)
def PropVe : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)],
    (2 ≤ n → ∀ (i : ι) (a : Fin n), i ∈ S →
      (isVec i = true →
        valS isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0 ∧
        lam1S isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 1) ∧
      (isVec i = false →
        valS isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = ((-1 : ℤ) : WithTop ℤ) ∧
        lam1S isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0)) ∧
    (∀ (i : ι) (a : Fin n), i ∉ S →
      valS isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0 ∧
      lam1S isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0) ∧
    (∀ z : ζ,
      valS isVec S (X (Sum.inr z) : MvPolynomial (LVar ι ζ n) k) = 0 ∧
      lam1S isVec S (X (Sum.inr z) : MvPolynomial (LVar ι ζ n) k) = 0) ∧
    (∀ c : k, c ≠ 0 →
      valS isVec S (C c : MvPolynomial (LVar ι ζ n) k) = 0 ∧
      lam1S isVec S (C c : MvPolynomial (LVar ι ζ n) k) = 0) ∧
    (1 ≤ n → ∀ A : Fin n → ι, Function.Injective A → (∀ l, A l ∈ S ∧ isVec (A l) = true) →
      valS isVec S (detLetters (ζ := ζ) k A) = 1 ∧ lam1S isVec S (detLetters (ζ := ζ) k A) = 1)
def PropVdSub : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (θ : WithTop ℤ) (M : WithBot ℤ) (c : k) (G H : MvPolynomial (LVar ι ζ n) k),
    (θ ≤ valS isVec S G → θ ≤ valS isVec S H → θ ≤ valS isVec S (c • G + H)) ∧
    (lam1S isVec S G ≤ M → lam1S isVec S H ≤ M → lam1S isVec S (c • G + H) ≤ M)
def CornerValSpecialize : Prop :=
  ∀ (k k₁ : Type) [Field k] [Field k₁] (φ : k →+* k₁) (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (G : MvPolynomial (LVar ι ζ n) k) (θ : ℤ) (g₀ : (Matrix (Fin n) (Fin n) k₁)ˣ),
    (θ : WithTop ℤ) ≤ valS isVec S G →
    ∀ j ∈ (conjAct φ isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁) true G).coeff.support, θ ≤ j
def sharpHom {k₁ ι ζ : Type*} [CommRing k₁] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (g gi : Matrix (Fin n) (Fin n) k₁) :
    MvPolynomial (LVar ι ζ n) k₁ →ₐ[k₁] MvPolynomial (LVar ι ζ n) k₁ :=
  aeval fun x =>
    match x with
    | Sum.inl (i, a) =>
      if i ∈ S then
        (if isVec i then Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a
        else Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a)
      else X (Sum.inl (i, a))
    | Sum.inr z => X (Sum.inr z)
def lastExp {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (e : LVar ι ζ n →₀ ℕ) : ℤ :=
  e.sum fun x d => match x with
    | Sum.inl (i, a) => if i ∈ S ∧ a.val + 1 = n then (if isVec i then (d : ℤ) else -(d : ℤ)) else 0
    | Sum.inr _ => 0
def CoordChangeCoeff : Prop :=
  ∀ (k₁ : Type) [Field k₁] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g₀ : (Matrix (Fin n) (Fin n) k₁)ˣ) (H : MvPolynomial (LVar ι ζ n) k₁),
    (∀ j : ℤ,
      (conjAct (RingHom.id k₁) isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁) true
          (sharpHom isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁) H)).coeff j =
        sharpHom isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁)
          (∑ e ∈ H.support.filter (fun e => lastExp isVec S e = j), monomial e (coeff e H))) ∧
    Function.Bijective (sharpHom (ζ := ζ) (n := n) isVec S (↑g₀ : Matrix (Fin n) (Fin n) k₁)
      (↑g₀⁻¹ : Matrix (Fin n) (Fin n) k₁))
def LetterDetIrreducible : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (r : ℕ) (A : Fin r → ι), 1 ≤ r → Function.Injective A →
    Irreducible (detLetters (ζ := ζ) k A)
def PowDvdOfFractionField : Prop :=
  ∀ (R₀ Q₀ : Type) [CommRing R₀] [IsDomain R₀] [UniqueFactorizationMonoid R₀] [Field Q₀] [Algebra R₀ Q₀]
    [IsFractionRing R₀ Q₀] (Z : Type) (D G : MvPolynomial Z R₀) (m : ℕ),
    Irreducible D → (∀ c : R₀, D ≠ C c) →
    (map (algebraMap R₀ Q₀) D) ^ m ∣ map (algebraMap R₀ Q₀) G → D ^ m ∣ G
def LemmaEa : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (r : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (U : Set ι) [DecidablePred (· ∈ U)] (A : Fin r → ι) (G : MvPolynomial (LVar ι ζ r) k) (B' : ℕ) (θ : ℤ),
    1 ≤ r → Function.Injective A → (∀ l, A l ∈ S ∧ isVec (A l) = true) →
    (∀ i, i ∈ U ↔ i ∈ S ∧ isVec i = true ∧ ∀ l, A l ≠ i) →
    G ≠ 0 → (∀ e ∈ G.support, degIn U e ≤ B') → (θ : WithTop ℤ) ≤ valS isVec S G → (B' : ℤ) < θ →
    (detLetters k A) ^ (θ - B').toNat ∣ G
def PropEb : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (r : ℕ) (isVec : ι → Bool) (S' : Set ι) [DecidablePred (· ∈ S')]
    (A : Fin r → ι), 1 ≤ r → Function.Injective A → (∀ l, isVec (A l) = true) →
    ((∀ l, A l ∈ S') → valS isVec S' (detLetters (ζ := ζ) k A) = 1) ∧
    ((∃ l, A l ∉ S') → valS isVec S' (detLetters (ζ := ζ) k A) = 0) ∧
    ∀ (H : MvPolynomial (LVar ι ζ r) k) (m : ℕ),
      valS isVec S' ((detLetters k A) ^ m * H) = valS isVec S' H + m • valS isVec S' (detLetters (ζ := ζ) k A) ∧
      valS isVec S' ((detLetters k A) ^ m * H) ≤ valS isVec S' H + (m : WithTop ℤ)
def LemmaEint : Prop :=
  ∀ (O Kf : Type) [CommRing O] [IsDomain O] [UniqueFactorizationMonoid O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] (ι ζ : Type) (r : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (U : Set ι) [DecidablePred (· ∈ U)] (A : Fin r → ι) (G : MvPolynomial (LVar ι ζ r) O) (B' : ℕ) (θ : ℤ),
    1 ≤ r → Function.Injective A → (∀ l, A l ∈ S ∧ isVec (A l) = true) →
    (∀ i, i ∈ U ↔ i ∈ S ∧ isVec i = true ∧ ∀ l, A l ≠ i) →
    G ≠ 0 → (∀ e ∈ G.support, degIn U e ≤ B') →
    (θ : WithTop ℤ) ≤ valS isVec S (map (algebraMap O Kf) G) → (B' : ℤ) < θ →
    (detLetters O A) ^ (θ - B').toNat ∣ G
def PropEsharp : Prop :=
  ∀ (k : Type) [Field k],
    valS (ζ := Empty) (fun _ : Fin 3 => true) Set.univ
      (detLetters k (fun l : Fin 2 => (Fin.castSucc l : Fin 3)) *
        detLetters k (fun l : Fin 2 => if l = 0 then (0 : Fin 3) else 2)) = 2 ∧
    ¬ (detLetters (ζ := Empty) k (fun l : Fin 2 => (Fin.castSucc l : Fin 3))) ^ 2 ∣
      (detLetters k (fun l : Fin 2 => (Fin.castSucc l : Fin 3)) *
        detLetters k (fun l : Fin 2 => if l = 0 then (0 : Fin 3) else 2))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases



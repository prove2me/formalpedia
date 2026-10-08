-- Prove2me | Definitions.Def_DimensionTenPair
-- name    : DimensionTenPair
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.776997+00:00
-- url     : https://prove2.me/theorems/09dc7565-7a72-4b85-bb2e-880318f86326
-- statement:
--   For complex n×n matrices Mₙ, this block constructs two maps M₁₀→M₁₀ and the Choi matrix of their composition. Its starting map is P(A)=∑ᵢⱼAᵢⱼBᵢᵀBⱼ, with four real 6×4 matrices viewed over ℂ: B₀=6[I₄;0₂×₄]; the rows of B₁ are (−12,0,0,0), (0,−6,0,0), (0,0,6,0), (0,0,0,12), (−6,0,6,6), (−6,−6,6,0); the rows of B₂ are (0,6,−2,0), (6,6,0,2), (−2,0,10,0), (0,2,0,24), (0,0,0,6), (0,−6,6,−6); and the rows of B₃ are (0,0,−4,−3), (0,−2,−3,−4), (−4,−3,11,6), (−3,−4,6,25), (6,6,0,0), (0,−6,6,6). Complex linearity means additivity and compatibility with all complex scalars. The amplification of F:Mₐ→M_b applies F separately to every a×a block of a matrix indexed by {0,…,k−1}×{0,…,a−1}. Complete positivity means that every such amplification preserves positive semidefiniteness for every positive integer k. PPT additionally requires complex linearity and complete positivity of X↦F(X)ᵀ. A matrix is separable when it is a finite sum ∑ᵢAᵢ⊗Bᵢ with both factors positive semidefinite; entanglement breaking means complete positivity and separability of every amplified positive semidefinite input. Complete positivity and entanglement breaking do not separately require linearity. The Choi matrix has entries C(F)_(i,u),(j,v)=F(Eᵢⱼ)ᵤᵥ. The tensor construction sends X to ∑ᵢⱼF(Xᵢⱼ)⊗G(Eᵢⱼ), where (Xᵢⱼ)ₐᵦ=X_(a,i),(b,j), and the basis-defined Hilbert–Schmidt adjoint is F*(Y)ᵢⱼ=∑ᵤᵥconj(F(Eᵢⱼ)ᵤᵥ)Yᵤᵥ. Let S:ℂ¹⁰→ℂ⁴⊗ℂ⁴ have columns eₚ⊗eₚ and (eₚ⊗e_q+e_q⊗eₚ)/√2 for p≤q, and W:ℂ⁶→ℂ⁴⊗ℂ⁴ have columns (eₚ⊗e_q−e_q⊗eₚ)/√2 for p<q, both ordered lexicographically with indices 0,…,3. Define E(A)=W†(P⊗P)(SAS†)W and K(A)=H E(A)ᵀH†, where H exchanges exterior coordinates 0↔5 and 2↔3 with positive signs and 1↔4 with negative signs. With J:ℂ⁶→ℂ¹⁰ the inclusion into the first six coordinates, the maps are φ₁(A)=J E(Aᵀ)J† and φ₂(B)=K*(J†BJ), and compositeChoi is C(φ₂∘φ₁). Finally, the product vector u⊗v has coordinate (i,j) equal to uᵢvⱼ. These are definitions; the block asserts no positivity or entanglement property of the constructed maps.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DimensionTenPair.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DimensionTenPair.lean; bytes 16..4289
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex
namespace DimensionTen

def blocksZ : Fin 4 → Matrix (Fin 6) (Fin 4) ℤ :=
  ![ ![ ![6,0,0,0], ![0,6,0,0], ![0,0,6,0], ![0,0,0,6], ![0,0,0,0], ![0,0,0,0] ],
     ![ ![-12,0,0,0], ![0,-6,0,0], ![0,0,6,0], ![0,0,0,12], ![-6,0,6,6], ![-6,-6,6,0] ],
     ![ ![0,6,-2,0], ![6,6,0,2], ![-2,0,10,0], ![0,2,0,24], ![0,0,0,6], ![0,-6,6,-6] ],
     ![ ![0,0,-4,-3], ![0,-2,-3,-4], ![-4,-3,11,6], ![-3,-4,6,25], ![6,6,0,0], ![0,-6,6,6] ] ]

def blocks (i : Fin 4) : Matrix (Fin 6) (Fin 4) ℂ :=
  (blocksZ i).map (Int.castRingHom ℂ)

def pencilMap (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, A i j • ((blocks i)ᵀ * blocks j)

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def IsComplexLinear {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  (∀ A B, F (A + B) = F A + F B) ∧
  (∀ (c : ℂ) A, F (c • A) = c • F A)

def amplify {a b : ℕ} (F : Mat a → Mat b) (k : ℕ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ :=
  fun u v => F (fun i j => X (u.1, i) (v.1, j)) u.2 v.2

def CompletelyPositive {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ,
    X.PosSemidef → (amplify F k X).PosSemidef

def PPT {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  IsComplexLinear F ∧ CompletelyPositive F ∧
    CompletelyPositive (fun X => (F X)ᵀ)

def separable {a b : ℕ} (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Prop :=
  ∃ r : ℕ, ∃ A : Fin r → Mat a, ∃ B : Fin r → Mat b,
    (∀ i, (A i).PosSemidef ∧ (B i).PosSemidef) ∧
    X = ∑ i, Matrix.kronecker (A i) (B i)

def EntanglementBreaking {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  CompletelyPositive F ∧
  ∀ k : ℕ, 0 < k → ∀ X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ,
    X.PosSemidef → separable (amplify F k X)

def choi {a b : ℕ} (F : Mat a → Mat b) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun u v => F (Matrix.single u.1 v.1 1) u.2 v.2

def tensorMap {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    Matrix (Fin b × Fin d) (Fin b × Fin d) ℂ :=
  ∑ i : Fin c, ∑ j : Fin c,
    Matrix.kronecker (F (fun a b => X (a, i) (b, j))) (G (Matrix.single i j 1))

def hsAdjoint {a b : ℕ} (F : Mat a → Mat b) (Y : Mat b) : Mat a :=
  fun i j => ∑ u : Fin b, ∑ v : Fin b, star (F (Matrix.single i j 1) u v) * Y u v

def symmetricPairs : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]

def exteriorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def symmetricIsometry : Matrix (Fin 4 × Fin 4) (Fin 10) ℂ :=
  fun ij a =>
    let p := (symmetricPairs a).1
    let q := (symmetricPairs a).2
    if p = q then (if ij = (p,p) then 1 else 0)
    else ((if ij = (p,q) then 1 else 0) + (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def exteriorIsometry : Matrix (Fin 4 × Fin 4) (Fin 6) ℂ :=
  fun ij a =>
    let p := (exteriorPairs a).1
    let q := (exteriorPairs a).2
    ((if ij = (p,q) then 1 else 0) - (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def hodgeComplement : Mat 6 :=
  ![ ![0,0,0,0,0,1], ![0,0,0,0,-1,0], ![0,0,0,1,0,0],
     ![0,0,1,0,0,0], ![0,-1,0,0,0,0], ![1,0,0,0,0,0] ]

def firstSix : Matrix (Fin 10) (Fin 6) ℂ :=
  fun i j => if i.val = j.val then 1 else 0

def exteriorMap (A : Mat 10) : Mat 6 :=
  exteriorIsometryᴴ *
    tensorMap pencilMap pencilMap (symmetricIsometry * A * symmetricIsometryᴴ) *
      exteriorIsometry

def complementaryMap (A : Mat 10) : Mat 6 :=
  hodgeComplement * (exteriorMap A)ᵀ * hodgeComplementᴴ

def phiOne (A : Mat 10) : Mat 10 :=
  firstSix * exteriorMap Aᵀ * firstSixᴴ

def phiTwo (B : Mat 10) : Mat 10 :=
  hsAdjoint complementaryMap (firstSixᴴ * B * firstSix)

def compositeChoi : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ :=
  choi (phiTwo ∘ phiOne)

def productVector {a b : ℕ} (u : Fin a → ℂ) (v : Fin b → ℂ) : Fin a × Fin b → ℂ :=
  fun ij => u ij.1 * v ij.2



end DimensionTen
end
end OAI



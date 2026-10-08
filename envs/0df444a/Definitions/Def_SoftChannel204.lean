-- Prove2me | Definitions.Def_SoftChannel204
-- name    : SoftChannel204
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:23.981186+00:00
-- url     : https://prove2.me/theorems/1506d25b-2e17-4189-84db-bb32cfc8780a
-- statement:
--   On the Boolean cube {true,false}^n, sign(b) is +1 for true and -1 for false, and avg is the uniform average of a real function over the cube. With L = log 2, psi(r) = ((1+r)/2)log(1+r) + ((1-r)/2)log(1-r) and H(r) = L - psi(r). The information of u : cube -> R is info(u) = H(avg u) - avg(H∘u), and psiInv is a chosen inverse of psi on [0,1]. The noise kernel with correlation ρ is the product over coordinates of (1+ρ)/2 where x and y agree and (1-ρ)/2 where they differ; noise(ρ,u)(y) = Σ_x kernel(ρ,y,x)u(x). Closed means all values of u lie in [-1,1], and Interior means they lie in (-1,1). softCoordinate(i,a) is the function x ↦ a·sign(x_i), flip i changes coordinate i, numberOperator g(x) = (1/2)Σ_i (g(x) - g(flip i x)), and production g = avg(artanh(g)·numberOperator g). Further auxiliary functions are F(s) = psiInv(s)·artanh(psiInv(s)), S(s) = 0 for s<0 and F(s) - 2s otherwise, reserve(m,I) = 2I + (1-m²)·S(L - (H m - I)/(1-m²)), hybrid(m,I) = max(reserve(m,I), F(I)), softJoint and boolJoint (joint laws of a bit and a noisy cube point, from a soft function u or a Boolean function f), their marginals, mutualInformation, and binaryEntropyBits(ε) = -(ε log ε + (1-ε)log(1-ε))/L. Seven defined propositions, not established theorems, are given. SoftContraction says that for all n, closed u and ρ in [-1,1], info(noise ρ u) ≤ psi(|ρ|·psiInv(info u)). SoftAttainment says equality holds for every softCoordinate with |a| ≤ 1. SoftInformationIdentity says the mutual information of softJoint equals info(noise ρ u) for closed u. RefinedBoolean says that for every Boolean f, with m = avg(sign∘f) and bound = psi(|ρ|·psiInv(H m)), the mutual information of boolJoint equals info(noise ρ (sign∘f)), is at most bound, bound ≤ psi|ρ|, and bound < psi|ρ| when 0<|m|<1 and ρ≠0. BooleanAttainment says that dictator functions x_i and its negation have mutual information exactly psi|ρ|. BitsConversion says that for ε in [0,1/2], psi(1-2ε)/L = 1 - binaryEntropyBits(ε) and the mutual information at ρ = 1-2ε, divided by L, is at most that value. SharpProduction says that for every interior g, hybrid(avg g, info g) ≤ production g and F(info g) ≤ hybrid(avg g, info g). FullMain is the conjunction of all seven.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SoftChannel204.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SoftChannel204.lean; bytes 16..4410
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace SoftChannel204

abbrev Cube (n : ℕ) := Fin n → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

def avg {n : ℕ} (g : Cube n → ℝ) : ℝ := (∑ x, g x) / (2 : ℝ) ^ n

def L : ℝ := Real.log 2

def psi (r : ℝ) : ℝ :=
  (1 + r) / 2 * Real.log (1 + r) + (1 - r) / 2 * Real.log (1 - r)

def H (r : ℝ) : ℝ := L - psi r

def info {n : ℕ} (u : Cube n → ℝ) : ℝ := H (avg u) - avg (H ∘ u)

def psiInv (s : ℝ) : ℝ := Function.invFunOn psi (Set.Icc 0 1) s

def kernel {n : ℕ} (ρ : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2

def noise {n : ℕ} (ρ : ℝ) (u : Cube n → ℝ) (y : Cube n) : ℝ :=
  ∑ x, kernel ρ y x * u x

def Closed {n : ℕ} (u : Cube n → ℝ) : Prop := ∀ x, u x ∈ Set.Icc (-1) 1

def Interior {n : ℕ} (g : Cube n → ℝ) : Prop := ∀ x, g x ∈ Set.Ioo (-1) 1

def softCoordinate {n : ℕ} (i : Fin n) (a : ℝ) (x : Cube n) : ℝ := a * sign (x i)

def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n := Function.update x i (!(x i))

def numberOperator {n : ℕ} (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (g x - g (flip i x))

def production {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  avg (fun x => Real.artanh (g x) * numberOperator g x)

/-- Defined by this formula on `[0, L)`; no finite endpoint value at `L` is asserted. -/
def F (s : ℝ) : ℝ := psiInv s * Real.artanh (psiInv s)

/-- The excess `F s - 2 * s`, used for `s < L`, is extended by zero to negative arguments. -/
def S (s : ℝ) : ℝ := if s < 0 then 0 else F s - 2 * s

/-- The reserve is used for `|m| < 1` and `0 ≤ I < H m`. -/
def reserve (m I : ℝ) : ℝ :=
  2 * I + (1 - m ^ 2) * S (L - (H m - I) / (1 - m ^ 2))

def hybrid (m I : ℝ) : ℝ := max (reserve m I) (F I)

def softJoint {n : ℕ} (ρ : ℝ) (u : Cube n → ℝ) (b : Bool) (y : Cube n) : ℝ :=
  avg (fun x => (1 + sign b * u x) / 2 * kernel ρ x y)

def boolJoint {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  avg (fun x => if f x = b then kernel ρ x y else 0)

def leftMarginal {n : ℕ} (p : Bool → Cube n → ℝ) (b : Bool) : ℝ := ∑ y, p b y

def rightMarginal {n : ℕ} (p : Bool → Cube n → ℝ) (y : Cube n) : ℝ := ∑ b, p b y

def mutualInformation {n : ℕ} (p : Bool → Cube n → ℝ) : ℝ :=
  ∑ b, ∑ y, if 0 < p b y then
    p b y * Real.log (p b y / (leftMarginal p b * rightMarginal p y)) else 0

def binaryEntropyBits (ε : ℝ) : ℝ :=
  -(ε * Real.log ε + (1 - ε) * Real.log (1 - ε)) / L

def SoftContraction : Prop := ∀ (n : ℕ) (u : Cube n → ℝ), Closed u →
  ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
    info (noise ρ u) ≤ psi (|ρ| * psiInv (info u))

def SoftAttainment : Prop := ∀ (n : ℕ) (i : Fin n) (a : ℝ), |a| ≤ 1 →
  ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
    info (noise ρ (softCoordinate i a)) =
      psi (|ρ| * psiInv (info (softCoordinate i a)))

def SoftInformationIdentity : Prop := ∀ (n : ℕ) (u : Cube n → ℝ), Closed u →
  ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
    mutualInformation (softJoint ρ u) = info (noise ρ u)

def RefinedBoolean : Prop := ∀ (n : ℕ) (f : Cube n → Bool)
  (ρ : ℝ), ρ ∈ Set.Icc (-1 : ℝ) 1 →
  let m := avg (sign ∘ f)
  let bound := psi (|ρ| * psiInv (H m))
  mutualInformation (boolJoint ρ f) = info (noise ρ (sign ∘ f)) ∧
  mutualInformation (boolJoint ρ f) ≤ bound ∧ bound ≤ psi |ρ| ∧
  (0 < |m| → |m| < 1 → 0 < |ρ| → bound < psi |ρ|)

def BooleanAttainment : Prop := ∀ (n : ℕ) (i : Fin n)
  (ρ : ℝ), ρ ∈ Set.Icc (-1 : ℝ) 1 →
  mutualInformation (boolJoint ρ (fun x => x i)) = psi |ρ| ∧
  mutualInformation (boolJoint ρ (fun x => !(x i))) = psi |ρ|

def BitsConversion : Prop := ∀ (n : ℕ) (f : Cube n → Bool)
  (ε : ℝ), ε ∈ Set.Icc (0 : ℝ) (1/2) →
  psi (1 - 2 * ε) / L = 1 - binaryEntropyBits ε ∧
  mutualInformation (boolJoint (1 - 2 * ε) f) / L ≤ 1 - binaryEntropyBits ε

def SharpProduction : Prop := ∀ (n : ℕ) (g : Cube n → ℝ), Interior g →
  hybrid (avg g) (info g) ≤ production g ∧ F (info g) ≤ hybrid (avg g) (info g)

def FullMain : Prop := SoftContraction ∧ SoftAttainment ∧ SoftInformationIdentity ∧
  RefinedBoolean ∧ BooleanAttainment ∧ BitsConversion ∧ SharpProduction



end SoftChannel204
end
end OAI



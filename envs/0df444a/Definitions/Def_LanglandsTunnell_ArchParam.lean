-- Prove2me | Definitions.Def_LanglandsTunnell_ArchParam
-- name    : LanglandsTunnell_ArchParam
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/56478ffb-bd44-54e8-b9aa-55bb7b69ece3
-- title:
--   Archimedean GL(2) L-parameters over R and C
-- statement:
--   Two data types record the archimedean component of a $\mathrm{GL}(2)$ automorphic representation in the currency of $\Gamma$-shifts. `RealArchParam` is an inductive type with two constructors: `principal u₁ a₁ u₂ a₂`, carrying two pairs $(u_i,a_i) \in \mathbb{C} \times \mathbb{Z}/2$ (the data of two quasi-characters $x \mapsto |x|^{u_i}\operatorname{sgn}(x)^{a_i}$ of $\mathbb{R}^\times$), and `discrete u k hk`, carrying $u \in \mathbb{C}$ and $k \in \mathbb{N}$ together with a proof of $1 \le k$. `ComplexArchParam` is a structure with fields $u_1, u_2 \in \mathbb{C}$ and $k_1, k_2 \in \mathbb{Z}$, the data of two quasi-characters of $\mathbb{C}^\times$.
--
--   The gamma-shift multisets are total functions: for `principal`, `gammaR` is $\{u_1 + \delta(a_1),\, u_2 + \delta(a_2)\}$ with $\delta(a) = 0$ for $a = 0$ and $\delta(a) = 1$ otherwise (`signShift`), and `gammaC` is empty; for `discrete u k`, `gammaR` is empty and `gammaC` is $\{u + k/2\}$; for `ComplexArchParam`, `gammaC` is $\{u_1 + |k_1|/2,\, u_2 + |k_2|/2\}$, the absolute values taken via `Int.natAbs`. In each case `archFactor P s` is the product of $\Gamma_{\mathbb{R}}(s+\mu)$ over $\mu \in$ `gammaR` times the product of $\Gamma_{\mathbb{C}}(s+\nu)$ over $\nu \in$ `gammaC`.
--
--   Twisting by a quasi-character adds $u$ to each exponent and $a$ (resp. $k$) to each sign (resp. integer) parameter, except that on `discrete` only $u$ moves and the sign argument is discarded; `dual` negates all exponents and integer parameters while fixing $a_1,a_2$ and $k$. The central quasi-character is recorded by `centralExponent` ($u_1+u_2$, resp. $2u$ in the discrete case) together with `centralSign` ($a_1+a_2$, resp. $k+1$ in $\mathbb{Z}/2$) or `centralTwist` ($k_1+k_2$). Accompanying lemmas give $\mathrm{twist}\,0\,0 = \mathrm{id}$, additivity of twisting, $\mathrm{dual}\circ\mathrm{dual} = \mathrm{id}$, the effect of twisting on the shift multisets (for `gammaR` and `ComplexArchParam.gammaC` only for the untwisted sign/integer part), and the distinguished parameters `oddArtin` $=$ `principal 0 0 0 1` and `trivialArtin` $=\langle 0,0,0,0\rangle$, whose shift multisets are $\{0,1\}$ and $\{0,0\}$ and whose archimedean factors are $\Gamma_{\mathbb{C}}(s)$ (by the Legendre duplication identity $\Gamma_{\mathbb{R}}(s)\Gamma_{\mathbb{R}}(s+1) = \Gamma_{\mathbb{C}}(s)$) and $\Gamma_{\mathbb{C}}(s)^2$. No $\varepsilon$-factors are recorded.
--
--   **Relation to Mathlib.** The gamma factors are Mathlib's `Complex.Gammaℝ` and `Complex.Gammaℂ`, together with the Mathlib identity `Gammaℝ_mul_Gammaℝ_add_one`. Mathlib has no notion of archimedean L-parameter for $\mathrm{GL}(2)$; these types and their operations are the project's own.
--
--   **Where it is used.** These parameters supply the archimedean bookkeeping for the automorphic and Artin-representation L-functions occurring on the Langlands–Tunnell side of the argument, where the odd two-dimensional Artin parameter `oddArtin` and the weight-one matching $\Gamma_{\mathbb{R}}(s)\Gamma_{\mathbb{R}}(s+1) = \Gamma_{\mathbb{C}}(s)$ are the relevant cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArchParam.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace LanglandsTunnell

open Complex

inductive RealArchParam where

  | principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) : RealArchParam

  | discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) : RealArchParam

@[ext]
structure ComplexArchParam where

  u₁ : ℂ

  k₁ : ℤ

  u₂ : ℂ

  k₂ : ℤ

def signShift (a : ZMod 2) : ℂ := if a = 0 then 0 else 1

@[simp] theorem signShift_zero : signShift 0 = 0 := by simp [signShift]

@[simp] theorem signShift_one : signShift 1 = 1 := by simp [signShift]

namespace RealArchParam

def gammaR : RealArchParam → Multiset ℂ
  | principal u₁ a₁ u₂ a₂ => {u₁ + signShift a₁, u₂ + signShift a₂}
  | discrete _ _ _ => 0

def gammaC : RealArchParam → Multiset ℂ
  | principal _ _ _ _ => 0
  | discrete u k _ => {u + (k : ℂ) / 2}

def archFactor (P : RealArchParam) (s : ℂ) : ℂ :=
  (P.gammaR.map fun μ => Gammaℝ (s + μ)).prod * (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist : RealArchParam → ℂ → ZMod 2 → RealArchParam
  | principal u₁ a₁ u₂ a₂, u, a => principal (u₁ + u) (a₁ + a) (u₂ + u) (a₂ + a)
  | discrete u₀ k hk, u, _ => discrete (u₀ + u) k hk

def dual : RealArchParam → RealArchParam
  | principal u₁ a₁ u₂ a₂ => principal (-u₁) a₁ (-u₂) a₂
  | discrete u k hk => discrete (-u) k hk

def centralExponent : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => u₁ + u₂
  | discrete u _ _ => 2 * u

def centralSign : RealArchParam → ZMod 2
  | principal _ a₁ _ a₂ => a₁ + a₂
  | discrete _ k _ => (k : ZMod 2) + 1

@[simp] theorem twist_zero (P : RealArchParam) : P.twist 0 0 = P := by
  cases P <;> simp [twist]

theorem twist_twist (P : RealArchParam) (u u' : ℂ) (a a' : ZMod 2) :
    (P.twist u a).twist u' a' = P.twist (u + u') (a + a') := by
  cases P <;> simp [twist, add_assoc]

@[simp] theorem dual_dual (P : RealArchParam) : P.dual.dual = P := by
  cases P <;> simp [dual]

theorem gammaC_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).gammaC = P.gammaC.map (· + u) := by
  cases P <;> simp [twist, gammaC, add_right_comm]

theorem gammaR_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).gammaR = P.gammaR.map (· + u) := by
  cases P <;> simp [twist, gammaR, add_right_comm]

end RealArchParam

namespace ComplexArchParam

def gammaC (P : ComplexArchParam) : Multiset ℂ :=
  {P.u₁ + (P.k₁.natAbs : ℂ) / 2, P.u₂ + (P.k₂.natAbs : ℂ) / 2}

def archFactor (P : ComplexArchParam) (s : ℂ) : ℂ :=
  (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) : ComplexArchParam :=
  ⟨P.u₁ + u, P.k₁ + k, P.u₂ + u, P.k₂ + k⟩

def dual (P : ComplexArchParam) : ComplexArchParam :=
  ⟨-P.u₁, -P.k₁, -P.u₂, -P.k₂⟩

def centralExponent (P : ComplexArchParam) : ℂ := P.u₁ + P.u₂

def centralTwist (P : ComplexArchParam) : ℤ := P.k₁ + P.k₂

@[simp] theorem twist_zero (P : ComplexArchParam) : P.twist 0 0 = P := by
  simp [twist]

theorem twist_twist (P : ComplexArchParam) (u u' : ℂ) (k k' : ℤ) :
    (P.twist u k).twist u' k' = P.twist (u + u') (k + k') := by
  simp [twist, add_assoc]

@[simp] theorem dual_dual (P : ComplexArchParam) : P.dual.dual = P := by
  simp [dual]

theorem gammaC_dual (P : ComplexArchParam) :
    P.dual.gammaC = {-P.u₁ + (P.k₁.natAbs : ℂ) / 2, -P.u₂ + (P.k₂.natAbs : ℂ) / 2} := by
  simp [dual, gammaC]

theorem gammaC_twist_zero (P : ComplexArchParam) (u : ℂ) :
    (P.twist u 0).gammaC = P.gammaC.map (· + u) := by
  simp [twist, gammaC, add_right_comm]

end ComplexArchParam

def RealArchParam.oddArtin : RealArchParam := .principal 0 0 0 1

def ComplexArchParam.trivialArtin : ComplexArchParam := ⟨0, 0, 0, 0⟩

theorem RealArchParam.gammaR_oddArtin : RealArchParam.oddArtin.gammaR = {0, 1} := by
  simp [oddArtin, gammaR]

theorem ComplexArchParam.gammaC_trivialArtin : ComplexArchParam.trivialArtin.gammaC = {0, 0} := by
  simp [trivialArtin, gammaC]

theorem RealArchParam.archFactor_oddArtin (s : ℂ) :
    RealArchParam.oddArtin.archFactor s = Gammaℂ s := by
  simp [oddArtin, archFactor, gammaR, gammaC, Gammaℝ_mul_Gammaℝ_add_one]

theorem ComplexArchParam.archFactor_trivialArtin (s : ℂ) :
    ComplexArchParam.trivialArtin.archFactor s = Gammaℂ s * Gammaℂ s := by
  simp [trivialArtin, archFactor, gammaC]

end LanglandsTunnell

end



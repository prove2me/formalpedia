-- Prove2me | Definitions.Def_LanglandsTunnell_ArchEpsilon
-- name    : LanglandsTunnell_ArchEpsilon
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/7dcd7486-6ae2-5186-85a1-49f37d50af0a
-- title:
--   Archimedean epsilon-factors of GL(2) parameters at real and complex places
-- statement:
--   Three definitions, all giving constants in $\mathbb{C}$, attached to the archimedean $L$-parameters of $\mathrm{GL}(2)$ encoded by the inductive type `RealArchParam` (a principal-series datum `principal u₁ a₁ u₂ a₂` with $u_i \in \mathbb{C}$, $a_i \in \mathbb{Z}/2$, or a discrete-series datum `discrete u k hk` with $k \ge 1$) and the structure `ComplexArchParam` (carrying $u_1, u_2 \in \mathbb{C}$ and $k_1, k_2 \in \mathbb{Z}$). First, `signEpsilon a` is $1$ for $a = 0$ and $i$ for $a = 1$, the $\varepsilon$-factor of $\mathrm{sgn}^{a}$ on $\mathbb{R}^\times$; its square is $1$ respectively $-1$, i.e. $\mathrm{sgn}^a(-1)$. Second, `RealArchParam.epsilonFactor` sends `principal u₁ a₁ u₂ a₂` to $\mathrm{signEpsilon}(a_1)\,\mathrm{signEpsilon}(a_2)$ and `discrete u k hk` to $i^{k+1}$. Third, `ComplexArchParam.epsilonFactor` is $i^{|k_1|}\,i^{|k_2|}$, the absolute values being the natural-number absolute values of the integers $k_1, k_2$. All three are plain constants: no variable $s$, no additive character and no measure occur, and nothing about local functional equations or zeta integrals is asserted.
--
--   The accompanying lemmas record the formal properties of these constants. Both factors are unchanged by the unramified twists `twist u 0` (adding $u$ to the exponents while leaving the sign, respectively the integers $k_i$, untouched) and by `dual` (negation of the exponents, and of $k_1, k_2$ in the complex case). The squares are computed: $\mathrm{signEpsilon}(a_1)^2\,\mathrm{signEpsilon}(a_2)^2$ in the principal case, $(-1)^{k+1}$ in the discrete case, and in the complex case the product of the factor with that of its dual is $(-1)^{|k_1|+|k_2|}$. Finally the value at the distinguished parameters is evaluated: $i$ at `RealArchParam.oddArtin` $= \mathrm{principal}\,0\,0\,0\,1$, and $1$ at `ComplexArchParam.trivialArtin` $= (0,0,0,0)$.
--
--   **Relation to Mathlib.** Mathlib supplies the Gamma factors $\Gamma_{\mathbb{R}}$, $\Gamma_{\mathbb{C}}$ used for the $L$-factors of these parameters, but has no notion of local $\varepsilon$-factor; these constants are the project's own.
--
--   **Where it is used.** These constants are the archimedean $\varepsilon$-factors of the parameters used to package the Langlands–Tunnell input, notably the odd two-dimensional Artin parameter at a real place and the trivial parameter at a complex place, where they supply the archimedean contribution to the sign in a functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArchEpsilon.lean

import Definitions.Def_LanglandsTunnell_ArchParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell

open Complex

def signEpsilon (a : ZMod 2) : ℂ := if a = 0 then 1 else I

@[simp] theorem signEpsilon_zero : signEpsilon 0 = 1 := by simp [signEpsilon]

@[simp] theorem signEpsilon_one : signEpsilon 1 = I := by simp [signEpsilon]

theorem signEpsilon_sq (a : ZMod 2) : signEpsilon a ^ 2 = if a = 0 then 1 else -1 := by
  by_cases h : a = 0
  · simp [signEpsilon, h]
  · simp [signEpsilon, h, I_sq]

namespace RealArchParam

def epsilonFactor : RealArchParam → ℂ
  | principal _ a₁ _ a₂ => signEpsilon a₁ * signEpsilon a₂
  | discrete _ k _ => I ^ (k + 1)

@[simp] theorem epsilonFactor_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).epsilonFactor = signEpsilon a₁ * signEpsilon a₂ := rfl

@[simp] theorem epsilonFactor_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).epsilonFactor = I ^ (k + 1) := rfl

theorem epsilonFactor_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).epsilonFactor = P.epsilonFactor := by
  cases P <;> simp [twist, epsilonFactor]

theorem epsilonFactor_dual (P : RealArchParam) : P.dual.epsilonFactor = P.epsilonFactor := by
  cases P <;> rfl

theorem epsilonFactor_principal_sq (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).epsilonFactor ^ 2 = signEpsilon a₁ ^ 2 * signEpsilon a₂ ^ 2 :=
  mul_pow _ _ _

theorem epsilonFactor_discrete_sq (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).epsilonFactor ^ 2 = (-1) ^ (k + 1) := by
  rw [epsilonFactor_discrete, ← pow_mul, mul_comm, pow_mul, I_sq]

theorem epsilonFactor_oddArtin : RealArchParam.oddArtin.epsilonFactor = I := by
  simp [RealArchParam.oddArtin, epsilonFactor]

end RealArchParam

namespace ComplexArchParam

def epsilonFactor (P : ComplexArchParam) : ℂ :=
  I ^ P.k₁.natAbs * I ^ P.k₂.natAbs

theorem epsilonFactor_twist_zero (P : ComplexArchParam) (u : ℂ) :
    (P.twist u 0).epsilonFactor = P.epsilonFactor := by
  simp [twist, epsilonFactor]

theorem epsilonFactor_dual (P : ComplexArchParam) : P.dual.epsilonFactor = P.epsilonFactor := by
  simp [dual, epsilonFactor, Int.natAbs_neg]

theorem epsilonFactor_mul_epsilonFactor_dual (P : ComplexArchParam) :
    P.epsilonFactor * P.dual.epsilonFactor = (-1) ^ (P.k₁.natAbs + P.k₂.natAbs) := by
  rw [epsilonFactor_dual, epsilonFactor, ← pow_add, ← pow_add,
    show P.k₁.natAbs + P.k₂.natAbs + (P.k₁.natAbs + P.k₂.natAbs) = 2 * (P.k₁.natAbs + P.k₂.natAbs) by ring,
    pow_mul, I_sq]

theorem epsilonFactor_trivialArtin : ComplexArchParam.trivialArtin.epsilonFactor = 1 := by
  simp [ComplexArchParam.trivialArtin, epsilonFactor]

end ComplexArchParam

end LanglandsTunnell

end



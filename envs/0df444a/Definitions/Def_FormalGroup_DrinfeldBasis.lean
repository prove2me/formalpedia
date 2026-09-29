-- Prove2me | Definitions.Def_FormalGroup_DrinfeldBasis
-- name    : FormalGroup_DrinfeldBasis
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/817e402f-4577-5317-b5f2-3d6bf2c4e913
-- title:
--   Drinfeld bases of level q on a formal group
-- statement:
--   Throughout, $T$ is a commutative ring carrying a uniform structure and $F$ is a one‑dimensional formal group law over $T$, i.e. a two‑variable power series $F(X,Y)$ satisfying the formal group axioms. Evaluation of $F$ at points of $T$ and the iterated sums $[n]_F x$ are taken from the companion formal‑group module: `eval` evaluates $F$ through `MvPowerSeries.eval₂` for the given uniformity, `evalNSMul` is defined by $[0]_F x = 0$ and $[n+1]_F x = F([n]_F x, x)$, and `nthSeries` is the multiplication series $[n]_F(Z)$, defined by $[0]_F(Z)=0$ and $[n+1]_F(Z) = F([n]_F(Z), Z)$.
--
--   Four notions are defined. `linComb F x₀ x₁ a b` is the element $[a]_F x_0 +_F [b]_F x_1$ of $T$, for natural numbers $a,b$. `drinfeldDivisor F q x₀ x₁` is the power series $\prod_{a<q}\prod_{b<q}\bigl(Z - ([a]_F x_0 +_F [b]_F x_1)\bigr)$, a monic polynomial of degree $q^2$ regarded in $T[[Z]]$. `IsDrinfeldBasis F q x₀ x₁` is the predicate asserting the existence of a unit $u \in T[[Z]]^{\times}$ with $[q]_F(Z) = u(Z)\cdot\prod_{a,b<q}(Z - ([a]_F x_0 +_F [b]_F x_1))$; thus it is an equality of divisors, stated as a factorisation of the chosen multiplication series. `baseAct F g x₀ x₁`, for a $2\times 2$ matrix $g$ of natural numbers, returns the pair $\bigl([g_{00}]_F x_0 +_F [g_{10}]_F x_1,\ [g_{01}]_F x_0 +_F [g_{11}]_F x_1\bigr)$.
--
--   The structure `DrinfeldLevel F q e ζ` packages a pair $x_0,x_1 \in T$ together with, as fields, a proof that it is a Drinfeld basis of level $q$ and a proof that $e\,x_0\,x_1 = \zeta$; here the pairing $e : T \to T \to T$ and the value $\zeta \in T$ are parameters of the structure, with no property of $e$ imposed.
--
--   A second section repeats `linComb`, `drinfeldDivisor`, `IsDrinfeldBasis` and `baseAct` for a commutative ring $T$ with no ambient uniformity, each taking an ideal $I \subseteq T$ and using the $I$‑adic uniformity; `isDrinfeldBasisAdic_iff` restates the adic predicate as the existence of a unit $u$ with $[q]_F(Z) = u \cdot$ (the adic Drinfeld divisor).
--
--   **Relation to Mathlib.** The structure `FormalGroup`, power‑series substitution and evaluation, and the `WithIdeal` mechanism for the $I$‑adic uniformity are Mathlib's; evaluation of $F$ at ring elements, the multiplication series $[n]_F$, and the notion of a Drinfeld basis and of a level structure are the project's own.
--
--   **Where it is used.** These definitions give the formal‑local form of a Drinfeld $\Gamma(q)$‑structure, as met on the deformation ring of a formal group of height two, and serve as the local model for full level structures on modular curves used in the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FormalGroup_DrinfeldBasis.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace FormalGroup

variable {T : Type*} [CommRing T] [UniformSpace T]

def linComb (F : FormalGroup T) (x₀ x₁ : T) (a b : ℕ) : T :=
  F.eval (F.evalNSMul a x₀) (F.evalNSMul b x₁)

def drinfeldDivisor (F : FormalGroup T) (q : ℕ) (x₀ x₁ : T) : PowerSeries T :=
  ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (F.linComb x₀ x₁ a b))

def IsDrinfeldBasis (F : FormalGroup T) (q : ℕ) (x₀ x₁ : T) : Prop :=
  ∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * F.drinfeldDivisor q x₀ x₁

def baseAct (F : FormalGroup T) (g : Matrix (Fin 2) (Fin 2) ℕ) (x₀ x₁ : T) : T × T :=
  (F.linComb x₀ x₁ (g 0 0) (g 1 0), F.linComb x₀ x₁ (g 0 1) (g 1 1))

structure DrinfeldLevel (F : FormalGroup T) (q : ℕ) (e : T → T → T) (ζ : T) where

  x₀ : T

  x₁ : T

  isDrinfeldBasis : F.IsDrinfeldBasis q x₀ x₁

  pairing_eq : e x₀ x₁ = ζ

section Adic

variable {T : Type*} [CommRing T]

def linCombAdic (F : FormalGroup T) (I : Ideal T) (x₀ x₁ : T) (a b : ℕ) : T :=
  letI : WithIdeal T := ⟨I⟩
  F.linComb x₀ x₁ a b

def drinfeldDivisorAdic (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) : PowerSeries T :=
  letI : WithIdeal T := ⟨I⟩
  F.drinfeldDivisor q x₀ x₁

def IsDrinfeldBasisAdic (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) : Prop :=
  letI : WithIdeal T := ⟨I⟩
  F.IsDrinfeldBasis q x₀ x₁

def baseActAdic (F : FormalGroup T) (I : Ideal T) (g : Matrix (Fin 2) (Fin 2) ℕ) (x₀ x₁ : T) : T × T :=
  letI : WithIdeal T := ⟨I⟩
  F.baseAct g x₀ x₁

theorem isDrinfeldBasisAdic_iff (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) :
    F.IsDrinfeldBasisAdic I q x₀ x₁ ↔
      ∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * F.drinfeldDivisorAdic I q x₀ x₁ :=
  Iff.rfl

end Adic

end FormalGroup

end



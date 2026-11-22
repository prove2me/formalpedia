-- Prove2me | Definitions.Def_ZInQLiterature
-- name    : ZInQLiterature
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T20:06:32.237+00:00
-- url     : https://prove2.me/theorems/062be642-713c-4e38-9dec-52541e1f3268
-- title:
--   Literature predicates: $L$-series continuations, Gross–Zagier, TYZ, and CR$_3$
-- statement:
--   This bundle defines the literature-level predicates over Mathlib's $L$-series of an elliptic curve, with the genus-sum definitions inlined. $\mathrm{IsLContinuation}(E,F)$ says $F$ is an entire function agreeing with $E$'s $L$-series on $\Re s>3/2$. The completed $L$-function is $\Lambda(s)=N^{s/2}(2\pi)^{-s}\Gamma(s)F(s)$. Gross–Zagier (positive-rank half) says a simple zero at $s=1$ forces a point of infinite order. Hecke continuation gives an entire continuation for $C_d$ ($d\ne 0$); the functional equation has conductor $32d^2$ and root number $-1$ on $0<\Re s<2$. TYZ Theorem 3.5(2) in reading A says order $\ge 2$ at $s=1$ forces both genus sums $T_{5a},T_{5b}$ even; row 5b says odd $T_{5b}$ gives order $\le 1$. Finally CR$_3^{\mathrm{TYZ\_Cl,Rk}}$ says odd $T_{5b}(d)$ gives a point of infinite order on $C_d:y^2=x^3-d^2x$ for squarefree $d\equiv 5\pmod 8$.
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/Hypotheses/CR3Literature.lean#L36-L180

import Mathlib
import Mathlib.Algebra.QuadraticAlgebra.Basic

noncomputable section

open NumberField

namespace ZInQ.RouteK.Rank5b

/-- The field Q(sqrt(-n)), as Mathlib's quadratic algebra. -/
abbrev QNeg (n : ℕ) : Type := QuadraticAlgebra ℚ (-(n : ℚ)) 0

/-- No rational r satisfies r^2 = -n (for n != 0); this is the Fact the
QuadraticAlgebra field instance requires at this Mathlib pin. -/
instance QNeg.factNoRoot (n : ℕ) [NeZero n] : Fact (∀ r : ℚ, r ^ 2 ≠ -(n : ℚ) + 0 * r) := by
  refine ⟨fun r hr => ?_⟩
  have h0 : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [zero_mul, add_zero] at hr
  nlinarith [sq_nonneg r]

instance QNeg.numberField (n : ℕ) [NeZero n] : NumberField (QNeg n) where

/-- d_B = product of the primes in B. -/
def dProd {d : ℕ} (B : Finset d.primeFactors) : ℕ := ∏ p ∈ B, (p : ℕ)

instance neZero_dProd {d : ℕ} (B : Finset d.primeFactors) : NeZero (dProd B) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun p _ => (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

/-- TYZ's genus class number g(n) = #(2 Cl(Q(sqrt(-n)))). -/
def gCl (n : ℕ) [NeZero n] : ℕ :=
  Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range

/-- Admissibility for row 5b: one block = 7, one block = 3, all blocks 7, 3 or 1 mod 8. -/
def Admissible5bNat (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) : Prop :=
  (P.parts.filter fun B => dProd B % 8 = 7).card = 1 ∧
  (P.parts.filter fun B => dProd B % 8 = 3).card = 1 ∧
  ∀ B ∈ P.parts, dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1

instance (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) :
    Decidable (Admissible5bNat d P) := by
  unfold Admissible5bNat; infer_instance

/-- The genus sum of row 5b with TYZ's class-number g. -/
def T5bCl (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5bNat d P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

end ZInQ.RouteK.Rank5b

open WeierstrassCurve

namespace ZInQ.Literature

open ZInQ.RouteK.Rank5b

/-- F is an entire continuation of L(E, s) from the half-plane Re s > 3/2. -/
def IsLContinuation (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

/-- Admissibility for T_5a: exactly one block = 5 mod 8, all others = 1 or 5 mod 8. -/
def Admissible5aNat (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) : Prop :=
  (P.parts.filter fun B => dProd B % 8 = 5).card = 1 ∧
  ∀ B ∈ P.parts, dProd B % 8 = 5 ∨ dProd B % 8 = 1

instance (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) :
    Decidable (Admissible5aNat d P) := by
  unfold Admissible5aNat; infer_instance

/-- TYZ's first sum T_5a(d) with g = #2Cl. -/
noncomputable def T5aCl (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5aNat d P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-- The completed L-function Lambda(s) = N^{s/2} (2 pi)^{-s} Gamma(s) F(s). -/
noncomputable def completedL (N : ℕ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s

/-- Gross-Zagier (positive-rank half): a simple zero of L(E,s) at s=1 gives infinite order. -/
def GrossZagier : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → ∀ F : ℂ → ℂ, IsLContinuation E F →
    analyticOrderAt F 1 = 1 → ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P

/-- Root number -1 for C_d, d = 5 mod 8: the continuation vanishes at s=1. -/
def RootNumberVanishing : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (WeierstrassCurve.mk 0 0 0 (-(d : ℚ) ^ 2) 0) F → F 1 = 0

/-- TYZ row 5b: odd genus sum gives order of vanishing at most 1. -/
def TYZRow5b : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 →
    ∃ F : ℂ → ℂ, IsLContinuation (WeierstrassCurve.mk 0 0 0 (-(d : ℚ) ^ 2) 0) F ∧ analyticOrderAt F 1 ≤ 1

/-- Hecke: L(C_d, s) has an entire continuation for d != 0. -/
def HeckeContinuation : Prop :=
  ∀ d : ℕ, d ≠ 0 → ∃ F : ℂ → ℂ, IsLContinuation (WeierstrassCurve.mk 0 0 0 (-(d : ℚ) ^ 2) 0) F

/-- TYZ Theorem 3.5(2), reading A, case L(n)=0: order >= 2 forces both genus sums even. -/
def TYZThm35ReadingA : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (WeierstrassCurve.mk 0 0 0 (-(d : ℚ) ^ 2) 0) F → 2 ≤ analyticOrderAt F 1 →
      T5aCl d = 0 ∧ T5bCl d = 0

/-- Functional equation of L(C_d,s), conductor 32 d^2, root number -1, on 0 < Re s < 2. -/
def FunctionalEquation5 : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (WeierstrassCurve.mk 0 0 0 (-(d : ℚ) ^ 2) 0) F →
      ∀ s : ℂ, 0 < s.re → s.re < 2 →
        completedL (32 * d ^ 2) F (2 - s) = -completedL (32 * d ^ 2) F s

end ZInQ.Literature

namespace ZInQ.RouteK.Rank

open WeierstrassCurve ZInQ.RouteK.Rank5b

/-- CR_3^{TYZ_Cl,Rk}: odd genus sum gives a point of infinite order on C_d. -/
def CertifiedRankTYZClRk : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 →
    ∃ P : (WeierstrassCurve.mk 0 0 0 (-(d : ℚ) ^ 2) 0).toAffine.Point, ¬IsOfFinAddOrder P

end ZInQ.RouteK.Rank



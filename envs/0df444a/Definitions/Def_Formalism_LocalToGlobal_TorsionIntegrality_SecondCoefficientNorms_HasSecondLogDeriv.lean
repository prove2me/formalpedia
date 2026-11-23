-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_HasSecondLogDeriv
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_HasSecondLogDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:05.581186+00:00
-- url     : https://prove2.me/theorems/d850eb71-afa9-4600-a9a6-8d9998cacb6b
-- title:
--   Has Second Log Deriv
-- statement:
--   Definitions and structural lemmas for Has Second Log Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/HasSecondLogDeriv.lean

import Mathlib
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
namespace Formalism.L2.Th1.C
section Basic
variable {K : Type} [Field K] {σ : Type}
def IntMv (R : Subring K) (f : MvPowerSeries σ K) : Prop :=
  ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n f ∈ R
def IntPS (R : Subring K) (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n f ∈ R
def mvExp [CharZero K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst f (PowerSeries.exp K)
def LG [CharZero K] (R : Subring K) (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ IntMv R (mvExp f)
def Cong [CharZero K] (R : Subring K) (f g : MvPowerSeries σ K) : Prop := LG R (f - g)
def IsPt (R : Subring K) (a : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff a = 0 ∧ IntMv R a
def IsOneUnit (R : Subring K) (f : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff f = 1 ∧ IntPS R f
def binom (z : K) (n : ℕ) : K := (∏ i ∈ Finset.range n, (z - (i : K))) / (n.factorial : K)
def IsBinomScalar (R : Subring K) (z : K) : Prop := ∀ n : ℕ, binom z n ∈ R
end Basic
section ZSide
variable {K : Type} [Field K]
def dblInt (e : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => if n < 2 then 0 else PowerSeries.coeff (n - 2) e / ((n : K) * ((n : K) - 1))
def lam (e : PowerSeries K) (s2 : K) : PowerSeries K :=
  dblInt e + PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2
def sgStar [CharZero K] (e : PowerSeries K) (s2 : K) : PowerSeries K :=
  PowerSeries.X * mvExp (-(lam e s2))
def wpShift (e : PowerSeries K) (c : K) : PowerSeries K :=
  1 + PowerSeries.X ^ 2 * (e - PowerSeries.C c)
def HasSecondLogDeriv (f g : PowerSeries K) : Prop :=
  PowerSeries.derivative K (PowerSeries.derivative K f) * f - (PowerSeries.derivative K f) ^ 2
    = g * f ^ 2
def IsEndoZ (e : PowerSeries K) {ι : Type} [Fintype ι] (neg : ι → ι) (c : ι → K)
    (w : ι → PowerSeries K) (al : K) : Prop :=
  (∀ P, neg (neg P) = P) ∧
  (∀ P, HasSecondLogDeriv (wpShift e (c P)) (2 * e - w P - w (neg P))) ∧
  PowerSeries.C (al ^ 2) * PowerSeries.rescale al e = e + ∑ P, (w P - PowerSeries.C (c P))
def IsogenyFormula [CharZero K] (e : PowerSeries K) (s2 : K) {ι : Type} [Fintype ι] (c : ι → K)
    (al : K) : Prop :=
  (PowerSeries.rescale al (sgStar e s2)) ^ 2 * PowerSeries.X ^ (2 * Fintype.card ι) =
    PowerSeries.C (al ^ 2) * (sgStar e s2) ^ (2 * (Fintype.card ι + 1)) * ∏ P, wpShift e (c P)
end ZSide
section USide
variable {K : Type} [Field K] {σ : Type}
def IsLogPair (l linv : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff l = 0 ∧ PowerSeries.coeff 1 l = 1 ∧
  PowerSeries.constantCoeff linv = 0 ∧
  PowerSeries.subst l linv = PowerSeries.X ∧ PowerSeries.subst linv l = PowerSeries.X
def mulBy (l linv : PowerSeries K) (a : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C a * l) linv
def fadd (l linv : PowerSeries K) (a b : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) linv
def fmul (l linv : PowerSeries K) (α : K) (a : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst (MvPowerSeries.C α * PowerSeries.subst a l) linv
def be0 (l linv ph : PowerSeries K) (a b : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst (fadd l linv a b) ph - PowerSeries.subst a ph - PowerSeries.subst b ph
def FGInt (R : Subring K) (l linv : PowerSeries K) : Prop :=
  IntMv R (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))
def IsPh [CharZero K] (e : PowerSeries K) (s2 : K) (l ph : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff ph = 0 ∧
  PowerSeries.X * mvExp (-ph) = PowerSeries.subst l (sgStar e s2)
def XIsWp (e l A : PowerSeries K) (c0 : K) : Prop :=
  (A + PowerSeries.C c0 * PowerSeries.X ^ 2) * l ^ 2 =
    PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e 0)
end USide
end Formalism.L2.Th1.C



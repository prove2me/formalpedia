-- Prove2me | Definitions.Def_FormalGroup_NSeries
-- name    : FormalGroup_NSeries
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/4d89b815-db4f-5968-aee3-db4f76797dc2
-- title:
--   Multiplication-by-n series and invariant differential of a formal group
-- statement:
--   Throughout, $R$ is a commutative ring and $F : \mathtt{FormalGroup } R$ a one-dimensional formal group law, i.e. a power series $F \in R[[X_0,X_1]]$ (Mathlib's `toPowerSeries`, an `MvPowerSeries (Fin 2) R`) with vanishing constant term, linear part $X_0+X_1$, and the associativity identity. Two evaluation maps are introduced for a commutative $R$-algebra $A$ equipped with a uniform structure: [`FormalGroup.eval F x y`](../def/FormalGroup_NSeries.html#L19) is the value $F(x,y)$, obtained as `MvPowerSeries.eval₂` of $F$ along $\mathrm{algebraMap}\,R\,A$ at the pair $(x,y)$, with $R$ given the discrete uniformity, and [`FormalGroup.evalSeries f x`](../def/FormalGroup_NSeries.html#L85) is the analogous one-variable evaluation of $f \in R[[T]]$ at $x$; [`FormalGroup.eval_eq_eval₂`](../def/FormalGroup_NSeries.html#L23) and `evalSeries_eq_eval₂` record that these agree with `eval₂` whenever $R$ carries any discrete uniformity. The multiplication-by-$n$ series is defined recursively by $[0](T)=0$ and $[n+1](T)=F([n](T),T)$, the substitution being legitimate because each $[n]$ has zero constant term (`constantCoeff_nthSeries`, `hasSubst_nthSeries`); [`FormalGroup.evalNSMul F n x`](../def/FormalGroup_NSeries.html#L96) is the parallel recursion on points, $0$ and $F(\,\cdot\,,x)$ iterated $n$ times. For the invariant differential, [`MvPowerSeries.pderivLin i`](../def/FormalGroup_NSeries.html#L122) is the $R$-linear formal partial derivative $\partial/\partial X_i$, given on coefficients by $d \mapsto (d_i+1)\,\mathrm{coeff}_{d+e_i}$; then `partialX` is $\partial F/\partial X_0$, `invDiffDenom` its specialisation $\partial_X F(0,T) \in R[[T]]$, whose constant coefficient is $1$, and `invDiff` is the inverse power series $\bigl(\partial_X F(0,T)\bigr)^{-1}$, produced by Mathlib's `invOfUnit` with chosen unit $1$; `invDiffDenom_mul_invDiff` and `constantCoeff_invDiff` record that it is indeed a two-sided inverse with constant term $1$. Finally `qFoldSeriesB F q` is the series whose $k$-th coefficient is that of $[q](T)$ when $q \mid k$ and $k \ge q$, and $0$ otherwise, with `coeff_qFoldSeriesB` reading off its coefficients.
--
--   **Relation to Mathlib.** Mathlib's `FormalGroup` carries no multiplication-by-$n$ series and no invariant differential, and Mathlib has no formal partial derivative on `MvPowerSeries`; these are added here on top of Mathlib's `MvPowerSeries.subst`, `MvPowerSeries.eval₂` and `PowerSeries.invOfUnit`.
--
--   **Where it is used.** These definitions form the power-series side of the analysis of the formal group of a Weierstrass curve near the origin: the series $[q](T)$ and its decomposition through `qFoldSeriesB`, together with the invariant differential, feed the divisibility and congruence statements for $q$-division on the formal group that are used in the study of the Galois representation attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FormalGroup_NSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

noncomputable def eval (F : FormalGroup R) (x y : A) : A :=
  letI : UniformSpace R := ⊥
  MvPowerSeries.eval₂ (algebraMap R A) ![x, y] F.toPowerSeries

theorem eval_eq_eval₂ {R : Type*} [CommRing R] [u : UniformSpace R] [DiscreteUniformity R]
    {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A] (F : FormalGroup R) (x y : A) :
    F.eval x y = MvPowerSeries.eval₂ (algebraMap R A) ![x, y] F.toPowerSeries := by
  obtain rfl : u = ⊥ := DiscreteUniformity.eq_bot
  rfl

variable [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
  [IsTopologicalRing A] [IsLinearTopology A A]

end FormalGroup

end

end

end

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

noncomputable def nthSeries (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst ![F.nthSeries n, PowerSeries.X] F.toPowerSeries

@[simp]
theorem nthSeries_zero (F : FormalGroup R) : F.nthSeries 0 = 0 := rfl

theorem nthSeries_succ (F : FormalGroup R) (n : ℕ) :
    F.nthSeries (n + 1)
      = MvPowerSeries.subst ![F.nthSeries n, PowerSeries.X] F.toPowerSeries := rfl

theorem constantCoeff_nthSeries (F : FormalGroup R) (n : ℕ) :
    PowerSeries.constantCoeff (F.nthSeries n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [nthSeries_succ]
    have hcc : ∀ s : Fin 2, MvPowerSeries.constantCoeff
        ((![F.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R) s) = 0 := by
      intro s
      fin_cases s
      · exact ih
      · exact MvPowerSeries.constantCoeff_X (R := R) ()
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hcc) hcc F.zero_constantCoeff

theorem hasSubst_nthSeries (F : FormalGroup R) (n : ℕ) :
    MvPowerSeries.HasSubst (![F.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
  fin_cases s
  · exact F.constantCoeff_nthSeries n
  · exact MvPowerSeries.constantCoeff_X (R := R) ()

noncomputable def evalSeries (f : PowerSeries R) (x : A) : A :=
  letI : UniformSpace R := ⊥
  PowerSeries.eval₂ (algebraMap R A) x f

theorem evalSeries_eq_eval₂ {R : Type*} [CommRing R] [u : UniformSpace R]
    [DiscreteUniformity R] {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]
    (f : PowerSeries R) (x : A) :
    evalSeries f x = PowerSeries.eval₂ (algebraMap R A) x f := by
  obtain rfl : u = ⊥ := DiscreteUniformity.eq_bot
  rfl

noncomputable def evalNSMul (F : FormalGroup R) : ℕ → A → A
  | 0, _ => 0
  | n + 1, x => F.eval (F.evalNSMul n x) x

@[simp]
theorem evalNSMul_zero (F : FormalGroup R) (x : A) : F.evalNSMul 0 x = 0 := rfl

theorem evalNSMul_succ (F : FormalGroup R) (n : ℕ) (x : A) :
    F.evalNSMul (n + 1) x = F.eval (F.evalNSMul n x) x := rfl

end FormalGroup

end

end

end

section
section

open scoped Classical

namespace MvPowerSeries
variable {σ : Type*} {R : Type*} [CommRing R]

noncomputable def pderivLin (i : σ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun F := (fun d => (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) F :
              MvPowerSeries σ R)
  map_add' F G := by
    funext d
    show (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) (F + G)
       = (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) F
       + (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) G
    rw [map_add, smul_add]
  map_smul' r F := by
    funext d
    show (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) (r • F)
       = r • ((d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) F)
    rw [map_smul, smul_comm]

@[simp] theorem kw_coeff_pderiv (i : σ) (d : σ →₀ ℕ) (F : MvPowerSeries σ R) :
    MvPowerSeries.coeff d (pderivLin i F)
      = (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) F := rfl

end MvPowerSeries

end

end

section
section

noncomputable section

open PowerSeries MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

noncomputable def partialX : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.pderivLin (0 : Fin 2) F.toPowerSeries

theorem constantCoeff_partialX : MvPowerSeries.constantCoeff F.partialX = 1 := by
  unfold partialX
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.kw_coeff_pderiv]
  simpa using F.lin_coeff_X

noncomputable def invDiffDenom : PowerSeries R :=
  MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] F.partialX

theorem hasSubst_invDiff :
    MvPowerSeries.HasSubst (![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    intro s; fin_cases s
    · simp
    · exact MvPowerSeries.constantCoeff_X _)

theorem constantCoeff_invDiffDenom : PowerSeries.constantCoeff F.invDiffDenom = 1 := by
  unfold invDiffDenom
  rw [show (PowerSeries.constantCoeff : PowerSeries R →+* R)
      = MvPowerSeries.constantCoeff (σ := Unit) from rfl,
    MvPowerSeries.constantCoeff_subst hasSubst_invDiff]
  rw [finsum_eq_single _ (0 : Fin 2 →₀ ℕ) (fun d hd => ?_)]
  · simp [F.constantCoeff_partialX, MvPowerSeries.coeff_zero_eq_constantCoeff]
  · rcases Finsupp.ne_iff.mp hd with ⟨i, hi⟩
    rw [Finsupp.prod, map_prod]
    refine smul_eq_zero_of_right _ (Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr hi) ?_)
    have hcc : MvPowerSeries.constantCoeff
        ((![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R) i) = 0 := by
      fin_cases i
      · simp
      · exact MvPowerSeries.constantCoeff_X _
    rw [map_pow, hcc]
    exact zero_pow (by simpa using hi)

noncomputable def invDiff : PowerSeries R :=
  PowerSeries.invOfUnit F.invDiffDenom (1 : Rˣ)

theorem invDiffDenom_mul_invDiff : F.invDiffDenom * F.invDiff = 1 := by
  unfold invDiff
  exact PowerSeries.mul_invOfUnit F.invDiffDenom 1 (by simp [F.constantCoeff_invDiffDenom])

theorem constantCoeff_invDiff : PowerSeries.constantCoeff F.invDiff = 1 := by
  unfold invDiff
  simp [PowerSeries.constantCoeff_invOfUnit]

end FormalGroup

end

end

end

section
section

set_option maxHeartbeats 1200000

noncomputable section
open PowerSeries MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

noncomputable def qFoldSeriesB (q : ℕ) : PowerSeries R :=
  PowerSeries.mk fun k => if q ∣ k ∧ q ≤ k then PowerSeries.coeff k (F.nthSeries q) else 0

theorem coeff_qFoldSeriesB (q k : ℕ) :
    PowerSeries.coeff k (F.qFoldSeriesB q)
      = if q ∣ k ∧ q ≤ k then PowerSeries.coeff k (F.nthSeries q) else 0 :=
  PowerSeries.coeff_mk _ _

end FormalGroup

end

end

end



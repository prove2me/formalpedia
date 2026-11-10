-- Prove2me | Definitions.Def_StableCountSub3_RandomReveal
-- name    : StableCountSub3_RandomReveal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:49:28.193213+00:00
-- url     : https://prove2.me/theorems/ac0c0bea-a967-4d83-b38d-da8e2c11b8ce
-- title:
--   The random-reveal model: priorities, candidate counts $N_m(D,U)$, unrevealed depths $L_m$, $R_m$
-- statement:
--   The model of §3.1. The priorities $U=(U_{m_1},\dots,U_{m_n})$ are independent and uniform on $[0,1]$: `unifCube n` is Lebesgue measure on $[0,1]^n$.
--
--   - $N_m(D,U)=\bigl|\{T_m(E): E\text{ a downset of }\mathcal R,\ T_v(E)=T_v(D)\text{ for all }v\text{ with }U_v<U_m\}\bigr|$ (`numCand`). Ties have probability zero; the strict inequality is the paper's.
--   - $E_{D,U}[f]$ (`avgDU`): $\mu$ uniform on $\Omega$, $D=D(\mu)$, and independently $U$ uniform on $[0,1]^n$, i.e. $\frac1{|\Omega|}\sum_{\mu\in\Omega}\int_{[0,1]^n}f(D(\mu),U)\,dU$, with $|\Omega|$ the published `StableCount.numStable`.
--   - **Maximum unrevealed depths** (Definition 3.6): $L_m(D,U)=\max\{k\ge0: S^-_{m,D}(k)\text{ defined and }U_m<U_v\ \forall v\in S^-_{m,D}(k)\setminus\{m\}\}$, and $R_m(D,U)$ the same with $S^+$. $k=0$ always qualifies, and a defined support has $k\le|\mathcal R|$, so the maximum is taken over $0\le k\le|\mathcal R|$.
--   - `probAt m x E` and `expAt m x f` are probabilities and expectations conditional on $U_m=x$: the other priorities stay independent uniform on $[0,1]$.
--   - `expLogN I D m` is $E_U[\log N_m(D,U)\mid D]$, over all priorities including $U_m$, with $D$ fixed (Lemma 4.5). All logarithms are natural.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), §3.1, p. 12 (PDF 14); Definition 3.6, p. 15 (PDF 17); §3.4, p. 17 (PDF 19); Lemma 4.5, p. 23 (PDF 25)

import Mathlib
import Definitions.Def_StableCount_Count
import Definitions.Def_StableCountSub3_Cones

open StableMatching MeasureTheory

noncomputable section

namespace StableCountSub3

variable {n : ℕ}

/-- The law of the priority vector `U = (U_{m₁}, …, U_{m_n})` (§3.1): independent uniform
variables on `[0, 1]`, i.e. Lebesgue measure on the cube `[0, 1]ⁿ` (a probability measure). -/
def unifCube (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- `N_m(D, U)` (§3.1): the number of distinct values `T_m(E)` over the downsets `E` of `ℛ` that
agree with `D` at every revealed man, i.e. `T_v(E) = T_v(D)` for all `v` with `U_v < U_m`. -/
def numCand (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (U : Fin n → ℝ) : ℕ := by
  classical
  exact (((downsets I).filter fun E => ∀ v, U v < U m → boundary I v E = boundary I v D).image
    (boundary I m)).card

/-- The stable matchings `Ω` of `I`, as a finset. -/
def stableSet (I : Instance n) : Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun μ => I.IsStable μ

/-- `E_{D,U}[f(D, U)]` (§3.1): `μ` uniform on `Ω`, `D = D(μ)`, and independently `U` uniform on
`[0, 1]ⁿ`: `(1/|Ω|) ∑_{μ ∈ Ω} ∫ f(D(μ), U) dU`. -/
def avgDU (I : Instance n) (f : Finset (Rot n) → (Fin n → ℝ) → ℝ) : ℝ :=
  (1 / (StableCount.numStable I : ℝ)) * ∑ μ ∈ stableSet I, ∫ U, f (Dof I μ) U ∂(unifCube n)

/-- Definition 3.6: the maximum unrevealed depth in direction `dir`,
`max {k ≥ 0 : S^dir_{m,D}(k) is defined and U_m < U_v for all v ∈ S^dir_{m,D}(k) \ {m}}`.
`k = 0` always qualifies (`S(0) = {m}`), and a defined support has `k ≤ |ℛ|`, so the maximum is
taken over `k ≤ |ℛ|`. -/
def maxDepth (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) (U : Fin n → ℝ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k => ∃ S, supp I D m dir k = some S ∧ ∀ v ∈ S, v ≠ m → U m < U v) (rotations I).card

/-- Definition 3.6: `L_m(D, U)`, the maximum unrevealed depth backward. -/
def Lm (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (U : Fin n → ℝ) : ℕ :=
  maxDepth I D m .bwd U

/-- Definition 3.6: `R_m(D, U)`, the maximum unrevealed depth forward. -/
def Rm (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (U : Fin n → ℝ) : ℕ :=
  maxDepth I D m .fwd U

/-- Probability of an event of the priority vector conditional on `U_m = x` (§3.4, §4): the other
priorities are independent uniform on `[0, 1]` and `U_m` is set to `x`. -/
def probAt (m : Fin n) (x : ℝ) (E : (Fin n → ℝ) → Prop) : ℝ :=
  (unifCube n {U | E (Function.update U m x)}).toReal

/-- Expectation of a function of the priority vector conditional on `U_m = x` (the other
priorities independent uniform on `[0, 1]`). -/
def expAt (m : Fin n) (x : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ U, f (Function.update U m x) ∂(unifCube n)

/-- `E_U[log N_m(D, U) | D]` (Lemma 4.5): the expectation over all priorities, including `U_m`,
with `D` fixed. -/
def expLogN (I : Instance n) (D : Finset (Rot n)) (m : Fin n) : ℝ :=
  ∫ U, Real.log (numCand I D m U) ∂(unifCube n)

end StableCountSub3



-- Prove2me | Definitions.Def_PrecDTree_Main_Rounding
-- name    : PrecDTree_Main_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:50:31.707003+00:00
-- url     : https://prove2.me/theorems/0755e989-eebf-4c14-856f-33c9c4844e44
-- title:
--   The random construction of Theorem 4.2's proof: γ, R⁺, S₀, B′, groups, coins, C, R, M, W and the potential Φ (14)
-- statement:
--   Fix an instance, a guess $K$ and a feasible LP point. Put $\gamma=m^{1/3}$, $R^+=\{r: y_r\ge 1/\gamma\}$, $R'_S=R_S\setminus R^+$, $\mathcal S_0=\{S:R'_S=\emptyset\}$, $B'=B\setminus\mathrm{cov}(\mathcal S_0)$. For each scale $d=2^j\le|R|$, $\mathcal S_d=\{S: d\le|R'_S|<2d\}$ and, for $r\in R\setminus R^+$ with $y_r>0$, the group $\mathcal S_{r,d}=\{S\in\mathcal S_d: r\in R'_S\}$. Independent coins: activation $A_{r,d}$ with probability $y_r/d$; trial $T_{r,d,S}$ ($S\in\mathcal S_{r,d}$) with probability $x_S/y_r$; mark $Z_{r,d,S,u}$ ($u\in B_S\cap B'$) with probability $a_{u,S}/x_S$, always $0$ if $x_S=0$. Then $\mathcal F_{r,d}=\{S\in\mathcal S_{r,d}: A_{r,d}, T_{r,d,S}\}$, $\mathcal C=\mathcal S_0\cup\bigcup\mathcal F_{r,d}$, $R_{r,d}=\bigcup_{S\in\mathcal F_{r,d}}R'_S$, $R_0=\bigcup R_{r,d}$, $R=|R^+|+|R_0|$; $M_{r,d,S}=\{u\in B_S\cap B': T_{r,d,S},\ Z_{r,d,S,u}=1\}$, $M_{r,d}=\bigcup_{S\in\mathcal F_{r,d}}M_{r,d,S}$, $\mathbf M=\bigcup M_{r,d}$, $M=|\mathbf M|$; $W_{r,d}=\mathbf 1_{A_{r,d}}\sum_{S\in\mathcal S_{r,d}}|M_{r,d,S}|$, $W=\sum W_{r,d}$, and the potential
--   $$\Phi=M-\frac{W^2}{72\,t}-\frac{7\,t\,R}{360\,K\,\gamma}-\frac t8 .\qquad(14)$$
--
--   **Formalization Note.** $\gamma$ is the real power `(m : ℝ) ^ (1/3)`; $R^+$ is written $1\le\gamma\,y_r$. A scale is indexed by `j : Fin k` ($2^j\le k$ forces $j<k$). The coins are indexed by `Coin I`; an outcome is `ω : Coin I → Bool`, its probability `prob` is the product of the Bernoulli laws `coinProb` (coins that do not occur have probability $0$), and `expect X = Σ_ω prob ω · X ω`. `Cout`, `Rval`, `Mval`, `Wval`, `Phi s K` are $\mathcal C$, $R$, $M$, $W$, $\Phi$.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), pp. 10–15, §4.1, proof of Theorem 4.2

import Mathlib
import Definitions.Def_PrecDTree_Main_RBSC

set_option autoImplicit false

/-!
# The random construction of the proof of Theorem 4.2 (pp. 10–15)

Szyfelbein, Dereniowski, *Precedence-Constrained Decision Trees and Coverings*, arXiv:2602.21312
(STOC 2027 submission version), pp. 10–15, §4.1: `γ`, `R⁺`, `R'_S`, `S₀`, `B'`, scales, groups,
the activation, trial and marking coins, `F_{r,d}`, `C`, `R_{r,d}`, `R₀`, `R`, `M_{r,d,S}`,
`M_{r,d}`, `M`, `W_{r,d}`, `W` and the potential `Φ` of (14).

Conventions.
* `γ = m^{1/3}` (real cube root). `R⁺ = {r : y_r ≥ 1/γ}` is written `1 ≤ γ · y_r`.
* A scale `d = 2^j` is indexed by `j : Fin k` (every power of two `≤ k` has `j < k`); the group
  `S_{r,d}` exists iff `r ∉ R⁺`, `y_r > 0` and `2^j ≤ k`.
* The coins form a finite family indexed by `Coin I`; an outcome is `ω : Coin I → Bool`. Each coin
  is an independent Bernoulli variable with the success probability `coinProb` (`y_r/d`, `x_S/y_r`,
  `a_{u,S}/x_S`; coins that do not occur in the construction have probability `0`, and a marking
  coin of a set with `x_S = 0` is always zero). The law of `ω` is the product law `prob`, and
  `expect X = Σ_ω prob ω · X ω` is the expectation.
-/

namespace PrecDTree.Main

open Classical

namespace RBInstance

variable (I : RBInstance) (s : LPSol I)

/-- `γ = m^{1/3}`. -/
noncomputable def gamma : ℝ := (I.m : ℝ) ^ ((1 : ℝ) / 3)

/-- `R⁺ = {r ∈ R : y_r ≥ 1/γ}`. -/
noncomputable def Rplus : Finset (Fin I.k) :=
  Finset.univ.filter (fun r => 1 ≤ I.gamma * s.y r)

/-- The residual red part `R'_S = R_S \ R⁺`. -/
noncomputable def resid (S : Fin I.m) : Finset (Fin I.k) := I.red S \ I.Rplus s

/-- `S₀ = {S : R'_S = ∅}`. -/
noncomputable def S0 : Finset (Fin I.m) := Finset.univ.filter (fun S => I.resid s S = ∅)

/-- `B' = B \ cov(S₀)`. -/
noncomputable def Bprime : Finset (Fin I.n) := Finset.univ \ I.blueCov (I.S0 s)

/-- The scale `d = 2^j`. -/
def scale (j : Fin I.k) : ℕ := 2 ^ (j : ℕ)

/-- `S_d = {S : d ≤ |R'_S| < 2d}`. -/
noncomputable def Sd (j : Fin I.k) : Finset (Fin I.m) :=
  Finset.univ.filter (fun S => I.scale j ≤ (I.resid s S).card ∧ (I.resid s S).card < 2 * I.scale j)

/-- The group `S_{r,d}` exists: `r ∈ R \ R⁺`, `y_r > 0`, and `d = 2^j ≤ |R|`. -/
def IsGroup (r j : Fin I.k) : Prop := r ∉ I.Rplus s ∧ 0 < s.y r ∧ 2 ^ (j : ℕ) ≤ I.k

/-- `S_{r,d} = {S ∈ S_d : r ∈ R'_S}`. -/
noncomputable def group (r j : Fin I.k) : Finset (Fin I.m) :=
  (I.Sd s j).filter (fun S => r ∈ I.resid s S)

/-- The existing groups `(r, j)`. -/
noncomputable def groups : Finset (Fin I.k × Fin I.k) :=
  Finset.univ.filter (fun p => I.IsGroup s p.1 p.2)

/-- Coin indices: activation `A_{r,d}`, trial `T_{r,d,S}`, mark `Z_{r,d,S,u}`. -/
abbrev Coin : Type :=
  (Fin I.k × Fin I.k) ⊕ (Fin I.k × Fin I.k × Fin I.m) ⊕ (Fin I.k × Fin I.k × Fin I.m × Fin I.n)

/-- Success probability of each coin: `Pr[A_{r,d}] = y_r/d`, `Pr[T_{r,d,S}] = x_S/y_r` for
`S ∈ S_{r,d}`, `Pr[Z_{r,d,S,u} = 1] = a_{u,S}/x_S` for `u ∈ B_S ∩ B'` and `x_S > 0`; `0` for a coin
that does not occur. -/
noncomputable def coinProb : I.Coin → ℝ
  | .inl (r, j) => if I.IsGroup s r j then s.y r / (I.scale j : ℝ) else 0
  | .inr (.inl (r, j, S)) =>
      if I.IsGroup s r j ∧ S ∈ I.group s r j then s.x S / s.y r else 0
  | .inr (.inr (r, j, S, u)) =>
      if I.IsGroup s r j ∧ S ∈ I.group s r j ∧ u ∈ I.blue S ∧ u ∈ I.Bprime s ∧ 0 < s.x S then
        s.a u S / s.x S else 0

/-- Probability of an outcome under the product of the independent coin laws. -/
noncomputable def prob (ω : I.Coin → Bool) : ℝ :=
  ∏ c : I.Coin, if ω c then I.coinProb s c else 1 - I.coinProb s c

/-- Expectation `E[X]` under the product law. -/
noncomputable def expect (X : (I.Coin → Bool) → ℝ) : ℝ :=
  ∑ ω : I.Coin → Bool, I.prob s ω * X ω

/-- The event `A_{r,d}`: the group exists and is activated. -/
def Act (ω : I.Coin → Bool) (r j : Fin I.k) : Prop := I.IsGroup s r j ∧ ω (.inl (r, j)) = true

/-- The event `T_{r,d,S}`: the trial of `S` in group `S_{r,d}` succeeds. -/
def Trial (ω : I.Coin → Bool) (r j : Fin I.k) (S : Fin I.m) : Prop := ω (.inr (.inl (r, j, S))) = true

/-- `Z_{r,d,S,u} = 1` (always zero when `x_S = 0`). -/
def Mark (ω : I.Coin → Bool) (r j : Fin I.k) (S : Fin I.m) (u : Fin I.n) : Prop :=
  0 < s.x S ∧ ω (.inr (.inr (r, j, S, u))) = true

/-- `F_{r,d} = {S ∈ S_{r,d} : A_{r,d} and T_{r,d,S} occur}`. -/
noncomputable def F (ω : I.Coin → Bool) (r j : Fin I.k) : Finset (Fin I.m) :=
  (I.group s r j).filter (fun S => I.Act s ω r j ∧ I.Trial ω r j S)

/-- The output `C = S₀ ∪ ⋃_{r,d} F_{r,d}`. -/
noncomputable def Cout (ω : I.Coin → Bool) : Finset (Fin I.m) :=
  I.S0 s ∪ (I.groups s).biUnion (fun p => I.F s ω p.1 p.2)

/-- `R_{r,d} = ⋃_{S ∈ F_{r,d}} R'_S`. -/
noncomputable def Rrd (ω : I.Coin → Bool) (r j : Fin I.k) : Finset (Fin I.k) :=
  (I.F s ω r j).biUnion (I.resid s)

/-- `R₀ = ⋃_{r,d} R_{r,d}`. -/
noncomputable def R0 (ω : I.Coin → Bool) : Finset (Fin I.k) :=
  (I.groups s).biUnion (fun p => I.Rrd s ω p.1 p.2)

/-- `R = |R⁺| + |R₀|`. -/
noncomputable def Rval (ω : I.Coin → Bool) : ℕ := (I.Rplus s).card + (I.R0 s ω).card

/-- `M_{r,d,S} = {u ∈ B_S ∩ B' : T_{r,d,S} occurs and Z_{r,d,S,u} = 1}`. -/
noncomputable def Mrds (ω : I.Coin → Bool) (r j : Fin I.k) (S : Fin I.m) : Finset (Fin I.n) :=
  (I.blue S ∩ I.Bprime s).filter (fun u => I.Trial ω r j S ∧ I.Mark s ω r j S u)

/-- `M_{r,d} = ⋃_{S ∈ F_{r,d}} M_{r,d,S}`. -/
noncomputable def Mrd (ω : I.Coin → Bool) (r j : Fin I.k) : Finset (Fin I.n) :=
  (I.F s ω r j).biUnion (I.Mrds s ω r j)

/-- The set `M = ⋃_{r,d} M_{r,d}` of distinct marked blue elements. -/
noncomputable def Mset (ω : I.Coin → Bool) : Finset (Fin I.n) :=
  (I.groups s).biUnion (fun p => I.Mrd s ω p.1 p.2)

/-- `M = |M|`. -/
noncomputable def Mval (ω : I.Coin → Bool) : ℕ := (I.Mset s ω).card

/-- `W_{r,d} = 1_{A_{r,d}} · Σ_{S ∈ S_{r,d}} |M_{r,d,S}|`. -/
noncomputable def Wrd (ω : I.Coin → Bool) (r j : Fin I.k) : ℕ :=
  if I.Act s ω r j then ∑ S ∈ I.group s r j, (I.Mrds s ω r j S).card else 0

/-- `W = Σ_{r,d} W_{r,d}`. -/
noncomputable def Wval (ω : I.Coin → Bool) : ℕ := ∑ p ∈ I.groups s, I.Wrd s ω p.1 p.2

/-- The potential (14): `Φ = M − W²/(72 t) − 7 t R/(360 K γ) − t/8`. -/
noncomputable def Phi (K : ℕ) (ω : I.Coin → Bool) : ℝ :=
  (I.Mval s ω : ℝ) - (I.Wval s ω : ℝ) ^ 2 / (72 * (I.t : ℝ))
    - 7 * (I.t : ℝ) * (I.Rval s ω : ℝ) / (360 * (K : ℝ) * I.gamma) - (I.t : ℝ) / 8

end RBInstance

end PrecDTree.Main



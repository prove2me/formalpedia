-- Prove2me | Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP
-- name    : HarmonicRanking_Main_Supplement_PriceLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:46:03.651457+00:00
-- url     : https://prove2.me/theorems/3358d394-baf7-4471-8ba7-bcc31ad6136b
-- title:
--   Mahdian–Yan program $\mathrm{polyLP}'(m)$, price tables and $R_m(F)$
-- statement:
--   Fix $m\ge1$. This file defines the linear-programming objects of Appendices A.2 and B (pp. 31–32, 38).
--
--   1. Variables $x(\ell,r,p)\ge0$, $\ell,r,p\in[m]$, with cumulative rows $y(\ell,r,p)=\sum_{h=1}^{\ell}x(h,r,p)$ and row masses $W_{\ell r}=\sum_{p=1}^m x(\ell,r,p)$. The program $\mathrm{polyLP}'(m)$ minimizes $\frac1m\sum_{\ell,r,p}x(\ell,r,p)$ (49) subject to
--   $$\begin{aligned}
--   &y(\ell,r,\ell)+y(r,\ell,p)\ge \tfrac1m &&(\ell,r,p\in[m]), &(50)\\
--   &y(\ell+1,r,p+1)\ge y(\ell,r,p) &&(p\le\ell<m), &(51)\\
--   &y(\ell,r,p)=y(\ell,r,\ell+1) &&(\ell<p), &(52)\\
--   &y(\ell+1,r,p)\ge y(\ell,r,\ell+1) &&(p\le\ell<m), &(53)\\
--   &W_{\ell r}=W_{r\ell} &&(\ell,r\in[m]). &(54)
--   \end{aligned}$$
--   $\mathrm{val}(\mathrm{polyLP}'(m))$ is its optimal value. $C_m$ is the region cut out by $x\ge0$ and (50)–(53) without (54), and $\hat C_m$ adds $0\le y(\ell,r,p)\le 1/m$.
--   2. $D_m=\{F\in\mathbb R^{m\times m}:F_{\ell r}+F_{r\ell}=1\}$ and, by (56), $A_m=\{F\in D_m:0\le F_{\ell r}\le1,\ F_{\ell r}\ge F_{\ell+1,r},\ F_{\ell r}\le F_{\ell,r+1}\}$. For an arbitrary real table $F$, (55) is
--   $$R_m(F)=\inf_{(x,y)\in C_m}\frac2m\sum_{\ell,r,p}F_{\ell r}\,x(\ell,r,p)\in[-\infty,\infty).$$
--   3. With $M_{\ell r}=\sum_p m\,x(\ell,r,p)$ (74), the intervals $I_m=\{[\ell,r]:1\le\ell<r\le m\}$ ordered by inclusion, $h_I=2F_{\ell r}-1$ and $\delta_I=M_{\ell r}-M_{r\ell}$ for $I=[\ell,r]$, equation (75) is $\sigma(\delta)=\max_{U}\sum_{I\in U}\delta_I$ over upward-closed families $U\subseteq I_m$ (the empty family included). The order polytope is $\{h:0\le h_I\le1,\ I\subseteq J\Rightarrow h_I\le h_J\}$.
--   4. The reflected table of Theorem B.3 is $g(i,q)=F_{m+1-q,m+1-i}$, with $g(i,0)=0$.
--
--   These objects carry the balance–price duality that identifies the two-path game value $V_m$ with $\mathrm{val}(\mathrm{polyLP}'(m))$.
--
--   **Formalization Note** Indices are zero-based (`Fin m` index `i` is the paper's `i+1`); $y$ is computed from $x$, so $C_m$ is a set of arrays $x$. $R_m$, its capped version and $\mathrm{val}(\mathrm{polyLP}'(m))$ are infima in `EReal`, so $R_m(F)=-\infty$ is representable and no junk value arises. $\sigma$ is a `Finset.sup'` over the finite nonempty family of upward-closed sets of intervals.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF pp. 31 (eqs. (49)–(54)), 32 (C_m, D_m, eqs. (55)–(56)), 33 (eq. (57)), 37 (Theorem B.3), 38 (Ĉ_m, eqs. (74)–(75))

import Definitions.Def_HarmonicRanking_Main_Supplement_GridGames

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main.Supplement

/-! Variables `x(ℓ,r,p)`, `ℓ,r,p ∈ [m]`, of the Mahdian–Yan program; `Fin m` index `i`
stands for the paper's one-based index `i + 1`. -/

/-- Cumulative rows `y(ℓ,r,p) = Σ_{h=1}^{ℓ} x(h,r,p)`. -/
def cumY {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) (ℓ r p : Fin m) : ℝ :=
  ∑ h : Fin m, if h ≤ ℓ then x h r p else 0

/-- Row masses `W_ℓr = Σ_p x(ℓ,r,p)`. -/
def rowMass {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) (ℓ r : Fin m) : ℝ :=
  ∑ p : Fin m, x ℓ r p

/-- The region `C_m` (App. B, p. 32): `x ≥ 0` together with constraints (50)–(53) on the
cumulative rows `y`, and no transpose-balance equations. -/
def InC {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) : Prop :=
  (∀ ℓ r p, 0 ≤ x ℓ r p) ∧
  -- (50) crossed coverage: y(ℓ,r,ℓ) + y(r,ℓ,p) ≥ 1/m
  (∀ ℓ r p, 1 / (m : ℝ) ≤ cumY x ℓ r ℓ + cumY x r ℓ p) ∧
  -- (51) y(ℓ+1,r,p+1) ≥ y(ℓ,r,p) for p ≤ ℓ < m
  (∀ (ℓ r p : Fin m) (hℓ : ℓ.val + 1 < m) (hp : p.val ≤ ℓ.val),
      cumY x ℓ r p ≤ cumY x ⟨ℓ.val + 1, hℓ⟩ r ⟨p.val + 1, by omega⟩) ∧
  -- (52) y(ℓ,r,p) = y(ℓ,r,ℓ+1) for ℓ < p
  (∀ (ℓ r p : Fin m) (hℓ : ℓ.val + 1 < m), ℓ < p →
      cumY x ℓ r p = cumY x ℓ r ⟨ℓ.val + 1, hℓ⟩) ∧
  -- (53) y(ℓ+1,r,p) ≥ y(ℓ,r,ℓ+1) for p ≤ ℓ < m
  (∀ (ℓ r p : Fin m) (hℓ : ℓ.val + 1 < m), p ≤ ℓ →
      cumY x ℓ r ⟨ℓ.val + 1, hℓ⟩ ≤ cumY x ⟨ℓ.val + 1, hℓ⟩ r p)

/-- The capped region `Ĉ_m = {(x,y) ∈ C_m : 0 ≤ y(ℓ,r,p) ≤ 1/m}`. -/
def InCcap {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) : Prop :=
  InC x ∧ ∀ ℓ r p, 0 ≤ cumY x ℓ r p ∧ cumY x ℓ r p ≤ 1 / (m : ℝ)

/-- Feasibility for `polyLP′(m)`: the region `C_m` plus the transpose-balance equations (54). -/
def LPFeasible {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) : Prop :=
  InC x ∧ ∀ ℓ r, rowMass x ℓ r = rowMass x r ℓ

/-- Objective (49): `(1/m) Σ_{ℓ,r,p} x(ℓ,r,p)`. -/
def lpObjective {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) : ℝ :=
  (∑ ℓ, ∑ r, ∑ p, x ℓ r p) / (m : ℝ)

/-- `val(polyLP′(m))`: the infimum of the objective (49) over the feasible region of
`polyLP′(m)`, as an extended real. -/
def lpValue (m : ℕ) : EReal :=
  ⨅ (x : Fin m → Fin m → Fin m → ℝ) (_ : LPFeasible x), ((lpObjective x : ℝ) : EReal)

/-- `D_m = {F ∈ ℝ^{m×m} : F_ℓr + F_rℓ = 1}`. -/
def InD {m : ℕ} (F : Fin m → Fin m → ℝ) : Prop :=
  ∀ ℓ r, F ℓ r + F r ℓ = 1

/-- The monotone price class `A_m` (56): `F ∈ D_m`, `0 ≤ F ≤ 1`, `F_ℓr ≥ F_{ℓ+1,r}`,
`F_ℓr ≤ F_{ℓ,r+1}`. -/
def InA {m : ℕ} (F : Fin m → Fin m → ℝ) : Prop :=
  InD F ∧ (∀ ℓ r, 0 ≤ F ℓ r ∧ F ℓ r ≤ 1) ∧
  (∀ r, Antitone (fun ℓ => F ℓ r)) ∧ (∀ ℓ, Monotone (F ℓ))

/-- The priced objective `(2/m) Σ_{ℓ,r,p} F_ℓr x(ℓ,r,p)`. -/
def pricedObjective {m : ℕ} (F : Fin m → Fin m → ℝ) (x : Fin m → Fin m → Fin m → ℝ) : ℝ :=
  2 / (m : ℝ) * ∑ ℓ, ∑ r, ∑ p, F ℓ r * x ℓ r p

/-- Equation (55): `R_m(F) = inf_{(x,y) ∈ C_m} (2/m) Σ F_ℓr x(ℓ,r,p)`, for an arbitrary real
table `F`, valued in the extended reals (it may be `-∞`). -/
def Rm {m : ℕ} (F : Fin m → Fin m → ℝ) : EReal :=
  ⨅ (x : Fin m → Fin m → Fin m → ℝ) (_ : InC x), ((pricedObjective F x : ℝ) : EReal)

/-- The same infimum restricted to the capped region `Ĉ_m`. -/
def RmCapped {m : ℕ} (F : Fin m → Fin m → ℝ) : EReal :=
  ⨅ (x : Fin m → Fin m → Fin m → ℝ) (_ : InCcap x), ((pricedObjective F x : ℝ) : EReal)

/-- The reflected table of Theorem B.3: `g(i,q) := F_{m+1-q, m+1-i}` (and `g(i,0) := 0`,
the implicit boundary of `gAt`). -/
def priceReflect {m : ℕ} (F : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i q => F (Fin.rev q) (Fin.rev i)

/-- Aggregate matrix (74): `M_ℓr = m W_ℓr = Σ_p m x(ℓ,r,p)`. -/
def aggM {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) (ℓ r : Fin m) : ℝ :=
  (m : ℝ) * rowMass x ℓ r

/-- `I_m = {[ℓ,r] : 1 ≤ ℓ < r ≤ m}`. -/
abbrev Interval (m : ℕ) := {I : Fin m × Fin m // I.1 < I.2}

/-- Inclusion of intervals: `[ℓ,r] ⊆ [L,R]` iff `L ≤ ℓ` and `r ≤ R`. -/
def IntervalSub {m : ℕ} (I J : Interval m) : Prop :=
  J.1.1 ≤ I.1.1 ∧ I.1.2 ≤ J.1.2

/-- `U ⊆ I_m` is upward closed: `I ∈ U`, `I ⊆ J` imply `J ∈ U`. -/
def IsUpClosed {m : ℕ} (U : Finset (Interval m)) : Prop :=
  ∀ I J, I ∈ U → IntervalSub I J → J ∈ U

/-- Interval imbalance `δ_I = M_ℓr - M_rℓ` for `I = [ℓ,r]`. -/
def imbalance {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) (I : Interval m) : ℝ :=
  aggM x I.1.1 I.1.2 - aggM x I.1.2 I.1.1

/-- Equation (75): `σ(δ) = max_{U ⊆ I_m upward closed} Σ_{I ∈ U} δ_I` (the empty family is
upward closed, so the maximum is over a finite nonempty family). -/
def sigma {m : ℕ} (δ : Interval m → ℝ) : ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset (Interval m))).filter IsUpClosed).sup'
    ⟨∅, by simp [IsUpClosed]⟩ (fun U => ∑ I ∈ U, δ I)

/-- The objective of (76): `(1/m²)[Σ_{ℓ,r} M_ℓr + σ(δ)]`. -/
def minimaxObjective {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) : ℝ :=
  ((∑ ℓ, ∑ r, aggM x ℓ r) + sigma (imbalance x)) / (m : ℝ) ^ 2

/-- The interval coordinates `h_I = 2F_ℓr - 1`, `I = [ℓ,r] ∈ I_m`. -/
def intervalCoords {m : ℕ} (F : Fin m → Fin m → ℝ) : Interval m → ℝ :=
  fun I => 2 * F I.1.1 I.1.2 - 1

/-- The order polytope `0 ≤ h_I ≤ 1`, `I ⊆ J ⇒ h_I ≤ h_J` on `I_m`. -/
def InOrderPolytope {m : ℕ} (h : Interval m → ℝ) : Prop :=
  (∀ I, 0 ≤ h I ∧ h I ≤ 1) ∧ ∀ I J, IntervalSub I J → h I ≤ h J

end HarmonicRanking.Main.Supplement



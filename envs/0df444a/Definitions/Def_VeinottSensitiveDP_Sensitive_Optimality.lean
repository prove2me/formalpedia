-- Prove2me | Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
-- name    : VeinottSensitiveDP_Sensitive_Optimality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:33.027794+00:00
-- url     : https://prove2.me/theorems/e3cf91e7-eb71-4da6-823d-512540a48b42
-- title:
--   n^± and ∞^± discount optimality (27)–(28), D_n^±, D_∞^±, y_n^±, Y_n^±, the lexicographic order ⪰, ≻, ψ_n^±, Ψ_n^± and G_n^± (§4)
-- statement:
--   In the model of §2/§4, with discount factor $\beta=(1+\rho)^{-1}$ and returns $V_\rho(\pi)$:
--
--   1. A policy $\pi^*$ is **$n^\pm$ discount optimal** ($n=-1,0,1,\dots$) if, componentwise,
--   $$\liminf_{\rho\to0\pm}|\rho|^{-n}\,[V_\rho(\pi^*)-V_\rho(\pi)]\ge 0\qquad\text{for all policies }\pi,$$
--   and **$\infty^\pm$ discount optimal** if for some $\rho^*>0$, $V_\rho(\pi^*)\ge V_\rho(\pi)$ for all $\pi$ and $0<\pm\rho<\rho^*$.
--   2. $D_n^\pm$ is the set of $f\in F$ for which $f^\infty$ is $n^\pm$ discount optimal, $D_{-2}=F$, and $D_\infty^\pm$ likewise.
--   3. $y_{-2}^\pm(f)=0$, $y_{-1}^\pm(f)=\pm P^*(f)r(f)$ and $y_n^\pm(f)=(\mp1)^nH(f)^{n+1}r(f)$ for $n\ge0$; $Y_n^\pm(f)$ is the $S\times(n+2)$ matrix with columns $y_{-1}^\pm(f),\dots,y_n^\pm(f)$, and $Y_n^\pm(f)=0$ for $n<-1$.
--   4. A real matrix $C$ is **lexicographically non-negative**, $C\succeq0$, if the first nonvanishing element of each row is positive, and **lexicographically positive**, $C\succ0$, if $C\succeq0$ and $C\neq0$; $C\succ B$ means $C-B\succ0$.
--   5. With $r_0(g)=r(g)$, $r_n(g)=0$ for $n\ne0$,
--   $$\psi_n^\pm(g,f)=r_n(g)+Q(g)y_n^\pm(f)\mp y_{n-1}^\pm(f)\qquad(n\ge-1),$$
--   $\Psi_n^\pm(g,f)=(\psi_{-1}^\pm(g,f),\dots,\psi_n^\pm(g,f))$, $\Psi_n^\pm=0$ for $n<-1$, and $G_n^\pm(f)=\{g\in F:\Psi_n^\pm(g,f)\succ0\}$.
--
--   The criteria grow more selective as $n$ increases; $y_n^\pm(f)$ are the Laurent coefficients of $V_\rho(f^\infty)$ in $\rho$, and $G_n^\pm(f)$ is the set of improvements of order $n$ used by the policy improvement method.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. The one-sided limit $\rho\to0\pm$ is the punctured neighbourhood of $0$ within $\{\rho:\sigma\rho>0\}$. The extended-real $\liminf\ge0$ is encoded as "for every $\varepsilon>0$, eventually $-\varepsilon\le|\rho|^{-n}[V_\rho(\pi^*)-V_\rho(\pi)]$"; the comparison is with every policy $\pi:\mathbb N\to F$. Matrices with columns $k=-1,\dots,n$ are functions $\mathbb Z\to(\text{states}\to\mathbb R)$ read on $k\in[-1,n]$ and zero elsewhere. $D_n$ is all of $F$ for $n<-1$, and $\psi_n=0$ for $n<-1$.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, pp. 1644 ((27), (28)), 1645 (D_n^±, y_n^± of Theorem 3), 1646 (⪰, ≻, Y_n^±), 1647 (r_n, y_{−2}, (32), Ψ_n^±, G_n^±), 1648 (D_{−2} ≡ F)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

variable {St : Type} [Fintype St] [DecidableEq St] {A : St → Type}

/-! The sign `±` of §4 is a real parameter `σ` with `σ = 1` (the `+` objects, `ρ → 0+`) or
`σ = −1` (the `−` objects, `ρ → 0−`); `∓1 = −σ`. -/

/-- `C ⪰ 0` (**lexicographically non-negative**) for a real matrix `C` with rows indexed by the
states and columns indexed by `k = −1, 0, …, n`: the first nonvanishing element of each row of `C`
is positive (a zero row is allowed).

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4.

**Formalization Note.** The matrix is `C : ℤ → St → ℝ` read on the columns `k ∈ [−1, n]` only
(`C k s` is the `(s, k)` entry); for `n < −1` there are no columns and every `C` is `⪰ 0`. -/
def LexNonneg (n : ℤ) (C : ℤ → St → ℝ) : Prop :=
  ∀ s : St, (∀ k ∈ Set.Icc (-1 : ℤ) n, C k s = 0) ∨
    ∃ k ∈ Set.Icc (-1 : ℤ) n, 0 < C k s ∧ ∀ j ∈ Set.Ico (-1 : ℤ) k, C j s = 0

/-- `C ≻ 0` (**lexicographically positive**): `C ⪰ 0` and `C ≠ 0`, on the columns `k = −1, …, n`.
`C ≻ B` means `C − B ≻ 0`, and `C ⪰ B` means `C − B ⪰ 0`.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4.

**Formalization Note.** `C ≠ 0` is for the whole matrix (some entry in a column `k ∈ [−1, n]` is
nonzero), not row by row. For `n < −1` the matrix is empty and never `≻ 0`. -/
def LexPos (n : ℤ) (C : ℤ → St → ℝ) : Prop :=
  LexNonneg n C ∧ ∃ k ∈ Set.Icc (-1 : ℤ) n, ∃ s : St, C k s ≠ 0

namespace Model

variable (M : Model St A)

/-- `π*` is **`n^±` discount optimal** (`n = −1, 0, 1, ⋯`):
`lim inf_{ρ→0±} |ρ|^{−n}[V_ρ(π*) − V_ρ(π)] ≧ 0` for all policies `π`, componentwise (27).

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1644, §4, (27).

**Formalization Note.** `σ = 1` is `n⁺` (`ρ → 0+`), `σ = −1` is `n⁻` (`ρ → 0−`); the one-sided
neighbourhood is `𝓝[{ρ | 0 < σρ}] 0`. The extended-real `lim inf ≧ 0` of a real function is
encoded as: for every `ε > 0`, eventually `−ε ≦ |ρ|^{−n}[V_ρ(π*) − V_ρ(π)]` (a real
`Filter.liminf` would be meaningless when the expression is unbounded below). `π` ranges over
**all** policies `ℕ → F`, not only stationary ones. `|ρ|^{−n}` is an integer power. The paper
defines `n⁻` discount optimality only in the transient case; theorems about it assume
`M.TransientCase`. -/
def IsDiscountOptimal (σ : ℝ) (n : ℤ) (πstar : Policy A) : Prop :=
  ∀ π : Policy A, ∀ s : St, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ ρ in 𝓝[{ρ : ℝ | 0 < σ * ρ}] 0, -ε ≤ |ρ| ^ (-n) * (M.V ρ πstar s - M.V ρ π s)

/-- `π*` is **`∞^±` discount optimal**: for some `ρ* > 0`, `V_ρ(π*) − V_ρ(π) ≧ 0` for all policies
`π` and `0 < ±ρ < ρ*` (28).

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1644, §4, (28). -/
def IsInfDiscountOptimal (σ : ℝ) (πstar : Policy A) : Prop :=
  ∃ ρstar : ℝ, 0 < ρstar ∧ ∀ π : Policy A, ∀ ρ : ℝ, 0 < σ * ρ → σ * ρ < ρstar →
    M.V ρ π ≤ M.V ρ πstar

/-- `D_n^±`: the set of `f ε F` for which `f^∞` is `n^±` discount optimal, `n = −1, 0, 1, ⋯`
(p. 1645), and `D_{−2} ≡ F` (p. 1648).

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1645 and p. 1648, §4.

**Formalization Note.** For `n < −1` the set is all of `F` (the paper only uses `n = −2`). -/
def D (σ : ℝ) (n : ℤ) : Set (DecisionRule A) :=
  if n < -1 then Set.univ else {f | M.IsDiscountOptimal σ n (stationary f)}

/-- `D_∞^±`: the set of `f ε F` for which `f^∞` is `∞^±` discount optimal.
Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4. -/
def Dinf (σ : ℝ) : Set (DecisionRule A) :=
  {f | M.IsInfDiscountOptimal σ (stationary f)}

/-- The Laurent coefficients `y_n^±(f)` of Theorem 3 (29):
`y_{−1}^±(f) ≡ ±P*(f)r(f)`, `y_n^±(f) ≡ (∓1)ⁿH(f)ⁿ⁺¹r(f)` for `n = 0, 1, ⋯`, and `y_{−2}^±(f) = 0`.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1645, Theorem 3, and p. 1647, §4.

**Formalization Note.** `y σ f n` with `n : ℤ`; it is `0` for every `n ≦ −2` (the paper uses only
`n = −2`). -/
noncomputable def y (σ : ℝ) (f : DecisionRule A) (n : ℤ) : St → ℝ :=
  if n < -1 then 0
  else if n = -1 then σ • (M.Pstar f *ᵥ M.rv f)
  else (-σ) ^ n.toNat • (M.H f ^ (n.toNat + 1) *ᵥ M.rv f)

/-- `Y_n^±(f) = (y_{−1}^±(f), ⋯, y_n^±(f))` for `n ≧ −1`, and `Y_n^±(f) = 0` for `n < −1`: the
`S × (n + 2)` matrix whose columns are `y_{−1}^±(f), …, y_n^±(f)`.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4.

**Formalization Note.** Encoded as `ℤ → St → ℝ`, equal to `y_k^±(f)` in the columns
`k ∈ [−1, n]` and `0` elsewhere (so `Y_n = 0` for `n < −1`). -/
noncomputable def Y (σ : ℝ) (f : DecisionRule A) (n : ℤ) : ℤ → St → ℝ :=
  fun k => if -1 ≤ k ∧ k ≤ n then M.y σ f k else 0

/-- `r_0(g) = r(g)` and `r_n(g) = 0` for `n ≠ 0`. Veinott (1969), p. 1647, §4. -/
def rn (g : DecisionRule A) (n : ℤ) : St → ℝ := if n = 0 then M.rv g else 0

/-- `ψ_n^±(g, f) = r_n(g) + Q(g)y_n^±(f) ∓ y_{n−1}^±(f)` for `n ≧ −1` (32).

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4, (32).

**Formalization Note.** Defined to be `0` for `n < −1`, where the paper does not define it (the
formula would give `0` at `n = −2` as well). -/
noncomputable def ψ (σ : ℝ) (g f : DecisionRule A) (n : ℤ) : St → ℝ :=
  if n < -1 then 0
  else M.rn g n + M.Q g *ᵥ M.y σ f n - σ • M.y σ f (n - 1)

/-- `Ψ_n^±(g, f) = (ψ_{−1}^±(g, f), ⋯, ψ_n^±(g, f))` for `n ≧ −1`, and `Ψ_n^±(g, f) = 0` for
`n < −1`.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4.

**Formalization Note.** Encoded like `Y`: `ψ_k^±(g, f)` in the columns `k ∈ [−1, n]`, `0`
elsewhere. -/
noncomputable def Ψ (σ : ℝ) (g f : DecisionRule A) (n : ℤ) : ℤ → St → ℝ :=
  fun k => if -1 ≤ k ∧ k ≤ n then M.ψ σ g f k else 0

/-- `G_n^±(f) = {g : g ε F, Ψ_n^±(g, f) ≻ 0}` for all `n` (empty for `n < −1`, since then
`Ψ_n^±(g, f) = 0`).

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4. -/
noncomputable def G (σ : ℝ) (n : ℤ) (f : DecisionRule A) : Set (DecisionRule A) :=
  {g | LexPos n (M.Ψ σ g f n)}

end Model

end VeinottSensitiveDP.Sensitive



-- Prove2me | Definitions.Def_BotNguyenADMM_KL_Setting
-- name    : BotNguyenADMM_KL_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:24.099592+00:00
-- url     : https://prove2.me/theorems/f1a1fa7e-49d2-4ef7-95a2-049103fad107
-- title:
--   Proximal ADMM: problem (1), L_r, Algorithms 1–2, Assumption 1, the constants T_0–C_13, F_r (47), KKT points and the vectors d^{k+1}, D^{k+1}
-- statement:
--   This file fixes the model of Boţ and Nguyen's proximal alternating direction method of multipliers for the nonconvex problem
--   $$\min_{x\in\mathbb R^n}\ \{g(Ax)+h(x)\},\tag{1}$$
--   where $g:\mathbb R^m\to\mathbb R\cup\{+\infty\}$ is proper and lower semicontinuous, $h:\mathbb R^n\to\mathbb R$ is differentiable with $L$-Lipschitz gradient and $A:\mathbb R^n\to\mathbb R^m$ is linear. Products such as $\mathbb R^n\times\mathbb R^m\times\mathbb R^m$ carry the Euclidean norm $|||(x,z,y)|||=\sqrt{\|x\|^2+\|z\|^2+\|y\|^2}$ and the sum inner product; $\|x\|_M^2=\langle Mx,x\rangle$.
--
--   **Augmented Lagrangian.** For $r>0$,
--   $$L_r(x,z,y)=g(z)+h(x)+\langle y,Ax-z\rangle+\frac r2\|Ax-z\|^2 .$$
--
--   **Algorithms 1 and 2.** Given symmetric positive semidefinite matrices $M_1^k$, $M_2^k$, $r>0$, $0<\rho<2$ and an arbitrary start $(x^0,z^0,y^0)$, for every $k\ge0$:
--   1. $z^{k+1}$ minimizes $g(z)+\langle y^k,Ax^k-z\rangle+\frac r2\|Ax^k-z\|^2+\frac12\|z-z^k\|^2_{M_2^k}$;
--   2. $x^{k+1}$ minimizes $h(x)+\langle y^k,Ax-z^{k+1}\rangle+\frac r2\|Ax-z^{k+1}\|^2+\frac12\|x-x^k\|^2_{M_1^k}$ (Algorithm 1), or the same expression with $h(x)$ replaced by its linearization $\langle x-x^k,\nabla h(x^k)\rangle$ (Algorithm 2);
--   3. $y^{k+1}=y^k+\rho r(Ax^{k+1}-z^{k+1})$.
--
--   **Assumption 1.** $g$ and $h$ are bounded from below; $A$ is surjective; $\mu_1:=\sup_k\|M_1^k\|<\infty$ and $\mu_2:=\sup_k\|M_2^k\|<\infty$; and
--   $$r\ge 4T_0L>0,\qquad 2M_1^k+rA^*A\succeq\Big(L+\frac{C_M}{r}\Big)\mathrm{Id}\quad\forall k\ge0,$$
--   where $T_0=\frac{1}{\lambda_{\min}(AA^*)\rho}$ if $0<\rho\le1$ and $T_0=\frac{\rho}{\lambda_{\min}(AA^*)(2-\rho)^2}$ if $1<\rho<2$, and $C_M=(6\mu_1^2+4(L+\mu_1)^2)T_0$ for Algorithm 1, $C_M=(4\mu_1^2+6(L+\mu_1)^2)T_0$ for Algorithm 2.
--
--   **Constants.** With $\lambda:=\lambda_{\min}(AA^*)$:
--   - $C_0=L+4T_0(L+\mu_1)^2/r$, $C_1=4T_0\mu_1^2/r$ (Algorithm 1); $C_0=L+4T_0\mu_1^2/r$, $C_1=4T_0(L+\mu_1)^2/r$ (Algorithm 2);
--   - $T_1=\frac{1-\rho}{\lambda\rho^2r}$ if $\rho\le1$, $T_1=\frac{\rho-1}{\lambda(2-\rho)\rho r}$ if $\rho>1$; $M_3^k=2M_1^k+rA^*A-C_0\mathrm{Id}$;
--   - $T_2=\frac{|1-\rho|}{\sqrt\lambda(1-|1-\rho|)}$, and $C_3$, $C_4$ equal $\frac{\rho(L+\mu_1)}{\sqrt\lambda(1-|1-\rho|)}$ and $\frac{\rho\mu_1}{\sqrt\lambda(1-|1-\rho|)}$ (Algorithm 1; swapped for Algorithm 2);
--   - $C_2=0$ (Algorithm 1), $1$ (Algorithm 2); $C_5=C_2L+\mu_1+r\|A\|$, $C_6=\mu_2$, $C_7=1+\|A\|+\frac1{\rho r}$; $C_8=2C_1+C_5$, $C_9=C_6$, $C_{10}=C_7+4T_1\|A\|^2$;
--   - $C_{11}=\max\{C_8+C_9\|A\|+C_3C_{10}+\frac{C_3C_9}{\rho r},\,C_4C_{10}+\frac{C_3C_9}{\rho r},\,\frac{C_4C_9}{\rho r}\}$, $C_{12}=(C_{10}+\frac{C_9}{\rho r})T_2$, $C_{13}=\frac{C_9T_2}{\rho r}$.
--
--   **Regularized augmented Lagrangian.** On $\mathbb R^n\times\mathbb R^m\times\mathbb R^m\times\mathbb R^n\times\mathbb R^m$,
--   $$F_r(x,z,y,x',y')=L_r(x,z,y)+T_1\|A^*(y-y')\|^2+\frac{C_1}2\|x-x'\|^2,\qquad F_k=F_r(x^k,z^k,y^k,x^{k-1},y^{k-1})\ (k\ge1).$$
--
--   **Subgradient vectors.** $d^{k+1}=(d_x^{k+1},d_z^{k+1},d_y^{k+1})$ with $d_x^{k+1}=C_2(\nabla h(x^{k+1})-\nabla h(x^k))+A^*(y^{k+1}-y^k)+M_1^k(x^k-x^{k+1})$, $d_z^{k+1}=y^k-y^{k+1}+rA(x^k-x^{k+1})+M_2^k(z^k-z^{k+1})$, $d_y^{k+1}=\frac1{\rho r}(y^{k+1}-y^k)$; and $D^{k+1}=(d_x^{k+1}+C_1(x^{k+1}-x^k),\ d_z^{k+1},\ d_y^{k+1}+2T_1AA^*(y^{k+1}-y^k),\ -C_1(x^{k+1}-x^k),\ -2T_1AA^*(y^{k+1}-y^k))$.
--
--   **Critical and KKT points.** $\mathrm{crit}(L_r)=\{u:0\in\partial L_r(u)\}$ with $\partial$ the limiting subdifferential; $(\hat x,\hat z,\hat y)$ is a KKT point of (1) if $-A^*\hat y=\nabla h(\hat x)$, $\hat y\in\partial g(\hat z)$ and $\hat z=A\hat x$. $\omega(u)$ is the set of cluster points of a sequence $u$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Values in $\mathbb R\cup\{+\infty\}$ are `EReal`; the products are nested `WithLp 2` products, whose norm is $|||\cdot|||$. The data are bundled in a structure `Data`; the algorithm is a parameter `v : Variant` (`prox` = Algorithm 1, `linearized` = Algorithm 2), and every algorithm-dependent constant is defined by cases on it. A run is a relation (any minimizer may be selected; existence is not claimed). $\lambda_{\min}(AA^*)$ and $\mu_1,\mu_2$ are replaced by parameters `lam > 0` with `lam‖y‖² ≤ ‖A*y‖²` and bounds `‖Mᵢᵏ‖ ≤ μᵢ`; the paper's statement is the instance `lam = λ_min(AA*)`, `μᵢ = sup_k ‖Mᵢᵏ‖`, and all constants are computed from these parameters. `Assumption1` also carries the standing hypotheses of problem (1) (p. 1) and the parameter ranges of the algorithms. $F_k$ at $k=0$ uses the natural number $0-1=0$ and is not used.
-- source:
--   Boţ and Nguyen, The proximal ADMM in the nonconvex setting, arXiv:1801.01994v2, pp. 1, 3–5, 7–8, 10, 12–14, 17–19, (1), (5), Algorithms 1–2 (12a)–(13c), Assumption 1 (14)–(15), constants of §2.2, Lemma 5 (C_3, C_4, T_2), (47), (53a)–(53c), (59), Corollary 10 (C_11–C_13), Remark 3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
open NonconvexSplitting.Shared
open Filter Topology
open scoped RealInnerProductSpace

namespace BotNguyenADMM.KL

/-- The Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The Euclidean product `ℝⁿ × ℝᵐ × ℝᵐ` of the triples `(x, z, y)`, with the norm
`|||(x, z, y)||| = √(‖x‖² + ‖z‖² + ‖y‖²)` and the sum inner product of (5) (p. 3), not the
sup-norm product. -/
abbrev Triple (n m : ℕ) : Type := WithLp 2 (E n × WithLp 2 (E m × E m))

/-- The Euclidean product `ℝⁿ × ℝᵐ × ℝᵐ × ℝⁿ × ℝᵐ` of the 5-tuples `(x, z, y, x', y')` on which
`F_r` lives, again with the norm and inner product of (5). -/
abbrev Quint (n m : ℕ) : Type :=
  WithLp 2 (E n × WithLp 2 (E m × WithLp 2 (E m × WithLp 2 (E n × E m))))

/-- The triple `(x, z, y)`. -/
def pack3 {n m : ℕ} (x : E n) (z y : E m) : Triple n m :=
  WithLp.toLp 2 (x, WithLp.toLp 2 (z, y))

/-- The 5-tuple `(x, z, y, x', y')`. -/
def pack5 {n m : ℕ} (x : E n) (z y : E m) (x' : E n) (y' : E m) : Quint n m :=
  WithLp.toLp 2 (x, WithLp.toLp 2 (z, WithLp.toLp 2 (y, WithLp.toLp 2 (x', y'))))

/-- The components of a triple `u = (x, z, y)`. -/
def tx {n m : ℕ} (u : Triple n m) : E n := (WithLp.ofLp u).1
def tz {n m : ℕ} (u : Triple n m) : E m := (WithLp.ofLp (WithLp.ofLp u).2).1
def ty {n m : ℕ} (u : Triple n m) : E m := (WithLp.ofLp (WithLp.ofLp u).2).2

/-- The components of a 5-tuple `u = (x, z, y, x', y')`. -/
def qx {n m : ℕ} (u : Quint n m) : E n := (WithLp.ofLp u).1
def qz {n m : ℕ} (u : Quint n m) : E m := (WithLp.ofLp (WithLp.ofLp u).2).1
def qy {n m : ℕ} (u : Quint n m) : E m :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp u).2).2).1
def qx' {n m : ℕ} (u : Quint n m) : E n :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp u).2).2).2).1
def qy' {n m : ℕ} (u : Quint n m) : E m :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp u).2).2).2).2

/-- The data of problem (1) (p. 1) and of Algorithms 1–2 (pp. 7–8): `g : ℝᵐ → ℝ ∪ {+∞}`,
`h : ℝⁿ → ℝ`, the linear operator `A`, the Lipschitz constant `L` of `∇h`, the parameters `r`
and `ρ`, the variable metrics `M₁ᵏ`, `M₂ᵏ`, a lower bound `lam` for `λ_min(AA*)` and upper bounds
`μ₁`, `μ₂` for `sup_k ‖M₁ᵏ‖`, `sup_k ‖M₂ᵏ‖`. The hypotheses on these data are `Assumption1`. -/
structure Data (n m : ℕ) where
  g : E m → EReal
  h : E n → ℝ
  A : E n →L[ℝ] E m
  L : ℝ
  r : ℝ
  ρ : ℝ
  M₁ : ℕ → (E n →L[ℝ] E n)
  M₂ : ℕ → (E m →L[ℝ] E m)
  lam : ℝ
  μ₁ : ℝ
  μ₂ : ℝ

/-- The two algorithms of the paper: `prox` is Algorithm 1 (p. 7, (12a)–(12c)), `linearized` is
Algorithm 2 (p. 8, (13a)–(13c)). -/
inductive Variant
  | prox
  | linearized

variable {n m : ℕ}

/-- The augmented Lagrangian (p. 7):
`L_r(x, z, y) = g(z) + h(x) + ⟨y, Ax − z⟩ + (r/2)‖Ax − z‖²`, with values in `ℝ ∪ {+∞}`. -/
noncomputable def Lr (P : Data n m) (x : E n) (z y : E m) : EReal :=
  P.g z + ((P.h x + ⟪y, P.A x - z⟫ + P.r / 2 * ‖P.A x - z‖ ^ 2 : ℝ) : EReal)

/-- `L_r` as a function on the Euclidean product `ℝⁿ × ℝᵐ × ℝᵐ`. -/
noncomputable def LrT (P : Data n m) (u : Triple n m) : EReal :=
  Lr P (tx u) (tz u) (ty u)

/-- `T₀` of Assumption 1.2 (p. 8), with `lam` in place of `λ_min(AA*)`. -/
noncomputable def T0 (P : Data n m) : ℝ :=
  if P.ρ ≤ 1 then 1 / (P.lam * P.ρ) else P.ρ / (P.lam * (2 - P.ρ) ^ 2)

/-- `C_M` of Assumption 1.4 (p. 8). -/
noncomputable def CM (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => (6 * P.μ₁ ^ 2 + 4 * (P.L + P.μ₁) ^ 2) * T0 P
  | .linearized => (4 * P.μ₁ ^ 2 + 6 * (P.L + P.μ₁) ^ 2) * T0 P

/-- `C₀` (p. 10). -/
noncomputable def C0 (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => P.L + 4 * T0 P * (P.L + P.μ₁) ^ 2 / P.r
  | .linearized => P.L + 4 * T0 P * P.μ₁ ^ 2 / P.r

/-- `C₁` (p. 10). -/
noncomputable def C1 (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => 4 * T0 P * P.μ₁ ^ 2 / P.r
  | .linearized => 4 * T0 P * (P.L + P.μ₁) ^ 2 / P.r

/-- `T₁` (p. 10), with `lam` in place of `λ_min(AA*)`. -/
noncomputable def T1 (P : Data n m) : ℝ :=
  if P.ρ ≤ 1 then (1 - P.ρ) / (P.lam * P.ρ ^ 2 * P.r)
  else (P.ρ - 1) / (P.lam * (2 - P.ρ) * P.ρ * P.r)

/-- `‖x‖²_{M₃ᵏ}` for `M₃ᵏ := 2M₁ᵏ + rA*A − C₀ Id` (p. 10); note `⟨rA*Ax, x⟩ = r‖Ax‖²`. -/
noncomputable def normSqM3 (v : Variant) (P : Data n m) (k : ℕ) (x : E n) : ℝ :=
  2 * ⟪P.M₁ k x, x⟫ + P.r * ‖P.A x‖ ^ 2 - C0 v P * ‖x‖ ^ 2

/-- `T₂` of Lemma 5 (p. 13). -/
noncomputable def T2 (P : Data n m) : ℝ :=
  |1 - P.ρ| / (Real.sqrt P.lam * (1 - |1 - P.ρ|))

/-- `C₃` of Lemma 5 (p. 13). -/
noncomputable def C3 (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => P.ρ * (P.L + P.μ₁) / (Real.sqrt P.lam * (1 - |1 - P.ρ|))
  | .linearized => P.ρ * P.μ₁ / (Real.sqrt P.lam * (1 - |1 - P.ρ|))

/-- `C₄` of Lemma 5 (p. 13). -/
noncomputable def C4 (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => P.ρ * P.μ₁ / (Real.sqrt P.lam * (1 - |1 - P.ρ|))
  | .linearized => P.ρ * (P.L + P.μ₁) / (Real.sqrt P.lam * (1 - |1 - P.ρ|))

/-- `C₂` of Lemma 8 (p. 17). -/
def C2 (v : Variant) : ℝ :=
  match v with
  | .prox => 0
  | .linearized => 1

/-- `C₅`, `C₆`, `C₇` of Lemma 8 (p. 17). -/
noncomputable def C5 (v : Variant) (P : Data n m) : ℝ := C2 v * P.L + P.μ₁ + P.r * ‖P.A‖
def C6 (P : Data n m) : ℝ := P.μ₂
noncomputable def C7 (P : Data n m) : ℝ := 1 + ‖P.A‖ + 1 / (P.ρ * P.r)

/-- `C₈`, `C₉`, `C₁₀` of Lemma 9 (p. 17). -/
noncomputable def C8 (v : Variant) (P : Data n m) : ℝ := 2 * C1 v P + C5 v P
def C9 (P : Data n m) : ℝ := C6 P
noncomputable def C10 (P : Data n m) : ℝ := C7 P + 4 * T1 P * ‖P.A‖ ^ 2

/-- `C₁₁`, `C₁₂`, `C₁₃` of Corollary 10 (p. 18). -/
noncomputable def C11 (v : Variant) (P : Data n m) : ℝ :=
  max (C8 v P + C9 P * ‖P.A‖ + C3 v P * C10 P + C3 v P * C9 P / (P.ρ * P.r))
    (max (C4 v P * C10 P + C3 v P * C9 P / (P.ρ * P.r)) (C4 v P * C9 P / (P.ρ * P.r)))
noncomputable def C12 (P : Data n m) : ℝ := (C10 P + C9 P / (P.ρ * P.r)) * T2 P
noncomputable def C13 (P : Data n m) : ℝ := C9 P * T2 P / (P.ρ * P.r)

/-- The objective of the `z`-update (12a) = (13a) (pp. 7–8), second displayed form:
`g(z) + ⟨yᵏ, Axᵏ − z⟩ + (r/2)‖Axᵏ − z‖² + ½‖z − zᵏ‖²_{M₂ᵏ}`. -/
noncomputable def zObj (P : Data n m) (k : ℕ) (xk : E n) (zk yk : E m) (w : E m) : EReal :=
  P.g w + ((⟪yk, P.A xk - w⟫ + P.r / 2 * ‖P.A xk - w‖ ^ 2
    + 1 / 2 * ⟪P.M₂ k (w - zk), w - zk⟫ : ℝ) : EReal)

/-- The objective of the `x`-update: (12b) for Algorithm 1,
`h(x) + ⟨yᵏ, Ax − zᵏ⁺¹⟩ + (r/2)‖Ax − zᵏ⁺¹‖² + ½‖x − xᵏ‖²_{M₁ᵏ}`, and (13b) for Algorithm 2,
`⟨x − xᵏ, ∇h(xᵏ)⟩ + ⟨yᵏ, Ax − zᵏ⁺¹⟩ + (r/2)‖Ax − zᵏ⁺¹‖² + ½‖x − xᵏ‖²_{M₁ᵏ}`. -/
noncomputable def xObj (v : Variant) (P : Data n m) (k : ℕ) (xk : E n) (zk1 yk : E m)
    (u : E n) : ℝ :=
  (match v with
    | .prox => P.h u
    | .linearized => ⟪u - xk, gradient P.h xk⟫)
  + ⟪yk, P.A u - zk1⟫ + P.r / 2 * ‖P.A u - zk1‖ ^ 2 + 1 / 2 * ⟪P.M₁ k (u - xk), u - xk⟫

/-- `(x, z, y)` is a sequence generated by Algorithm 1 (`v = prox`) or Algorithm 2
(`v = linearized`) from the arbitrary starting point `(x⁰, z⁰, y⁰)`: for every `k ≥ 0`,
`zᵏ⁺¹` is a minimizer in (12a)/(13a), `xᵏ⁺¹` is a minimizer in (12b)/(13b), and
`yᵏ⁺¹ = yᵏ + ρr(Axᵏ⁺¹ − zᵏ⁺¹)` (12c)/(13c). Any minimizer may be selected. -/
def IsRun (v : Variant) (P : Data n m) (x : ℕ → E n) (z y : ℕ → E m) : Prop :=
  ∀ k : ℕ,
    (∀ w : E m, zObj P k (x k) (z k) (y k) (z (k + 1)) ≤ zObj P k (x k) (z k) (y k) w) ∧
    (∀ u : E n, xObj v P k (x k) (z (k + 1)) (y k) (x (k + 1)) ≤
        xObj v P k (x k) (z (k + 1)) (y k) u) ∧
    y (k + 1) = y k + (P.ρ * P.r) • (P.A (x (k + 1)) - z (k + 1))

/-- The standing hypotheses of problem (1) (p. 1) and the parameter ranges of Algorithms 1–2
(pp. 7–8), together with Assumption 1 (p. 8) for the algorithm `v`:
* (p. 1) `g` proper and lower semicontinuous, `h` differentiable with `L`-Lipschitz gradient;
* (Alg.) `M₁ᵏ`, `M₂ᵏ` symmetric positive semidefinite, `r > 0`, `0 < ρ < 2`;
* (A1.1) `g`, `h` bounded from below;
* (A1.2) `A` surjective, used through `lam > 0` with `lam ‖y‖² ≤ ‖A*y‖²` for all `y`
  (the paper's choice is `lam = λ_min(AA*)`);
* (A1.3) `‖M₁ᵏ‖ ≤ μ₁`, `‖M₂ᵏ‖ ≤ μ₂` for all `k` (the paper's choice is `μᵢ = sup_k ‖Mᵢᵏ‖`);
* (A1.4) `μ₁ ≥ 0`, (14) `r ≥ 4T₀L > 0` and (15) `2M₁ᵏ + rA*A ≥ (L + C_M/r) Id` for all `k`. -/
structure Assumption1 (v : Variant) (P : Data n m) : Prop where
  g_proper : IsProperFn P.g
  g_lsc : LowerSemicontinuous P.g
  h_diff : Differentiable ℝ P.h
  h_lip : ∀ x x' : E n, ‖gradient P.h x - gradient P.h x'‖ ≤ P.L * ‖x - x'‖
  M₁_pos : ∀ k, (P.M₁ k).IsPositive
  M₂_pos : ∀ k, (P.M₂ k).IsPositive
  r_pos : 0 < P.r
  ρ_pos : 0 < P.ρ
  ρ_lt : P.ρ < 2
  g_bdd : ∃ c : ℝ, ∀ z, (c : EReal) ≤ P.g z
  h_bdd : ∃ c : ℝ, ∀ x, c ≤ P.h x
  lam_pos : 0 < P.lam
  lam_le : ∀ y : E m, P.lam * ‖y‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint P.A y‖ ^ 2
  μ₁_bound : ∀ k, ‖P.M₁ k‖ ≤ P.μ₁
  μ₂_bound : ∀ k, ‖P.M₂ k‖ ≤ P.μ₂
  μ₁_nonneg : 0 ≤ P.μ₁
  eq14 : 4 * T0 P * P.L ≤ P.r ∧ 0 < 4 * T0 P * P.L
  eq15 : ∀ (k : ℕ) (x : E n),
    (P.L + CM v P / P.r) * ‖x‖ ^ 2 ≤ 2 * ⟪P.M₁ k x, x⟫ + P.r * ‖P.A x‖ ^ 2

/-- The regularized augmented Lagrangian (p. 14):
`F_r(x, z, y, x', y') = L_r(x, z, y) + T₁‖A*(y − y')‖² + (C₁/2)‖x − x'‖²`. -/
noncomputable def Fr (v : Variant) (P : Data n m) (u : Quint n m) : EReal :=
  Lr P (qx u) (qz u) (qy u)
    + ((T1 P * ‖ContinuousLinearMap.adjoint P.A (qy u - qy' u)‖ ^ 2
      + C1 v P / 2 * ‖qx u - qx' u‖ ^ 2 : ℝ) : EReal)

/-- `F_k := F_r(xᵏ, zᵏ, yᵏ, xᵏ⁻¹, yᵏ⁻¹)` (47), meaningful for `k ≥ 1` (at `k = 0` the natural
number `k - 1` is `0`). -/
noncomputable def Fseq (v : Variant) (P : Data n m) (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) :
    EReal :=
  Fr v P (pack5 (x k) (z k) (y k) (x (k - 1)) (y (k - 1)))

/-- The set `ω(u)` of cluster points of a sequence (p. 18). -/
def clusterSet {X : Type*} [TopologicalSpace X] (u : ℕ → X) : Set X :=
  {w | MapClusterPt w atTop u}

/-- `crit(L_r) = {u | 0 ∈ ∂L_r(u)}`, with the limiting subdifferential on `ℝⁿ × ℝᵐ × ℝᵐ`. -/
def critLr (P : Data n m) : Set (Triple n m) :=
  {u | (0 : Triple n m) ∈ LimitingSubdiff (LrT P) u}

/-- A KKT point of problem (1) (Remark 3, p. 19): `−A*ŷ = ∇h(x̂)`, `ŷ ∈ ∂g(ẑ)`, `ẑ = Ax̂`. -/
def IsKKTPoint (P : Data n m) (xh : E n) (zh yh : E m) : Prop :=
  -(ContinuousLinearMap.adjoint P.A yh) = gradient P.h xh ∧
    yh ∈ LimitingSubdiff P.g zh ∧ zh = P.A xh

/-- The element `dᵏ⁺¹ = (d_xᵏ⁺¹, d_zᵏ⁺¹, d_yᵏ⁺¹)` of Lemma 8, (53a)–(53c) (p. 17):
`d_x = C₂(∇h(xᵏ⁺¹) − ∇h(xᵏ)) + A*(yᵏ⁺¹ − yᵏ) + M₁ᵏ(xᵏ − xᵏ⁺¹)`,
`d_z = yᵏ − yᵏ⁺¹ + rA(xᵏ − xᵏ⁺¹) + M₂ᵏ(zᵏ − zᵏ⁺¹)`, `d_y = (1/(ρr))(yᵏ⁺¹ − yᵏ)`. -/
noncomputable def dVec (v : Variant) (P : Data n m) (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) :
    Triple n m :=
  pack3
    (C2 v • (gradient P.h (x (k + 1)) - gradient P.h (x k))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) + P.M₁ k (x k - x (k + 1)))
    (y k - y (k + 1) + P.r • P.A (x k - x (k + 1)) + P.M₂ k (z k - z (k + 1)))
    ((1 / (P.ρ * P.r)) • (y (k + 1) - y k))

/-- The element `Dᵏ⁺¹` of Lemma 9, (59) (p. 17):
`D_x = d_x + C₁(xᵏ⁺¹ − xᵏ)`, `D_z = d_z`, `D_y = d_y + 2T₁AA*(yᵏ⁺¹ − yᵏ)`,
`D_{x'} = −C₁(xᵏ⁺¹ − xᵏ)`, `D_{y'} = −2T₁AA*(yᵏ⁺¹ − yᵏ)`. -/
noncomputable def DVec (v : Variant) (P : Data n m) (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) :
    Quint n m :=
  pack5
    (tx (dVec v P x z y k) + C1 v P • (x (k + 1) - x k))
    (tz (dVec v P x z y k))
    (ty (dVec v P x z y k)
      + (2 * T1 P) • P.A (ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)))
    (-(C1 v P • (x (k + 1) - x k)))
    (-((2 * T1 P) • P.A (ContinuousLinearMap.adjoint P.A (y (k + 1) - y k))))

end BotNguyenADMM.KL



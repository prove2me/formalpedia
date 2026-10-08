-- Prove2me | Definitions.Def_BellmanDP_Inventory_Model
-- name    : BellmanDP_Inventory_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T16:25:40.391054+00:00
-- url     : https://prove2.me/theorems/504ef125-6516-41a0-a167-d9aff1393981
-- title:
--   The optimal inventory equation $f(x)=\min_{y\ge x}T(y,x,f)$ with proportional costs, its solution classes and approximations
-- statement:
--   This file sets up Bellman's one-item inventory process with proportional costs. At each stage the stock is $x \ge 0$; the decision is to order up to a level $y \ge x$ at cost $k(y-x)$. A demand $s \ge 0$ with density $\varphi$ then arrives. If $s > y$ the excess $s-y$ is bought at the penalty rate $p$ and the next stock is $0$; otherwise the next stock is $y-s$. Future costs are discounted by the factor $a$.
--
--   1. The one-stage operator (Chapter V, Eq. (5.1); Chapter IV, Eq. (9.2) with $k(z)=kz$, $p(z)=pz$):
--   $$T(y,x,f) = k(y-x) + a\Big[\int_y^\infty p(s-y)\varphi(s)\,ds + f(0)\int_y^\infty \varphi(s)\,ds + \int_0^y f(y-s)\varphi(s)\,ds\Big].$$
--   2. The same operator with a fixed penalty $q$ for every stock-out (Chapter V, Eq. (9.1)), where $p(s-y)$ is replaced by $p(s-y)+q$, and the function of Theorem 4, Eq. (6):
--   $$\psi(y) = ky + a\Big[\int_y^\infty [p(s-y)+q]\varphi(s)\,ds - k\int_0^y (y-s)\varphi(s)\,ds\Big].$$
--   3. The solution predicate: $f$ solves the equation when $f(x) = \inf_{y \ge x} T(y,x,f)$ for every $x \ge 0$ (Chapter IV, Eq. (9.3)).
--   4. The demand-density hypotheses (2b) of Chapter V, Theorem 1: $\varphi(s) > 0$ for $s>0$, $\int_0^\infty \varphi = 1$, $\int_0^\infty s\varphi(s)\,ds < \infty$.
--   5. Two solution classes: measurable functions bounded on $[0,\infty)$ (Chapter V, p. 164), and measurable functions bounded on every finite interval $[0,x_0]$ (Chapter IV, Theorem 6; Appendix, Theorem 9).
--   6. The critical-level equation (3) of Theorem 1: $k = ap\int_y^\infty \varphi(s)\,ds + ak\int_0^y \varphi(s)\,ds$.
--   7. The successive approximations $f_{n+1}(x) = \min_{y\ge x} T(y,x,f_n)$ (Chapter IV, Eq. (9.5)); with $a=1$ and $f_0=0$ they are the finite-horizon costs of Chapter V, Eq. (7.2).
--   8. The renewal equation $u(x) = f(x) + \int_0^x u(x-s)\varphi(s)\,ds$ and its approximations $u_0=f$, $u_{n+1} = f + \int_0^x u_n(x-s)\varphi(s)\,ds$ (Appendix to Chapter V, Eqs. (1), (4)).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Functions are `ℝ → ℝ`; only their values on $[0,\infty)$ enter. Integrals over $(y,\infty)$ are Lebesgue integrals, integrals $\int_0^y$ are interval integrals. The equation is stated with an infimum (`IsGLB`), as Chapter IV writes it; results that assert a minimizing order level state attainment (`IsLeast`). Both solution classes require measurability, the standing convention that makes $\int_0^y f(y-s)\varphi(s)\,ds$ meaningful. The approximations use `sInf`; every theorem using them either asserts the infimum is attained or works with a set bounded below.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter V, § 5, Theorem 1, Eqs. (1)-(3), pp. 159-160; § 7, Eq. (2), p. 166; § 9, Eq. (1), p. 170 and Theorem 4, Eq. (6), p. 171; Appendix, Eqs. (1), (4), pp. 177-178; Chapter IV, § 9, Eqs. (2)-(5), p. 130

import Mathlib

namespace BellmanDP.Inventory

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. V, § 5, Eq. (5.1), p. 159 (= Ch. IV, § 9, Eq. (9.2),
p. 130, with `k(z) = kz`, `p(z) = pz`): the one-period cost of ordering up to the level `y ≥ x`
from the stock `x`, followed by the discounted cost `f` of the next state,
`T(y, x, f) = k(y − x) + a [∫_y^∞ p(s − y) φ(s) ds + f(0) ∫_y^∞ φ(s) ds + ∫_0^y f(y − s) φ(s) ds]`.
The discount factor `a` multiplies all three terms of the bracket, as in (5.1). -/
noncomputable def invT (k p a : ℝ) (φ f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  k * (y - x) + a * ((∫ s in Set.Ioi y, p * (s - y) * φ s)
    + f 0 * (∫ s in Set.Ioi y, φ s) + ∫ s in (0 : ℝ)..y, f (y - s) * φ s)

/-- Ch. V, § 9, Eq. (9.1), p. 170: the one-period cost with a fixed "red-tape" penalty `q`
charged whenever demand exceeds supply,
`k(y − x) + a [∫_y^∞ [p(s − y) + q] φ(s) ds + f(0) ∫_y^∞ φ(s) ds + ∫_0^y f(y − s) φ(s) ds]`. -/
noncomputable def invTq (k p q a : ℝ) (φ f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  k * (y - x) + a * ((∫ s in Set.Ioi y, (p * (s - y) + q) * φ s)
    + f 0 * (∫ s in Set.Ioi y, φ s) + ∫ s in (0 : ℝ)..y, f (y - s) * φ s)

/-- Ch. V, § 9, Theorem 4, Eq. (6), p. 171:
`ψ(y) = ky + a [∫_y^∞ [p(s − y) + q] φ(s) ds − k ∫_0^y (y − s) φ(s) ds]`
(the closing bracket, missing in print, is placed at the end). -/
noncomputable def psiQ (k p q a : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  k * y + a * ((∫ s in Set.Ioi y, (p * (s - y) + q) * φ s)
    - k * ∫ s in (0 : ℝ)..y, (y - s) * φ s)

/-- A function `f` solves `f(x) = Inf_{y ≥ x} T(y, x, f)` for every stock level `x ≥ 0`
(Ch. IV, Eq. (9.3), p. 130; Ch. V, Eq. (5.1), p. 159). `T f x y` is the cost of ordering up to
`y` from `x` when the continuation cost is `f`. Only the values of `f` on `[0, ∞)` enter. -/
def SolvesInf (T : (ℝ → ℝ) → ℝ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → IsGLB (T f x '' Set.Ici x) (f x)

/-- Hypotheses (2b) of Ch. V, Theorem 1, p. 160, on the demand density `φ`:
`φ(s) > 0` (for `s > 0`), `∫_0^∞ φ(s) ds = 1`, `∫_0^∞ s φ(s) ds < ∞`. -/
structure DemandDensity (φ : ℝ → ℝ) : Prop where
  /-- `φ(s) > 0` for every demand level `s > 0`. -/
  pos : ∀ s : ℝ, 0 < s → 0 < φ s
  /-- `φ` is integrable on `(0, ∞)`. -/
  integrable : IntegrableOn φ (Set.Ioi 0)
  /-- `∫_0^∞ φ(s) ds = 1`. -/
  total : ∫ s in Set.Ioi 0, φ s = 1
  /-- `∫_0^∞ s φ(s) ds < ∞`. -/
  mean : IntegrableOn (fun s => s * φ s) (Set.Ioi 0)

/-- The class of Ch. V, § 5, p. 164 ("the class of uniformly bounded functions over `x ≥ 0`"),
restricted to measurable functions: `f` is measurable and `|f(x)| ≤ M` for all `x ≥ 0`. -/
def BoundedClass (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∃ M : ℝ, ∀ x : ℝ, 0 ≤ x → |f x| ≤ M

/-- The class of Ch. IV, Theorem 6, p. 130, and of the Appendix to Ch. V, Theorem 9, p. 178
("bounded for `x` in any finite interval"), restricted to measurable functions: `f` is
measurable and bounded on `[0, x₀]` for every `x₀ ≥ 0`. -/
def LocallyBoundedClass (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∀ x₀ : ℝ, 0 ≤ x₀ → ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) x₀, |f x| ≤ M

/-- Ch. V, Theorem 1, Eq. (3), p. 160: `y` is a root of
`k = ap ∫_y^∞ φ(s) ds + ak ∫_0^y φ(s) ds`. -/
def StockLevelRoot (k p a : ℝ) (φ : ℝ → ℝ) (y : ℝ) : Prop :=
  k = a * p * (∫ s in Set.Ioi y, φ s) + a * k * ∫ s in (0 : ℝ)..y, φ s

/-- Successive approximations, Ch. IV, Eq. (9.5), p. 130:
`f_{n+1}(x) = Min_{y ≥ x} T(y, x, f_n)` from an initial function `f₀`. The minimum is written
as the infimum `sInf` of the image of `[x, ∞)`; the theorems that use it assert that it is
attained. With `a = 1` and `f₀ = 0` this is the finite-horizon recurrence (7.2) of Ch. V. -/
noncomputable def invIter (k p a : ℝ) (φ f₀ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f₀
  | n + 1 => fun x => sInf (invT k p a φ (invIter k p a φ f₀ n) x '' Set.Ici x)

/-- Appendix to Ch. V, Eq. (1), p. 177: `u` solves the renewal equation
`u(x) = f(x) + ∫_0^x u(x − s) φ(s) ds` for every `x ≥ 0`. -/
def IsRenewalSolution (f φ u : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → u x = f x + ∫ s in (0 : ℝ)..x, u (x - s) * φ s

/-- Appendix to Ch. V, Eq. (4), p. 178: `u₀ = f`,
`u_{n+1}(x) = f(x) + ∫_0^x u_n(x − s) φ(s) ds`. -/
noncomputable def renewalIter (f φ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n + 1 => fun x => f x + ∫ s in (0 : ℝ)..x, renewalIter f φ n (x - s) * φ s

end BellmanDP.Inventory



-- Prove2me | Definitions.Def_CapitationRisk_PerfectRA_Model
-- name    : CapitationRisk_PerfectRA_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:57.092777+00:00
-- url     : https://prove2.me/theorems/de215586-3e54-43b5-9a6d-f5879a153af5
-- title:
--   §4–§5, pp. 11–17 — Medicare quality game: service and health-plan demand, TM prices (3), capitation rates (7), black-swan set (8), health-plan problem (9)
-- statement:
--   This file sets up the model of She, Ayer and Montanera for comparing Perfect Information Traditional Medicare (TM) with the Medicare Advantage (MA) capitation program.
--
--   **Primitives.** There is a finite set $S$ of healthcare services and a finite set $I$ of patient types. A quality vector is $\boldsymbol w = (w_s)_{s\in S} \in \mathbb R^S$. The model consists of
--
--   1. service demand functions $\lambda^s_i(w_s)$: the demand of type-$i$ patients for service $s$ at quality $w_s$, eq. (1);
--   2. health-plan demand functions $\lambda_i(\boldsymbol w)$: the number of type-$i$ enrollees of a representative MA health plan offering quality $\boldsymbol w$, eq. (5);
--   3. fixed costs $C^f_s(w_s)$ and linear variable costs $C^v_s(x) = c_s x$;
--   4. minimum quality levels $\underline w_s$, with feasible box $\prod_{s\in S}[\underline w_s, 1]$;
--   5. the targeted quality $\boldsymbol w^* = (w^*_s)_{s\in S}$.
--
--   **Derived objects.** Write $D_s(x) = \sum_{i\in I}\lambda^s_i(x)$ and $D_s'(x) = \sum_{i\in I} \partial\lambda^s_i(x)/\partial x$. The TM provider of service $s$, paid $P$ per unit of service, earns the payoff (2)
--   $$\pi_s(x) = D_s(x)\,P - C^f_s(x) - c_s\,D_s(x).$$
--   The TM price (3) inducing quality $x$ is
--   $$P_s(x) = \Big(D_s'(x)\Big)^{-1}\Big(D_s'(x)\,c_s + \frac{dC^f_s(x)}{dx}\Big),$$
--   and the TM reimbursement is $P^*_s := P_s(w^*_s)$. The informationally perfect MA capitation rates (7) are
--   $$r_i = \sum_{s\in S}\frac{\lambda^s_i(w^*_s)}{\lambda_i(\boldsymbol w^*)}\,P^*_s .$$
--   The black-swan condition (8) says that some service $s$ has $P^*_s > r_i$ for every patient type $i$, i.e. $P^*_s > \max_{i\in I} r_i$. Under capitation rates $r = (r_i)_{i\in I}$ the health plan's expected profit (10) is
--   $$\pi(\boldsymbol w) = \sum_{i\in I}\lambda_i(\boldsymbol w)\,r_i - \sum_{s\in S}C^f_s(w_s) - \sum_{s\in S}c_s\,D_s(w_s),$$
--   and an MA equilibrium is a maximizer of $\pi$ over the box, i.e. a solution of problem (9). The pricing kernel of (12) is $q_{sj}(\boldsymbol w^*) = \big(\partial\lambda_j(\boldsymbol w^*)/\partial w_s\big)/D_s'(w^*_s)$, and the no-arbitrage condition (12) is $\sum_{j\in I} q_{sj}(\boldsymbol w^*)\,r_j = P^*_s$ for every $s$.
--
--   **Standing assumptions** (§4.1, §4.2, §5.2, p. 17): $\underline w_s < 1$; each $\lambda^s_i$ is twice differentiable, increasing and concave on $[\underline w_s,1]$; each $\lambda_i$ is of the form $f(\{\lambda^s_i(w_s)\}_{s\in S})$, twice differentiable, nondecreasing and jointly concave on the box; assumption (6) $\partial\lambda_i(\boldsymbol w)/\partial w_s \le \partial\lambda^s_i(w_s)/\partial w_s$ holds on the box; each $C^f_s$ is twice differentiable, increasing and strictly convex; $c_s \ge 0$; the total cost $C^f_s(x) + c_s D_s(x)$ is strictly convex on $[\underline w_s,1]$; and $\underline w_s < w^*_s \le 1$.
--
--   These objects are shared by every statement of the mission: the TM prices and the rates are computed from the model, never chosen freely.
--
--   **Formalization Note.** All functions are taken $C^2$ on the whole of $\mathbb R$ (resp. $\mathbb R^S$), while monotonicity, concavity and convexity are imposed on the feasible box only; this avoids one-sided derivatives at the boundary. Partial derivatives $\partial\lambda_i/\partial w_s$ are Fréchet derivatives applied to the unit vector $e_s$. "Nondecreasing in each $w_s$" is stated as monotonicity for the product order on the box, which is equivalent on a box. The variable cost is passed as its slope $c_s$ (a constant term cancels in every maximization). Three hypotheses not on the page are added: $\lambda^s_i \ge 0$ on the box (demands are patient counts), $\lambda_i(\boldsymbol w^*) > 0$ (division in (7)) and $D_s'(w^*_s) > 0$ (division in (3) and in $q_{sj}$). The black-swan condition is written as $\exists s\,\forall i,\ r_i < P^*_s$, which equals $P^*_s > \max_i r_i$ when $I$ is nonempty.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 11–18, §4–§5, (1)–(3), (5)–(10), (12) and p. 17 (w∗_s > w̲_s)

import Mathlib

namespace CapitationRisk.PerfectRA

/-- The Medicare quality game of She, Ayer & Montanera (§4–§5, pp. 11–17): a set of services `S`
and of patient types `I`, service demands `λ^s_i` (1), health-plan demands `λ_i` (5), fixed costs
`C^f_s`, linear variable costs `C^v_s(x) = c_s x`, minimum quality levels `w̲_s` and the targeted
quality `w∗`. -/
structure Model (S I : Type*) where
  /-- `lamS s i x = λ^s_i(x)`, demand of type-`i` patients for service `s` at quality `x` (1). -/
  lamS : S → I → ℝ → ℝ
  /-- `lam i w = λ_i(w)`, demand of type-`i` patients for the health plan at quality vector `w` (5). -/
  lam : I → (S → ℝ) → ℝ
  /-- `Cf s x = C^f_s(x)`, fixed cost of quality `x` in service `s`. -/
  Cf : S → ℝ → ℝ
  /-- Slope of the linear variable cost: `C^v_s(x) = c s * x`. -/
  c : S → ℝ
  /-- `wl s = w̲_s`, the minimum quality of service `s`. -/
  wl : S → ℝ
  /-- `wstar s = w∗_s`, the targeted quality of service `s`. -/
  wstar : S → ℝ

namespace Model

variable {S I : Type*} [Fintype S] [Fintype I]

/-- The feasible quality region `∏_s [w̲_s, 1]` of (2) and (9). -/
def box (M : Model S I) : Set (S → ℝ) :=
  Set.pi Set.univ (fun s => Set.Icc (M.wl s) 1)

/-- Total demand for service `s` at quality `x`: `Σ_{i∈I} λ^s_i(x)`. -/
def totDemand (M : Model S I) (s : S) (x : ℝ) : ℝ :=
  ∑ i, M.lamS s i x

/-- Marginal total demand for service `s` at quality `x`: `Σ_{i∈I} ∂λ^s_i(x)/∂x`. -/
noncomputable def dDemand (M : Model S I) (s : S) (x : ℝ) : ℝ :=
  ∑ i, deriv (M.lamS s i) x

/-- Payoff (2) of the TM provider of service `s` at unit reimbursement `P` and quality `x`:
`Σ_i λ^s_i(x) P − C^f_s(x) − C^v_s(Σ_i λ^s_i(x))`, with `C^v_s(y) = c_s y`. -/
def providerPayoff (M : Model S I) (s : S) (P x : ℝ) : ℝ :=
  M.totDemand s x * P - M.Cf s x - M.c s * M.totDemand s x

/-- The TM service price (3) inducing quality `x` in service `s`:
`P_s(x) = (Σ_i ∂λ^s_i(x)/∂x)⁻¹ (Σ_i ∂λ^s_i(x)/∂x · c_s + dC^f_s(x)/dx)`. -/
noncomputable def TMPrice (M : Model S I) (s : S) (x : ℝ) : ℝ :=
  (M.dDemand s x)⁻¹ * (M.dDemand s x * M.c s + deriv (M.Cf s) x)

/-- The TM reimbursement `P∗_s := P_s(w∗_s)` (p. 13). -/
noncomputable def Pstar (M : Model S I) (s : S) : ℝ :=
  M.TMPrice s (M.wstar s)

/-- The informationally perfect MA capitation rate (7):
`r_i = Σ_{s∈S} (λ^s_i(w∗_s) / λ_i(w∗)) P∗_s`. -/
noncomputable def rate (M : Model S I) (i : I) : ℝ :=
  ∑ s, M.lamS s i (M.wstar s) / M.lam i M.wstar * M.Pstar s

/-- The black-swan set (8) is nonempty: some service `s` has `P∗_s > r_i` for every patient type
`i`, i.e. `P∗_s > max_{i∈I} r_i` with `r` the rates (7). -/
def BlackSwan (M : Model S I) : Prop :=
  ∃ s, ∀ i, M.rate i < M.Pstar s

/-- The health plan's expected profit (10) under capitation rates `r` at quality vector `w`:
`Σ_i λ_i(w) r_i − Σ_s C^f_s(w_s) − Σ_s C^v_s(Σ_i λ^s_i(w_s))`, with `C^v_s(y) = c_s y`. -/
def profit (M : Model S I) (r : I → ℝ) (w : S → ℝ) : ℝ :=
  ∑ i, M.lam i w * r i - ∑ s, M.Cf s (w s) - ∑ s, M.c s * M.totDemand s (w s)

/-- `w` is an MA market equilibrium under rates `r`: a solution of the health plan's problem (9),
i.e. a maximizer of the profit (10) over the box `w̲_s ≤ w_s ≤ 1`. -/
def IsMAEquilibrium (M : Model S I) (r : I → ℝ) (w : S → ℝ) : Prop :=
  w ∈ M.box ∧ IsMaxOn (M.profit r) M.box w

/-- The pricing kernel of (12): `q_sj(w∗) = (∂λ_j(w∗)/∂w_s) / (Σ_{i∈I} ∂λ^s_i(w∗_s)/∂w_s)`. -/
noncomputable def kernel (M : Model S I) [DecidableEq S] (s : S) (j : I) : ℝ :=
  fderiv ℝ (M.lam j) M.wstar (Pi.single s 1) / M.dDemand s (M.wstar s)

/-- The no-arbitrage condition (12): `Σ_{j∈I} q_sj(w∗) r_j = P∗_s` for every service `s`. -/
def NoArbitrage (M : Model S I) [DecidableEq S] (r : I → ℝ) : Prop :=
  ∀ s, ∑ j, M.kernel s j * r j = M.Pstar s

/-- The standing assumptions of §4.1, §4.2, §5.2, (6) and p. 17, plus the disclosed additions
`lamS_nonneg`, `lam_wstar_pos` and `dDemand_wstar_pos`. Every function is taken `C²` on the whole
space; the shape assumptions are imposed on the feasible box. -/
structure Standing (M : Model S I) [DecidableEq S] : Prop where
  /-- The feasible interval `[w̲_s, 1]` is nondegenerate. -/
  wl_lt_one : ∀ s, M.wl s < 1
  /-- `λ^s_i` is twice (continuously) differentiable (p. 11). -/
  lamS_smooth : ∀ s i, ContDiff ℝ 2 (M.lamS s i)
  /-- Demands are patient counts, hence nonnegative on the feasible interval (added). -/
  lamS_nonneg : ∀ s i, ∀ x ∈ Set.Icc (M.wl s) 1, 0 ≤ M.lamS s i x
  /-- `λ^s_i` is increasing in service quality (p. 11). -/
  lamS_mono : ∀ s i, MonotoneOn (M.lamS s i) (Set.Icc (M.wl s) 1)
  /-- `λ^s_i` is concave in service quality (p. 11). -/
  lamS_concave : ∀ s i, ConcaveOn ℝ (Set.Icc (M.wl s) 1) (M.lamS s i)
  /-- (5): `λ_i(w) = f({λ^s_i(w_s)}_{s∈S})` for some function `f` (p. 14). -/
  lam_factor : ∀ i, ∃ f : (S → ℝ) → ℝ, ∀ w ∈ M.box, M.lam i w = f (fun s => M.lamS s i (w s))
  /-- `λ_i` is twice (continuously) differentiable (p. 14). -/
  lam_smooth : ∀ i, ContDiff ℝ 2 (M.lam i)
  /-- `λ_i` is nondecreasing in each service quality (p. 14), stated for the product order on the
  box. -/
  lam_mono : ∀ i, MonotoneOn (M.lam i) M.box
  /-- `λ_i` is jointly concave in `w` (p. 14). -/
  lam_concave : ∀ i, ConcaveOn ℝ M.box (M.lam i)
  /-- Assumption (6): `∂λ_i(w)/∂w_s ≤ ∂λ^s_i(w_s)/∂w_s` for all `i`, `s` (p. 14). -/
  option_demand : ∀ w ∈ M.box, ∀ i s,
    fderiv ℝ (M.lam i) w (Pi.single s 1) ≤ deriv (M.lamS s i) (w s)
  /-- `C^f_s` is twice (continuously) differentiable (p. 12). -/
  Cf_smooth : ∀ s, ContDiff ℝ 2 (M.Cf s)
  /-- `C^f_s` is increasing (p. 12). -/
  Cf_mono : ∀ s, MonotoneOn (M.Cf s) (Set.Icc (M.wl s) 1)
  /-- `C^f_s` is strictly convex (p. 12). -/
  Cf_strictConvex : ∀ s, StrictConvexOn ℝ (Set.Icc (M.wl s) 1) (M.Cf s)
  /-- `C^v_s(x) = c_s x` is increasing linear (p. 12). -/
  c_nonneg : ∀ s, 0 ≤ M.c s
  /-- The total cost `C^f_s(x) + C^v_s(Σ_i λ^s_i(x))` is strictly convex in `x` (p. 12). -/
  totalCost_strictConvex : ∀ s,
    StrictConvexOn ℝ (Set.Icc (M.wl s) 1) (fun x => M.Cf s x + M.c s * M.totDemand s x)
  /-- The target is feasible and strictly above the minimum quality (p. 17). -/
  wstar_mem : ∀ s, M.wl s < M.wstar s ∧ M.wstar s ≤ 1
  /-- Positive plan demand at the target (added: (7) divides by `λ_i(w∗)`). -/
  lam_wstar_pos : ∀ i, 0 < M.lam i M.wstar
  /-- Positive marginal service demand at the target (added: (3) and `q_sj` divide by it). -/
  dDemand_wstar_pos : ∀ s, 0 < M.dDemand s (M.wstar s)

end Model

end CapitationRisk.PerfectRA



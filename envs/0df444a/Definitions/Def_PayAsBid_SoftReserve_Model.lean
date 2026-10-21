-- Prove2me | Definitions.Def_PayAsBid_SoftReserve_Model
-- name    : PayAsBid_SoftReserve_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:06.771844+00:00
-- url     : https://prove2.me/theorems/cce1dc52-4950-4017-b946-019d526a9d18
-- title:
--   §2–§4.1 and Problem (8), pp. 6–16, A2 — pay-as-bid assortment game: Model 2 demand, equitable rules, k-soft reserves, symmetric Bayes–Nash pricing, expected consumer surplus
-- statement:
--   This file fixes the model of Choi, Saban and Weintraub for a procurement agency that, after suppliers post prices, chooses which suppliers' products to show to buyers.
--
--   **Parameters (Model 2, p. 10; §4.2, p. 16).** There are $n$ suppliers $N=\{1,\dots,n\}$. Products have a common quality $\alpha_i=a\in\mathbb R$, and the substitution matrix is
--   $$\Gamma=\begin{pmatrix} r_o & -r_c & \cdots & -r_c\\ -r_c & r_o & \cdots & -r_c\\ \vdots & & \ddots & \vdots\\ -r_c & -r_c & \cdots & r_o\end{pmatrix}.$$
--   Each supplier's cost is $\theta_L$ with probability $f_L$ and $\theta_H$ with probability $f_H=1-f_L$, independently across suppliers. The **standing assumptions** are $n\ge1$, $r_o>0$, $r_c\ge0$, $\Gamma$ positive definite (p. 8), $0<\theta_L<\theta_H$ (costs are positive, p. 7, and the two types are distinct) and $0<f_L<1$ (both types are in the support).
--
--   **Demand (Problem (1), p. 8).** With $D=\Gamma^{-1}$ and $c=\Gamma^{-1}\alpha$, the consumer surplus of an allocation $x$ at prices $p$ is $CS(x,p)=c'x-\tfrac12x'Dx-p'x$. For an assortment $Q\subseteq N$, the demand $d(Q,p)$ is the maximizer of $CS(\cdot,p)$ over $\{x:\ \mathbf 1'x=1,\ x\ge0,\ x_i=0\text{ for }i\notin Q\}$.
--
--   **Mechanisms (§2.3, Definitions 2–4, pp. 10–12).** An assortment function $q:\mathbb R^n_+\to\{0,1\}^n$ includes supplier $i$ iff $q_i(b)=1$. It is *anonymous* if $q(P_\pi b)=P_\pi q(b)$ for every permutation $\pi$, *monotone* if lowering one supplier's price weakly raises its own $q_i$ and weakly lowers every other $q_j$, and *equitable* ($q\in\mathcal E$) if it is both. The reserve price $r$ requires $q_i(b)=0$ whenever $b_i>r$ (RP(1)). The allocation is $x^q(b)=d(q(b),b)$.
--
--   **Benchmark rules (§3.2, p. 14; Definition 5, p. 15).** The no-competition rule includes $i$ iff $b_i\le r$. The $k$-soft-reserve rule with soft reserve $s$ and hard reserve $r$ sets
--   $$q^{k,s,r}_i(b)=\begin{cases}0 & \text{if } b_i>r,\ \text{or } s<b_i\le r \text{ and } |\{j: b_j\le s\}|\ge k,\\ 1 & \text{otherwise.}\end{cases}$$
--
--   **Problem (8) (p. A2).** Suppliers use the symmetric pricing strategy $(b_L,b_H)$. For a type profile $\theta$, $\beta(\theta)$ is the price vector, and the interim utility (5) of supplier $i$ of type $t$ deviating to $b'$ is $U_i(b'\mid t)=\sum_{\theta_{-i}}f_{-i}(\theta_{-i})\,(b'-\theta_t)\,x^q_i(b',\beta_{-i}(\theta_{-i}))$. The expected consumer surplus is $ECS(q,b_L,b_H)=\mathbb E_\theta[CS(x^q(\beta(\theta)),\beta(\theta))]$. A tuple $(q,r,b_L,b_H)$ is feasible if:
--   1. (BN-L), (BN-H): no supplier of either type gains by deviating to any $b'\in\mathbb R_+$;
--   2. (IR-L), (IR-H): $b_L\ge\theta_L$ and $b_H\ge\theta_H$;
--   3. (AM): $q\in\mathcal E$;
--   4. (RP(1)) for $r$, and (RP(2)): $r\ge\min_i\max\Theta_i=\theta_H$;
--   5. the domain of Problem (1): the assortment is nonempty whenever some price is at most $r$ (total demand is one, p. 8), and on every equilibrium price profile ((Demand) of Problem (6)).
--
--   It is optimal if no feasible tuple has a larger $ECS$.
--
--   This file is the shared model for every statement of the mission: Lemmas 1–4 and Proposition 1 are all about these objects.
--
--   **Formalization Note.** Suppliers are `Fin n`, 0-indexed. Types are `Bool` with `true` $=\theta_L$, and inclusion is `Bool` with the order `false < true`. The demand is a chosen maximizer of Problem (1), and `0` when none exists (only for $Q=\emptyset$). The last two clauses of feasibility keep this junk value out of the expected surplus. The interim utility sums over full profiles with supplier $i$'s own price replaced by $b'$; the summand does not depend on $\theta_i$, so this equals (5)'s sum over $\theta_{-i}$. Individual rationality is written in Problem (8)'s form $b_L\ge\theta_L$, $b_H\ge\theta_H$.
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), pp. 6–16 (PDF 6–16) and p. A2 (PDF 35): §2, §2.3, §3.1, §3.2, §4.1, Definitions 2–5, Model 2, Problems (1), (6), (7), (8)

import Mathlib

namespace PayAsBid.SoftReserve


open Matrix

/-- Parameters of the symmetric generalized affine demand model (Model 2, p. 10) with two-point
costs `Θᵢ = {θL, θH}` and `fᵢ(θL) = fL` (§4.2, p. 16), for `n` suppliers indexed by `Fin n`
(Lean supplier `i` is the paper's supplier `i + 1`). -/
structure Params (n : ℕ) where
  /-- common quality `αᵢ = a` -/
  a : ℝ
  /-- diagonal entry of `Γ` -/
  ro : ℝ
  /-- minus the off-diagonal entry of `Γ` -/
  rc : ℝ
  /-- low cost type -/
  θL : ℝ
  /-- high cost type -/
  θH : ℝ
  /-- probability of the low type -/
  fL : ℝ

variable {n : ℕ}

/-- The substitution matrix `Γ` of Model 2: `ro` on the diagonal, `-rc` off the diagonal. -/
def Params.Γ (P : Params n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then P.ro else -P.rc

/-- Standing assumptions: `n ≥ 1`, `ro > 0`, `rc ≥ 0` (Model 2), `Γ` positive definite (p. 8),
`0 < θL < θH` (positive costs, p. 7, two distinct types), `0 < fL < 1` (both types in the support). -/
def Params.Standing (P : Params n) : Prop :=
  1 ≤ n ∧ 0 < P.ro ∧ 0 ≤ P.rc ∧ P.Γ.PosDef ∧ 0 < P.θL ∧ P.θL < P.θH ∧ 0 < P.fL ∧ P.fL < 1

/-- `D = Γ⁻¹`. -/
noncomputable def Params.D (P : Params n) : Matrix (Fin n) (Fin n) ℝ := P.Γ⁻¹

/-- `c = Γ⁻¹ α` with `α = (a, …, a)`. -/
noncomputable def Params.c (P : Params n) : Fin n → ℝ := P.Γ⁻¹ *ᵥ (fun _ => P.a)

/-- Consumer surplus `CS(x, p) = c′x − ½ x′Dx − p′x` (Problem (1), p. 8). -/
noncomputable def CS (P : Params n) (x p : Fin n → ℝ) : ℝ :=
  P.c ⬝ᵥ x - (1 / 2) * (x ⬝ᵥ (P.D *ᵥ x)) - p ⬝ᵥ x

/-- Feasible set of Problem (1) for assortment `Q`: `1′x = 1`, `x ≥ 0`, `xᵢ = 0` for `i ∉ Q`. -/
def Admissible (Q : Finset (Fin n)) (x : Fin n → ℝ) : Prop :=
  ∑ i, x i = 1 ∧ (∀ i, 0 ≤ x i) ∧ ∀ i, i ∉ Q → x i = 0

/-- `x` solves Problem (1) for assortment `Q` and prices `p`. -/
def IsDemand (P : Params n) (Q : Finset (Fin n)) (p x : Fin n → ℝ) : Prop :=
  Admissible Q x ∧ ∀ y, Admissible Q y → CS P y p ≤ CS P x p

/-- The demand `d(Q, p)`: a solution of Problem (1) (unique for nonempty `Q` under the standing
assumptions); the junk value `0` when Problem (1) has no solution (e.g. `Q = ∅`). -/
noncomputable def demand (P : Params n) (Q : Finset (Fin n)) (p : Fin n → ℝ) : Fin n → ℝ :=
  open Classical in
  if h : ∃ x, IsDemand P Q p x then h.choose else 0

/-- An assortment function `q : ℝⁿ₊ → {0,1}ⁿ` (`true` = included), §2.3, p. 10. -/
abbrev AssortFn (n : ℕ) := (Fin n → ℝ) → Fin n → Bool

/-- The assortment `{i : qᵢ(b) = 1}`. -/
def assortSet (q : AssortFn n) (b : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => q b i = true)

/-- The allocation `x^q(b) = d(q(b), b)` (p. 13). -/
noncomputable def alloc (P : Params n) (q : AssortFn n) (b : Fin n → ℝ) : Fin n → ℝ :=
  demand P (assortSet q b) b

/-- `b ∈ ℝⁿ₊`. -/
def Nonneg (b : Fin n → ℝ) : Prop := ∀ j, 0 ≤ b j

/-- Definition 2 (anonymity), (2): `q(P_π b) = P_π q(b)` for every permutation and `b ∈ ℝⁿ₊`. -/
def Anonymous (q : AssortFn n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∀ b, Nonneg b → q (b ∘ σ) = q b ∘ σ

/-- Definition 3 (monotonicity), (3)–(4): lowering supplier `i`'s price from `bᵢ` to `b'`
(other prices fixed) weakly raises `qᵢ` and weakly lowers every `qⱼ`, `j ≠ i`
(`Bool` order: `false < true`). -/
def IsMonotone (q : AssortFn n) : Prop :=
  ∀ b, Nonneg b → ∀ (i : Fin n) (b' : ℝ), 0 ≤ b' → b' < b i →
    q b i ≤ q (Function.update b i b') i ∧
    ∀ j, j ≠ i → q (Function.update b i b') j ≤ q b j

/-- Definition 4: `q` is equitable (`q ∈ 𝓔`): anonymous and monotone. -/
def IsEquitable (q : AssortFn n) : Prop := Anonymous q ∧ IsMonotone q

/-- (RP(1)) with reserve price `r`: `qᵢ(b) = 0` whenever `bᵢ > r`. -/
def ReserveRP1 (q : AssortFn n) (r : ℝ) : Prop :=
  ∀ b, Nonneg b → ∀ i, r < b i → q b i = false

/-- Domain condition from "total demand across all products adds up to one for any vector of
prices" (p. 8): the assortment is nonempty whenever some price is at most the reserve `r`. -/
def TotalDemandOne (q : AssortFn n) (r : ℝ) : Prop :=
  ∀ b, Nonneg b → (∃ i, b i ≤ r) → ∃ i, q b i = true

/-- Definition 5 (k-soft reserve, p. 15): `q^{k,s,r}_i(b) = 0` if `bᵢ > r`, or if `s < bᵢ ≤ r` and
at least `k` suppliers price at most `s`; `1` otherwise. -/
noncomputable def kSR (k : ℕ) (s r : ℝ) : AssortFn n := fun b i =>
  decide (¬ (r < b i ∨ (s < b i ∧ b i ≤ r ∧ k ≤ (Finset.univ.filter (fun j => b j ≤ s)).card)))

/-- The no-competition mechanism `q^{NC,r}` (§3.2, p. 14): `i` is included iff `bᵢ ≤ r`. -/
noncomputable def NC (r : ℝ) : AssortFn n := fun b i => decide (b i ≤ r)

/-- Cost of a type (`true` = `θL`, `false` = `θH`). -/
def cost (P : Params n) (t : Bool) : ℝ := if t then P.θL else P.θH

/-- Probability `f(θ) = ∏ᵢ fᵢ(θᵢ)` of a type profile. -/
def weight (P : Params n) (θ : Fin n → Bool) : ℝ := ∏ i, if θ i then P.fL else 1 - P.fL

/-- The price profile `β(θ)` of the symmetric strategy `(bL, bH)`. -/
def price (bL bH : ℝ) (θ : Fin n → Bool) : Fin n → ℝ := fun i => if θ i then bL else bH

/-- Interim utility (5) of supplier `i` of type `t` pricing `b'` when the others play `(bL, bH)`:
`∑_θ f(θ) (b' − θ_t) x^q_i(b', β_{−i}(θ_{−i}))`. The summand does not depend on `θᵢ`, so this is
(5)'s sum over `θ_{−i}` weighted by `f_{−i}`. -/
noncomputable def utility (P : Params n) (q : AssortFn n) (bL bH : ℝ) (i : Fin n) (t : Bool)
    (b' : ℝ) : ℝ :=
  ∑ θ : Fin n → Bool, weight P θ * ((b' - cost P t) * alloc P q (Function.update (price bL bH θ) i b') i)

/-- Expected consumer surplus `E_θ[CS(x^q(β(θ)), β(θ))]`. -/
noncomputable def ECS (P : Params n) (q : AssortFn n) (bL bH : ℝ) : ℝ :=
  ∑ θ : Fin n → Bool, weight P θ * CS P (alloc P q (price bL bH θ)) (price bL bH θ)

/-- Feasibility in Problem (8) (p. A2), plus the domain of Problem (1): (BN-L), (BN-H) for every
supplier and every deviation `b' ∈ ℝ₊`, (IR-L), (IR-H), (AM), (RP(1)), (RP(2)) with
`min_i max Θᵢ = θH`, total demand one (p. 8), and a nonempty assortment on every equilibrium
profile ((Demand) of Problem (6)). -/
def Feasible8 (P : Params n) (q : AssortFn n) (r bL bH : ℝ) : Prop :=
  (∀ i b', 0 ≤ b' → utility P q bL bH i true b' ≤ utility P q bL bH i true bL) ∧
  (∀ i b', 0 ≤ b' → utility P q bL bH i false b' ≤ utility P q bL bH i false bH) ∧
  P.θL ≤ bL ∧ P.θH ≤ bH ∧
  IsEquitable q ∧ ReserveRP1 q r ∧ P.θH ≤ r ∧
  TotalDemandOne q r ∧
  (∀ θ : Fin n → Bool, (assortSet q (price bL bH θ)).Nonempty)

/-- `(q, r, bL, bH)` is an optimal solution of Problem (8). -/
def IsOptimal8 (P : Params n) (q : AssortFn n) (r bL bH : ℝ) : Prop :=
  Feasible8 P q r bL bH ∧
  ∀ (q' : AssortFn n) (r' bL' bH' : ℝ), Feasible8 P q' r' bL' bH' → ECS P q' bL' bH' ≤ ECS P q bL bH

end PayAsBid.SoftReserve



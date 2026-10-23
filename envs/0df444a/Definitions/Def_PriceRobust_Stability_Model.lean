-- Prove2me | Definitions.Def_PriceRobust_Stability_Model
-- name    : PriceRobust_Stability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:32.794726+00:00
-- url     : https://prove2.me/theorems/408680f1-2393-4a5b-bcae-207837d42bcd
-- title:
--   §3–§4, (1), (4)–(5), (7)–(8), (12)–(14), pp. 7–16 — multi-firm affine demand market, (P), (Z), (IS), T(R), Ψ(R), cost projection, special equilibrium, robust best response, Λ(R)
-- statement:
--   **The market.** A finite set $\mathcal N$ of products is partitioned among firms: product $l$ belongs to the product set $\mathcal N(i)$ of exactly one firm $i$. The foundational affine demands are
--   $$q(p) = a - Rp,$$
--   with intercept vector $a\in\mathbb R^{\mathcal N}$ and price-sensitivity matrix $R\in\mathbb R^{\mathcal N\times\mathcal N}$.
--
--   **Standing assumptions** (§3):
--   1. $a\ge 0$;
--   2. (P) $R$ is positive definite: $x^\top R x>0$ for every $x\ne 0$ (no symmetry is required);
--   3. (Z) $R$ is a Z-matrix: $R_{lm}\le 0$ for $l\ne m$;
--   4. (IS) $R$ is intra-firm symmetric: $R_{lm}=R_{ml}$ whenever $l$ and $m$ belong to the same firm.
--
--   **Derived matrices.** $T(R)=\mathrm{diag}(R^\top_{\mathcal N(1),\mathcal N(1)},\dots,R^\top_{\mathcal N(I),\mathcal N(I)})$ keeps the transposed diagonal firm blocks of $R$ and is $0$ elsewhere; $\Psi(R)=T(R)[R+T(R)]^{-1}$; $\Lambda(R)=I-[T(R)]^{-1}R$.
--
--   **Cost projection.** For a cost vector $w$, let $Q(w')=\Psi(R)a-\Psi(R)Rw'$. A vector $w'$ is a cost projection $w'=\Theta(w)$ of $w$ if it solves the linear complementarity problem
--   $$w'\le w,\qquad Q(w')^\top(w-w')=0,\qquad Q(w')\ge 0.$$
--   **Special equilibrium.** $(p^*|w)=p^*(w')=w'+[R+T(R)]^{-1}(a-Rw')$.
--
--   **Robust best response.** Given prices $p$, firm $i$ faces $\alpha=a_{\mathcal N(i)}-R_{\mathcal N(i),-\mathcal N(i)}p_{-\mathcal N(i)}$ and chooses $x_{\mathcal N(i)}$ to maximize
--   $$(x_{\mathcal N(i)}-w_{\mathcal N(i)})^\top(\alpha-R_{\mathcal N(i),\mathcal N(i)}x_{\mathcal N(i)})$$
--   over $x_{\mathcal N(i)}\ge 0$ with $\alpha-R_{\mathcal N(i),\mathcal N(i)}x_{\mathcal N(i)}\ge 0$. A vector $q$ is a robust best response to $p$, written $q=RB(p)$, if for every firm $i$ the block $q_{\mathcal N(i)}$ is such a maximizer. The block $R_{\mathcal N(i),\mathcal N(i)}$ and the vector $\alpha$ are also defined as standalone objects.
--
--   These are the objects of Theorems 2 and 3: the robust best-response dynamics and the special equilibrium they converge to.
--
--   **Formalization Note** Products form a finite type and firms a type, with `firm l` the owner of product `l`. Assumption (P) is the quadratic-form condition, not Mathlib's `Matrix.PosDef` (which would add symmetry). $(p^*|w)$ is written through any solution $w'$ of the LCP (12)–(14); the paper notes this form is valid for all $w>0$, and the case split on the polyhedron $W$ is not used. $RB$ is a relation rather than a function, so no choice is made; Lemma 1 makes it single-valued. Matrix inverses are Mathlib's `⁻¹`, which returns $0$ on singular matrices; $R+T(R)$, $T(R)$ and $R_{\mathcal N(i),\mathcal N(i)}$ are invertible under the standing assumptions.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), pp. 2, 7–16 (PDF 3, 8–17), §3, §4, eqs. (1), (4), (5), (7), (8), (12)–(14), Assumptions (P), (Z), (IS), definition of Λ(R) p. 16

import Mathlib

namespace PriceRobust.Stability

open Matrix

/-- The data of the market of §3: the intercept vector `a` and the price-sensitivity
matrix `R` of the affine demands `q(p) = a - R p` (eq. (1)), and the assignment of each
product `l` to the firm `firm l` that offers it, so that `N(i) = {l | firm l = i}`. -/
structure Market (ι F : Type*) where
  /-- intercepts `a` of the affine demands (1) -/
  a : ι → ℝ
  /-- price-sensitivity matrix `R` of the affine demands (1) -/
  R : Matrix ι ι ℝ
  /-- product `l` belongs to the product set `N(firm l)` -/
  firm : ι → F

namespace Market

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
variable (M : Market ι F)

/-- The standing assumptions of §3 (pp. 7–9): `a ≥ 0`; Assumption (P), `R` positive
definite in the quadratic-form sense `xᵀ R x > 0` for `x ≠ 0` (no symmetry required);
Assumption (Z), `R` has non-positive off-diagonal entries; Assumption (IS), `R` is
symmetric within each firm. -/
def Standing : Prop :=
  0 ≤ M.a ∧
  (∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M.R *ᵥ x)) ∧
  (∀ l m, l ≠ m → M.R l m ≤ 0) ∧
  (∀ l m, M.firm l = M.firm m → M.R l m = M.R m l)

/-- `T(R) = diag(R_{N(1),N(1)}ᵀ, …, R_{N(I),N(I)}ᵀ)` (p. 9): the transposed diagonal
firm blocks of `R`, and `0` outside them. -/
def Tmat : Matrix ι ι ℝ :=
  fun l m => if M.firm l = M.firm m then M.R m l else 0

/-- `Ψ(R) = T(R) [R + T(R)]⁻¹` (p. 9). -/
noncomputable def Psi : Matrix ι ι ℝ :=
  M.Tmat * (M.R + M.Tmat)⁻¹

/-- `Q(w) = Ψ(R) a - Ψ(R) R w` (eq. (14)). -/
noncomputable def Qw (w : ι → ℝ) : ι → ℝ :=
  M.Psi *ᵥ M.a - M.Psi *ᵥ (M.R *ᵥ w)

/-- `w'` solves the projection LCP (12)–(14) that defines `w' = Θ(w)`:
`w' ≤ w`, `Q(w')ᵀ (w - w') = 0`, `Q(w') ≥ 0`. -/
def IsCostProjection (w w' : ι → ℝ) : Prop :=
  w' ≤ w ∧ M.Qw w' ⬝ᵥ (w - w') = 0 ∧ 0 ≤ M.Qw w'

/-- `p*(w') = w' + [R + T(R)]⁻¹ q(w') = w' + [R + T(R)]⁻¹ (a - R w')`
(eq. (5), second line). -/
noncomputable def pstar (w' : ι → ℝ) : ι → ℝ :=
  w' + (M.R + M.Tmat)⁻¹ *ᵥ (M.a - M.R *ᵥ w')

/-- The price vector in which the products of firm `i` are priced at `x` and every other
product at `p`, i.e. `(x_{N(i)}, p_{-N(i)})`. -/
def mix (i : F) (x p : ι → ℝ) : ι → ℝ :=
  fun m => if M.firm m = i then x m else p m

/-- The affine demands `a - R (x_{N(i)}, p_{-N(i)})`; on `N(i)` these are
`α - R_{N(i),N(i)} x_{N(i)}` with `α = a_{N(i)} - R_{N(i),-N(i)} p_{-N(i)}`. -/
def ownDemand (i : F) (x p : ι → ℝ) : ι → ℝ :=
  M.a - M.R *ᵥ M.mix i x p

/-- The feasible set `P_i(p_{-N(i)})` of (8): `x_{N(i)} ≥ 0` and
`α - R_{N(i),N(i)} x_{N(i)} ≥ 0`. Only the coordinates of `x` in `N(i)` matter. -/
def RobustFeasible (i : F) (p x : ι → ℝ) : Prop :=
  ∀ l, M.firm l = i → 0 ≤ x l ∧ 0 ≤ M.ownDemand i x p l

/-- The objective of (7):
`(x_{N(i)} - w_{N(i)})ᵀ (α - R_{N(i),N(i)} x_{N(i)})`. -/
def robustProfit (w : ι → ℝ) (i : F) (p x : ι → ℝ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => M.firm l = i), (x l - w l) * M.ownDemand i x p l

/-- `q = RB(p)` (p. 13): for every firm `i`, the block `q_{N(i)}` is a maximizer of the
robust best response problem (7) over the feasible set (8), given the competitors'
prices `p_{-N(i)}` and the cost vector `w`. -/
def IsRobustBR (w p q : ι → ℝ) : Prop :=
  ∀ i, M.RobustFeasible i p q ∧
    ∀ x, M.RobustFeasible i p x → M.robustProfit w i p x ≤ M.robustProfit w i p q

/-- `α = a_{N(i)} - R_{N(i),-N(i)} p_{-N(i)}` (p. 11), as a vector on all products
(only its coordinates in `N(i)` are used). -/
def blockAlpha (i : F) (p : ι → ℝ) : ι → ℝ :=
  fun l => M.a l - ∑ m ∈ Finset.univ.filter (fun m => M.firm m ≠ i), M.R l m * p m

/-- The diagonal block `R_{N(i),N(i)}`, indexed by the products of firm `i`. -/
def Rblock (i : F) : Matrix {l // M.firm l = i} {l // M.firm l = i} ℝ :=
  M.R.submatrix Subtype.val Subtype.val

/-- `Λ(R) = I - [T(R)]⁻¹ R` (p. 16). -/
noncomputable def Lam : Matrix ι ι ℝ :=
  1 - M.Tmat⁻¹ * M.R

end Market

end PriceRobust.Stability



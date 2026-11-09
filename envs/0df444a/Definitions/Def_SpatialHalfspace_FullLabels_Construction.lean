-- Prove2me | Definitions.Def_SpatialHalfspace_FullLabels_Construction
-- name    : SpatialHalfspace_FullLabels_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:24:47.290741+00:00
-- url     : https://prove2.me/theorems/ed02c562-2e68-4b56-9268-845c18375d20
-- title:
--   Midpoint switch, paired midpoint family $\mathcal M_D$, marginals $\mu_D$, $c_D$, and $\tilde P^\sigma$
-- statement:
--   **Constants (10).** $\alpha=1/64$, $\rho=4\alpha=1/16$, $\zeta=1-\alpha-2\rho=55/64$; $\varepsilon_*=\alpha/8=1/512$ (Appendix E); $a_0=1-h_2(1/4)$.
--
--   **Midpoint switch (§3.1).** For vectors $z_0,z_1$ with midpoint $a=(z_0+z_1)/2$ and a bit $s$, the law $Q_s$ has feature masses $(\zeta,\alpha,\rho,\rho)$ at $(0,a,z_0,z_1)$ and conditional label probabilities
--
--   $$\eta_0=0,\quad \eta_a=1,\quad \eta_{z_s}=\tfrac12,\quad \eta_{z_{1-s}}=0 .$$
--
--   $Q_{s,t}=(Q_s+Q_t)/2$ and $Z(s,t)=1\{s=t\}$. The feasible prediction patterns $(h(a),h(z_0),h(z_1))$ of homogeneous halfspaces are $\mathcal P=\{000,110,010,101,001,111\}$.
--
--   **Paired midpoint family (§3.2, Definition 3.2).** For $D\ge 2$: $q=\lfloor D/2\rfloor$, terminals $U=[q]\times\{0,1\}$, $z_{e,0}=e_{2e-1}$, $z_{e,1}=e_{2e}$, $a_e=(z_{e,0}+z_{e,1})/2$. Terminal $u=(e,b)$ has marginal
--
--   $$\mu_u(0)=\zeta,\quad \mu_u(a_e)=\alpha,\quad \mu_u(z_{e,i})=\rho\ (i=0,1),$$
--
--   and $\mu_D=(\mu_u)_u$. For $\sigma\in\{0,1\}^U$, $P^\sigma_u$ is the switch law of pair $e$ with $s=\sigma_u$, $\mathcal M_D=\{(P^\sigma_u)_u\}$, $Z_e(\sigma)=1\{\sigma_{(e,0)}=\sigma_{(e,1)}\}$, and $Q^{(e)}_{s,t}$ is the switch of pair $e$.
--
--   **Improper classifier (22).** With $x_{e,i}=\langle x,z_{e,i}\rangle$: $h^{(i)}(x)=1\{\sum_e(2x_{e,i}-x_{e,1-i})>0\}$ and $c_D=h^{(0)}\wedge h^{(1)}$.
--
--   **Appendix B (26)–(27).** For $P\in\mathcal E(\mu_D)$: $\eta_{e,x}=(\eta_{(e,0),x}+\eta_{(e,1),x})/2$; $\ell(b,t)=t+b(1-2t)$;
--
--   $$R_e(A,B_0,B_1)=\alpha\,\ell(A,\eta_{e,a_e})+\rho\,\ell(B_0,\eta_{e,z_{e,0}})+\rho\,\ell(B_1,\eta_{e,z_{e,1}}),$$
--
--   $\min_{b\in\mathcal P}R_e(b)$, and $C_0(P)=\zeta\,\bar P(Y=1\mid X=0)$.
--
--   **Appendix D.1.** For $\sigma\in\{0,1\}^q$: at terminal $(e,0)$ the three nonzero support points have conditional label probability $\sigma_e$, at $(e,1)$ they have $1/2$, and the origin always has label $0$; this defines $\tilde P^\sigma\in\mathcal E(\mu_D)$.
--
--   These are the hard instances and the bookkeeping of all the lower and upper bounds.
--
--   **Formalization Note** Pairs are indexed from $0$ (`Fin q`), so $z_{e,0},z_{e,1}$ are the standard basis vectors with 0-based indices $2e$ and $2e+1$; for odd $D$ the last coordinate is unused. Bits are `Bool`, converted to the reals $0,1$ by `bitR`. A law with mass $m$ at $x$ and label probability $\eta$ is $m\eta\,\delta_{(x,1)}+m(1-\eta)\,\delta_{(x,0)}$. The three nonzero support points of pair $e$ are indexed $0\mapsto a_e$, $1\mapsto z_{e,0}$, $2\mapsto z_{e,1}$. The minimum over $\mathcal P$ is a minimum over a finite nonempty set.
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 7, PDF p. 8, §3.1 eqs. (10)–(12), PDF p. 8; §3.2 eqs. (16)–(18) and Definition 3.2, PDF p. 9; §3.3 eq. (22), PDF p. 10; App. B eqs. (26)–(27), PDF p. 16; App. D.1, PDF p. 20; ε_* = α/8, App. E, PDF p. 22

import Definitions.Def_SpatialHalfspace_FullLabels_Learning
import Definitions.Def_SpatialHalfspace_FullLabels_Information

/-!
# The midpoint switch, the paired midpoint family and the hard instances
(Yang, STOC 2027 submission #119, §3 eqs. (10)–(22), Definition 3.2, App. B eqs. (26)–(27),
App. D.1; printed pp. 7–9, 15, 19)

* Constants (10): `α = 1/64`, `ρ = 4α = 1/16`, `ζ = 1 − α − 2ρ = 55/64`; `ε_* = α/8 = 1/512`
  (App. E); `a₀ = 1 − h₂(1/4)`.
* Midpoint switch (11): for vectors `z₀, z₁`, `a = (z₀ + z₁)/2`, the law `Q_s` has feature masses
  `(ζ, α, ρ, ρ)` at `(0, a, z₀, z₁)` and `P(Y=1|X)` equal to `0, 1, 1/2, 0` at `0, a, z_s, z_{1−s}`;
  `Q_{s,t} = (Q_s + Q_t)/2`.
* Paired midpoint family (16)–(18), Def. 3.2: `q = ⌊D/2⌋` pairs, terminals `U = [q] × {0,1}`
  (here `Fin q × Bool`, pairs indexed from `0`), `z_{e,0}, z_{e,1}` the standard basis vectors
  with (0-based) indices `2e, 2e + 1`, `a_e` their midpoint; marginal `μ_u` as in (17);
  `P^σ_u` uses the switch law of pair `e` with `s = σ_u`; `M_D = {P^σ}`; `Z_e(σ) = 1{σ_(e,0) = σ_(e,1)}`.
* Feasible patterns `𝒫 = {000, 110, 010, 101, 001, 111}` of `(h(a), h(z₀), h(z₁))`.
* The improper classifier (22): `x_{e,i} = ⟨x, z_{e,i}⟩`,
  `h⁽ⁱ⁾(x) = 1{∑_e (2x_{e,i} − x_{e,1−i}) > 0}`, `c_D = h⁽⁰⁾ ∧ h⁽¹⁾`.
* App. B (26)–(27): `η_{e,x} = (η_{(e,0),x} + η_{(e,1),x})/2`, `ℓ(b, t) = t + b(1 − 2t)`,
  `R_e(A, B₀, B₁) = αℓ(A, η_{e,a_e}) + ρℓ(B₀, η_{e,z_{e,0}}) + ρℓ(B₁, η_{e,z_{e,1}})`,
  `C₀(P) = ζ P̄(Y = 1 | X = 0)`.
* App. D.1: `P̃^σ` for `σ ∈ {0,1}^q`: at terminal `(e,0)` the three nonzero support points have
  `P(Y=1|X) = σ_e`, at `(e,1)` they have `1/2`; the origin always has label `0`.
-/

namespace SpatialHalfspace.FullLabels

open MeasureTheory UnderstandingML
open scoped ENNReal InnerProductSpace

/-- `α = 1/64` (10). -/
noncomputable def alpha : ℝ := 1 / 64
/-- `ρ = 4α = 1/16` (10). -/
noncomputable def rho : ℝ := 4 * alpha
/-- `ζ = 1 − α − 2ρ = 55/64` (10). -/
noncomputable def zeta : ℝ := 1 - alpha - 2 * rho
/-- `ε_* = α/8 = 1/512` (Appendix E). -/
noncomputable def epsStar : ℝ := alpha / 8
/-- `a₀ = 1 − h₂(1/4)` (Theorem 4.3). -/
noncomputable def a0 : ℝ := 1 - h2 (1 / 4)

/-- A bit as the real number `0` or `1`. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

variable {d D : ℕ}

/-- The law on `ℝ^d × {0,1}` with mass `m` at the feature point `x` and `P(Y = 1 | X = x) = η`. -/
noncomputable def atom (m : ℝ) (x : Vec d) (η : ℝ) : Measure (Example d) :=
  ENNReal.ofReal (m * η) • Measure.dirac (x, true) + ENNReal.ofReal (m * (1 - η)) • Measure.dirac (x, false)

/-- The midpoint `a = (z₀ + z₁)/2`. -/
noncomputable def midpoint2 (z0 z1 : Vec d) : Vec d := (1 / 2 : ℝ) • (z0 + z1)

/-- (11): the switch law `Q_s` for the points `z₀, z₁` and bit `s`. -/
noncomputable def switchLaw (z0 z1 : Vec d) (s : Bool) : Measure (Example d) :=
  atom zeta 0 0 + atom alpha (midpoint2 z0 z1) 1 +
    atom rho z0 (if s then 0 else 1 / 2) + atom rho z1 (if s then 1 / 2 else 0)

/-- `Q_{s,t} = (Q_s + Q_t)/2`, the midpoint switch. -/
noncomputable def switchPair (z0 z1 : Vec d) (s t : Bool) : Measure (Example d) :=
  (2⁻¹ : ℝ≥0∞) • (switchLaw z0 z1 s + switchLaw z0 z1 t)

/-- `Z(s, t) = 1{s = t}`. -/
def Zbit (s t : Bool) : Bool := decide (s = t)

/-- The feasible patterns `𝒫 = {000, 110, 010, 101, 001, 111}` of `(h(a), h(z₀), h(z₁))`. -/
def feasiblePatterns : Finset (Bool × Bool × Bool) :=
  {(false, false, false), (true, true, false), (false, true, false), (true, false, true),
   (false, false, true), (true, true, true)}

/-- (16): the terminals `U = [q] × {0, 1}`, `q = ⌊D/2⌋` (pairs indexed `0, …, q − 1`). -/
abbrev Term (D : ℕ) := Fin (D / 2) × Bool

/-- `z_{e,i}`: the standard basis vector with 0-based index `2e + i` (the source's `e_{2e−1}`,
`e_{2e}` for 1-based `e`). -/
noncomputable def zpt (e : Fin (D / 2)) (i : Bool) : Vec D :=
  EuclideanSpace.single (⟨2 * e.val + i.toNat, by have := e.isLt; cases i <;> simp <;> omega⟩ : Fin D) 1

/-- `a_e = (z_{e,0} + z_{e,1})/2`. -/
noncomputable def mid (e : Fin (D / 2)) : Vec D := midpoint2 (zpt e false) (zpt e true)

/-- The three nonzero support points of pair `e`: `0 ↦ a_e`, `1 ↦ z_{e,0}`, `2 ↦ z_{e,1}`. -/
noncomputable def pairPoint (e : Fin (D / 2)) : Fin 3 → Vec D := ![mid e, zpt e false, zpt e true]

/-- (17): the feature marginal `μ_u` of terminal `u = (e, b)`; `μ_D = (μ_u)_u`. -/
noncomputable def muD (D : ℕ) (u : Term D) : Measure (Vec D) :=
  ENNReal.ofReal zeta • Measure.dirac 0 + ENNReal.ofReal alpha • Measure.dirac (mid u.1) +
    ENNReal.ofReal rho • Measure.dirac (zpt u.1 false) + ENNReal.ofReal rho • Measure.dirac (zpt u.1 true)

/-- Definition 3.2: `P^σ_u`, the local law of terminal `u = (e, b)` with bit `σ_u`. -/
noncomputable def PM (D : ℕ) (σ : Term D → Bool) (u : Term D) : Measure (Example D) :=
  switchLaw (zpt u.1 false) (zpt u.1 true) (σ u)

/-- Definition 3.2: the paired midpoint family `M_D = {P^σ : σ ∈ {0,1}^U}`. -/
def familyM (D : ℕ) : Set (Term D → Measure (Example D)) := Set.range (PM D)

/-- `Z(σ) = (Z_e(σ))_e`, `Z_e(σ) = 1{σ_(e,0) = σ_(e,1)}`. -/
def Zvec (σ : Term D → Bool) : Fin (D / 2) → Bool := fun e => Zbit (σ (e, false)) (σ (e, true))

/-- The midpoint switch `Q^{(e)}_{s,t}` of pair `e`. -/
noncomputable def pairSwitch (e : Fin (D / 2)) (s t : Bool) : Measure (Example D) :=
  switchPair (zpt e false) (zpt e true) s t

/-- The prediction pattern `(h(a_e), h(z_{e,0}), h(z_{e,1}))` of `h` on pair `e`. -/
noncomputable def pattern (h : Vec D → Bool) (e : Fin (D / 2)) : Bool × Bool × Bool :=
  (h (mid e), h (zpt e false), h (zpt e true))

/-- `h⁽ⁱ⁾(x) = 1{∑_e (2x_{e,i} − x_{e,1−i}) > 0}` (22). -/
noncomputable def hcoord (D : ℕ) (i : Bool) (x : Vec D) : Bool :=
  decide (0 < ∑ e : Fin (D / 2), (2 * ⟪x, zpt e i⟫_ℝ - ⟪x, zpt e (!i)⟫_ℝ))

/-- `c_D = h⁽⁰⁾ ∧ h⁽¹⁾` (22). -/
noncomputable def cD (D : ℕ) (x : Vec D) : Bool := hcoord D false x && hcoord D true x

/-- The Bernoulli prediction loss `ℓ(b, t) = t + b(1 − 2t)`. -/
def bernLoss (b : Bool) (t : ℝ) : ℝ := t + bitR b * (1 - 2 * t)

/-- (26): `η_{e,x} = (η_{(e,0),x} + η_{(e,1),x})/2` at the support point `pairPoint e j`. -/
noncomputable def pairEta (P : Term D → Measure (Example D)) (e : Fin (D / 2)) (j : Fin 3) : ℝ :=
  (condProbOne (P (e, false)) (pairPoint e j) + condProbOne (P (e, true)) (pairPoint e j)) / 2

/-- (27): `R_e(b)` for the conditional probabilities `η 0, η 1, η 2` at `a_e, z_{e,0}, z_{e,1}`. -/
noncomputable def pairRisk (η : Fin 3 → ℝ) (b : Bool × Bool × Bool) : ℝ :=
  alpha * bernLoss b.1 (η 0) + rho * bernLoss b.2.1 (η 1) + rho * bernLoss b.2.2 (η 2)

/-- `min_{b ∈ 𝒫} R_e(b)` (a minimum over the finite nonempty set `𝒫`). -/
noncomputable def minPairRisk (η : Fin 3 → ℝ) : ℝ :=
  feasiblePatterns.inf' ⟨(false, false, false), by decide⟩ (pairRisk η)

/-- `C₀(P) = ζ P̄(Y = 1 | X = 0)`, the origin's contribution to the risk of every halfspace. -/
noncomputable def originRisk (P : Term D → Measure (Example D)) : ℝ :=
  zeta * condProbOne (mixture P) 0

/-- App. D.1: the local law `P̃^σ_u`, `σ ∈ {0,1}^q`. -/
noncomputable def PT (D : ℕ) (σ : Fin (D / 2) → Bool) (u : Term D) : Measure (Example D) :=
  let η : ℝ := if u.2 then 1 / 2 else bitR (σ u.1)
  atom zeta 0 0 + atom alpha (mid u.1) η + atom rho (zpt u.1 false) η + atom rho (zpt u.1 true) η

end SpatialHalfspace.FullLabels



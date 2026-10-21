-- Prove2me | Definitions.Def_SwitchOptStop_Boundary_Value
-- name    : SwitchOptStop_Boundary_Value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:38.160506+00:00
-- url     : https://prove2.me/theorems/3036cb02-e07e-4915-a6fe-adf0c602e187
-- title:
--   §2–§5 — value functions V, V^N, Ṽ^{1,N}, regions C_ι, D_ι, D^N_ε, entry time τ_D, boundaries b_ι, b^N_ι, x̄¹_ι, generator 𝕃, Assumption 2.3, admissible class, (5.1)
-- statement:
--   The objects of the optimal stopping problem (2.1). Write $\mathsf P_{\iota,x}$ for the law of $(\alpha,X^x)$ started from $(\iota,x)$, and $\Lambda_t=\int_0^t\lambda(\alpha_s)\,ds$.
--
--   1. **Value functions.**
--   $$
--   V(\iota,x)=\inf_{\tau}\mathsf E_{\iota,x}\int_0^\tau e^{-\Lambda_t}H(\alpha_t,X_t)\,dt,\qquad V^N(\iota,x)=\inf_{\tau}\mathsf E_{\iota,x}\int_0^\tau e^{-\Lambda_t}H^N(\alpha_t,X_t)\,dt,
--   $$
--   over the stopping times of $(\alpha,X)$ (2.1), (3.4), and $\tilde V^{1,N}(\iota,z)=\inf_\tau\mathsf E_{\iota,z}\int_0^\tau e^{-\Lambda_t}H^N(\alpha_t,(\tilde X^1_t,0))\,dt$ over the stopping times of $(\alpha,\tilde X^1)$ (2.7).
--   2. **Regions.** $C_\iota=\{x\in(0,\infty)^2:V(\iota,x)<0\}$, $D_\iota=\{x\in(0,\infty)^2:V(\iota,x)=0\}$ (3.3), and $D^N_\varepsilon=\{V^N\ge-\varepsilon\}$, $D^N=D^N_0$ (p. 8).
--   3. **Entry time** $\tau_D=\inf\{t\ge0:(\alpha_t,X_t)\in D\}$ with $\inf\emptyset=\infty$ (2.6).
--   4. **Boundaries** $b_\iota(x_1)=\inf\{x_2>0:V(\iota,x_1,x_2)=0\}$, $b^N_\iota$ likewise with $V^N$ (p. 10), and the threshold $\bar x^1_\iota=\inf\{z>0:\tilde V^{1,N}(\iota,z)=0\}$ of (2.7).
--   5. **Assumption 2.3.** Each $\tilde X^i$ is recurrent to $(c,\infty)$ for every $c>0$: from every regime and every $z>0$ it enters $(c,\infty)$ almost surely.
--   6. **Generator** (2.4): $\mathbb L f(\iota,x)=\sum_i\big(a^i(\iota)+\sum_j b^{ij}(\iota)x_j\big)\partial_if(\iota,x)+\tfrac12\sum_i(\sigma^i(\iota)x_i)^2\partial_{ii}f(\iota,x)+\sum_\kappa q_{\iota\kappa}f(\kappa,x)$.
--   7. **Green regularity** (3.17): $\tau_D^{\iota,x}\to0$ as $x\in C_\iota$ tends to a boundary point of $C_\iota$ in $(0,\infty)^2$.
--   8. **Admissible class** (Theorem 5.1): families $c=(c_\iota)$ of bounded continuous functions on $(0,\infty)$ with values in $[0,\infty)$ and $H(\iota,(z,c_\iota(z)))\ge0$ for all $z>0$; and, with $\lambda\equiv\lambda_0$, $c$ **solves (5.1) at $(\iota,x_1)$** if
--   $$
--   \int_0^\infty e^{-\lambda_0t}\,\mathsf E_{\iota,(x_1,c_\iota(x_1))}\Big[H(\alpha_t,X_t)\,\mathbf 1\{X^1_t>0,\ 0<X^2_t<c_{\alpha_t}(X^1_t)\}\Big]dt=0,
--   $$
--   the integral converging absolutely.
--
--   These are the objects that the theorems of the mission are about.
--
--   **Formalization Note** $\mathsf P_{\iota,x}$ is $P$ conditioned on $\{\alpha_0=\iota\}$ applied to the flow $X^x$. Values are computed in `EReal` and converted to reals; under the standing hypotheses $\tau=0$ gives $0$ and the negative part is at most $|\underline H|/\underline\lambda$, so the values lie in $[\underline H/\underline\lambda,0]$ and the conversion loses nothing. In Lean `sInf ∅ = 0`; the theorems show the sets defining $b_\iota$, $b^N_\iota$, $\bar x^1_\iota$ are nonempty. Green regularity is read in probability: $\mathsf P_{\iota,x}(\tau_D\ge\varepsilon)\to0$. The integral (5.1) is written as an expectation, which equals the paper's transition-density form $\int_0^\infty\sum_\kappa\int_0^\infty\int_0^{c_\kappa(y_1)}e^{-\lambda_0t}p_t(\iota,x;\kappa,y)H(\kappa,y)\,dy_2\,dy_1\,dt$ by Fubini–Tonelli whenever the density $p_t$ exists; integrability is part of "solves", because a divergent Bochner integral is $0$ in Lean. Partial derivatives are `fderiv` applied to coordinate vectors.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, pp. 3–15, (2.1), (2.4), (2.6), Assumption 2.3 (p. 4), (2.7), (3.3), (3.4), D^N_ε (p. 8), b_ι (p. 10), (3.17) (p. 13), (5.1) and the admissible class (p. 15)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Model

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

variable {Ω : Type} [MeasurableSpace Ω]

/-- `P_{ι,·}`: the measure `P` conditioned on the initial regime `α₀ = ι`. Together with the flow
`X x` (resp. `Xt i z`) it is the law `P_{ι,x}` (resp. `P_{ι,z}`) of the paper. -/
noncomputable def Pι (S : Setting Ω) (ι : Fin 2) : Measure Ω :=
  ProbabilityTheory.cond S.P {ω | S.α 0 ω = ι}

/-- `Λ_t = ∫₀ᵗ λ(α_s) ds` (p. 8). -/
noncomputable def Λ (m : Model) (S : Setting Ω) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..t, m.lam (S.α u.toNNReal ω)

/-- The discounted running cost `e^{−Λ_t} H(α_t, X_t)` of (2.1), for the process started at `x`. -/
noncomputable def costV (m : Model) (S : Setting Ω) (x : Pt) : ℝ → Ω → ℝ :=
  fun t ω => Real.exp (-Λ m S t ω) * m.H (S.α t.toNNReal ω) (S.X x t.toNNReal ω)

/-- The discounted truncated cost `e^{−Λ_t} H^N(α_t, X_t)` of (3.4). -/
noncomputable def costVN (m : Model) (S : Setting Ω) (N : ℝ) (x : Pt) : ℝ → Ω → ℝ :=
  fun t ω => Real.exp (-Λ m S t ω) * HN m N (S.α t.toNNReal ω) (S.X x t.toNNReal ω)

/-- The discounted cost `e^{−Λ_t} H^N(α_t, (X̃¹_t, 0))` of (2.7), for `X̃¹` started at `z`. -/
noncomputable def cost1N (m : Model) (S : Setting Ω) (N : ℝ) (z : ℝ) : ℝ → Ω → ℝ :=
  fun t ω => Real.exp (-Λ m S t ω) * HN m N (S.α t.toNNReal ω) ![S.Xt 0 z t.toNNReal ω, 0]

/-- The value `V(ι, x)` of (2.1), in `EReal`: the infimum over the stopping times of `(α, X)`. -/
noncomputable def valueE (m : Model) (S : Setting Ω) (ι : Fin 2) (x : Pt) : EReal :=
  stopValE (Pι S ι) (S.𝔾 x) (costV m S x)

/-- The value function `V(ι, x)` of (2.1), as a real number. -/
noncomputable def value (m : Model) (S : Setting Ω) (ι : Fin 2) (x : Pt) : ℝ :=
  (valueE m S ι x).toReal

/-- The value `V^N(ι, x)` of (3.4), in `EReal`. -/
noncomputable def valueNE (m : Model) (S : Setting Ω) (N : ℝ) (ι : Fin 2) (x : Pt) : EReal :=
  stopValE (Pι S ι) (S.𝔾 x) (costVN m S N x)

/-- The value function `V^N(ι, x)` of (3.4), as a real number. -/
noncomputable def valueN (m : Model) (S : Setting Ω) (N : ℝ) (ι : Fin 2) (x : Pt) : ℝ :=
  (valueNE m S N ι x).toReal

/-- The value `Ṽ^{1,N}(ι, z)` of (2.7), in `EReal`: the infimum over the stopping times of
`(α, X̃¹)`. -/
noncomputable def value1NE (m : Model) (S : Setting Ω) (N : ℝ) (ι : Fin 2) (z : ℝ) : EReal :=
  stopValE (Pι S ι) (S.𝔾₁ z) (cost1N m S N z)

/-- The value function `Ṽ^{1,N}(ι, z)` of (2.7), as a real number. -/
noncomputable def value1N (m : Model) (S : Setting Ω) (N : ℝ) (ι : Fin 2) (z : ℝ) : ℝ :=
  (value1NE m S N ι z).toReal

/-- The `ι`-th layer `C_ι = {x ∈ (0, ∞)² : V(ι, x) < 0}` of the continuation region (3.3). -/
def contSet (m : Model) (S : Setting Ω) (ι : Fin 2) : Set Pt :=
  {x | x ∈ openQuadrant ∧ value m S ι x < 0}

/-- The `ι`-th layer `D_ι = {x ∈ (0, ∞)² : V(ι, x) = 0}` of the stopping region (3.3). -/
def stopSet (m : Model) (S : Setting Ω) (ι : Fin 2) : Set Pt :=
  {x | x ∈ openQuadrant ∧ value m S ι x = 0}

/-- The `ι`-th layer of `D^N_ε = {V^N ≥ −ε}` (p. 8), inside `(0, ∞)²`; `ε = 0` gives `D^N`. -/
def stopSetN (m : Model) (S : Setting Ω) (N ε : ℝ) (ι : Fin 2) : Set Pt :=
  {x | x ∈ openQuadrant ∧ -ε ≤ valueN m S N ι x}

/-- The first entry time `τ_A = inf{t ≥ 0 : X_t ∈ A_{α_t}}` (2.6) of `(α, X x)` into the set
`A = ⋃_ι {ι} × A ι`, with `inf ∅ = ∞`. -/
noncomputable def entryTime (S : Setting Ω) (x : Pt) (A : Fin 2 → Set Pt) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | S.X x t ω ∈ A (S.α t ω)}, (t : WithTop ℝ≥0)

/-- The first entry time of `(α, X̃¹)`, started at `z`, into `⋃_ι {ι} × A ι`, with `inf ∅ = ∞`. -/
noncomputable def entryTime1 (S : Setting Ω) (z : ℝ) (A : Fin 2 → Set ℝ) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | S.Xt 0 z t ω ∈ A (S.α t ω)}, (t : WithTop ℝ≥0)

/-- The optimal stopping boundary `b_ι(x₁) = inf{x₂ > 0 : V(ι, x₁, x₂) = 0}` (p. 10). In Lean the
infimum of an empty set is `0`; Lemma 3.6 shows the set is nonempty for `x₁ > 0`. -/
noncomputable def bdry (m : Model) (S : Setting Ω) (ι : Fin 2) (x1 : ℝ) : ℝ :=
  sInf {x2 : ℝ | 0 < x2 ∧ value m S ι ![x1, x2] = 0}

/-- The boundary `b^N_ι(x₁) = inf{x₂ > 0 : V^N(ι, x₁, x₂) = 0}` of the truncated problem (p. 10). -/
noncomputable def bdryN (m : Model) (S : Setting Ω) (N : ℝ) (ι : Fin 2) (x1 : ℝ) : ℝ :=
  sInf {x2 : ℝ | 0 < x2 ∧ valueN m S N ι ![x1, x2] = 0}

/-- The threshold `x̄¹_ι = inf{z > 0 : Ṽ^{1,N}(ι, z) = 0}` of the one-dimensional problem (2.7)
(Proposition 2.4). -/
noncomputable def xbar1 (m : Model) (S : Setting Ω) (N : ℝ) (ι : Fin 2) : ℝ :=
  sInf {z : ℝ | 0 < z ∧ value1N m S N ι z = 0}

/-- Assumption 2.3 (p. 4): for `i = 1, 2`, the solution `X̃^i` is recurrent to `(c, ∞)` for every
`c > 0`: from every regime `ι` and every starting point `z > 0`, it enters `(c, ∞)` almost surely. -/
def Assumption23 (S : Setting Ω) : Prop :=
  ∀ (i ι : Fin 2) (z : ℝ), 0 < z → ∀ c : ℝ, 0 < c →
    ∀ᵐ ω ∂(Pι S ι), ∃ t : ℝ≥0, c < S.Xt i z t ω

/-- The partial derivative `∂_i f(x)`. -/
noncomputable def pd (i : Fin 2) (f : Pt → ℝ) (x : Pt) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The generator `𝕃` of (2.4) applied to `V = (V(1, ·), V(2, ·))`:
`𝕃V(ι, x) = Σ_i (a^i(ι) + Σ_j b^{ij}(ι) x_j) ∂_i V(ι, x) + ½ Σ_i (σ^i(ι) x_i)² ∂_{ii} V(ι, x)
 + Σ_κ q_{ικ} V(κ, x)`. -/
noncomputable def gen (m : Model) (V : Fin 2 → Pt → ℝ) (ι : Fin 2) (x : Pt) : ℝ :=
  (∑ i, (m.a ι i + ∑ j, m.b ι i j * x j) * pd i (V ι) x)
    + (1 / 2) * (∑ i, (m.σ ι i * x i) ^ 2 * pd i (pd i (V ι)) x)
    + ∑ κ, m.q ι κ * V κ x

/-- Green regularity (3.17) of the optimal stopping boundary, read in probability: for every regime
`ι` and every point `x̄ ∈ (0, ∞)²` of the boundary of `C_ι`, the entry time `τ_D` of the process started
at `x` tends to `0` in `P_{ι,x}`-probability as `x → x̄` within `C_ι`. -/
def IsGreenRegular (m : Model) (S : Setting Ω) : Prop :=
  ∀ ι : Fin 2, ∀ xb ∈ frontier (contSet m S ι) ∩ openQuadrant, ∀ ε : ℝ≥0, 0 < ε →
    Tendsto (fun x => Pι S ι {ω | ((ε : ℝ≥0) : WithTop ℝ≥0) ≤ entryTime S x (stopSet m S) ω})
      (𝓝[contSet m S ι] xb) (𝓝 0)

/-- The admissible class of Theorem 5.1 (p. 15): `c = (c_ι)_ι` with each `c_ι` bounded and continuous
on `(0, ∞)`, `[0, ∞)`-valued there (so that `(z, c_ι(z))` lies in the domain `[0, ∞)²` of `H`), and
`H(ι, (z, c_ι(z))) ≥ 0` for all `(ι, z) ∈ M × (0, ∞)`. -/
def Admissible (m : Model) (c : Fin 2 → ℝ → ℝ) : Prop :=
  ∀ ι : Fin 2,
    (∃ B : ℝ, ∀ z : ℝ, 0 < z → |c ι z| ≤ B) ∧ ContinuousOn (c ι) (Ioi 0) ∧
    ∀ z : ℝ, 0 < z → 0 ≤ c ι z ∧ 0 ≤ m.H ι ![z, c ι z]

/-- The integrand of (5.1)/(5.2) in expectation form, for the process started at `y` and the
candidate boundary `c`: `(t, ω) ↦ e^{−λ₀ t} H(α_t, X_t) 𝟙{X¹_t > 0, 0 < X²_t < c_{α_t}(X¹_t)}`.
Its integral against `dt ⊗ P_{ι}` on `(0, ∞) × Ω` is
`∫₀^∞ Σ_κ ∫₀^∞ ∫₀^{c_κ(y₁)} e^{−λ₀t} p_t(ι, y; κ, y') H(κ, y') dy'₂ dy'₁ dt` whenever the transition
density `p_t` exists. -/
noncomputable def ieIntegrand (m : Model) (S : Setting Ω) (lam0 : ℝ) (c : Fin 2 → ℝ → ℝ) (y : Pt) :
    ℝ × Ω → ℝ :=
  fun p =>
    Real.exp (-lam0 * p.1) *
      (if 0 < S.X y p.1.toNNReal p.2 0 ∧ 0 < S.X y p.1.toNNReal p.2 1 ∧
          S.X y p.1.toNNReal p.2 1 < c (S.α p.1.toNNReal p.2) (S.X y p.1.toNNReal p.2 0)
        then m.H (S.α p.1.toNNReal p.2) (S.X y p.1.toNNReal p.2) else 0)

/-- `c` solves the integral equation (5.1) at `(ι, x₁)`: started from `(x₁, c_ι(x₁))`, the integral
of (5.1) converges absolutely and equals `0`. -/
def SolvesIE (m : Model) (S : Setting Ω) (lam0 : ℝ) (c : Fin 2 → ℝ → ℝ) (ι : Fin 2) (x1 : ℝ) :
    Prop :=
  Integrable (ieIntegrand m S lam0 c ![x1, c ι x1]) ((volume.restrict (Ioi 0)).prod (Pι S ι)) ∧
  ∫ p, ieIntegrand m S lam0 c ![x1, c ι x1] p ∂((volume.restrict (Ioi 0)).prod (Pι S ι)) = 0

end SwitchOptStop.Boundary



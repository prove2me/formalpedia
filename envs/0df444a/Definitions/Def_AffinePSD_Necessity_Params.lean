-- Prove2me | Definitions.Def_AffinePSD_Necessity_Params
-- name    : AffinePSD_Necessity_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:21.497148+00:00
-- url     : https://prove2.me/theorems/1a83bd61-4c5a-47a1-a0e7-05239554f375
-- title:
--   Truncation function, parameter set $(\alpha,b,\beta^{ij},c,\gamma,m,\mu)$, $F$, $R$ and admissibility (Definition 2.3)
-- statement:
--   This file encodes the parameters of Definition 2.3 and the functions (2.16)–(2.17).
--
--   A **truncation function** is a bounded continuous map $\chi : S_d \to S_d$ with $\chi(\xi) = \xi$ on a neighbourhood of $0$.
--
--   A **parameter set** $(\alpha, b, \beta^{ij}, c, \gamma, m, \mu)$ consists of matrices $\alpha, b, \gamma$, a family $\beta^{ij}$ of matrices, a real $c$, a Borel measure $m$ on $S_d^+\setminus\{0\}$ and a $d\times d$ matrix $\mu = (\mu_{ij})$ of finite signed measures on $S_d^+\setminus\{0\}$. From it one forms
--   $$B(x) = \sum_{i,j}\beta^{ij}x_{ij}, \qquad B^\top_{ij}(u) = \langle \beta^{ij}, u\rangle, \qquad M(x, d\xi) = \frac{\langle x, \mu(d\xi)\rangle}{\|\xi\|^2\wedge 1},$$
--   $$A_{ijkl}(x) = x_{ik}\alpha_{jl} + x_{il}\alpha_{jk} + x_{jk}\alpha_{il} + x_{jl}\alpha_{ik},$$
--   $$F(u) = \langle b,u\rangle + c - \int_{S_d^+\setminus\{0\}} \big(e^{-\langle u,\xi\rangle} - 1\big)\, m(d\xi),$$
--   $$R(u) = -2u\alpha u + B^\top(u) + \gamma - \int_{S_d^+\setminus\{0\}} \frac{e^{-\langle u,\xi\rangle} - 1 + \langle \chi(\xi), u\rangle}{\|\xi\|^2 \wedge 1}\, \mu(d\xi).$$
--
--   The parameter set is **admissible** (associated with $\chi$) if:
--
--   1. $\alpha \in S_d^+$ (2.3), $b \succeq (d-1)\alpha$ (2.4), $c \ge 0$ (2.5), $\gamma \in S_d^+$ (2.6);
--   2. $\int (\|\xi\| \wedge 1)\, m(d\xi) < \infty$ (2.7);
--   3. $\mu(E) \in S_d^+$ for every Borel $E$, and $\int \langle \chi(\xi), u\rangle M(x,d\xi) < \infty$ for all $x, u \in S_d^+$ with $\langle x,u\rangle = 0$ (2.9);
--   4. $\beta^{ij} = \beta^{ji} \in S_d$, and $\langle B(x), u\rangle - \int \langle \chi(\xi), u\rangle M(x,d\xi) \ge 0$ for all $x, u \in S_d^+$ with $\langle x,u\rangle = 0$ (2.11).
--
--   The predicate `AdmissibleCore` is everything except the drift condition (2.4), plus $b \in S_d$; `Admissible` adds (2.4). The split is needed because Proposition 4.9 first obtains only $b \in S_d^+$, and (2.4) is Proposition 4.18. A helper predicate records that the integrands of $F$ and $R$ at $u$ are integrable.
--
--   **Formalization Note.** The matrix measure $\mu$ is encoded by a finite measure $\nu$ on the cone with $\nu\{0\}=0$ and a measurable, positive semidefinite, entrywise $\nu$-integrable density $H$, so that $\mu_{ij}(d\xi) = H_{ij}(\xi)\,\nu(d\xi)$. Nothing is lost: every such $\mu$ has this form with $\nu = \sum_i \mu_{ii}$, since $|\mu_{ij}(E)| \le (\mu_{ii}(E) + \mu_{jj}(E))/2$, and conversely. The measures $m$ and $\nu$ are measures on the cone that do not charge $\{0\}$. Condition (2.9), written "$<\infty$" on the page, is stated as integrability: near $0$ the integrand equals $\langle \xi, u\rangle \ge 0$, and away from $0$ it is bounded against a finite measure, so the two agree. The truncation function is a continuous map on $M_d$ that preserves $S_d$, bounded and equal to the identity near $0$ on $S_d$; only its values on $S_d$ enter.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §2, p. 8 (truncation function), Definition 2.3 and (2.3)–(2.11), pp. 8–9; (2.13), p. 9; (2.16)–(2.17), p. 10

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

open MeasureTheory

namespace AffinePSD.Necessity

/-- A truncation function `χ : S_d → S_d`: bounded, continuous, with `χ(ξ) = ξ` in a neighbourhood of `0`
(arXiv:0910.0137v3, §2, p. 8, before Definition 2.3). It is given on `M_d`, maps `S_d` into `S_d`, and
only its values on `S_d` matter. -/
structure Trunc (d : ℕ) where
  χ : Mat d → Mat d
  cont : Continuous χ
  bdd : ∃ C : ℝ, ∀ ξ, fnorm (χ ξ) ≤ C
  symm : ∀ ξ, IsSym ξ → IsSym (χ ξ)
  near0 : ∃ ε > 0, ∀ ξ, IsSym ξ → fnorm ξ < ε → χ ξ = ξ

/-- The data of a parameter set `(α, b, β^{ij}, c, γ, m, μ)` of Definition 2.3 (pp. 8–9), without the
admissibility conditions (see `AdmissibleCore`, `Admissible`).

**Formalization Note (μ ↦ (ν, H)).** The matrix `μ = (μ_{ij})` of finite signed measures on
`S_d^+ ∖ {0}` with `μ(E) ∈ S_d^+` is encoded by a finite measure `ν` on the cone with `ν{0} = 0` and a
PSD-valued, entrywise `ν`-integrable density `H`: `μ_{ij}(dξ) = H_{ij}(ξ) ν(dξ)`. Every such `μ` has this
form (take `ν = ∑_i μ_{ii}`, which dominates every `μ_{ij}`), and conversely, so nothing is lost. The
measures `m`, `ν` live on the cone; "on `S_d^+ ∖ {0}`" is the condition that they do not charge `{0}`. -/
structure Params (d : ℕ) where
  α : Mat d
  b : Mat d
  β : Fin d → Fin d → Mat d
  c : ℝ
  γ : Mat d
  m : Measure (Cone d)
  ν : Measure (Cone d)
  H : Cone d → Mat d

/-- `B(x) = ∑_{i,j} β^{ij} x_{ij}` (2.10). -/
def Bmap {d : ℕ} (P : Params d) (x : Mat d) : Mat d := ∑ i, ∑ j, x i j • P.β i j

/-- `B^⊤(u)` with `B^⊤_{ij}(u) = ⟨β^{ij}, u⟩` (after (2.17), p. 10). -/
def BT {d : ℕ} (P : Params d) (u : Mat d) : Mat d := fun i j => tr (P.β i j) u

/-- The kernel `M(x, dξ) = ⟨x, μ(dξ)⟩ / (‖ξ‖² ∧ 1)` (2.8), here `tr(x H(ξ)) / (‖ξ‖² ∧ 1) ν(dξ)`.
It is used for `x ∈ S_d^+`, where `tr(x H(ξ)) ≥ 0`. At `ξ = 0` the denominator vanishes; `ν{0} = 0` makes
this irrelevant. -/
noncomputable def Mker {d : ℕ} (P : Params d) (x : Mat d) : Measure (Cone d) :=
  P.ν.withDensity (fun ξ => ENNReal.ofReal (tr x (P.H ξ) / min (fnorm (ξ : Mat d) ^ 2) 1))

/-- `A_{ijkl}(x) = x_{ik}α_{jl} + x_{il}α_{jk} + x_{jk}α_{il} + x_{jl}α_{ik}` (2.13). -/
def Acoef {d : ℕ} (P : Params d) (x : Mat d) (i j k l : Fin d) : ℝ :=
  x i k * P.α j l + x i l * P.α j k + x j k * P.α i l + x j l * P.α i k

/-- `F(u) = ⟨b, u⟩ + c − ∫_{S_d^+∖{0}} (e^{−⟨u,ξ⟩} − 1) m(dξ)` (2.16). -/
noncomputable def Fpar {d : ℕ} (P : Params d) (u : Mat d) : ℝ :=
  tr P.b u + P.c - ∫ ξ, (Real.exp (- tr u (ξ : Mat d)) - 1) ∂P.m

/-- `R(u) = −2uαu + B^⊤(u) + γ − ∫_{S_d^+∖{0}} (e^{−⟨u,ξ⟩} − 1 + ⟨χ(ξ), u⟩)/(‖ξ‖² ∧ 1) μ(dξ)` (2.17),
the integral taken entrywise against `μ_{ij}(dξ) = H_{ij}(ξ) ν(dξ)`. -/
noncomputable def Rpar {d : ℕ} (χ : Trunc d) (P : Params d) (u : Mat d) : Mat d :=
  -(2 : ℝ) • mmul (mmul u P.α) u + BT P u + P.γ -
    (fun i j => ∫ ξ, (Real.exp (- tr u (ξ : Mat d)) - 1 + tr (χ.χ ξ) u) /
      min (fnorm (ξ : Mat d) ^ 2) 1 * P.H ξ i j ∂P.ν)

/-- The integrands of (2.16) and (2.17) at `u` are integrable (used as the junk-integral guard wherever
a theorem concludes a formula for `F` or `R`). -/
def IntegrableFR {d : ℕ} (χ : Trunc d) (P : Params d) (u : Mat d) : Prop :=
  Integrable (fun ξ : Cone d => Real.exp (- tr u (ξ : Mat d)) - 1) P.m ∧
  ∀ i j, Integrable (fun ξ : Cone d => (Real.exp (- tr u (ξ : Mat d)) - 1 + tr (χ.χ ξ) u) /
      min (fnorm (ξ : Mat d) ^ 2) 1 * P.H ξ i j) P.ν

/-- Definition 2.3 (pp. 8–9) without the drift condition (2.4): conditions (2.3), (2.5)–(2.11) and
`b ∈ S_d`. -/
def AdmissibleCore {d : ℕ} (χ : Trunc d) (P : Params d) : Prop :=
  -- (2.3), (2.5), (2.6), b ∈ S_d
  PSD P.α ∧ 0 ≤ P.c ∧ PSD P.γ ∧ IsSym P.b ∧
  -- (2.7): m is a Borel measure on S_d^+ ∖ {0} with ∫ (‖ξ‖ ∧ 1) m(dξ) < ∞
  P.m {ξ : Cone d | (ξ : Mat d) = 0} = 0 ∧
  ∫⁻ ξ, ENNReal.ofReal (min (fnorm (ξ : Mat d)) 1) ∂P.m < ⊤ ∧
  -- μ: a matrix of finite signed measures on S_d^+ ∖ {0} with μ(E) ∈ S_d^+
  IsFiniteMeasure P.ν ∧ P.ν {ξ : Cone d | (ξ : Mat d) = 0} = 0 ∧ Measurable P.H ∧
  (∀ ξ, PSD (P.H ξ)) ∧ (∀ i j, Integrable (fun ξ => P.H ξ i j) P.ν) ∧
  -- (2.9)
  (∀ x u : Cone d, tr (x : Mat d) (u : Mat d) = 0 →
    Integrable (fun ξ : Cone d => tr (χ.χ ξ) (u : Mat d)) (Mker P x)) ∧
  -- β^{ij} = β^{ji} ∈ S_d
  (∀ i j, P.β i j = P.β j i ∧ IsSym (P.β i j)) ∧
  -- (2.11)
  (∀ x u : Cone d, tr (x : Mat d) (u : Mat d) = 0 →
    0 ≤ tr (Bmap P x) u - ∫ ξ, tr (χ.χ ξ) (u : Mat d) ∂(Mker P x))

/-- Definition 2.3 (pp. 8–9): an admissible parameter set associated with `χ`, i.e. `AdmissibleCore`
together with the drift condition (2.4) `b ⪰ (d − 1)α`. -/
def Admissible {d : ℕ} (χ : Trunc d) (P : Params d) : Prop :=
  AdmissibleCore χ P ∧ PSD (P.b - ((d : ℝ) - 1) • P.α)

end AffinePSD.Necessity



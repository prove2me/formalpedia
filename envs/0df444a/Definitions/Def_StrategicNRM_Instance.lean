-- Prove2me | Definitions.Def_StrategicNRM_Instance
-- name    : StrategicNRM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:51.111123+00:00
-- url     : https://prove2.me/theorems/a813dfe3-be45-4a1e-902e-f93b3aa8115b
-- title:
--   Primitives: products, resources, valuations and the type law $\mu$
-- statement:
--   A seller has $n$ products and $m$ resources over a selling season $[0,T]$, with $T>0$. Product $j$ uses $A_{ij}\in\{0,1\}$ units of resource $i$, and the initial inventory is $x_0\in\mathbb N^m$. Customers arrive at rate $\lambda>0$.
--
--   A customer **type** is $\phi=(t_\phi,v_\phi,d_\phi)$: the arrival time, the valuations upon arrival and the decay rates. The set $\Phi$ of types is $[0,T]\times\mathbb R_+^n\times\mathbb R_+^n$. A type's law $\mu$ is the following: $(t,d)$ has a law $\kappa$ with $t$ uniform on $[0,T]$ and $d\ge 0$; and $v^1,\dots,v^n$ are independent of $(t,d)$ and of each other, with densities $f_j$ on $[0,\infty)$. The customers of a season form a Poisson crowd of mean size $\lambda T$ with mark law $\mu$.
--
--   Writing $\phi_{j,w}$ for $\phi$ with $v^j$ replaced by $w$, the utility of $\phi$ from the outcome $y=(\tau,a,p)$ is
--
--   $$
--   U(\phi,y)=\sum_{j=1}^n v^j_\phi e^{-d^j_\phi(\tau-t_\phi)}a^j-p .
--   $$
--
--   This is the data of every result of the mission.
--
--   **Formalization Note** `Option (Fin n)` encodes $a\in\{0,1\}^n$ with $\mathbf 1^\top a\le 1$. The law $\kappa$ makes $d$ free to depend on $t$, as p.7 allows: only the valuations are independent of everything else. The inventory is natural-valued, because p.6 says resources are indivisible. $E_{-\phi}[g]$ is written as an integral over a fresh Poisson crowd, since the others of a customer form a Poisson crowd again. No condition is placed on $n$ or $m$.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §2, pp.6–7

import Mathlib
import Definitions.Def_StrategicNRM_PoissonCrowd

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StrategicNRM

/-- The primitives of the selling problem with `n` products and `m` resources.

Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), §2, pp.6–7: the horizon `T`, the arrival
rate `λ`, the resource-product matrix `A` with entries in `{0,1}`, the inventory `x₀`, the
valuation densities `fⱼ` on `[0,∞)`, and the joint law `κ` of (arrival time, decay rates), whose
arrival coordinate is uniform on `[0,T]` and whose decay rates are nonnegative.

**Formalization Note.** `x0` is natural-valued: p.6 writes `x₀ ∈ ℝᵐ` but also "Both resources and
products are indivisible" and tests `Xⁱ_{t−} = 0`. The decay rates may depend on the arrival time
and on each other, as p.7 allows; only the valuations are independent of everything else. No
condition is placed on `n` or `m`. -/
structure Instance (n m : ℕ) where
  T : ℝ
  lam : ℝ
  T_pos : 0 < T
  lam_pos : 0 < lam
  A : Fin m → Fin n → ℕ
  A_le_one : ∀ r j, A r j ≤ 1
  x0 : Fin m → ℕ
  f : Fin n → ℝ → ℝ
  f_meas : ∀ j, Measurable (f j)
  f_nonneg : ∀ j v, 0 ≤ f j v
  f_neg : ∀ j v, v < 0 → f j v = 0
  f_mass : ∀ j, ∫⁻ v, ENNReal.ofReal (f j v) = 1
  κ : Measure (ℝ × (Fin n → ℝ))
  κ_prob : IsProbabilityMeasure κ
  κ_arrival : κ.map Prod.fst = ProbabilityTheory.cond volume (Set.Icc 0 T)
  κ_decay : ∀ᵐ x ∂κ, ∀ j, 0 ≤ x.2 j

/-- A customer type `φ = (t_φ, v_φ, d_φ)`: arrival time, valuations upon arrival, decay rates.
Chen & Trichakis, SSRN 2959489, §2, p.6. -/
abbrev CType (n : ℕ) := ℝ × (Fin n → ℝ) × (Fin n → ℝ)

variable {n m : ℕ}

/-- The set `Φ` of types: `t_φ ∈ [0,T]`, `v_φ ∈ ℝⁿ₊`, `d_φ ∈ ℝⁿ₊` (p.6). -/
def Instance.IsType (I : Instance n m) (φ : CType n) : Prop :=
  φ.1 ∈ Set.Icc 0 I.T ∧ (∀ j, 0 ≤ φ.2.1 j) ∧ ∀ j, 0 ≤ φ.2.2 j

/-- `φ_{j,w}`: customer `φ` whose valuation for product `j` is `w` (p.9). -/
def withVal (φ : CType n) (j : Fin n) (w : ℝ) : CType n :=
  (φ.1, Function.update φ.2.1 j w, φ.2.2)

/-- The law of the valuation for product `j`, with density `fⱼ`. -/
noncomputable def Instance.valLaw (I : Instance n m) (j : Fin n) : Measure ℝ :=
  volume.withDensity fun v => ENNReal.ofReal (I.f j v)

/-- The law `μ` of one customer's type: `(t,d) ∼ κ`, and `v¹, …, vⁿ` independent of `(t,d)` and of
each other with densities `fⱼ`. This is the assumption of p.7 that `vʲ` is independent of
`t, v⁻ʲ, d`, for every `j`. -/
noncomputable def Instance.typeLaw (I : Instance n m) : Measure (CType n) :=
  (I.κ.prod (Measure.pi I.valLaw)).map fun x => (x.1.1, x.2, x.1.2)

/-- The law of the customers of a selling season: a Poisson crowd of mean size `λT` and i.i.d.
types with law `μ`. It is also the law, under `E₋φ`, of the customers other than `φ`, because
removing one point from a Poisson process leaves a Poisson process.

**Formalization Note.** `E₋φ[g(c)]` is written `∫ c, g c ∂I.law`. -/
noncomputable def Instance.law (I : Instance n m) : Measure (Crowd (CType n)) :=
  crowdLaw (Real.toNNReal (I.lam * I.T)) I.typeLaw

/-- `aʲ`, the indicator that `a` is a purchase of product `j`.

**Formalization Note.** `Option (Fin n)` encodes `a ∈ {0,1}ⁿ` with `1ᵀa ≤ 1`: `none` is no
purchase, `some j` is one unit of product `j`. -/
def alloc (a : Option (Fin n)) (j : Fin n) : ℝ := if a = some j then 1 else 0

/-- The units of resource `r` used by the purchase `a`: `Σⱼ A_{rj} aʲ`. -/
def Instance.usage (I : Instance n m) (r : Fin m) (a : Option (Fin n)) : ℕ :=
  match a with
  | some j => I.A r j
  | none => 0

/-- `U(φ, y) = Σⱼ vʲ e^{−dʲ(τ−t)} aʲ − p` for `y = (τ, a, p)` (p.7). -/
noncomputable def utility (φ : CType n) (y : ℝ × Option (Fin n) × ℝ) : ℝ :=
  (∑ j, φ.2.1 j * Real.exp (-φ.2.2 j * (y.1 - φ.1)) * alloc y.2.1 j) - y.2.2

end StrategicNRM



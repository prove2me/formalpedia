-- Prove2me | Definitions.Def_PuhaWardFluid_Limit_FluidModel
-- name    : PuhaWardFluid_Limit_FluidModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:44.45446+00:00
-- url     : https://prove2.me/theorems/cc441601-3253-4cda-9489-1dd1037f93ee
-- title:
--   §3.1, pp. 13–14 — class laws, hazards, the state space 𝕏, the auxiliary functions (38)–(43) and fluid model solutions (Definition 4)
-- statement:
--   This file defines the fluid model of Puha–Ward (§1.1.5, pp. 4–5, and §3.1, pp. 13–14).
--
--   **Class data.** For each class $j\in\{1,\dots,J\}$ the service-time distribution $G^s_j$ on $\mathbb R_+$ has density $g^s_j$, and the patience-time distribution $G^r_j$ on $[0,\infty]$ has density $g^r_j$ on $\mathbb R_+$ (the missing mass is an atom at $\infty$). For a distribution function $G$ with density $g$:
--   $$H=\sup\{x\in\mathbb R_+:G(x)<1\},\qquad h(x)=\frac{g(x)}{1-G(x)}\ (x\in[0,H)),\qquad G_y(x)=\frac{G(x+y)-G(y)}{1-G(y)} .$$
--
--   **State space.** $\mathbb X=\mathbb R^J_+\times\prod_j\mathbf M[0,H^s_j)\times\prod_j\mathbf M[0,H^r_j)$, where $\mathbf M[0,H)$ is the space of finite nonnegative Borel measures on $[0,H)$ with the weak topology. For a path $(X,\nu,\eta)$ in $\mathbb X$ write $F_{j,t}(x)=\langle 1_{[0,x]},\eta_j(t)\rangle$ and $(F_{j,t})^{-1}(y)=\inf\{x\in\mathbb R_+:F_{j,t}(x)\ge y\}$ ($=\infty$ if the set is empty).
--
--   **The set $\mathbf F$.** A path is in $\mathbf F$ if it is rcll and for every $t\ge0$ and $j$: (35) $\langle 1,\nu_j(t)\rangle\le X_j(t)\le\langle1,\nu_j(t)\rangle+\langle1,\eta_j(t)\rangle$; (36) $\sum_j\langle1,\nu_j(t)\rangle\le1$; (37) $\int_0^t\langle h^s_j,\nu_j(u)\rangle du<\infty$ and $\int_0^t\langle h^r_j,\eta_j(u)\rangle du<\infty$.
--
--   **Auxiliary functions** (38)–(43): $B_j=\langle1,\nu_j\rangle$, $Q_j=X_j-B_j$,
--   $$R_j(t)=\int_0^t\int_0^{Q_j(u)}h^r_j\big((F_{j,u})^{-1}(y)\big)\,dy\,du,\qquad D_j(t)=\int_0^t\langle h^s_j,\nu_j(u)\rangle du,$$
--   $K_j(t)=B_j(t)+D_j(t)-B_j(0)$ and $I(t)=1-\sum_jB_j(t)$.
--
--   **Definition 4.** Given an arrival function $E\in\mathbf D_\uparrow(\mathbb R^J_+)$, a **fluid model solution** for $E$ is a path $(X,\nu,\eta)\in\mathbf F$ such that every $K_j$ is nondecreasing (44), $X_j(t)=X_j(0)+E_j(t)-R_j(t)-D_j(t)$ (45), and for all $j$, $f\in C_b(\mathbb R_+)$, $t\ge0$,
--   $$\langle f,\nu_j(t)\rangle=\Big\langle f(\cdot+t)\tfrac{1-G^s_j(\cdot+t)}{1-G^s_j(\cdot)},\nu_j(0)\Big\rangle+\int_0^tf(t-u)\big(1-G^s_j(t-u)\big)\,dK_j(u),\tag{46}$$
--   $$\langle f,\eta_j(t)\rangle=\Big\langle f(\cdot+t)\tfrac{1-G^r_j(\cdot+t)}{1-G^r_j(\cdot)},\eta_j(0)\Big\rangle+\int_0^tf(t-u)\big(1-G^r_j(t-u)\big)\,dE_j(u).\tag{47}$$
--   A measure **does not charge points** if it gives zero mass to every singleton.
--
--   Fluid model solutions are the deterministic objects that, by Theorem 1, describe every fluid limit point of the many-server queue under an admissible head-of-the-line policy.
--
--   **Formalization Note** The auxiliary functions are computed from the path, never chosen: $R_j$, $D_j$ and the integrals of (37) are Lebesgue integrals of nonnegative functions in $[0,\infty]$, and $R_j$, $D_j$ are their real values (finite on $\mathbf F$). The hazard is valued in $[0,\infty]$ and set to $0$ off $[0,H)$; $h^r_j(\infty):=0$, which only affects a null set of $y$ in (40). In (46)–(47) the paper writes $G^s$, $G^r$ inside the bracket; the class-$j$ functions are meant. The $dK_j$ and $dE_j$ integrals are over $[0,t]$ against the Lebesgue–Stieltjes measure of the path extended by $0$ to $(-\infty,0)$ (no atom at $0$, since $K_j(0)=E_j(0)=0$); the junk value $0$ used when that extension is not monotone is never reached for a fluid model solution, since (44) is part of the definition. $\mathbf M[0,H)$ is `FiniteMeasure` on the subtype $[0,H)\subset\mathbb R_{\ge0}$; the distance on $\mathbb X$ used for $J_1$ is the maximum of the sup-norm distance on $\mathbb R^J$ and the Lévy–Prokhorov distances of the measure coordinates.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, pp. 4–6, 13–14 (PDF 5–7, 14–15), §1.1.5 (1)–(2), §2.1.2, §3.1 (33)–(47), Definition 4

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Paths

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace PuhaWardFluid.Limit

/-! ### Distribution data (§1.1.5, pp. 4–5; §2.1.2, p. 6) -/

/-- The cumulative distribution function `G(x) = ∫_0^x g(y) dy` of a density `g` on `ℝ₊`
(`G(x) = 0` for `x < 0`). -/
noncomputable def cdf (g : ℝ → ℝ≥0) (x : ℝ) : ℝ :=
  (∫⁻ y in Set.Icc 0 x, (g y : ℝ≥0∞)).toReal

/-- The right edge of the support (1): `H = sup {x ∈ ℝ₊ : G(x) < 1} ∈ (0, ∞]`. -/
noncomputable def edge (g : ℝ → ℝ≥0) : ℝ≥0∞ :=
  ⨆ (x : ℝ) (_ : 0 ≤ x ∧ cdf g x < 1), ENNReal.ofReal x

/-- The hazard function `h(x) = g(x)/(1 − G(x))` for `x ∈ [0, H)`, valued in `[0, ∞]`; it is set
to `0` off `[0, H)`, where the paper leaves it undefined. -/
noncomputable def hazard (g : ℝ → ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x ∧ ENNReal.ofReal x < edge g then (g x : ℝ≥0∞) / ENNReal.ofReal (1 - cdf g x) else 0

/-- The hazard at an extended argument `z ∈ [0, ∞]`; `h(∞) := 0`. -/
noncomputable def hazardE (g : ℝ → ℝ≥0) (z : ℝ≥0∞) : ℝ≥0∞ :=
  if z = ⊤ then 0 else hazard g z.toReal

/-- The conditional distribution function (2): `G_y(x) = (G(x + y) − G(y))/(1 − G(y))`. -/
noncomputable def condCdf (g : ℝ → ℝ≥0) (y x : ℝ) : ℝ :=
  (cdf g (x + y) - cdf g y) / (1 - cdf g y)

/-- The class data of the model (§2.1.2, p. 6): for each class `j`,
* `gs j`, the density of the absolutely continuous service-time distribution `G^s_j` on `ℝ₊`
  (total mass `1`);
* `gr j`, the density on `ℝ₊` of the patience-time distribution `G^r_j` on `[0, ∞]`
  (total mass `≤ 1` on `ℝ₊`; the deficit is the atom of `G^r_j` at `∞`).
Both densities vanish on `(−∞, 0)`. -/
structure ClassLaws (J : ℕ) where
  gs : Fin J → ℝ → ℝ≥0
  gr : Fin J → ℝ → ℝ≥0
  gs_meas : ∀ j, Measurable (gs j)
  gr_meas : ∀ j, Measurable (gr j)
  gs_neg : ∀ j x, x < 0 → gs j x = 0
  gr_neg : ∀ j x, x < 0 → gr j x = 0
  gs_total : ∀ j, ∫⁻ x, (gs j x : ℝ≥0∞) = 1
  gr_total : ∀ j, ∫⁻ x, (gr j x : ℝ≥0∞) ≤ 1

variable {J : ℕ}

namespace ClassLaws
/-- `G^s_j`. -/
noncomputable def Gs (L : ClassLaws J) (j : Fin J) : ℝ → ℝ := cdf (L.gs j)
/-- `G^r_j` restricted to `ℝ₊`. -/
noncomputable def Gr (L : ClassLaws J) (j : Fin J) : ℝ → ℝ := cdf (L.gr j)
/-- `H^s_j`. -/
noncomputable def Hs (L : ClassLaws J) (j : Fin J) : ℝ≥0∞ := edge (L.gs j)
/-- `H^r_j`. -/
noncomputable def Hr (L : ClassLaws J) (j : Fin J) : ℝ≥0∞ := edge (L.gr j)
/-- `h^s_j`. -/
noncomputable def hs (L : ClassLaws J) (j : Fin J) : ℝ → ℝ≥0∞ := hazard (L.gs j)
/-- `h^r_j`. -/
noncomputable def hr (L : ClassLaws J) (j : Fin J) : ℝ → ℝ≥0∞ := hazard (L.gr j)
end ClassLaws

/-! ### Measure spaces and the state space 𝕏 (§1.1.5, p. 4; §3.1, p. 13) -/

/-- The interval `[0, H)`, `H ∈ (0, ∞]`, as a subtype of `ℝ≥0`. -/
abbrev Iv (H : ℝ≥0∞) : Type := {x : ℝ≥0 // (x : ℝ≥0∞) < H}

/-- `⟨f, μ⟩ = ∫ f dμ` for a real function `f` on `ℝ` and `μ ∈ M[0, H)`. -/
noncomputable def pair {H : ℝ≥0∞} (f : ℝ → ℝ) (μ : FiniteMeasure (Iv H)) : ℝ :=
  ∫ x, f ((x : ℝ≥0) : ℝ) ∂(μ : Measure (Iv H))

/-- `⟨h, μ⟩ = ∫ h dμ ∈ [0, ∞]` for a nonnegative extended function `h`. -/
noncomputable def lpair {H : ℝ≥0∞} (h : ℝ → ℝ≥0∞) (μ : FiniteMeasure (Iv H)) : ℝ≥0∞ :=
  ∫⁻ x, h ((x : ℝ≥0) : ℝ) ∂(μ : Measure (Iv H))

/-- The total mass `⟨1, μ⟩`. -/
noncomputable def mass1 {H : ℝ≥0∞} (μ : FiniteMeasure (Iv H)) : ℝ := (μ.mass : ℝ)

/-- `μ` **does not charge points** (p. 4): `⟨1_{x}, μ⟩ = 0` for all `x ∈ [0, H)`. -/
def NoCharge {H : ℝ≥0∞} (μ : FiniteMeasure (Iv H)) : Prop :=
  ∀ x : Iv H, (μ : Measure (Iv H)) {x} = 0

/-- `F(x) = ⟨1_{[0,x]}, μ⟩` (33). -/
noncomputable def Fcdf {H : ℝ≥0∞} (μ : FiniteMeasure (Iv H)) (x : ℝ) : ℝ :=
  ((μ : Measure (Iv H)) {z | ((z : ℝ≥0) : ℝ) ≤ x}).toReal

/-- `F^{-1}(y) = inf {x ∈ ℝ₊ : F(x) ≥ y}` (34), valued in `[0, ∞]`, and `= ∞` when the set is
empty. -/
noncomputable def FcdfInv {H : ℝ≥0∞} (μ : FiniteMeasure (Iv H)) (y : ℝ) : ℝ≥0∞ :=
  ⨅ (x : ℝ≥0) (_ : y ≤ Fcdf μ x), (x : ℝ≥0∞)

/-- The state space `𝕏 = ℝ^J₊ × ×_j M[0, H^s_j) × ×_j M[0, H^r_j)` (p. 13), with the product of
the Euclidean and weak topologies. Nonnegativity of the first coordinate is imposed by (35). -/
abbrev Xsp (L : ClassLaws J) : Type :=
  (Fin J → ℝ) × (∀ j, FiniteMeasure (Iv (L.Hs j))) × (∀ j, FiniteMeasure (Iv (L.Hr j)))

/-- A metric for `𝕏`: the maximum of the sup-norm distance on `ℝ^J` and the Lévy–Prokhorov
distances of the measure coordinates (the latter metrize the weak topology). -/
noncomputable def dX (L : ClassLaws J) (a b : Xsp L) : ℝ :=
  max (dist a.1 b.1)
    (max (⨆ j, levyProkhorovDist (a.2.1 j : Measure (Iv (L.Hs j))) (b.2.1 j : Measure _))
      (⨆ j, levyProkhorovDist (a.2.2 j : Measure (Iv (L.Hr j))) (b.2.2 j : Measure _)))

/-- The distance on `ℝ` used for real-valued paths. -/
def dR (a b : ℝ) : ℝ := |a - b|

/-! ### Auxiliary functions (38)–(43) of a path `y = (X, ν, η) : ℝ₊ → 𝕏` -/

section Aux
variable (L : ClassLaws J) (y : ℝ≥0 → Xsp L)

/-- `X_j(t)`. -/
def flX (t : ℝ≥0) (j : Fin J) : ℝ := (y t).1 j
/-- `ν_j(t)`. -/
def flNu (t : ℝ≥0) (j : Fin J) : FiniteMeasure (Iv (L.Hs j)) := (y t).2.1 j
/-- `η_j(t)`. -/
def flEta (t : ℝ≥0) (j : Fin J) : FiniteMeasure (Iv (L.Hr j)) := (y t).2.2 j

/-- (38) `B_j(t) = ⟨1, ν_j(t)⟩`. -/
noncomputable def flB (t : ℝ≥0) (j : Fin J) : ℝ := mass1 (flNu L y t j)
/-- (39) `Q_j(t) = X_j(t) − B_j(t)`. -/
noncomputable def flQ (t : ℝ≥0) (j : Fin J) : ℝ := flX L y t j - flB L y t j

/-- The double integral of (40), in `[0, ∞]`:
`∫_0^t ∫_0^{Q_j(u)} h^r_j((F_{j,u})^{-1}(y)) dy du` with `F_{j,u}(x) = ⟨1_{[0,x]}, η_j(u)⟩`. -/
noncomputable def flRInt (t : ℝ≥0) (j : Fin J) : ℝ≥0∞ :=
  ∫⁻ u in Set.Icc (0 : ℝ) t, ∫⁻ z in Set.Icc (0 : ℝ) (flQ L y u.toNNReal j),
    hazardE (L.gr j) (FcdfInv (flEta L y u.toNNReal j) z)

/-- (40) `R_j(t)`, the real value of `flRInt` (finite for paths in `𝐅`). -/
noncomputable def flR (t : ℝ≥0) (j : Fin J) : ℝ := (flRInt L y t j).toReal

/-- The integral of (41), in `[0, ∞]`: `∫_0^t ⟨h^s_j, ν_j(u)⟩ du`. -/
noncomputable def flDInt (t : ℝ≥0) (j : Fin J) : ℝ≥0∞ :=
  ∫⁻ u in Set.Icc (0 : ℝ) t, lpair (L.hs j) (flNu L y u.toNNReal j)

/-- The integral `∫_0^t ⟨h^r_j, η_j(u)⟩ du ∈ [0, ∞]` of (37). -/
noncomputable def flSInt (t : ℝ≥0) (j : Fin J) : ℝ≥0∞ :=
  ∫⁻ u in Set.Icc (0 : ℝ) t, lpair (L.hr j) (flEta L y u.toNNReal j)

/-- (41) `D_j(t)`, the real value of `flDInt` (finite for paths in `𝐅`). -/
noncomputable def flD (t : ℝ≥0) (j : Fin J) : ℝ := (flDInt L y t j).toReal
/-- (42) `K_j(t) = B_j(t) + D_j(t) − B_j(0)`. -/
noncomputable def flK (t : ℝ≥0) (j : Fin J) : ℝ := flB L y t j + flD L y t j - flB L y 0 j
/-- (43) `I(t) = 1 − ∑_j B_j(t)`. -/
noncomputable def flI (t : ℝ≥0) : ℝ := 1 - ∑ j, flB L y t j

end Aux

/-- The extension by `0` to `(−∞, 0)` of a real path on `ℝ₊`. -/
noncomputable def extPath (x : ℝ≥0 → ℝ) (s : ℝ) : ℝ := if s < 0 then 0 else x s.toNNReal

open Classical in
/-- The Stieltjes integral `∫_{[0,t]} φ(u) dx(u)` of a nondecreasing real path `x` with `x(0) = 0`,
against the Lebesgue–Stieltjes measure of its extension by `0` to `(−∞, 0)` (no atom at `0`
since `x(0−) = x(0) = 0`). Junk value `0` if the extension is not monotone. -/
noncomputable def stieltjesInt (x : ℝ≥0 → ℝ) (φ : ℝ → ℝ) (t : ℝ≥0) : ℝ :=
  if h : Monotone (extPath x) then ∫ u in Set.Icc (0 : ℝ) t, φ u ∂h.stieltjesFunction.measure
  else 0

/-- The set `𝐅 ⊂ D(𝕏)` (p. 14): rcll paths satisfying (35)–(37) at every `t ≥ 0`. -/
def InF (L : ClassLaws J) (y : ℝ≥0 → Xsp L) : Prop :=
  IsCadlag y ∧ ∀ t : ℝ≥0,
    (∀ j, flB L y t j ≤ flX L y t j ∧ flX L y t j ≤ flB L y t j + mass1 (flEta L y t j)) ∧
    (∑ j, flB L y t j ≤ 1) ∧
    (∀ j, flDInt L y t j < ⊤ ∧ flSInt L y t j < ⊤)

/-- **Definition 4** (p. 14). A **fluid model solution** for the arrival function `E ∈ D↑(ℝ^J₊)`
is `(X, ν, η) ∈ 𝐅` satisfying (44) (`K_j` nondecreasing) and the fluid model equations
(45) `X_j(t) = X_j(0) + E_j(t) − R_j(t) − D_j(t)`,
(46) `⟨f, ν_j(t)⟩ = ⟨f(·+t)(1 − G^s_j(·+t))/(1 − G^s_j(·)), ν_j(0)⟩ + ∫_0^t f(t−u)(1 − G^s_j(t−u)) dK_j(u)`,
(47) `⟨f, η_j(t)⟩ = ⟨f(·+t)(1 − G^r_j(·+t))/(1 − G^r_j(·)), η_j(0)⟩ + ∫_0^t f(t−u)(1 − G^r_j(t−u)) dE_j(u)`,
for all `j`, `f ∈ C_b(ℝ₊)` and `t ≥ 0`, where the auxiliary functions are computed from the path
by (38)–(43). -/
def IsFluidSol (L : ClassLaws J) (E : ℝ≥0 → Fin J → ℝ) (y : ℝ≥0 → Xsp L) : Prop :=
  IsDUp E ∧ InF L y ∧
    (∀ j, Monotone fun t => flK L y t j) ∧
    (∀ j t, flX L y t j = flX L y 0 j + E t j - flR L y t j - flD L y t j) ∧
    (∀ j (f : ℝ≥0 →ᵇ ℝ) (t : ℝ≥0),
      pair (fun x => f x.toNNReal) (flNu L y t j) =
        pair (fun x => f (x.toNNReal + t) * (1 - L.Gs j (x + t)) / (1 - L.Gs j x)) (flNu L y 0 j) +
        stieltjesInt (fun s => flK L y s j)
          (fun u => f (t - u.toNNReal) * (1 - L.Gs j ((t : ℝ) - u))) t) ∧
    (∀ j (f : ℝ≥0 →ᵇ ℝ) (t : ℝ≥0),
      pair (fun x => f x.toNNReal) (flEta L y t j) =
        pair (fun x => f (x.toNNReal + t) * (1 - L.Gr j (x + t)) / (1 - L.Gr j x)) (flEta L y 0 j) +
        stieltjesInt (fun s => E s j)
          (fun u => f (t - u.toNNReal) * (1 - L.Gr j ((t : ℝ) - u))) t)

/-- Continuity of the auxiliary functions `B, Q, R, D, K` (each coordinate) and `I`. -/
def AuxContinuous (L : ClassLaws J) (y : ℝ≥0 → Xsp L) : Prop :=
  (∀ j, Continuous (fun t => flB L y t j) ∧ Continuous (fun t => flQ L y t j) ∧
    Continuous (fun t => flR L y t j) ∧ Continuous (fun t => flD L y t j) ∧
    Continuous (fun t => flK L y t j)) ∧
  Continuous (flI L y)

end PuhaWardFluid.Limit



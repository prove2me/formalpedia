-- Prove2me | Definitions.Def_SurgeSpatial_Attraction_Setting
-- name    : SurgeSpatial_Attraction_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:56.716881+00:00
-- url     : https://prove2.me/theorems/483a70d6-3c85-457e-b507-e680bbf12322
-- title:
--   §3.1–§6, App. B — the spatial pricing market: flows, utilities, V_B (3), equilibrium (Def. 1), (P2), local monopoly (4)–(5), ψ_x, attraction regions and sinks (Def. 2), X_a, Def. 3
-- statement:
--   This file sets up the spatial pricing model of Besbes, Castro and Lobel.
--
--   **The market.** The city is a set $\mathcal C\subseteq\mathbb R^2$ (with the Euclidean norm $\|\cdot\|$), carrying a finite *city measure* $\Gamma$, a finite *potential demand* measure $\Lambda$ and a finite *initial supply* measure $\Theta$ of drivers. At each location $y$ the willingness to pay of riders has CDF $F_y$, with $\bar F_y(q)=1-F_y(q)$; $\bar V>0$ is the top of its support, and $\alpha$ is the fraction of the fare paid to the driver. The **standing assumptions** (§3.1) are:
--
--   1. $\mathcal C$ is convex and compact; $\Gamma,\Lambda,\Theta$ are finite and concentrated on $\mathcal C$, with $\Lambda,\Theta\ll\Gamma$;
--   2. $\bar V>0$ and $0<\alpha<1$;
--   3. for every $y\in\mathcal C$, $F_y$ is a CDF supported on $[0,\bar V]$ ($F_y(q)=0$ for $q<0$, $F_y(\bar V)=1$), strictly increasing on $[0,\bar V]$, and the revenue $q\mapsto q\bar F_y(q)$ is continuous and unimodal on $[0,\bar V]$;
--   4. the demand density $\lambda=d\Lambda/d\Gamma$ is positive $\Gamma$-almost everywhere;
--   5. $(y,q)\mapsto F_y(q)$ is jointly measurable.
--
--   **Flows and utilities.** A feasible flow $\mathcal T\in\mathcal F(\Theta)$ is a finite measure on $\mathcal C\times\mathcal C$ with first marginal $\Theta$ and second marginal $\mathcal T_2\ll\Gamma$; $s^{\mathcal T}=d\mathcal T_2/d\Gamma$ is the post-relocation supply. Given a price mapping $p$, the utilization at $y$ is
--   $$R(y,q,s)=\begin{cases}\min\{1,\lambda(y)\bar F_y(q)/s\}&s>0,\\ 1&s=0,\ \lambda(y)\bar F_y(q)>0,\\ 0&\lambda(y)\bar F_y(q)=0,\end{cases}$$
--   a driver staying at $y$ earns $U(y,q,s)=\alpha\,q\,R(y,q,s)$ (eq. (1)), and a driver moving from $x$ to $y$ earns $\Pi(x,y)=U(y,p(y),s^{\mathcal T}(y))-\|y-x\|$ (eq. (2)). For $B\subseteq\mathcal C$,
--   $$V_B(x\mid p,\mathcal T)=\operatorname*{ess\,sup}_{B}\Pi(x,\cdot)$$
--   is the essential supremum with respect to $\Gamma$ restricted to $B$ (eq. (3)), and $V=V_{\mathcal C}$.
--
--   **Equilibrium and (P2).** $\mathcal T$ is a supply equilibrium (Definition 1) if $\mathcal T(\{(x,y)\in\mathcal C\times\mathcal C:\Pi(x,y)=V(x\mid p,\mathcal T)\})=\Theta(\mathcal C)$. A feasible solution of (P2) is a measurable $p$ with $p(y)\in[0,\bar V]$ on $\mathcal C$ together with an equilibrium $\mathcal T\in\mathcal F(\Theta)$; its value is $\gamma\int_{\mathcal C}V(x\mid p,\mathcal T)\,s^{\mathcal T}(x)\,d\Gamma(x)$ with $\gamma=(1-\alpha)/\alpha$.
--
--   **Local monopoly** (eqs. (4)–(5)). $R^{loc}_x(s)=\max_{q\in[0,\bar V]}q\min\{s,\lambda(x)\bar F_x(q)\}$; $\rho^{bal}_x(s)$ is the largest $\rho\in[0,\bar V]$ with $s\le\lambda(x)\bar F_x(\rho)$; $\rho^u_x$ is the maximizer of $\rho\bar F_x(\rho)$ on $[0,\bar V]$; $\rho^{loc}_x(s)=\max\{\rho^{bal}_x(s),\rho^u_x\}$. The **congestion function** is $\psi_x(s)=\alpha R^{loc}_x(s)/s$ for $s>0$ and $\psi_x(0)=\alpha\bar V$.
--
--   **Regions** (§6, App. B). $\mathcal{IR}(x\mid p,\mathcal T)=\{y\in\mathcal C: V(y)-\|y-x\|=V(x)\}$; the attraction region of $z$ is $A(z\mid p,\mathcal T)=\{x\in\mathcal C: z\in\mathcal{IR}(x)\}$ (Definition 2); $z\in\mathcal C$ is a **sink** if $A(z)\neq\emptyset$ and $z\notin A(z')$ for every $z'\in\mathcal C$, $z'\ne z$. Rays from $z$ are indexed by unit vectors $a$; $A_a(z)$ is the part of $A(z)$ on $\{z\}\cup\{z+ta:t>0\}$, and $X_a(z\mid p,\mathcal T)=z+t^*a$ with $t^*=\sup\{t\ge0:z+ta\in A(z)\}$.
--
--   **Local equilibrium** (p. B-5). For $B\subseteq\mathcal C$ and a measure $\tilde\Theta$, $\mathcal F_B(\tilde\Theta)$ is the set of finite measures on $B\times B$ with first marginal $\tilde\Theta$ and second marginal $\ll\Gamma|_B$; such a $\mathcal T$ is a local equilibrium in $B$ (Definition 3) if $\mathcal T(\{(x,y)\in B\times B:\Pi(x,y)=V_B(x)\})=\tilde\Theta(B)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)` (the paper says "a norm"; the ray geometry of Appendix B needs a strictly convex one). All measures live on $\mathbb R^2$ and are concentrated on $\mathcal C$. Densities are `rnDeriv … |>.toReal`, defined only $\Gamma$-a.e., so every pointwise claim about them in the mission is stated $\Gamma$-a.e. Prices are functions on $\mathbb R^2$; only their values on $\mathcal C$ enter. $\rho^{bal}$, $\rho^u$ and $R^{loc}$ are written as suprema, so $\rho^{loc}_x(0)=\bar V$ as in (5); $\rho^{bal}_x(s)=0$ when no price balances $s$, where (5) selects $\rho^u_x$ anyway. Added standing assumptions (implicit in the paper): Euclidean norm, joint measurability of $F$, $F_y$ a CDF supported on $[0,\bar V]$, unimodality as "strictly increasing then strictly decreasing", finiteness of the measures.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), pp. 8–16, B-1 and B-5: §3.1, (1)–(5), Definitions 1–3, (P2), ψ_x (p. 15), IR (p. 16), X_a (p. B-1), F_B(Θ̃) (p. B-5)

import Mathlib

namespace SurgeSpatial.Attraction

open MeasureTheory

/-- The plane `ℝ²` with its Euclidean norm. -/
abbrev E : Type := EuclideanSpace ℝ (Fin 2)

/-- The rays from a point are indexed by the unit vectors of `ℝ²`. -/
abbrev S1 : Type := Metric.sphere (0 : E) 1

/-- The primitives of the spatial pricing market of §3.1 (pp. 8–10): the city `C`, the city
measure `Γ`, the potential demand `Λ`, the initial supply `Θ`, the willingness-to-pay CDFs
`F y`, the upper end `Vbar` of their support, and the commission rate `α`. -/
structure Market where
  C : Set E
  Γ : Measure E
  Λ : Measure E
  Θ : Measure E
  F : E → ℝ → ℝ
  Vbar : ℝ
  α : ℝ

namespace Market

variable (M : Market)

/-- `F̄_y(q) = 1 - F_y(q)`. -/
noncomputable def Fbar (y : E) (q : ℝ) : ℝ := 1 - M.F y q

/-- `γ = (1 - α)/α`. -/
noncomputable def γ : ℝ := (1 - M.α) / M.α

/-- The potential demand density `λ(y) = dΛ/dΓ (y)`. -/
noncomputable def lam (y : E) : ℝ := (M.Λ.rnDeriv M.Γ y).toReal

/-- The standing assumptions of §3.1 (pp. 8–9). -/
structure Standing : Prop where
  convex_C : Convex ℝ M.C
  compact_C : IsCompact M.C
  finite_Γ : IsFiniteMeasure M.Γ
  finite_Λ : IsFiniteMeasure M.Λ
  finite_Θ : IsFiniteMeasure M.Θ
  Γ_conc : M.Γ M.Cᶜ = 0
  Λ_conc : M.Λ M.Cᶜ = 0
  Θ_conc : M.Θ M.Cᶜ = 0
  Λ_ac : M.Λ ≪ M.Γ
  Θ_ac : M.Θ ≪ M.Γ
  Vbar_pos : 0 < M.Vbar
  α_pos : 0 < M.α
  α_lt_one : M.α < 1
  F_mono : ∀ y ∈ M.C, Monotone (M.F y)
  F_nonneg : ∀ y ∈ M.C, ∀ q, 0 ≤ M.F y q
  F_le_one : ∀ y ∈ M.C, ∀ q, M.F y q ≤ 1
  F_neg : ∀ y ∈ M.C, ∀ q < 0, M.F y q = 0
  F_Vbar : ∀ y ∈ M.C, M.F y M.Vbar = 1
  F_strictMono : ∀ y ∈ M.C, StrictMonoOn (M.F y) (Set.Icc 0 M.Vbar)
  revenue_cont : ∀ y ∈ M.C, ContinuousOn (fun q => q * M.Fbar y q) (Set.Icc 0 M.Vbar)
  revenue_unimodal : ∀ y ∈ M.C, ∃ m ∈ Set.Icc 0 M.Vbar,
    StrictMonoOn (fun q => q * M.Fbar y q) (Set.Icc 0 m) ∧
    StrictAntiOn (fun q => q * M.Fbar y q) (Set.Icc m M.Vbar)
  lam_pos : ∀ᵐ y ∂M.Γ, 0 < M.lam y
  F_meas : Measurable (Function.uncurry M.F)

/-- The feasible flows `𝓕(Θ)` (p. 8): finite measures on `C × C` with first marginal `Θ` and
second marginal absolutely continuous with respect to `Γ`. -/
def FeasFlow (T : Measure (E × E)) : Prop :=
  IsFiniteMeasure T ∧ T (M.C ×ˢ M.C)ᶜ = 0 ∧ T.map Prod.fst = M.Θ ∧ T.map Prod.snd ≪ M.Γ

/-- The post-relocation supply density `s^𝒯(y) = d𝒯₂/dΓ (y)` (p. 9). -/
noncomputable def sT (T : Measure (E × E)) (y : E) : ℝ :=
  ((T.map Prod.snd).rnDeriv M.Γ y).toReal

/-- The utilization rate `R(y, q, s)` (p. 9), with explicit price `q` and supply `s`. -/
noncomputable def R (y : E) (q s : ℝ) : ℝ :=
  if 0 < s then min 1 (M.lam y * M.Fbar y q / s)
  else if 0 < M.lam y * M.Fbar y q then 1 else 0

/-- The utility `U(y, q, s) = α · q · R(y, q, s)` of a driver who ends at `y` (eq. (1)). -/
noncomputable def Ufun (y : E) (q s : ℝ) : ℝ := M.α * q * M.R y q s

/-- `U(y, p(y), s^𝒯(y))` for a price mapping `p` and a flow `𝒯`. -/
noncomputable def U (p : E → ℝ) (T : Measure (E × E)) (y : E) : ℝ :=
  M.Ufun y (p y) (M.sT T y)

/-- `Π(x, y, p(y), s^𝒯(y)) = U(y, p(y), s^𝒯(y)) - ‖y - x‖` (eq. (2)). -/
noncomputable def Pi (p : E → ℝ) (T : Measure (E × E)) (x y : E) : ℝ :=
  M.U p T y - ‖y - x‖

/-- `V_B(x | p, 𝒯) = ess sup_B Π(x, ·, p(·), s^𝒯(·))`, the essential supremum with respect to
the city measure restricted to `B` (eq. (3)). -/
noncomputable def VB (B : Set E) (p : E → ℝ) (T : Measure (E × E)) (x : E) : ℝ :=
  essSup (fun y => M.Pi p T x y) (M.Γ.restrict B)

/-- `V = V_C` (p. 13). -/
noncomputable def V (p : E → ℝ) (T : Measure (E × E)) (x : E) : ℝ := M.VB M.C p T x

/-- Supply equilibrium (Definition 1, p. 10). -/
def IsEquilibrium (p : E → ℝ) (T : Measure (E × E)) : Prop :=
  T {q | q ∈ M.C ×ˢ M.C ∧ M.Pi p T q.1 q.2 = M.V p T q.1} = M.Θ M.C

/-- Feasible solutions of (P2) (p. 13): a measurable price mapping with values in `[0, V̄]` on
`C` and an equilibrium flow in `𝓕(Θ)`. -/
def FeasibleP2 (p : E → ℝ) (T : Measure (E × E)) : Prop :=
  Measurable p ∧ (∀ y ∈ M.C, p y ∈ Set.Icc 0 M.Vbar) ∧ M.FeasFlow T ∧ M.IsEquilibrium p T

/-- The objective of (P2): `γ ∫_C V(x | p, 𝒯) s^𝒯(x) dΓ(x)`. -/
noncomputable def objP2 (p : E → ℝ) (T : Measure (E × E)) : ℝ :=
  M.γ * ∫ x, M.V p T x * M.sT T x ∂M.Γ

/-- Local monopoly revenue `R^loc_x(s) = max_{q ∈ [0, V̄]} q · min{s, λ(x) F̄_x(q)}` (eq. (4)). -/
noncomputable def Rloc (x : E) (s : ℝ) : ℝ :=
  sSup ((fun q => q * min s (M.lam x * M.Fbar x q)) '' Set.Icc 0 M.Vbar)

/-- The balance price `ρ^bal_x(s)`: the largest price in `[0, V̄]` with `s ≤ λ(x) F̄_x(ρ)`
(the solution of `s = λ(x) F̄_x(ρ)` in (5); equal to `V̄` at `s = 0`). -/
noncomputable def rhoBal (x : E) (s : ℝ) : ℝ :=
  sSup {ρ | ρ ∈ Set.Icc 0 M.Vbar ∧ s ≤ M.lam x * M.Fbar x ρ}

/-- The unconstrained revenue-maximizing price `ρ^u_x ∈ argmax_{ρ ∈ [0, V̄]} ρ F̄_x(ρ)` (eq. (5)). -/
noncomputable def rhoU (x : E) : ℝ :=
  sSup {ρ | ρ ∈ Set.Icc 0 M.Vbar ∧ ∀ q ∈ Set.Icc 0 M.Vbar, q * M.Fbar x q ≤ ρ * M.Fbar x ρ}

/-- The locally optimal price `ρ^loc_x(s) = max{ρ^bal_x(s), ρ^u_x}` (eq. (5)). -/
noncomputable def rhoLoc (x : E) (s : ℝ) : ℝ := max (M.rhoBal x s) (M.rhoU x)

/-- The supply congestion function `ψ_x` (p. 15). -/
noncomputable def psi (x : E) (s : ℝ) : ℝ :=
  if 0 < s then M.α * M.Rloc x s / s else M.α * M.Vbar

/-- The indifference region `IR(x | p, 𝒯)` (p. 16). -/
def IR (p : E → ℝ) (T : Measure (E × E)) (x : E) : Set E :=
  {y | y ∈ M.C ∧ M.V p T y - ‖y - x‖ = M.V p T x}

/-- The attraction region `A(z | p, 𝒯)` (Definition 2, p. 16). -/
def attr (p : E → ℝ) (T : Measure (E × E)) (z : E) : Set E :=
  {x | x ∈ M.C ∧ z ∈ M.IR p T x}

/-- `z` is a sink (Definition 2, p. 16). -/
def IsSink (p : E → ℝ) (T : Measure (E × E)) (z : E) : Prop :=
  (M.attr p T z).Nonempty ∧ ∀ z' ∈ M.C, z' ≠ z → z ∉ M.attr p T z'

/-- The endpoint `X_a(z | p, 𝒯)` of the attraction region of `z` along the ray of direction `a`
(p. B-1): the point `z + t* a`, `t*` the supremum of the `t ≥ 0` with `z + t a ∈ A(z | p, 𝒯)`. -/
noncomputable def Xend (p : E → ℝ) (T : Measure (E × E)) (z : E) (a : S1) : E :=
  z + sSup {t : ℝ | 0 ≤ t ∧ z + t • (a : E) ∈ M.attr p T z} • (a : E)

/-- `A_a(z | p, 𝒯)`: the restriction of `A(z | p, 𝒯)` to `z` and the ray of direction `a`
(p. B-1). -/
def attrRay (p : E → ℝ) (T : Measure (E × E)) (z : E) (a : S1) : Set E :=
  M.attr p T z ∩ ({z} ∪ (fun t : ℝ => z + t • (a : E)) '' Set.Ioi 0)

/-- The local feasible flows `𝓕_B(Θ̃)` (p. B-5). -/
def FeasFlowOn (B : Set E) (Θ' : Measure E) (T : Measure (E × E)) : Prop :=
  IsFiniteMeasure T ∧ T (B ×ˢ B)ᶜ = 0 ∧ T.map Prod.fst = Θ' ∧
    T.map Prod.snd ≪ M.Γ.restrict B

/-- Local equilibrium in `B` (Definition 3, p. B-5). -/
def IsLocalEquilibrium (B : Set E) (Θ' : Measure E) (p : E → ℝ) (T : Measure (E × E)) :
    Prop :=
  T {q | q ∈ B ×ˢ B ∧ M.Pi p T q.1 q.2 = M.VB B p T q.1} = Θ' B

end Market

end SurgeSpatial.Attraction



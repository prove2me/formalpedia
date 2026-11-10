-- Prove2me | Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring
-- name    : HiddenHardCoreColoring_Mixing_Coloring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:59:12.346737+00:00
-- url     : https://prove2.me/theorems/509f22eb-6e78-4236-979c-bee3e91eac5d
-- title:
--   Proper colorings, heat-bath and star operators, legal rectangles, mean and variance parts
-- statement:
--   This file fixes the coloring objects of §3.2 (p.7), §4.1 (p.9), §§5.3–5.4 (pp.13, 15) and §6.1 (pp.17–18). $G=(V,E)$ is a finite simple graph and $[q]$ the palette.
--
--   1. $\Omega$ is the set of proper colorings $\sigma:V\to[q]$ and $\mu$ the uniform law on $\Omega$; $\langle f,g\rangle_\mu=\sum_\sigma\mu(\sigma)f(\sigma)g(\sigma)$ and $\|f\|_\mu^2=\langle f,f\rangle_\mu$.
--   2. $A_v(\sigma)$ is the set of colors not used by a neighbor of $v$, $A_v^{-c}(\sigma)=A_v(\sigma)\setminus\{c\}$, $p_v(\sigma)=1/|A_v(\sigma)|$, and $\sigma^{v\leftarrow c}$ recolors $v$ with $c$.
--   3. **Heat-bath update** $P_v(\sigma,\sigma^{v\leftarrow c})=p_v(\sigma)$ for $c\in A_v(\sigma)$ (the old color included), $Q_v=\mathrm{Id}-P_v$, $L=\sum_vQ_v=n(\mathrm{Id}-P)$.
--   4. **Star operators** (9): for $c'\in A_v(\sigma)\setminus\{\sigma_v\}$, $P_{v,c}(\sigma,\sigma^{v\leftarrow c'})=p_v(\sigma)\,\mathbf 1\{c\in\{\sigma_v,c'\}\}$, the diagonal is the remaining probability, all other entries vanish; $Q_{v,c}=\mathrm{Id}-P_{v,c}$ and $L_c=\sum_vQ_{v,c}$.
--   5. $\omega_{uv}(\sigma)=\mu(\sigma)p_u(\sigma)p_v(\sigma)$; the legal-rectangle sum
--   $$X_{uv}(f)=\sum_{(\sigma,c_u,c_v)\in\mathcal R_{uv}}\omega_{uv}(\sigma)\big(f(\sigma)-f(\sigma^{u\leftarrow c_u})\big)\big(f(\sigma)-f(\sigma^{v\leftarrow c_v})\big),$$
--   with $\mathcal R_{uv}=\{(\sigma,c_u,c_v):c_u\in A_u^{-\sigma_u}(\sigma),\ c_v\in A_v^{-\sigma_v}(\sigma),\ c_u\ne c_v\}$; and $\Theta(f)=\sum_{u\ne v}\Theta_{uv}(f)$ over ordered pairs, where $\Theta_{uv}(f)$ is the $\omega_{uv}$-weighted sum over $c_u\in A_u(\sigma)$, $c_v\in A_v(\sigma)$ with $\sigma^{u\leftarrow c_u,v\leftarrow c_v}\in\Omega$ of $\big(f(\sigma)-f(\sigma^{u\leftarrow c_u})-f(\sigma^{v\leftarrow c_v})+f(\sigma^{u\leftarrow c_u,v\leftarrow c_v})\big)^2$.
--   6. $E_v^{-c}f(\sigma)$ is the average of $f(\sigma^{v\leftarrow c'})$ over $c'\in A_v^{-c}(\sigma)$, $\mathrm{Var}_v^{-c}f=E_v^{-c}(f^2)-(E_v^{-c}f)^2$,
--   $$M_{v,c}(f)=\mathbb E_\mu\big[\mathbf 1\{\sigma_v=c\}(1-p_v)(f-E_v^{-c}f)^2\big],\qquad V_{v,c}(f)=\mathbb E_\mu\big[\mathbf 1\{\sigma_v=c\}(1-p_v)\mathrm{Var}_v^{-c}f\big],$$
--   $M_c=\sum_vM_{v,c}$, $V_c=\sum_vV_{v,c}$, and the polarizations $M_c(f,g)=\tfrac14(M_c(f+g)-M_c(f-g))$, $V_c(f,g)$ likewise.
--
--   The star operators split each recoloring at $v$ according to its old and new color; $M_c$ and $V_c$ separate the two kinds of variation of $f$ at a vertex where $c$ is available.
--
--   **Formalization Note** $\Omega$ is the subtype of proper colorings (`MarkovMixing.IsProperColoring`), the same state space as the published `MarkovMixing.coloringGlauber`. Values of $f$ at recolorings are read through an extension by $0$ off $\Omega$, which every summation range avoids.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; §3.2, p.7; §4.1, eq. (9)–(10), p.9; §5.3, p.13 (ω_uv, R_uv, X_uv); §5.4, p.15 (Θ_uv, Θ); §6.1, pp.17–18 (E_v^{-c}, Var_v^{-c}, M_{v,c}, V_{v,c}, M_c, V_c, polarizations)

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Chain
import Definitions.Def_mm_transport

namespace HiddenHardCoreColoring.Mixing

open Finset

noncomputable section

/-!
# Proper colorings, heat-bath updates, star operators, and the forms of §§4–6

Xiongxin Yang, *Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via
Hidden Hard-Core Models*, STOC 2027 submission #964 (October 2026): §3.2 (p.7), §4.1 (p.9),
§5.3 (p.13), §5.4 (p.15), §6.1 (pp.17–18).

`G` is a finite simple graph on the vertex type `V` and `q` the number of colors, `[q] = Fin q`.
The state space `Ω` is the subtype `Col G q` of proper colorings; `L²(µ)` is the space of all real
functions `Col G q → ℝ` with the uniform weights `µ = colMu G q`. Every operator is a matrix on
`Ω`, acting by `M *ᵥ f`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ)

/-- `Ω`: the proper colorings `σ : V → [q]` (`σ u ≠ σ v` on every edge), §3.2, p.7. -/
abbrev Col : Type _ := {σ : V → Fin q // MarkovMixing.IsProperColoring G σ}

/-- `µ`: the uniform distribution on `Ω` (§3.2, p.7). -/
def colMu : Col G q → ℝ := MarkovMixing.uniformDist (Col G q)

/-- `⟨f, g⟩_µ = ∑_σ µ(σ) f(σ) g(σ)` (§3.1, p.6). -/
def ip (f g : Col G q → ℝ) : ℝ := MarkovMixing.innerPi (colMu G q) f g

/-- `‖f‖²_µ = ⟨f, f⟩_µ`. -/
def sqNorm (f : Col G q → ℝ) : ℝ := ip G q f f

variable {q}

/-- `A_v(σ)`: the colors not used by any neighbor of `v` in `σ` (§3.2, p.7). -/
def avail (σ : V → Fin q) (v : V) : Finset (Fin q) :=
  univ.filter fun c => ∀ u, G.Adj v u → σ u ≠ c

/-- `A_v^{-c}(σ) := A_v(σ) ∖ {c}` (§3.2, p.7). -/
def availMinus (σ : V → Fin q) (v : V) (c : Fin q) : Finset (Fin q) :=
  (avail G σ v).erase c

/-- `p_v(σ) := 1/|A_v(σ)|` (§3.2, p.7). -/
def pv (σ : V → Fin q) (v : V) : ℝ := 1 / ((avail G σ v).card : ℝ)

/-- The value of `f : Ω → ℝ` at an assignment `x : V → [q]`, which is `f(x)` when `x` is a proper
coloring. Every use below evaluates it at a recoloring `σ^{v←c}` (or `σ^{u←c_u, v←c_v}`) that the
summation range guarantees to be proper; the value `0` off `Ω` is never reached there. -/
def fext (f : Col G q → ℝ) (x : V → Fin q) : ℝ :=
  if h : MarkovMixing.IsProperColoring G x then f ⟨x, h⟩ else 0

variable (q)

/-- **The heat-bath update at `v`** (§3.2, p.7): from `σ`, recolor `v` with a uniform color of
`A_v(σ)`; `P_v(σ, σ^{v←c}) = p_v(σ)` for every `c ∈ A_v(σ)` (the old color included, which gives the
diagonal entry). A proper coloring `τ` agreeing with `σ` off `v` is exactly `σ^{v←c}` with
`c ∈ A_v(σ)`, so `(P_v f)(σ) = p_v(σ) ∑_{c∈A_v(σ)} f(σ^{v←c})`. -/
def Pv (v : V) : Matrix (Col G q) (Col G q) ℝ :=
  fun σ τ => if ∀ w, w ≠ v → τ.1 w = σ.1 w then pv G σ.1 v else 0

/-- `Q_v := Id − P_v` (§3.2, p.7). -/
def Qv (v : V) : Matrix (Col G q) (Col G q) ℝ := 1 - Pv G q v

/-- `L := ∑_v Q_v = n(Id − P)` (§3.2, p.7). -/
def Lap : Matrix (Col G q) (Col G q) ℝ := ∑ v, Qv G q v

/-- Off-diagonal entries of the star update `P_{v,c}` (eq. (9), p.9): for `τ = σ^{v←c'} ≠ σ`,
`P_{v,c}(σ, τ) = p_v(σ) 1{c ∈ {σ_v, c'}}`; all other off-diagonal entries vanish. -/
def starOff (v : V) (c : Fin q) (σ τ : Col G q) : ℝ :=
  if τ ≠ σ ∧ (∀ w, w ≠ v → τ.1 w = σ.1 w) ∧ (σ.1 v = c ∨ τ.1 v = c) then pv G σ.1 v else 0

/-- **The star update `P_{v,c}`** (§4.1, eq. (9), p.9): keep only the moves of `P_v` whose old or new
color is `c`, each with probability `p_v(σ)`; the diagonal entry `P_{v,c}(σ, σ)` is the remaining
probability. -/
def Pvc (v : V) (c : Fin q) : Matrix (Col G q) (Col G q) ℝ :=
  fun σ τ => if τ = σ then 1 - ∑ τ' ∈ univ.erase σ, starOff G q v c σ τ' else starOff G q v c σ τ

/-- The star operator `Q_{v,c} := Id − P_{v,c}` (§4.1, p.9). -/
def Qvc (v : V) (c : Fin q) : Matrix (Col G q) (Col G q) ℝ := 1 - Pvc G q v c

/-- The single-color operator `L_c := ∑_v Q_{v,c}` (§4.1, p.9). -/
def Lc (c : Fin q) : Matrix (Col G q) (Col G q) ℝ := ∑ v, Qvc G q v c

/-- `ω_{uv}(σ) := µ(σ) p_u(σ) p_v(σ)` (§5.3, p.13). -/
def omega (u v : V) (σ : Col G q) : ℝ := colMu G q σ * pv G σ.1 u * pv G σ.1 v

/-- **The legal-rectangle sum** (§5.3, p.13)
`X_{uv}(f) := ∑_{(σ,c_u,c_v)∈ℛ_{uv}} ω_{uv}(σ)(f(σ) − f(σ^{u←c_u}))(f(σ) − f(σ^{v←c_v}))`, where
`ℛ_{uv} = {(σ, c_u, c_v) : σ ∈ Ω, c_u ∈ A_u^{-σ_u}(σ), c_v ∈ A_v^{-σ_v}(σ), c_u ≠ c_v}`. -/
def Xuv (u v : V) (f : Col G q → ℝ) : ℝ :=
  ∑ σ : Col G q, ∑ cu ∈ availMinus G σ.1 u (σ.1 u), ∑ cv ∈ availMinus G σ.1 v (σ.1 v),
    if cu ≠ cv then
      omega G q u v σ * (f σ - fext G f (Function.update σ.1 u cu)) *
        (f σ - fext G f (Function.update σ.1 v cv))
    else 0

/-- `Θ_{uv}(f)` (§5.4, p.15): the `ω_{uv}`-weighted sum, over `c_u ∈ A_u(σ)`, `c_v ∈ A_v(σ)` with
`σ^{u←c_u, v←c_v} ∈ Ω`, of the squared mixed second difference
`(f(σ) − f(σ^{u←c_u}) − f(σ^{v←c_v}) + f(σ^{u←c_u, v←c_v}))²`. -/
def ThetaUV (u v : V) (f : Col G q → ℝ) : ℝ :=
  ∑ σ : Col G q, ∑ cu ∈ avail G σ.1 u, ∑ cv ∈ avail G σ.1 v,
    if MarkovMixing.IsProperColoring G (Function.update (Function.update σ.1 u cu) v cv) then
      omega G q u v σ *
        (f σ - fext G f (Function.update σ.1 u cu) - fext G f (Function.update σ.1 v cv) +
          fext G f (Function.update (Function.update σ.1 u cu) v cv)) ^ 2
    else 0

/-- `Θ(f) := ∑_{u≠v} Θ_{uv}(f)` over **ordered** pairs of distinct vertices (§5.4, p.15). -/
def Theta (f : Col G q → ℝ) : ℝ := ∑ u, ∑ v ∈ univ.erase u, ThetaUV G q u v f

/-- `E_v^{-c} f(σ) := |A_v^{-c}(σ)|⁻¹ ∑_{c'∈A_v^{-c}(σ)} f(σ^{v←c'})` (§6.1, p.17). -/
def Eminus (v : V) (c : Fin q) (f : Col G q → ℝ) (σ : Col G q) : ℝ :=
  (1 / ((availMinus G σ.1 v c).card : ℝ)) *
    ∑ c' ∈ availMinus G σ.1 v c, fext G f (Function.update σ.1 v c')

/-- `Var_v^{-c} f := E_v^{-c}(f²) − (E_v^{-c} f)²` (§6.1, p.17). -/
def VarMinus (v : V) (c : Fin q) (f : Col G q → ℝ) (σ : Col G q) : ℝ :=
  Eminus G q v c (fun τ => f τ ^ 2) σ - (Eminus G q v c f σ) ^ 2

/-- The mean part at `v`, `M_{v,c}(f) := E_{σ∼µ}[1{σ_v = c}(1 − p_v)(f − E_v^{-c} f)²]`
(§6.1, p.17). -/
def Mvc (v : V) (c : Fin q) (f : Col G q → ℝ) : ℝ :=
  ∑ σ : Col G q, colMu G q σ *
    (if σ.1 v = c then (1 - pv G σ.1 v) * (f σ - Eminus G q v c f σ) ^ 2 else 0)

/-- The variance part at `v`, `V_{v,c}(f) := E_{σ∼µ}[1{σ_v = c}(1 − p_v) Var_v^{-c} f]`
(§6.1, p.17). -/
def Vvc (v : V) (c : Fin q) (f : Col G q → ℝ) : ℝ :=
  ∑ σ : Col G q, colMu G q σ *
    (if σ.1 v = c then (1 - pv G σ.1 v) * VarMinus G q v c f σ else 0)

/-- The mean part `M_c := ∑_v M_{v,c}` (§6.1, p.17). -/
def Mc (c : Fin q) (f : Col G q → ℝ) : ℝ := ∑ v, Mvc G q v c f

/-- The variance part `V_c := ∑_v V_{v,c}` (§6.1, p.17). -/
def Vc (c : Fin q) (f : Col G q → ℝ) : ℝ := ∑ v, Vvc G q v c f

/-- The polarization `M_c(f, g) := (M_c(f + g) − M_c(f − g))/4` (§6.1, p.18). -/
def McBil (c : Fin q) (f g : Col G q → ℝ) : ℝ := (Mc G q c (f + g) - Mc G q c (f - g)) / 4

/-- The polarization `V_c(f, g) := (V_c(f + g) − V_c(f − g))/4` (§6.1, p.18). -/
def VcBil (c : Fin q) (f g : Col G q → ℝ) : ℝ := (Vc G q c (f + g) - Vc G q c (f - g)) / 4

end

end HiddenHardCoreColoring.Mixing



-- Prove2me | Definitions.Def_PowerOfDUniversality_Diffusion_PathSpace
-- name    : PowerOfDUniversality_Diffusion_PathSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:13.492863+00:00
-- url     : https://prove2.me/theorems/f2c70c06-2311-4fe0-b47b-55a95f49951d
-- title:
--   §2.1–2.3, pp. 5, 7 — ℓ¹-valued càdlàg paths $D_{\mathbb S}[0,\infty)$ and weak convergence to a continuous limit in coupling form
-- statement:
--   This file fixes the path space in which the diffusion-scaled occupancy processes of the JSQ(d(N)) scheme converge, and the meaning of weak convergence in it.
--
--   **States and distances.** A state is a real sequence $x=(x_i)_{i\ge 0}$; it belongs to $\ell_1$ when $\sum_i |x_i|<\infty$. For two sequences the $\ell_1$ distance is
--   $$\|x-y\|_1=\sum_{i\ge 0}|x_i-y_i|\in[0,\infty],$$
--   and for two paths $f,g:[0,\infty)\to\mathbb R^{\mathbb N}$ and a horizon $t\ge 0$,
--   $$\|f-g\|_t=\sup_{s\in[0,t]}\|f(s)-g(s)\|_1 .$$
--
--   **Càdlàg paths.** A path $x$ is an $\ell_1$-valued càdlàg path if $x(t)\in\ell_1$ for every $t\ge0$, $\|x(s)-x(t)\|_1\to0$ as $s\downarrow t$ for every $t\ge 0$, and for every $t>0$ there is $\ell\in\ell_1$ with $\|x(s)-\ell\|_1\to 0$ as $s\uparrow t$. This is the space $D_{\ell_1}[0,\infty)$; the paper writes $D_{\mathbb S}[0,\infty)$ and equips its state space "with $\ell_1$ topology" (p. 5).
--
--   **Weak convergence.** Let $Z_n$ be processes on probability spaces $(\Omega_n,P_n)$ and $Z$ a process on $(\Omega',P')$, all with $\ell_1$-valued paths. We say $Z_n\Rightarrow Z$ in coupling form if there are a probability space $(\Omega'',P'')$ and processes $Y_n,Y$ on it such that:
--   1. $Y_n$ has the law of $Z_n$ for all large $n$ and $Y$ has the law of $Z$ (laws of the paths on $[0,\infty)$, on the product σ-algebra of the coordinates);
--   2. every path of every $Y_n$ is an $\ell_1$-valued càdlàg path;
--   3. almost surely, $\|Y_n-Y\|_t\to0$ for every $t\ge0$.
--
--   When the limit has continuous paths, as every limit in the paper does, this is equivalent to weak convergence in $D_{\ell_1}[0,\infty)$ with the Skorokhod $J_1$ topology: one direction is the Skorokhod representation theorem, the other holds because almost sure uniform convergence on compacts implies almost sure $J_1$ convergence.
--
--   **Formalization Note** Sequences are `ℕ → ℝ` and paths are `ℝ → ℕ → ℝ`, evaluated only at times `t ≥ 0`. All distances live in `[0, ∞]`, so no junk value arises. The laws are compared with `IdentDistrib` of the restrictions to `ℝ≥0`; for càdlàg paths in the separable space $\ell_1$ the product σ-algebra is the Borel σ-algebra of $D_{\ell_1}[0,\infty)$. This extends `BellWilliams2001.ThresholdPolicy.CouplingConverges` from $\mathbb R^m$-valued paths on one probability space to $\ell_1$-valued paths on varying spaces.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 5, §2.1 (D_E[0,∞), −→^L) and §2.2 (𝕊 with ℓ₁ topology); p. 7, Theorem 2.4 (D_𝕊[0,∞))

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-!
Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, §2.1 (p. 5) and §2.3 (p. 7):
the path space `D_S[0, ∞)` of the diffusion-scaled occupancy processes, read as the space of
càdlàg paths with values in `ℓ¹` ("equipped with ℓ₁ topology", p. 5), and weak convergence in it
to a limit with continuous paths, rendered in coupling form.

A point of `ℓ¹` is represented as a sequence `x : ℕ → ℝ` that is summable; a path is a map
`ℝ → ℕ → ℝ` evaluated only at times `t ≥ 0`. Distances are computed in `[0, ∞]`, so they are never a
junk value.
-/

/-- The `ℓ¹` distance `‖x − y‖₁ = ∑ᵢ |xᵢ − yᵢ|` of two real sequences, computed in `[0, ∞]`. It is
finite when both sequences are summable. -/
noncomputable def l1Dist (x y : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal |x i - y i|

/-- An `ℓ¹`-valued **càdlàg path** on `[0, ∞)` (a member of `D_{ℓ¹}[0, ∞)`, p. 5): at every time
`t ≥ 0` the state `x t` is a summable sequence, the path is right continuous in the `ℓ¹` norm at
every `t ≥ 0`, and it has a left limit in `ℓ¹` at every `t > 0`. Values at negative times are
ignored. -/
def IsCadlagL1 (x : ℝ → ℕ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Summable (x t)) ∧
  (∀ t : ℝ, 0 ≤ t → Tendsto (fun s => l1Dist (x s) (x t)) (𝓝[≥] t) (𝓝 0)) ∧
  (∀ t : ℝ, 0 < t → ∃ l : ℕ → ℝ, Summable l ∧
    Tendsto (fun s => l1Dist (x s) l) (𝓝[<] t) (𝓝 0))

/-- **Weak convergence in `D_{ℓ¹}[0, ∞)` to a process with continuous paths, in coupling form.**
For each `n` the process `Z n` lives on its own probability space `(Ω n, P n)`, and `Zlim` lives on
`(Ω', P')`; all are `ℓ¹`-valued paths indexed by time `t ≥ 0`. The relation holds when there are a
probability space `(Ω'', P'')` and processes `Y n`, `Ylim` on it such that
1. `Y n` has the law of `Z n` for all large `n`, and `Ylim` has the law of `Zlim` (laws of the paths
   restricted to `[0, ∞)`, on the product σ-algebra of the coordinates `(t, i)`; for càdlàg paths
   in the separable space `ℓ¹` this is the Borel σ-algebra of `D_{ℓ¹}[0, ∞)`);
2. every path of every `Y n` is an `ℓ¹`-valued càdlàg path;
3. almost surely, `sup_{s ∈ [0, t]} ‖Y n (s) − Ylim (s)‖₁ → 0` for every `t ≥ 0` (uniform convergence
   in `ℓ¹` on compact time intervals).

When `Zlim` has continuous `ℓ¹`-valued paths and the `Z n` have càdlàg paths, this is equivalent to
`Z n ⟹ Zlim` in `D_{ℓ¹}[0, ∞)` with the Skorokhod `J₁` topology: one direction is the Skorokhod
representation theorem (`D_{ℓ¹}[0, ∞)` is Polish), the other holds because a.s. u.o.c. convergence
implies a.s. `J₁` convergence, hence weak convergence. Only the laws of the `Z n` for large `n`
matter, as for weak convergence. This extends `BellWilliams2001.ThresholdPolicy.CouplingConverges`
from `ℝ^m`-valued paths on one probability space to `ℓ¹`-valued paths on varying spaces. -/
def CouplingConvergesL1 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*}
    [MeasurableSpace Ω'] (P : ∀ n, Measure (Ω n)) (P' : Measure Ω')
    (Z : ∀ n, Ω n → ℝ → ℕ → ℝ) (Zlim : Ω' → ℝ → ℕ → ℝ) : Prop :=
  ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
    (Y : ℕ → Ω'' → ℝ → ℕ → ℝ) (Ylim : Ω'' → ℝ → ℕ → ℝ),
    IsProbabilityMeasure P'' ∧
    (∀ᶠ n in atTop, ProbabilityTheory.IdentDistrib (fun ω (t : ℝ≥0) => Y n ω t)
      (fun ω (t : ℝ≥0) => Z n ω t) P'' (P n)) ∧
    ProbabilityTheory.IdentDistrib (fun ω (t : ℝ≥0) => Ylim ω t)
      (fun ω (t : ℝ≥0) => Zlim ω t) P'' P' ∧
    (∀ n ω, IsCadlagL1 (Y n ω)) ∧
    ∀ᵐ ω ∂P'', ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => PowerOfDUniversality.Fluid.supDistL1 (Y n ω) (Ylim ω) t) atTop (𝓝 0)

end PowerOfDUniversality.Diffusion



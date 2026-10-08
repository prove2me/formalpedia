-- Prove2me | Definitions.Def_PolymerEndpoint_GeoLoc_Functionals
-- name    : PolymerEndpoint_GeoLoc_Functionals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:32:39.555349+00:00
-- url     : https://prove2.me/theorems/c23accfc-70c5-4360-a5c7-5f3b89b7b0b9
-- title:
--   (7.1), §7.1, §5.2, §7.3 — 𝒢_{δ,K}, N(f), W_δ(f), q_n, m(f), Q(f), max(f) and the favourite-region mass ρ_i(ω_i ∈ 𝒞_i^K)
-- statement:
--   The functionals used to describe geometric localization.
--
--   1. **(7.1)** For $\delta,K\in\mathbb R$, $\mathcal G_{\delta,K}$ is the set of $f:\mathbb Z^d\to[0,1]$ with $\|f\|=1$ for which some $D\subset\mathbb Z^d$ of diameter $\operatorname{diam}(D)=\sup\{\|x-y\|_1:x,y\in D\}\le K$ satisfies $\sum_{x\in D}f(x)>1-\delta$.
--   2. **Support number.** $N(f)=|H_f|\in\mathbb N\cup\{0,\infty\}$, where $H_f=\{n\in\mathbb N: f(n,x)>0\text{ for some }x\}$.
--   3. For $\delta\in(0,1)$,
--   $$W_\delta(f)=\inf\Big\{\operatorname{diam}(D):D\subset\mathbb Z^d,\ \sum_{x\in D}f(n,x)>1-\delta\text{ for some }n\in\mathbb N\Big\},$$
--   with $\inf\emptyset=\infty$.
--   4. $q_n(f)=\sum_{x}f(n,x)$, $m(f)=\max_n q_n(f)$, and $Q(f)=\sum_n\frac{q_n(f)}{1-q_n(f)}\in[0,\infty]$ with $1/0=\infty$.
--   5. **(§5.2)** $\max(f)=\max_{u\in\mathbb N\times\mathbb Z^d}f(u)$.
--   6. **(§7.3)** For $K\ge0$, $\mathcal C_i^K$ is the set of $x\in\mathbb Z^d$ within $\ell^1$ distance $K$ of every mode of $f_i$, and $\rho_i(\omega_i\in\mathcal C_i^K)$ is its polymer probability.
--
--   **Formalization Note.** In $\mathcal G_{\delta,K}$ the set $D$ ranges over finite sets: a subset of $\mathbb Z^d$ of finite diameter is finite. The same holds in $W_\delta$ (a summable mass exceeding $1-\delta$ on an infinite set already exceeds it on a finite subset). $N$ and $W_\delta$ take values in $\mathbb N\cup\{\infty\}$, so the empty infimum is $\infty$. $Q$ is computed in $[0,\infty]$, where $x/0=\infty$ for $x>0$ and $0/0=0$. $\max$ and $m$ are real suprema of families bounded by $1$; they are attained.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 46, (7.1); pp. 46–47, §7.1, (7.2); p. 39, §5.2; p. 50, §7.3

import Mathlib
import Definitions.Def_PolymerEndpoint_GeoLoc_Partitioned

namespace PolymerEndpoint.GeoLoc

open MeasureTheory

/-- `f ∈ 𝒢_{δ,K}` (7.1): `f : ℤ^d → [0, 1]`, `‖f‖ = 1`, and some `D ⊂ ℤ^d` of `ℓ¹`-diameter
`≤ K` carries PolymerEndpoint.Atomic.mass `> 1 − δ`. (A set of finite diameter in `ℤ^d` is finite.) -/
def InG {d : ℕ} (δ K : ℝ) (p : (Fin d → ℤ) → ℝ) : Prop :=
  (∀ x, 0 ≤ p x ∧ p x ≤ 1) ∧ ∑' x, p x = 1 ∧
    ∃ D : Finset (Fin d → ℤ), (∀ x ∈ D, ∀ y ∈ D, (PolymerEndpoint.Atomic.l1 (x - y) : ℝ) ≤ K) ∧ 1 - δ < ∑ x ∈ D, p x

/-- The support number `N(f) = |H_f|`, `H_f = {n : f(n, x) > 0 for some x}` (§7.1, p. 46). -/
noncomputable def suppNum {d : ℕ} (f : PolymerEndpoint.Atomic.PSM d) : ℕ∞ :=
  Set.encard {n : ℕ | ∃ x, 0 < f.toFun (n, x)}

/-- `diam(D) = max_{x, y ∈ D} ‖x − y‖₁` of a finite set (`0` for `D = ∅`). -/
def diamFin {d : ℕ} (D : Finset (Fin d → ℤ)) : ℕ :=
  D.sup (fun x => D.sup (fun y => PolymerEndpoint.Atomic.l1 (x - y)))

/-- `W_δ(f) = inf {diam(D) : D ⊂ ℤ^d, ∑_{x ∈ D} f(n, x) > 1 − δ for some n}` (§7.1, p. 46),
with `inf ∅ = ∞`. -/
noncomputable def Wdelta {d : ℕ} (δ : ℝ) (f : PolymerEndpoint.Atomic.PSM d) : ℕ∞ :=
  ⨅ (n : ℕ) (D : Finset (Fin d → ℤ)) (_ : 1 - δ < ∑ x ∈ D, f.toFun (n, x)),
    ((diamFin D : ℕ) : ℕ∞)

/-- `q_n(f) = ∑_x f(n, x)`, the PolymerEndpoint.Atomic.mass of copy `n` (p. 47). -/
noncomputable def qn {d : ℕ} (n : ℕ) (f : PolymerEndpoint.Atomic.PSM d) : ℝ := ∑' x, f.toFun (n, x)

/-- `m(f) = max_n q_n(f)` (p. 47). -/
noncomputable def mfun {d : ℕ} (f : PolymerEndpoint.Atomic.PSM d) : ℝ := ⨆ n, qn n f

/-- `Q(f) = ∑_n q_n(f) / (1 − q_n(f))` in `[0, ∞]`, with `1/0 = ∞` (p. 47). -/
noncomputable def Qfun {d : ℕ} (f : PolymerEndpoint.Atomic.PSM d) : ENNReal :=
  ∑' n, ENNReal.ofReal (qn n f) / ENNReal.ofReal (1 - qn n f)

/-- `max(f) = max_{u ∈ ℕ × ℤ^d} f(u)` (§5.2, p. 39). -/
noncomputable def maxS {d : ℕ} (f : PolymerEndpoint.Atomic.PSM d) : ℝ := ⨆ u, f.toFun u

/-- `ρ_i(ω_i ∈ 𝒞_i^K)`: the polymer PolymerEndpoint.Atomic.mass of endpoints within `ℓ¹` distance `K` of **every** mode
of the endpoint pmf `f_i` (§7.3, p. 50). -/
noncomputable def centerMass {d : ℕ} {Ω : Type*} (X : PolymerEndpoint.Atomic.Cell d → Ω → ℝ) (β : ℝ) (i : ℕ) (K : ℝ)
    (a : Ω) : ℝ := by
  classical
  exact (∑ s : Fin i → PolymerEndpoint.Atomic.Step d, weight X β s a *
      if (∀ y, (∀ z, PolymerEndpoint.Atomic.endpt X β i a z ≤ PolymerEndpoint.Atomic.endpt X β i a y) → (PolymerEndpoint.Atomic.l1 (PolymerEndpoint.Atomic.pos s i - y) : ℝ) ≤ K)
      then 1 else 0) / ∑ s : Fin i → PolymerEndpoint.Atomic.Step d, weight X β s a

end PolymerEndpoint.GeoLoc



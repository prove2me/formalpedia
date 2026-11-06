-- Prove2me | Definitions.Def_SKWeakPoincare_PathSpace
-- name    : SKWeakPoincare_PathSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:06.351786+00:00
-- url     : https://prove2.me/theorems/35c2d073-d80e-4cca-91d7-e07e42c7aa49
-- title:
--   Path space $C([0,T];\mathbb R^n)$, Cameron–Martin shifts, localization paths, path and terminal costs
-- statement:
--   Fix $T>0$. The **path space** $C([0,T];\mathbb R^n)$ consists of continuous paths $\omega:[0,T]\to\mathbb R^n$, with the uniform norm $\|\omega\|_\infty=\sup_{0\le t\le T}\|\omega_t\|_2$ and the Borel $\sigma$-algebra. Its closed subset $C_0([0,T];\mathbb R^n)$ consists of the paths with $\omega_0=0$.
--
--   1. The **Cameron–Martin space** $H_T$ consists of the paths $h_s=\int_0^sg(u)\,du$ with $g\in L^2([0,T];\mathbb R^n)$, and $\|h\|_{H_T}=\big(\int_0^T\|g(u)\|_2^2\,du\big)^{1/2}$.
--   2. For a drift $b:\mathbb R^n\to\mathbb R^n$, a path $Y$ **solves the localization equation** driven by $\omega$ if
--   $$
--   Y_t=\omega_t+\int_0^tb(Y_s)\,ds,\qquad0\le t\le T.
--   $$
--   With $b=m$ this is eq. (8).
--   3. For a cost function $\mathfrak e(t;y)$, the **path cost** is $U=\int_0^T\mathfrak e(t;Y_t)\,dt$ and the **terminal cost** is $E=\mathfrak e(T;Y_T)$.
--
--   **Formalization Note** The path space is `C(Set.Icc 0 T, EuclideanSpace ℝ (Fin n))`, whose norm is exactly $\sup_t\|\omega_t\|_2$. `pathExt ω t` evaluates a path at a real time and returns $0$ outside $[0,T]$, which is never used. $h\in H_T$ is the predicate `IsCMShift g h`, and $\|h\|_{H_T}$ is `cmNorm T g`, with $g=dh/dt$ almost everywhere.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Section 3.2, p.15 (C₀([0,T];ℝⁿ), uniform norm, H_T); eq. (8), p.16; Lemma 3.4, p.16; Lemma 6.1, p.37 (U, E)

import Mathlib

open MeasureTheory

namespace SKWeakPoincare

/-- The path space `C([0, T]; ℝ^n)` of continuous paths `ω : [0, T] → ℝ^n`, with the uniform norm
`‖ω‖_∞ = sup_{0 ≤ t ≤ T} ‖ω_t‖₂` and the Borel σ-algebra.
Hou–Liu–Yu, arXiv:2610.09882, Section 3.2, p. 15.

**Formalization Note.** The target is `EuclideanSpace ℝ (Fin n)`, so the norm of a continuous map on
the compact interval is exactly `sup_t ‖ω_t‖₂`. The paper's `C₀([0, T]; ℝ^n)` is the closed subset
`{ω | pathExt ω 0 = 0}`; statements about `C₀` say `pathExt ω 0 = 0` explicitly. -/
abbrev PathSpace (T : ℝ) (n : ℕ) : Type :=
  C(Set.Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n))

noncomputable instance (T : ℝ) (n : ℕ) : MeasurableSpace (PathSpace T n) := borel _

instance (T : ℝ) (n : ℕ) : BorelSpace (PathSpace T n) := ⟨rfl⟩

/-- A path evaluated at a real time `t`: `ω_t` for `t ∈ [0, T]`, and `0` outside `[0, T]`
(the value outside is never used: every use is at `t ∈ [0, T]`). -/
noncomputable def pathExt {T : ℝ} {n : ℕ} (ω : PathSpace T n) (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  if ht : t ∈ Set.Icc (0 : ℝ) T then ω ⟨t, ht⟩ else 0

/-- `h` is the **Cameron–Martin path** `h_s = ∫₀ˢ g(u) du` of a square-integrable derivative `g`.
Hou–Liu–Yu, arXiv:2610.09882, Section 3.2, p. 15: `H_T` consists of absolutely continuous paths `h`
with `h_0 = 0` and square-integrable derivative.

**Formalization Note.** `h ∈ H_T` iff `IsCMShift T g h` for some `g`, and then `‖h‖_{H_T} = cmNorm T g`
(`g = dh/dt` almost everywhere). -/
def IsCMShift {T : ℝ} {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) (h : PathSpace T n) : Prop :=
  MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
    ∀ s : Set.Icc (0 : ℝ) T, h s = ∫ u in (0 : ℝ)..(s : ℝ), g u

/-- The **Cameron–Martin norm** `‖h‖_{H_T} = (∫₀ᵀ ‖dh_t/dt‖₂² dt)^{1/2}`, written in terms of the
derivative `g` of `h` (p. 15). -/
noncomputable def cmNorm {n : ℕ} (T : ℝ) (g : ℝ → EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∫ u in (0 : ℝ)..T, ‖g u‖ ^ 2)

/-- `Y` solves the **localization integral equation** driven by `ω` with drift `b`:
`Y_t = ω_t + ∫₀ᵗ b(Y_s) ds` for `0 ≤ t ≤ T`.
Hou–Liu–Yu, arXiv:2610.09882, eq. (8), p. 16 (with `b = m(A, ·)`), Lemma 3.4, p. 16 (general `b`),
Section 6, p. 37 (with `b = m`). -/
def IsLocPath {T : ℝ} {n : ℕ} (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ω Y : PathSpace T n) : Prop :=
  ∀ t : Set.Icc (0 : ℝ) T, Y t = ω t + ∫ s in (0 : ℝ)..(t : ℝ), b (pathExt Y s)

/-- The **path cost** `U = ∫₀ᵀ 𝔢(t; Y_t) dt` of a path `Y` for a cost function `𝔢(t; y)`
(Lemma 6.1, p. 37). -/
noncomputable def pathCost {n : ℕ} (T : ℝ) (e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (Y : PathSpace T n) : ℝ :=
  ∫ t in (0 : ℝ)..T, e t (pathExt Y t)

/-- The **terminal cost** `E = 𝔢(T; Y_T)` of a path `Y` (Lemma 6.1, p. 37). -/
noncomputable def termCost {n : ℕ} (T : ℝ) (e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (Y : PathSpace T n) : ℝ :=
  e T (pathExt Y T)

end SKWeakPoincare



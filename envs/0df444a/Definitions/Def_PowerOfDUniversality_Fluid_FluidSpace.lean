-- Prove2me | Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace
-- name    : PowerOfDUniversality_Fluid_FluidSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:31.398474+00:00
-- url     : https://prove2.me/theorems/93bb7dea-0b69-4ae9-a1ce-26c0f1f9eeec
-- title:
--   The fluid space 𝕊 with the ℓ¹ topology, m(q), the coefficients p_i(q) of (4.4), solutions of (2.1), and weak J₁ convergence in coupling form
-- statement:
--   This file sets up the fluid-scale objects of §2.2 and §4.1.
--
--   **The fluid space.** For a buffer $b\in\{1,2,\dots\}\cup\{\infty\}$,
--   $$\mathcal S=\Big\{\mathbf q\in[0,1]^b:\ q_i\le q_{i-1}\text{ for } i=2,\dots,b,\ \ \sum_{i=1}^{b}q_i<\infty\Big\},$$
--   equipped with the $\ell_1$ distance $\|\mathbf x-\mathbf y\|_1=\sum_i|x_i-y_i|$. It is the set of possible fluid-scaled occupancy states $\mathbf q=\mathbf Q/N$.
--
--   **The coefficients.** For $\mathbf q\in\mathcal S$ let $m(\mathbf q)=\min\{i: q_{i+1}<1\}$, with $q_{b+1}=0$ if $b<\infty$; it is finite because $\mathbf q\in\ell_1$. Following (4.4), if $m(\mathbf q)=0$ then $p_0(\mathbf q)=1$ and $p_i(\mathbf q)=0$ for $i\ge 1$; if $m(\mathbf q)>0$ then
--   $$p_{m(\mathbf q)-1}(\mathbf q)=\min\Big\{\frac{1-q_{m(\mathbf q)+1}}{\lambda},1\Big\},\qquad p_{m(\mathbf q)}(\mathbf q)=1-p_{m(\mathbf q)-1}(\mathbf q),$$
--   and $p_i(\mathbf q)=0$ otherwise. The number $p_i(\mathbf q)$ is the fraction of incoming tasks that join servers with exactly $i$ tasks.
--
--   **The integral equations.** A path $\mathbf q:[0,\infty)\to\mathcal S$ solves (2.1) with initial value $\mathbf q^\infty$ if, for every $t\ge 0$ and every $i=1,\dots,b$,
--   $$q_i(t)=q^\infty_i+\lambda\int_0^t p_{i-1}(\mathbf q(s))\,ds-\int_0^t\big(q_i(s)-q_{i+1}(s)\big)\,ds ,$$
--   with $q_{b+1}\equiv 0$ if $b<\infty$ and both integrands integrable on $[0,t]$.
--
--   **Weak convergence.** A sequence of $\mathcal S$-valued càdlàg processes converges weakly with respect to the Skorohod $J_1$ topology on $D_{\mathcal S}[0,\infty)$ to a process with continuous paths if and only if, on some probability space, there are copies of the processes and of the limit, with the same laws, that converge almost surely uniformly on compact time intervals in $\ell_1$. The file takes this coupling form as the definition and builds on it the statement "any subsequence has a further subsequence that converges weakly to a limit solving (2.1)", in which the limit's existence is part of the claim.
--
--   **Formalization Note** A fluid state is a function `ℕ → ℝ` with the paper's level index; coordinate `0` equals $1$ (the convention $q_0\equiv 1$), so it does not contribute to $\ell_1$ distances between states. The $\ell_1$ distance and all suprema are computed in $[0,\infty]$. The coefficient $p_{m-1}$ is written as $1$ if $\lambda\le 1-q_{m+1}$ and $(1-q_{m+1})/\lambda$ otherwise: this is the minimum of (4.4) for $\lambda>0$, agrees with the two-case definition on p. 5 wherever that is defined (p. 5 leaves $\lambda=1-q_{m+1}$ open), and never divides by $0$. Laws of paths are taken on the product σ-algebra of $\mathbb R_{\ge 0}\to\mathbb R^{\mathbb N}$. For the compactness statements, $\mathcal S$ is also viewed inside the Banach space $\ell^1$ (`lp`).
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 5, 17, §2.2 (𝕊, m(q), p_i(q), (2.1)), (4.4), (4.5); §2.1 notation D_E[0,∞) and weak convergence, p. 5

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-!
Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, §2.2 (p. 5) and (4.4)–(4.5)
(p. 17): the space `𝕊` of fluid-scaled occupancy states with the `ℓ¹` topology, the index
`m(q)`, the coefficients `p_i(q)`, the integral equations (2.1)/(4.5), and the notion of weak
convergence (Skorohod `J₁`, continuous limit) in `D_𝕊[0, ∞)` used by Theorems 2.1 and 4.1.

**Index base.** A fluid state is a function `q : ℕ → ℝ` with the paper's level index: `q i` is
`q_i` for `i ≥ 1`, and coordinate `0` carries the convention `q₀ ≡ 1` (the scaled `Q₀ ≡ N`).
Coordinate `0` therefore contributes nothing to the `ℓ¹` distance between two states of `𝕊`.
-/

/-- The `ℓ¹` distance `‖x − y‖₁ = ∑_i |x_i − y_i|`, computed in `[0, ∞]` (never a junk value;
it is finite for summable `x, y`). -/
noncomputable def l1dist (x y : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal |x i - y i|

/-- The **fluid space** `𝕊` (p. 5): `q ∈ [0,1]^b` with `q_i ≤ q_{i−1}` for `i = 2, …, b` and
`∑_{i=1}^{b} q_i < ∞`. Here: `q 0 = 1` (the convention `q₀ ≡ 1`), `q i ∈ [0, 1]` and
nonincreasing for `i ≥ 1`, `q i = 0` for `i > b` (the convention `q_{b+1} = 0`), and `q` summable.
`𝕊` carries the `ℓ¹` topology (`l1dist`). -/
def FluidSpace (b : ℕ∞) : Set (ℕ → ℝ) :=
  {q | q 0 = 1 ∧ (∀ i, 1 ≤ i → 0 ≤ q i ∧ q i ≤ 1) ∧ (∀ i j, 1 ≤ i → i ≤ j → q j ≤ q i) ∧
    (∀ i : ℕ, b < (i : ℕ∞) → q i = 0) ∧ Summable q}

/-- `𝕊` as a subset of the Banach space `ℓ¹ = lp (fun _ : ℕ => ℝ) 1`, carrying its norm
topology (for the compactness statements of Lemmas 4.6 and 4.7). -/
def FluidSpaceL1 (b : ℕ∞) : Set (lp (fun _ : ℕ => ℝ) 1) :=
  {x | ⇑x ∈ FluidSpace b}

/-- The scaled occupancy vector `Q/N`, coordinatewise. -/
noncomputable def scaledOcc (N : ℕ) (Q : ℕ →₀ ℕ) : ℕ → ℝ :=
  fun i => (Q i : ℝ) / N

/-- `m(q) = min {i : q_{i+1} < 1}` (p. 5), with `i` ranging over `ℕ` (so `m(q) = 0` iff
`q_1 < 1`). For `q ∈ 𝕊` the set is nonempty (`q_i → 0` because `q` is summable; for finite `b`,
`q_{b+1} = 0`), so the infimum is the minimum. -/
noncomputable def mIdx (q : ℕ → ℝ) : ℕ :=
  sInf {i : ℕ | q (i + 1) < 1}

/-- The coefficient `p_{m(q)−1}(q) = min {(1 − q_{m(q)+1})/λ, 1}` of (4.4), written as
`1` if `λ ≤ 1 − q_{m(q)+1}` and `(1 − q_{m(q)+1})/λ` otherwise. For `λ > 0` this is exactly the
minimum of (4.4); it agrees with the two-case definition on p. 5 wherever that one is defined; and
it never divides by `0` (the second branch forces `λ > 1 − q_{m(q)+1} ≥ 0`). -/
noncomputable def pTop (lam : ℝ) (q : ℕ → ℝ) : ℝ :=
  if lam ≤ 1 - q (mIdx q + 1) then 1 else (1 - q (mIdx q + 1)) / lam

/-- The coefficients `p_i(q)`, `i ≥ 0`, of (4.4) (p. 17; also p. 5): if `m(q) = 0` then
`p_0(q) = 1` and `p_i(q) = 0` for `i ≥ 1`; if `m(q) > 0` then `p_{m(q)−1}(q) = pTop`,
`p_{m(q)}(q) = 1 − p_{m(q)−1}(q)`, and `p_i(q) = 0` otherwise. `p_i(q)` is the fraction of
incoming tasks assigned to servers with exactly `i` tasks. -/
noncomputable def pCoef (lam : ℝ) (q : ℕ → ℝ) (i : ℕ) : ℝ :=
  if mIdx q = 0 then (if i = 0 then 1 else 0)
  else if i + 1 = mIdx q then pTop lam q
  else if i = mIdx q then 1 - pTop lam q
  else 0

/-- `q` is a **solution of (2.1)** (equivalently (4.5) with `q(0) = q^∞`) on `[0, ∞)`: `q(t) ∈ 𝕊`
for every `t ≥ 0`, and for every level `i = 1, …, b` and every `t ≥ 0` the integrands are
integrable on `[0, t]` and
`q_i(t) = q^∞_i + λ ∫_0^t p_{i−1}(q(s)) ds − ∫_0^t (q_i(s) − q_{i+1}(s)) ds`,
with `q_{b+1} ≡ 0` for finite `b` (part of `q(s) ∈ 𝕊`). The integrability clauses rule out the
junk value `0` of a Bochner integral of a non-integrable function. -/
def IsFluidSolution (b : ℕ∞) (lam : ℝ) (qinf : ℕ → ℝ) (q : ℝ → ℕ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → q t ∈ FluidSpace b) ∧
  ∀ i : ℕ, 1 ≤ i → (i : ℕ∞) ≤ b → ∀ t : ℝ, 0 ≤ t →
    IntervalIntegrable (fun s => pCoef lam (q s) (i - 1)) volume 0 t ∧
    IntervalIntegrable (fun s => q s i - q s (i + 1)) volume 0 t ∧
    q t i = qinf i + lam * ∫ s in (0 : ℝ)..t, pCoef lam (q s) (i - 1)
      - ∫ s in (0 : ℝ)..t, (q s i - q s (i + 1))

/-- `sup_{s ∈ [0, t]} ‖x(s) − y(s)‖₁`, in `[0, ∞]`. -/
noncomputable def supDistL1 (x y : ℝ → ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (s : ℝ) (_ : s ∈ Set.Icc 0 t), l1dist (x s) (y s)

/-- A path `x : [0, ∞) → ℓ¹` is **càdlàg in `ℓ¹`**: right-continuous on `[0, ∞)` and with left
limits on `(0, ∞)`, both in the `ℓ¹` distance. -/
def IsCadlagL1 (x : ℝ → ℕ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Tendsto (fun s => l1dist (x s) (x t)) (𝓝[≥] t) (𝓝 0)) ∧
  (∀ t : ℝ, 0 < t → ∃ l : ℕ → ℝ, Tendsto (fun s => l1dist (x s) l) (𝓝[<] t) (𝓝 0))

/-- **Weak convergence in `D_{ℓ¹}[0, ∞)` (Skorohod `J₁`) to a process with continuous paths,
in coupling form**; the `ℓ¹`-valued analogue of `BellWilliams2001.ThresholdPolicy.CouplingConverges`.
Processes `Z n` on `(Ω, P)` and `Zlim` on `(Ω', P')` with values in `ℕ → ℝ` and time `t ≥ 0` are
related by: there are a probability space `(Ω'', P'')` and processes `Y n`, `Ylim` on it such
that `Y n` has the law of `Z n` for all large `n` and `Ylim` has the law of `Zlim` (laws of the
paths on `[0, ∞)`, product σ-algebra of `ℝ≥0 → ℕ → ℝ`, which is the Borel σ-algebra of
`D_{ℓ¹}[0, ∞)` on càdlàg paths), every path of every `Y n` is `ℓ¹`-càdlàg, and almost surely
`sup_{s ≤ t} ‖Y n(s) − Ylim(s)‖₁ → 0` for every `t ≥ 0`. When the limit has continuous paths this
is equivalent to `Z n ⟹ Zlim` in `D_{ℓ¹}[0, ∞)` with the `J₁` topology (Skorohod representation
in one direction; a.s. locally uniform convergence implies a.s. `J₁` convergence, hence weak
convergence, in the other). -/
def CouplingConvergesL1 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (Z : ℕ → Ω → ℝ → ℕ → ℝ) (Zlim : Ω' → ℝ → ℕ → ℝ) : Prop :=
  ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
    (Y : ℕ → Ω'' → ℝ → ℕ → ℝ) (Ylim : Ω'' → ℝ → ℕ → ℝ),
    IsProbabilityMeasure P'' ∧
    (∀ᶠ n in atTop, IdentDistrib (fun ω (t : ℝ≥0) => Y n ω t)
      (fun ω (t : ℝ≥0) => Z n ω t) P'' P) ∧
    IdentDistrib (fun ω (t : ℝ≥0) => Ylim ω t) (fun ω (t : ℝ≥0) => Zlim ω t) P'' P' ∧
    (∀ n ω, IsCadlagL1 (Y n ω)) ∧
    ∀ᵐ ω ∂P'', ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => supDistL1 (Y n ω) (Ylim ω) t) atTop (𝓝 0)

/-- The conclusion of Theorems 2.1 and 4.1: **any subsequence of the processes `Z n` has a
further subsequence that converges weakly (Skorohod `J₁`, `ℓ¹` topology) to a limit satisfying
(2.1)**. For every strictly increasing `φ` there are a strictly increasing `ψ`, a probability
space `(Ω', P')` and a process `q` on it whose paths almost surely solve (2.1) with initial value
`q^∞`, such that `Z (φ (ψ n)) ⟹ q`. The limit is asserted to exist; it may depend on the
subsequence, the equation it satisfies does not. -/
def SubseqFluidLimit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (b : ℕ∞) (lam : ℝ)
    (qinf : ℕ → ℝ) (Z : ℕ → Ω → ℝ → ℕ → ℝ) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (q : Ω' → ℝ → ℕ → ℝ),
      IsProbabilityMeasure P' ∧ (∀ᵐ ω ∂P', IsFluidSolution b lam qinf (q ω)) ∧
      CouplingConvergesL1 P P' (fun n => Z (φ (ψ n))) q

end PowerOfDUniversality.Fluid



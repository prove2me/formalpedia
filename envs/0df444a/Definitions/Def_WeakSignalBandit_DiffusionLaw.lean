-- Prove2me | Definitions.Def_WeakSignalBandit_DiffusionLaw
-- name    : WeakSignalBandit_DiffusionLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:25.411316+00:00
-- url     : https://prove2.me/theorems/18e1d2a5-c24b-4844-9933-d5b0b1c44d57
-- title:
--   Path space $C([0,1],\mathbb R^d)$, the generator $Lf=\tfrac12\sum a_{kl}\partial_k\partial_l f+\sum b_k\partial_k f$, and solutions of $dZ=b\,dt+\eta\,dB$ on $[0,1]$ as a martingale problem
-- statement:
--   Let $\iota$ be a finite set of coordinates and $\mathbb R^\iota$ the Euclidean space with norm $|z|$ (the paper's $\mathbb R^d$; for the bandit, $\mathbb R^{2K}$).
--
--   1. **Path space.** $\mathcal C=C([0,1],\mathbb R^\iota)$ is the space of continuous paths with the uniform metric $d(x,y)=\sup_{t\in[0,1]}|x(t)-y(t)|$ and its Borel $\sigma$-algebra.
--   2. **Generator.** For a matrix-valued $a(z)=(a_{k,l}(z))$ and a vector field $b(z)=(b_k(z))$, and a twice differentiable $f:\mathbb R^\iota\to\mathbb R$,
--   $$Lf(z)=\frac12\sum_{k,l}a_{k,l}(z)\,\partial_k\partial_l f(z)+\sum_k b_k(z)\,\partial_k f(z).$$
--   3. **Diffusion law.** A Borel measure $P$ on $\mathcal C$ is a *solution law* of the stochastic differential equation
--   $$dZ_t=b(Z_t)\,dt+\eta(Z_t)\,dB_t,\qquad Z_0=z_0,\qquad a=\eta\eta^{\top},\qquad t\in[0,1],$$
--   if $P$ is a probability measure, the canonical process $X_t(x)=x(t)$ satisfies $X_0=z_0$ $P$-almost surely, and for every smooth compactly supported $f$, all $0\le s\le t\le 1$, all times $r_1,\dots,r_m\le s$ and all bounded measurable $h_1,\dots,h_m$,
--   $$\mathbb E_P\Big[\Big(f(X_t)-f(X_s)-\int_s^t Lf(X_u)\,du\Big)\prod_{i=1}^m h_i(X_{r_i})\Big]=0,$$
--   that is, $f(X_t)-f(X_0)-\int_0^tLf(X_u)\,du$ is a martingale on $[0,1]$ for the natural filtration of $X$ (the martingale problem of Stroock and Varadhan).
--
--   These objects state both the paper's goal (Theorem 1: the limit of the bandit's sample paths solves (3.1)) and the diffusion approximation it rests on (Theorem 11).
--
--   **Formalization Note** Mathlib has no Itô integral, so solutions of an SDE are represented by their laws through the martingale problem; a probability law on $\mathcal C$ solves the martingale problem for $(a,b)$ exactly when it is the law of a weak solution of the SDE for some $\eta$ with $\eta\eta^\top=a$ (Ethier and Kurtz, *Markov Processes*, Ch. 5, Prop. 3.1 and Thm. 3.3). This is also why the SDE "is uniquely defined by $a$" (footnote 5 of the paper). The horizon is $[0,1]$. Derivatives are Fréchet derivatives along the coordinate vectors.
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (3.1) p.12; §3.1 p.12 (the space C); (A.3) p.31; (A.10), (A.16) and footnote 5, pp.32–33

import Mathlib

open MeasureTheory
open scoped ContDiff

namespace WeakSignalBandit

/-- The Euclidean space `ℝ^ι` of a finite coordinate set `ι` (the paper's `ℝ^d`, and for the bandit
`ℝ^{2K}` with coordinates `I_Q ⊔ I_S`), with the Euclidean norm `|z|`.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, §A.1, pp.31–32 (`Z^n_i` takes values in `ℝ^d`; `|z| < R`). -/
abbrev Sp (ι : Type*) := EuclideanSpace ℝ ι

/-- The path space `C = C([0,1], ℝ^ι)` with the uniform metric
`d(x, y) = sup_{t∈[0,1]} |x(t) − y(t)|`.
Kuang, Wager, arXiv:2101.09855v7, §3.1, p.12 ("Let C be the space of continuous functions
`[0,1] ↦ ℝ^{2K}` equipped with the uniform metric").

**Formalization Note** `C(unitInterval, ·)` carries the compact-open topology, which on a compact
domain is the topology of the uniform metric. -/
abbrev Path (ι : Type*) := C(unitInterval, EuclideanSpace ℝ ι)

/-- The Borel σ-algebra of the path space `C` (laws of processes with paths in `C` live on it). -/
instance instMeasurableSpacePath (ι : Type*) [Fintype ι] : MeasurableSpace (Path ι) := borel _

instance instBorelSpacePath (ι : Type*) [Fintype ι] : BorelSpace (Path ι) := ⟨rfl⟩

/-- A path evaluated at a real time `u`, clamped to `[0,1]` (only used for `u ∈ [0,1]`). -/
noncomputable def Path.evalR {ι : Type*} (x : Path ι) (u : ℝ) : Sp ι :=
  x (Set.projIcc 0 1 zero_le_one u)

/-- The second-order operator (generator) of the diffusion with diffusion matrix `a` and drift `b`:
`L f(z) = ½ Σ_{k,l} a_{k,l}(z) ∂_k ∂_l f(z) + Σ_k b_k(z) ∂_k f(z)`.
Kuang, Wager, arXiv:2101.09855v7, §A.1, pp.31–33: the SDE `dZ_t = b(Z_t)dt + η(Z_t)dB_t` (A.10)
with `a(z) = η(z)η(z)ᵀ` (A.16); footnote 5, p.32: the SDE "is uniquely defined by `a`".

**Formalization Note** Partial derivatives are `fderiv` along the coordinate vectors
`EuclideanSpace.single i 1`. -/
noncomputable def generator {ι : Type*} [Fintype ι] [DecidableEq ι] (a : Sp ι → ι → ι → ℝ) (b : Sp ι → ι → ℝ)
    (f : Sp ι → ℝ) (z : Sp ι) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, a z i j *
      fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
    ∑ i, b z i * fderiv ℝ f z (EuclideanSpace.single i 1)

/-- `P` is the law on `C([0,1], ℝ^ι)` of a (weak) solution on the horizon `t ∈ [0,1]` of the SDE
`dZ_t = b(Z_t) dt + η(Z_t) dB_t`, `Z_0 = z₀`, with `ηηᵀ = a`, written as its martingale problem
(Stroock–Varadhan): `P` is a probability measure, the canonical process `X` starts at `z₀` almost
surely, and for every smooth compactly supported `f` the process
`f(X_t) − f(X_0) − ∫_0^t L f(X_u) du` is a martingale on `[0,1]` for the natural filtration of `X`;
the martingale property is tested against all finite products of bounded measurable functions of
the past values `X_{r_1}, …, X_{r_m}`, `r_i ≤ s`.
Kuang, Wager, arXiv:2101.09855v7, (3.1) p.12, (A.3) p.31, (A.10) and footnote 5 p.32; the paper's
proof is "based on the martingale framework of Stroock and Varadhan [2007]" (p.31).

**Formalization Note** Mathlib has no Itô integral, so solutions of the SDE are encoded by the
martingale problem; a law solves the martingale problem for `(a, b)` exactly when it is the law of
a weak solution of the SDE for some `η` with `ηηᵀ = a` (Ethier–Kurtz, Ch. 5, Prop. 3.1 and
Thm 3.3), which is the sense of footnote 5. The time horizon is `[0,1]`, as in Theorem 1
("over `t ∈ [0,1]`"). -/
def IsDiffusionLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (a : Sp ι → ι → ι → ℝ) (b : Sp ι → ι → ℝ)
    (z₀ : Sp ι) (P : Measure (Path ι)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ᵐ x ∂P, x 0 = z₀) ∧
  ∀ f : Sp ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    ∀ s t : unitInterval, s ≤ t →
    ∀ (m : ℕ) (r : Fin m → unitInterval), (∀ i, r i ≤ s) →
    ∀ h : Fin m → Sp ι → ℝ, (∀ i, Measurable (h i) ∧ ∃ C : ℝ, ∀ z, |h i z| ≤ C) →
      ∫ x, (f (x t) - f (x s) - ∫ u in (s : ℝ)..(t : ℝ), generator a b f (x.evalR u)) *
          ∏ i, h i (x (r i)) ∂P = 0

end WeakSignalBandit



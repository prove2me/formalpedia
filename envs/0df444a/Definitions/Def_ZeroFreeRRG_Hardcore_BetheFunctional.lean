-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
-- name    : ZeroFreeRRG_Hardcore_BetheFunctional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:36:26.804111+00:00
-- url     : https://prove2.me/theorems/cdae16b1-bdfb-429d-a381-614fbade55c9
-- title:
--   Cavity message laws 𝒫_π, the Bethe functional B_{r,t}, Condition 1, variational replica symmetry, and the threshold α_RSB(d)
-- statement:
--   Fix a model and a real parameter $t$. The **cavity message distributions with mean $\pi(t)$** are
--   $$\mathcal P_{\pi(t)}=\{\nu\in\mathcal P(\Delta_\Omega):\ \mathbb E_{\mu\sim\nu}[\mu]=\pi(t)\},$$
--   all Borel probability laws on the simplex $\Delta_\Omega$ with mean $\pi(t)$; $\delta_{\pi(t)}$ is the point mass at $\pi(t)$. For i.i.d. $\mu_1,\mu_2,\dots\sim\nu$ and an integer $k\ge0$, the vertex and edge factors and the **Bethe functional** are (eq. (10))
--   $$V_{k,t}=\sum_{a\in\Omega}\pi_a(t)\prod_{i=1}^k(M(t)\mu_i)_a,\qquad E_t=\mu_1^\top M(t)\mu_2,\qquad \mathcal B_{k,t}(\nu)=\mathbb E[V_{k,t}\log V_{k,t}]-\tfrac k2\,\mathbb E[E_t\log E_t],$$
--   with $0\log0=0$, extended to real $r\ge0$ by $\mathcal B_{r,t}=(1-r+\lfloor r\rfloor)\mathcal B_{\lfloor r\rfloor,t}+(r-\lfloor r\rfloor)\mathcal B_{\lfloor r\rfloor+1,t}$. **Variational replica symmetry** at $(d,t)$ means $\mathcal B_{d,t}(\nu)\le0$ for all $\nu\in\mathcal P_{\pi(t)}$. **Condition 1** at $(d,t)$: $\mathcal B_{d,t}(\nu)<0$ for every $\nu\in\mathcal P_{\pi(t)}\setminus\{\delta_{\pi(t)}\}$. The parameter lies in the **interior of the variational replica-symmetric regime** (Lemma 4.17, as its proof uses it) if variational replica symmetry holds at some $\alpha'\in(\alpha,1/2)$ (hardcore) or some $\beta'\in[0,\beta)$ (Potts).
--
--   The **replica symmetry breaking threshold** (32) is
--   $$S_d=\{\alpha\in(0,1/2):\exists\nu\in\mathcal P_{\pi_\alpha},\ \mathcal B_{d,\alpha}(\nu)>0\},\qquad \alpha_{\mathrm{RSB}}(d)=\inf S_d,\quad \inf\emptyset=1/2 .$$
--   It is the endpoint of the zero-free region of the goal theorem.
--
--   **Formalization Note.** A message law is a `ProbabilityMeasure` on $\mathbb R^\Omega$ giving the complement of `stdSimplex ℝ Ω` measure zero, with coordinatewise Bochner mean $\pi(t)$; for hardcore $\mu=(\mu_0,\mu_1)=(1-u,u)$. The two expectations of $\mathcal B_{k,t}$ are Bochner integrals over $\nu^{\otimes k}$ (`Measure.pi`) and $\nu\otimes\nu$; $V$ and $E$ are bounded on the simplex, so they are integrable. `alphaRSB` writes the empty case explicitly because Lean's `sInf ∅ = 0`.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 17, Definition 2.7; p. 29, Condition 1; pp. 29–30, Lemma 4.17 and its proof; p. 33, eq. (32)

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels

open scoped Classical
open MeasureTheory

namespace ZeroFreeRRG.Hardcore

/-- `x log x`, with `0 log 0 = 0` (Lean's `Real.log 0 = 0`). -/
noncomputable def xlogx (x : ℝ) : ℝ := x * Real.log x

/-- The space `𝒫_{π(t)}` of cavity message distributions with mean `π(t)` (Definition 2.7, p. 17):
the Borel probability measures `ν` on the simplex `Δ_Ω` with `E_{μ∼ν}[μ] = π(t)`.

**Formalization Note.** `ν` is a Borel probability measure on `ℝ^Ω` giving the complement of the
simplex `Δ_Ω = stdSimplex ℝ Ω` measure zero; the mean is taken coordinatewise. All Borel laws are
allowed, not only finitely supported ones. For hardcore, `μ = (μ_0, μ_1) = (1 − u, u)`. -/
def cavityLaws (m : Model) (t : ℝ) : Set (ProbabilityMeasure (m.Spin → ℝ)) :=
  {ν | (ν : Measure (m.Spin → ℝ)) (stdSimplex ℝ m.Spin)ᶜ = 0 ∧
      ∀ a, ∫ μ, μ a ∂(ν : Measure (m.Spin → ℝ)) = m.pi t a}

/-- The point mass `δ_{π(t)}` at the constant message `π(t)`. -/
noncomputable def diracPi (m : Model) (t : ℝ) : ProbabilityMeasure (m.Spin → ℝ) :=
  ⟨Measure.dirac (m.pi t), inferInstance⟩

/-- `(M(t) μ)_a = ∑_b M_{ab}(t) μ_b`. -/
noncomputable def Mmul (m : Model) (t : ℝ) (μ : m.Spin → ℝ) (a : m.Spin) : ℝ :=
  ∑ b, m.M t a b * μ b

/-- The cavity vertex factor (10): `V_{k,t} = ∑_a π_a(t) ∏_{i=1}^k (M(t) μ_i)_a` (empty product `1`). -/
noncomputable def vertexFactor (m : Model) (t : ℝ) (k : ℕ) (μs : Fin k → m.Spin → ℝ) : ℝ :=
  ∑ a, m.pi t a * ∏ i, Mmul m t (μs i) a

/-- The cavity edge factor (10): `E_t = μ_1ᵀ M(t) μ_2`. -/
noncomputable def edgeFactor (m : Model) (t : ℝ) (μ₁ μ₂ : m.Spin → ℝ) : ℝ :=
  ∑ a, ∑ b, μ₁ a * m.M t a b * μ₂ b

/-- The Bethe functional at integer degree `k ≥ 0` (10):
`B_{k,t}(ν) = E[V_{k,t} log V_{k,t}] − (k/2) E[E_t log E_t]`, with `μ_1, μ_2, … ∼ ν` i.i.d.: the
first expectation is over `ν^{⊗k}`, the second over `ν^{⊗2}`. -/
noncomputable def betheK (m : Model) (t : ℝ) (k : ℕ) (ν : ProbabilityMeasure (m.Spin → ℝ)) : ℝ :=
  (∫ μs, xlogx (vertexFactor m t k μs)
      ∂(Measure.pi fun _ : Fin k => (ν : Measure (m.Spin → ℝ))))
    - (k : ℝ) / 2 * ∫ p, xlogx (edgeFactor m t p.1 p.2)
      ∂((ν : Measure (m.Spin → ℝ)).prod (ν : Measure (m.Spin → ℝ)))

/-- The Bethe functional at real degree `r ≥ 0` by piecewise-linear interpolation (Definition 2.7):
`B_{r,t} = (1 − r + ⌊r⌋) B_{⌊r⌋,t} + (r − ⌊r⌋) B_{⌊r⌋+1,t}`. At integer `r = k` it is `B_{k,t}`. -/
noncomputable def betheR (m : Model) (t : ℝ) (r : ℝ) (ν : ProbabilityMeasure (m.Spin → ℝ)) : ℝ :=
  (1 - r + ⌊r⌋₊) * betheK m t ⌊r⌋₊ ν + (r - ⌊r⌋₊) * betheK m t (⌊r⌋₊ + 1) ν

/-- Variational replica symmetry at `(d, t)` (Definition 2.7): `B_{d,t}(ν) ≤ 0` for every
`ν ∈ 𝒫_{π(t)}`. -/
def VariationalRS (m : Model) (d : ℕ) (t : ℝ) : Prop :=
  ∀ ν ∈ cavityLaws m t, betheK m t d ν ≤ 0

/-- Condition 1 (p. 29) at `(d, t)`: `B_{d,t}(ν) < 0` for all `ν ∈ 𝒫_{π(t)} \ {δ_{π(t)}}`. -/
def Condition1 (m : Model) (d : ℕ) (t : ℝ) : Prop :=
  ∀ ν ∈ cavityLaws m t, ν ≠ diracPi m t → betheK m t d ν < 0

/-- `t` lies in the interior of the variational replica-symmetric regime (Lemma 4.17, p. 29), read as
the proof of Lemma 4.17 (p. 30) and of Theorems 4.1–4.2 (p. 33) use it: for hardcore at `α`, some
`α' ∈ (α, 1/2)` satisfies variational replica symmetry; for Potts at `β`, some `β' ∈ [0, β)` does. -/
def InteriorVariationalRS : Model → ℕ → ℝ → Prop
  | .hardcore, d, α => ∃ α' : ℝ, α < α' ∧ α' < 1 / 2 ∧ VariationalRS .hardcore d α'
  | .potts q, d, β => ∃ β' : ℝ, 0 ≤ β' ∧ β' < β ∧ VariationalRS (.potts q) d β'

/-- The positive-witness set (32): `S_d = {α ∈ (0, 1/2) : ∃ ν ∈ 𝒫_{π_α}, B_{d,α}(ν) > 0}`. -/
def S (d : ℕ) : Set ℝ :=
  {α | 0 < α ∧ α < 1 / 2 ∧ ∃ ν ∈ cavityLaws .hardcore α, 0 < betheK .hardcore α d ν}

/-- The replica symmetry breaking threshold (32): `α_RSB(d) = inf S_d`, with `inf ∅ = 1/2`.

**Formalization Note.** Lean's `sInf ∅ = 0` on `ℝ`, so the empty case is written out. `S_d` lies in
`(0, 1/2)`, so it is bounded below and `sInf` is its infimum. -/
noncomputable def alphaRSB (d : ℕ) : ℝ :=
  if S d = ∅ then 1 / 2 else sInf (S d)

end ZeroFreeRRG.Hardcore



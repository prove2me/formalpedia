-- Prove2me | Definitions.Def_JuHardCoreTransition_Mixing_BooleanLaws
-- name    : JuHardCoreTransition_Mixing_BooleanLaws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:15:36.134281+00:00
-- url     : https://prove2.me/theorems/05671c7b-adfc-4f1b-9bec-5b2b639324e9
-- title:
--   Boolean laws: marginals, covariance, field tilts, pinnings and the influence matrix $\Psi_\mu$
-- statement:
--   A **Boolean law** on $\{0,1\}^V$ ($V$ finite) is a probability vector $\mu$ on configurations, identified with their sets of occupied coordinates $I\subseteq V$ ($X_v=1$ iff $v\in I$). For $X\sim\mu$ write $p_v=\mu(X_v=1)$ and $\mathrm{Cov}(X_u,X_v)=\mu(X_u=X_v=1)-p_up_v$; the quadratic form $z^\top\mathrm{Cov}_\mu(X)z=\sum_{u,v}z_uz_v\mathrm{Cov}(X_u,X_v)$ is the variance of $\sum_v z_vX_v$.
--
--   For a vector $\psi$ of positive reals, the **field tilt** is
--   $$(\psi*\mu)(I)=\frac{\mu(I)\prod_{v\in I}\psi_v}{\sum_J\mu(J)\prod_{v\in J}\psi_v}.$$
--   A **pinning** $\tau$ is a partial assignment ($\tau_v\in\{0,1,\text{free}\}$); it is **feasible** for $\mu$ if the event "$X$ agrees with $\tau$" has positive probability, and $\mu^\tau$ is $\mu$ conditioned on that event.
--
--   **Definition 2.1 (spectral independence).** Omit the deterministic coordinates (those with $p_v\in\{0,1\}$) and set, on the remaining (free) coordinates,
--   $$\Psi_\mu(i,j)=\frac{\mathrm{Cov}(X_i,X_j)}{p_i(1-p_i)}=\mu(X_j=1\mid X_i=1)-\mu(X_j=1\mid X_i=0)\quad(i\neq j),$$
--   with diagonal entries equal to one. $\lambda_{\max}(\Psi_\mu)$ is its largest eigenvalue; the matrix is similar to a symmetric one, so its eigenvalues are real.
--
--   **Formalization Note.** Laws are functions `Finset V → ℝ` (`IsBoolLaw`: nonnegative, total mass one); `marg`, `pairProb`, `cov`, `covQuad`, `tilt`; a pinning is `V → Option Bool` (`some true`/`some false` pin to $1$/$0$), `pinMass`, `IsFeasiblePinning`, `condition`. `freeSet μ` is the set of coordinates with $0<p_v<1$; `influence μ` is $\Psi_\mu$ indexed by it; `influenceMax μ` is the supremum of the set of real eigenvalues of $\Psi_\mu$ (a finite set, so its maximum); with no free coordinate this set is empty and the value is $0$, where the paper's condition is vacuous. `NoDeterministic μ` means $0<p_v<1$ for every $v$.
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Definition 2.1 and §2.1 (field tilt), §3, printed pp.8 / PDF pp.9

import Mathlib

namespace JuHardCoreTransition.Mixing

/-!
# Boolean laws: marginals, covariance, field tilts, pinnings and the influence matrix

Ju, Liu and Yin, *Fine-Grained Complexity Across the Computational Phase Transition*,
arXiv:2611.02702, pinned source.pdf dated 2026-11-02 (SHA256 6288a2d2…3678; arXiv version suffix
not supplied), §2.1 (printed pp.8–9 / PDF pp.9–10), Definition 2.1 and the field tilt before
Lemma 2.2; §3 (printed p.16 / PDF p.17).

A configuration `X ∈ {0,1}^V` is identified with its set of occupied coordinates `I ⊆ V`
(`X_v = 1` iff `v ∈ I`). A *Boolean law* on `{0,1}^V` is a function `μ : Finset V → ℝ`, nonnegative
and summing to one (`IsBoolLaw`).

* `marg μ v = μ(X_v = 1)`, `pairProb μ u v = μ(X_u = X_v = 1)`, `cov μ u v = Cov(X_u, X_v)`.
* `tilt ψ μ` is the field tilt `(ψ ∗ μ)(I) ∝ μ(I) ∏_{v ∈ I} ψ_v`.
* A *pinning* `τ : V → Option Bool` fixes `X_v = 1` where `τ v = some true` and `X_v = 0` where
  `τ v = some false`; it is *feasible* when the pinned event has positive probability, and
  `condition μ τ` is the conditional law `μ^τ`.
* `freeSet μ` is the set of non-deterministic coordinates (`0 < p_v < 1`); the influence matrix
  `Ψ_μ(i,j) = Cov(X_i,X_j)/(p_i(1-p_i))` of Definition 2.1 is indexed by it, with diagonal entries
  equal to one, and `influenceMax μ = λ_max(Ψ_μ)` is its largest (real) eigenvalue.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `μ` is a probability law on `{0,1}^V` (configurations identified with occupied sets). -/
def IsBoolLaw (μ : Finset V → ℝ) : Prop :=
  (∀ I, 0 ≤ μ I) ∧ ∑ I, μ I = 1

/-- The occupation marginal `p_v = μ(X_v = 1)`. -/
noncomputable def marg (μ : Finset V → ℝ) (v : V) : ℝ :=
  ∑ I, if v ∈ I then μ I else 0

/-- `μ(X_u = 1, X_v = 1)`. -/
noncomputable def pairProb (μ : Finset V → ℝ) (u v : V) : ℝ :=
  ∑ I, if u ∈ I ∧ v ∈ I then μ I else 0

/-- The covariance `Cov(X_u, X_v) = E[X_u X_v] − E[X_u] E[X_v]`. -/
noncomputable def cov (μ : Finset V → ℝ) (u v : V) : ℝ :=
  pairProb μ u v - marg μ u * marg μ v

/-- The quadratic form `zᵀ Cov_μ(X) z = Var_μ(∑_v z_v X_v)`. -/
noncomputable def covQuad (μ : Finset V → ℝ) (z : V → ℝ) : ℝ :=
  ∑ u, ∑ v, z u * z v * cov μ u v

/-- The field tilt `(ψ ∗ μ)(I) = μ(I) ∏_{v ∈ I} ψ_v / ∑_J μ(J) ∏_{v ∈ J} ψ_v` (§2.1, p.8). -/
noncomputable def tilt (ψ : V → ℝ) (μ : Finset V → ℝ) (I : Finset V) : ℝ :=
  μ I * (∏ v ∈ I, ψ v) / ∑ J, μ J * ∏ v ∈ J, ψ v

/-- A partial assignment (pinning): `some true` pins a coordinate to `1`, `some false` to `0`,
`none` leaves it free. -/
abbrev Pinning (V : Type*) := V → Option Bool

/-- The configuration `I` agrees with the pinning `τ`. -/
def Agrees (τ : Pinning V) (I : Finset V) : Prop :=
  ∀ v, (τ v = some true → v ∈ I) ∧ (τ v = some false → v ∉ I)

/-- The probability `μ(X agrees with τ)` of the pinned event. -/
noncomputable def pinMass (μ : Finset V → ℝ) (τ : Pinning V) : ℝ := by
  classical
  exact ∑ I, if Agrees τ I then μ I else 0

/-- `τ` is a *feasible pinning* of `μ`: an assignment of positive probability. -/
def IsFeasiblePinning (μ : Finset V → ℝ) (τ : Pinning V) : Prop :=
  0 < pinMass μ τ

/-- The conditional law `μ^τ = μ(· | X agrees with τ)`. -/
noncomputable def condition (μ : Finset V → ℝ) (τ : Pinning V) (I : Finset V) : ℝ := by
  classical
  exact (if Agrees τ I then μ I else 0) / pinMass μ τ

/-- The non-deterministic coordinates of `μ`: those with `0 < μ(X_v = 1) < 1`. Definition 2.1
omits the deterministic coordinates. -/
noncomputable def freeSet (μ : Finset V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => 0 < marg μ v ∧ marg μ v < 1

/-- `μ` has no deterministic coordinates. -/
def NoDeterministic (μ : Finset V → ℝ) : Prop :=
  ∀ v, 0 < marg μ v ∧ marg μ v < 1

/-- **The influence matrix** of Definition 2.1 (p.8), on the non-deterministic coordinates:
`Ψ_μ(i,j) = Cov(X_i,X_j) / (p_i (1 − p_i))`
(`= μ(X_j = 1 | X_i = 1) − μ(X_j = 1 | X_i = 0)` off the diagonal); its diagonal entries are `1`. -/
noncomputable def influence (μ : Finset V → ℝ) :
    Matrix (freeSet μ) (freeSet μ) ℝ :=
  fun i j => cov μ i j / (marg μ i * (1 - marg μ i))

/-- **`λ_max(Ψ_μ)`**, the largest eigenvalue of the influence matrix. `Ψ_μ` is similar to a
symmetric matrix, so its eigenvalues are real and finitely many; this is the supremum of the
(finite) set of real eigenvalues, i.e. their maximum. When no free coordinate remains the set is
empty and the value is `0` (the paper's condition is then vacuous). -/
noncomputable def influenceMax (μ : Finset V → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ z : freeSet μ → ℝ, z ≠ 0 ∧ (influence μ).mulVec z = r • z}

end JuHardCoreTransition.Mixing



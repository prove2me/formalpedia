-- Prove2me | Definitions.Def_PrettyGoodShadow_Delta
-- name    : PrettyGoodShadow_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:40.877813+00:00
-- url     : https://prove2.me/theorems/53cf0991-7fa6-4d57-b17f-a4d7d2393a9d
-- title:
--   Bernoulli states $B_x$, $B^{(k)}_{\hat x}$, the state $S^+$ and the quantity $\Delta_x(p,n)$
-- statement:
--   Fix an observable $0\preceq A\preceq I$ and write $\theta_x=\operatorname{tr}(A\rho_x)$. The auxiliary Bernoulli state and the estimated Bernoulli state of a label law $\lambda$ are
--
--   $$
--   B_x=(1-\theta_x)|0\rangle\langle0|+\theta_x|1\rangle\langle1|,\qquad B^{(k)}_{\hat x}=\sum_y\lambda(y)\,B_y^{\otimes k}.
--   $$
--
--   The extended average state and the central quantity of the analysis are
--
--   $$
--   S^+(p,n,k)=\sum_x p_x\,\rho_x^{\otimes n}\otimes B_x^{\otimes k},\qquad
--   \Delta_x(p,n)=D\big(\rho_x^{\otimes n}\otimes B_x^{\otimes k}\,\big\|\,S^+(p,n,k)\big)-D\big(\rho_x^{\otimes n}\,\big\|\,S(p,n)\big).
--   $$
--
--   $\Delta_x$ measures how much relative entropy is lost when the $k$ Bernoulli registers are discarded.
--
--   **Formalization Note** $D$ is the published relative entropy, in nats, with value $+\infty$ off support and values in the extended reals. $\Delta_x$ is real: the difference of the real values of the two terms, never a subtraction of extended reals. For $p_x>0$ both terms are finite. For $p_x=0$ the real value may be a junk value, but every statement either assumes $p_x>0$ or multiplies by a weight that vanishes where $p_x=0$.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Definitions 4.4 and 4.6, pp.19–20; p.20

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_PrettyGoodShadow_obs
import Definitions.Def_DimFreeShadow_recoveryEffect

open scoped Kronecker

namespace PrettyGoodShadow

open DimFreeShadow (ensembleState)

open ShadowTomography.UpperBound (tensorPow)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **The diagonal Bernoulli state** `Ber(θ) = (1 − θ)|0⟩⟨0| + θ|1⟩⟨1|` (arXiv:2610.06781, sha256 bd055b7d…,
Definition 4.4, p.19), which is `B_x` at `θ = tr(O ρ_x)`. -/
noncomputable def bern (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((1 - θ : ℝ) : ℂ), (θ : ℂ)]

/-- **The estimated auxiliary Bernoulli state** `B^{(k)}_{x̂} = Σ_y Pr[x̂ = y] B_y^{⊗k}` (arXiv:2610.06781,
sha256 bd055b7d…, Definition 4.6, eq. (12), p.20), for an observable `A` and a law `lam` of the label estimate.

**Formalization Note** The shorthand `B^{(k)}_{x̂}(p, n)` of eq. (13) is `bernMix A ρ (pgmLaw p ρ n x) k`.
Taking `lam = q` gives the mixture `Σ_x q_x B_x^{⊗k}` of eq. (25), p.26. -/
noncomputable def bernMix {L d : Type} [Fintype L] [Fintype d] (A : Matrix d d ℂ)
    (ρ : L → Matrix d d ℂ) (lam : L → ℝ) (k : ℕ) : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ :=
  ∑ y, (lam y : ℂ) • tensorPow (bern (obs A (ρ y))) k

/-- **The extended average state** `S⁺(p, n, k) = Σ_x p_x ρ_x^{⊗n} ⊗ B_x^{⊗k}` (arXiv:2610.06781, sha256
bd055b7d…, p.20). -/
noncomputable def Splus {L d : Type} [Fintype L] [Fintype d] (p : L → ℝ) (ρ : L → Matrix d d ℂ)
    (A : Matrix d d ℂ) (n k : ℕ) :
    Matrix ((Fin n → d) × (Fin k → Fin 2)) ((Fin n → d) × (Fin k → Fin 2)) ℂ :=
  ∑ x, (p x : ℂ) • (tensorPow (ρ x) n ⊗ₖ tensorPow (bern (obs A (ρ x))) k)

/-- **The quantity** `Δ_x(p, n) = D(ρ_x^{⊗n} ⊗ B_x^{⊗k} ∥ S⁺(p, n, k)) − D(ρ_x^{⊗n} ∥ S(p, n))`
(arXiv:2610.06781, sha256 bd055b7d…, p.20).

**Formalization Note** `D` is the published `relativeEntropy` (natural logarithm, `EReal`-valued, `⊤` off
support). `Delta` is real: the difference of the `.toReal` of the two values, never an `EReal` subtraction. For
`p_x > 0` both supports hold, since `S⁺ ⪰ p_x ρ_x^{⊗n} ⊗ B_x^{⊗k}` and `S ⪰ p_x ρ_x^{⊗n}`, so both values are
finite and this is the paper's `Δ_x`. For `p_x = 0` the `.toReal` may read a junk value, but every statement
multiplies `Delta` by a weight vanishing where `p_x = 0`, or assumes `p_x > 0`. -/
noncomputable def Delta {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (p : L → ℝ)
    (ρ : L → Matrix d d ℂ) (A : Matrix d d ℂ) (n k : ℕ) (x : L) : ℝ :=
  (relativeEntropy (tensorPow (ρ x) n ⊗ₖ tensorPow (bern (obs A (ρ x))) k) (Splus p ρ A n k)).toReal -
    (relativeEntropy (tensorPow (ρ x) n) (ensembleState p ρ n)).toReal

end PrettyGoodShadow



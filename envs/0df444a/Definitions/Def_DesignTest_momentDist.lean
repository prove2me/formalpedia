-- Prove2me | Definitions.Def_DesignTest_momentDist
-- name    : DesignTest_momentDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:09:58.967125+00:00
-- url     : https://prove2.me/theorems/04ede708-68a2-4b81-bbe4-0c6be129d972
-- title:
--   Moment operator $M_t(\nu)$, Hilbert–Schmidt norm, $D_{\mathrm{Sym}}$, moment trace distance $\mathrm{Dist}_1^{(t)}$, frame potential $F^{\mathrm{st}}_t$
-- statement:
--   Fix $d,t\ge1$. Write $(\mathbb C^d)^{\otimes t}$ in the basis $|x_1\cdots x_t\rangle$, $x_k\in[d]$.
--
--   1. The **$t$-th moment operator** of a probability measure $\nu$ on pure states is
--   $$M_t(\nu)=\mathbb E_{\psi\sim\nu}\big[(|\psi\rangle\langle\psi|)^{\otimes t}\big],$$
--   the entrywise expectation of $(|\psi\rangle\langle\psi|)^{\otimes t}$, whose $(x,y)$ entry is $\prod_k\psi_{x_k}\overline{\psi_{y_k}}$.
--   2. For a square complex matrix $A$, the **Hilbert–Schmidt norm** is $\|A\|_2=(\sum_{i,j}|A_{ij}|^2)^{1/2}$; the **trace norm** $\|A\|_1=\mathrm{Tr}|A|$ is the sum of the singular values of $A$.
--   3. $D_{\mathrm{Sym}}=\binom{d+t-1}{t}$, the dimension of the symmetric subspace of $(\mathbb C^d)^{\otimes t}$.
--   4. The **$t$-th moment trace distance** of two probability measures is
--   $$\mathrm{Dist}_1^{(t)}(\mu,\nu)=\tfrac12\,\|M_t(\mu)-M_t(\nu)\|_1 .$$
--   A measure $\nu$ is an **exact state $t$-design** when $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)=0$, and $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)$ is its distance to the set of exact designs.
--   5. The **$t$-th state frame potential** is $F^{\mathrm{st}}_t(\nu)=\mathrm{Tr}[M_t(\nu)^2]$.
--
--   These are the quantities in which the state design testing problem (SDT) and all its bounds are stated.
--
--   **Formalization Note** Basis words are `Fin t → Fin d`. The trace norm is the published `DistQuantumQuery.traceNorm`, $\sum_i\sqrt{\lambda_i(A^\dagger A)}$, which needs no Hermitian hypothesis; for Hermitian $A$ it equals $\sum_i|\lambda_i(A)|$. The frame potential takes the real part of the trace, which is real because $M_t(\nu)$ is Hermitian. The paper's second expression $F^{\mathrm{st}}_t(\nu)=\mathbb E_{\psi,\phi\sim\nu}|\langle\psi|\phi\rangle|^{2t}$ is a consequence, not part of the definition.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Definition 3.11 eq. (6), p.17; Definition 3.12, p.17; Definition 3.13 eq. (8), p.18; Schatten norms, p.14; D_Sym, p.19; eq. (30), p.23

import Mathlib
import Definitions.Def_DesignTest_haarState
import Definitions.Def_DistQuantumQuery_traceNorm

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- `(|ψ⟩⟨ψ|)^{⊗t}` as a matrix on `(ℂ^d)^{⊗t}` (STOC 2027 submission (sha256 e2f0a429…), (6), p.17).

**Formalization Note.** `(ℂ^d)^{⊗t}` is indexed by words `x : Fin t → Fin d`; the entry at `(x, y)` is
`∏_k ψ(x_k) · conj(ψ(y_k))`. -/
noncomputable def tensorPow {d : ℕ} (ψ : PureVec d) (t : ℕ) :
    Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ :=
  Matrix.of fun x y =>
    ∏ k, (ψ : EuclideanSpace ℂ (Fin d)) (x k) * star ((ψ : EuclideanSpace ℂ (Fin d)) (y k))

/-- **The `t`-th moment operator** `M_t(ν) := E_{|ψ⟩∼ν}[|ψ⟩⟨ψ|^{⊗t}]` (STOC 2027 submission
(sha256 e2f0a429…), Definition 3.11, eq. (6), p.17).

**Formalization Note.** The expectation is taken entrywise (Bochner integral of each entry). Every entry is
a continuous function of `ψ` bounded by `1`, so it is integrable against every probability measure. -/
noncomputable def moment {d : ℕ} (ν : Measure (PureVec d)) (t : ℕ) :
    Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ :=
  Matrix.of fun x y => ∫ ψ, tensorPow ψ t x y ∂ν

/-- **Hilbert–Schmidt norm** `‖A‖₂ = (Tr A†A)^{1/2} = (Σ_{i,j} |A_{ij}|²)^{1/2}` (STOC 2027 submission
(sha256 e2f0a429…), p.14). -/
noncomputable def hsNorm {n : Type} [Fintype n] (A : Matrix n n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

/-- `D_Sym := C(d + t − 1, t)`, the dimension of the symmetric subspace of `(ℂ^d)^{⊗t}` (STOC 2027
submission (sha256 e2f0a429…), p.19, below (12)). Natural-number subtraction is harmless for `d ≥ 1`. -/
def DSym (d t : ℕ) : ℕ := Nat.choose (d + t - 1) t

/-- **The `t`-th moment trace distance** `Dist₁^{(t)}(μ, ν) := ½‖M_t(μ) − M_t(ν)‖₁` (STOC 2027 submission
(sha256 e2f0a429…), eq. (30), p.23). An input `ν` is an exact state `t`-design iff
`momentDist t (haarState d) ν = 0` (Definition 3.12, p.17), and by (31) `momentDist t (haarState d) ν` is
its distance to the set of exact designs.

**Formalization Note.** `‖·‖₁` is the published `DistQuantumQuery.traceNorm`, the sum of the singular
values `Σ_i √λ_i(A†A)` (no Hermitian hypothesis needed); for the Hermitian difference of two moment
operators it equals `Σ_i |λ_i|`. -/
noncomputable def momentDist {d : ℕ} (t : ℕ) (μ ν : Measure (PureVec d)) : ℝ :=
  DistQuantumQuery.traceNorm (moment μ t - moment ν t) / 2

/-- **The `t`-th state frame potential** `F^st_t(ν) := Tr[M_t(ν)²]` (STOC 2027 submission
(sha256 e2f0a429…), Definition 3.13, eq. (8), p.18).

**Formalization Note.** The real part of the trace is taken; `M_t(ν)` is Hermitian, so `Tr[M_t(ν)²]` is
real. The paper's second expression `E_{ψ,ϕ∼ν}|⟨ψ|ϕ⟩|^{2t}` is an identity, not part of this definition. -/
noncomputable def framePotential {d : ℕ} (ν : Measure (PureVec d)) (t : ℕ) : ℝ :=
  (Matrix.trace (moment ν t * moment ν t)).re

end DesignTest



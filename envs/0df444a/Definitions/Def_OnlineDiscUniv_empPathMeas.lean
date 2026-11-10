-- Prove2me | Definitions.Def_OnlineDiscUniv_empPathMeas
-- name    : OnlineDiscUniv_empPathMeas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:09.073183+00:00
-- url     : https://prove2.me/theorems/a54617b2-3672-455e-9622-fa33ca0ca507
-- title:
--   Doob decomposition paths $(A_{N,i},B_{N,i})$ and the random empirical measure $\widehat\nu_N$
-- statement:
--   Fix an online algorithm with seed $U$ and let $X_k=N^{-1/2}\sum_{j\le k}\varepsilon_j\xi_j$. With respect to the filtration $\big(\sigma(U,\xi_1,\dots,\xi_k)\big)_{k=0}^N$ write the Doob decomposition of each coordinate,
--   $$
--   X_{k,i}=A_{N,i}(k/N)+B_{N,i}(k/N),\qquad 0\le k\le N,\qquad(5.1)
--   $$
--   with $A_{N,i}(k/N)=\sum_{j<k}\mathbb E[X_{j+1,i}-X_{j,i}\mid\sigma(U,\xi_1,\dots,\xi_j)]$ the predictable drift and $B_{N,i}$ the centered martingale part, both linearly interpolated between mesh points. The **random empirical measure** is
--   $$
--   \widehat\nu_N:=\frac1M\sum_{i=1}^M\delta_{(A_{N,i},B_{N,i})}\in\mathcal P(\mathcal C^2).
--   $$
--
--   **Formalization Note** The conditional expectations are taken under the joint law of seed and input. The pair $(A_{N,i},B_{N,i})$ is one path in $C([0,1],\mathbb R^2)$.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §5.1, (5.1), pp.23–24 (PDF pp.24–25)

import Mathlib
import Definitions.Def_OnlineDiscUniv_optDisc
import Definitions.Def_OnlineDiscUniv_empMeas

set_option autoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory
open scoped ENNReal

namespace OnlineDiscUniv

variable {S : Type*} [MeasurableSpace S] {M N : ℕ}

/-- The information `σ(U, ξ_1, …, ξ_k)` available after `k` columns (Jo–Lee, arXiv:2610.00103,
artifact sha256 cb190f12…, §5.1, printed p.23, PDF p.24), as a σ-algebra on the joint space
`S × (Fin N → Fin M → ℝ)` of seed and input.

**Formalization Note** Columns are 0-based, so `ξ_1, …, ξ_k` are the columns `j` with `j < k`. -/
def infoAlg (S : Type*) [MeasurableSpace S] (M N : ℕ) (k : ℕ) :
    MeasurableSpace (S × (Fin N → Fin M → ℝ)) :=
  MeasurableSpace.comap Prod.fst inferInstance ⊔
    ⨆ (j : Fin N) (_ : (j : ℕ) < k), MeasurableSpace.comap (fun p => p.2 j) inferInstance

/-- The increment `X_{k+1,i} − X_{k,i} = N^{-1/2} ε_{k+1} ξ_{k+1,i}` of coordinate `i` of the
normalized state (Jo–Lee, arXiv:2610.00103, (2.1), p.5, PDF p.6), written for the 0-based column
`j`. -/
noncomputable def stateIncr (A : OnlineAlg S M N) (j : Fin N) (i : Fin M)
    (p : S × (Fin N → Fin M → ℝ)) : ℝ :=
  (1 / Real.sqrt N) * A.sign j p * p.2 j i

/-- The predictable drift `A_{N,i}(k/N) = ∑_{j<k} E[X_{j+1,i} − X_{j,i} | σ(U, ξ_1, …, ξ_j)]` of the
Doob decomposition (5.1) (Jo–Lee, arXiv:2610.00103, §5.1, p.23, PDF p.24), at mesh point `k`,
under the joint law `ρ ⊗ inputLaw μ M N`.

**Formalization Note** The conditional expectations are Mathlib's `condExp` (each information
σ-algebra is a sub-σ-algebra of the product σ-algebra, and the joint law is a probability measure
when `ρ` and `μ` are, so no junk branch of `condExp` is taken). -/
noncomputable def doobDrift (μ : Measure ℝ) (ρ : Measure S) (A : OnlineAlg S M N) (k : ℕ)
    (i : Fin M) : S × (Fin N → Fin M → ℝ) → ℝ :=
  ∑ j : Fin N, if (j : ℕ) < k then
    (ρ.prod (inputLaw μ M N))[stateIncr A j i | infoAlg S M N j] else 0

/-- The centered martingale part `B_{N,i}(k/N) = X_{k,i} − A_{N,i}(k/N)` of the Doob
decomposition (5.1) (Jo–Lee, arXiv:2610.00103, §5.1, p.23, PDF p.24), at mesh point `k`. -/
noncomputable def doobMart (μ : Measure ℝ) (ρ : Measure S) (A : OnlineAlg S M N) (k : ℕ)
    (i : Fin M) (p : S × (Fin N → Fin M → ℝ)) : ℝ :=
  (∑ j : Fin N, if (j : ℕ) < k then stateIncr A j i p else 0) - doobDrift μ ρ A k i p

/-- The random empirical measure `ν̂_N := (1/M) ∑_{i=1}^{M} δ_{(A_{N,i}, B_{N,i})}` on `C²`
(Jo–Lee, arXiv:2610.00103, §5.1, pp.23–24, PDF pp.24–25), as a function of the seed and the
input: the paths `A_{N,i}`, `B_{N,i}` of the Doob decomposition (5.1), linearly interpolated
between the mesh points `k/N`.

**Formalization Note** The pair `(A_{N,i}, B_{N,i})` is one path in `C([0,1], ℝ²)`
(see `pathMeasurableSpace`). -/
noncomputable def empPathMeas (μ : Measure ℝ) (ρ : Measure S) (A : OnlineAlg S M N)
    (p : S × (Fin N → Fin M → ℝ)) : ProbabilityMeasure C(unitInterval, ℝ × ℝ) :=
  empMeas fun i : Fin M => hatPath N fun k => (doobDrift μ ρ A k i p, doobMart μ ρ A k i p)

end OnlineDiscUniv



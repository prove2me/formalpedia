-- Prove2me | Definitions.Def_DesignTest_NACTester
-- name    : DesignTest_NACTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:14.522314+00:00
-- url     : https://prove2.me/theorems/7ab8c11c-e6db-4877-8dcb-b11e480caf6b
-- title:
--   Non-adaptive coherent tester with $m$ samples and $q$ queries per sample, and its acceptance probability
-- statement:
--   In the **state-preparation access model** a tester draws $m$ independent samples $\psi_1,\dots,\psi_m\sim\nu$; each query to sample $i$ produces one more copy of $|\psi_i\rangle\langle\psi_i|$. With $q$ queries to every sample the tester holds
--   $$\rho_\psi=\bigotimes_{i=1}^{m}\big(|\psi_i\rangle\langle\psi_i|\big)^{\otimes q}.$$
--   A **non-adaptive coherent tester** fixes this allocation in advance and performs an arbitrary joint two-outcome POVM $\{E,\,I-E\}$ on $\rho_\psi$, with $0\le E\le I$; $E$ is the accepting effect. Its **acceptance probability** on the input $\nu$ is
--   $$\Pr[\text{accept}]=\mathbb E_{\psi\sim\nu^{\otimes m}}\,\mathrm{Tr}\big[E\,\rho_\psi\big].$$
--
--   This is the class of testers in the upper bound (Theorem 4.11).
--
--   **Formalization Note** The $mq$ copies are indexed by $(i,k)\in[m]\times[q]$ and a basis word is `Fin m → Fin q → Fin d`. $0\le E\le I$ is written as positive semidefiniteness of $E$ and $I-E$. Ancillas, initial classical randomness (a mixture of POVMs is a POVM) and classical post-processing are absorbed into $E$; an effect that acts trivially on some copies represents a tester using fewer queries.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.3, 3.5 and 3.6, p.15; §3.2.4, pp.16–17

import Mathlib
import Definitions.Def_DesignTest_haarState

set_option autoImplicit false

namespace DesignTest

open MeasureTheory
open scoped ComplexOrder

/-- The supplied state `⊗_{i=1}^{m} (|ψ_i⟩⟨ψ_i|)^{⊗q}` for a uniform allocation of `q` queries to each of
the `m` sampled preparation processes (STOC 2027 submission (sha256 e2f0a429…), Definition 3.5, p.15).

**Formalization Note.** The `m·q` copies are indexed by `(i, k) : Fin m × Fin q`; a basis word is
`x : Fin m → Fin q → Fin d`, and the entry at `(x, y)` is `∏_{i,k} ψ_i(x_{ik}) · conj(ψ_i(y_{ik}))`. -/
noncomputable def copies {d m : ℕ} (q : ℕ) (ψ : Fin m → PureVec d) :
    Matrix (Fin m → Fin q → Fin d) (Fin m → Fin q → Fin d) ℂ :=
  Matrix.of fun x y => ∏ i, ∏ k,
    ((ψ i : PureVec d) : EuclideanSpace ℂ (Fin d)) (x i k) *
      star (((ψ i : PureVec d) : EuclideanSpace ℂ (Fin d)) (y i k))

/-- **A non-adaptive coherent tester** in the state-preparation access model with `m` samples and `q`
queries per sample (STOC 2027 submission (sha256 e2f0a429…), Definitions 3.3 and 3.6, pp.15; §3.2.4,
p.17): it fixes its query allocation in advance and performs an arbitrary joint two-outcome POVM
`{E, 1 − E}` on the supplied copies; `E` is the "accept" effect.

**Formalization Note.** A POVM effect is a matrix with `0 ≤ E ≤ 1`. Ancillas, initial classical
randomness (a mixture of POVMs is a POVM), and classical post-processing are absorbed into `E`. Using
fewer than `q` copies of some sample is the special case of an effect that acts trivially on the unused
copies, so a uniform allocation of `q` copies per sample covers every allocation with at most `q` queries
per sample. -/
structure NACTester (d m q : ℕ) where
  /-- the accepting POVM effect -/
  E : Matrix (Fin m → Fin q → Fin d) (Fin m → Fin q → Fin d) ℂ
  /-- `0 ≤ E` -/
  psd : E.PosSemidef
  /-- `E ≤ 1` -/
  le_one : (1 - E).PosSemidef

/-- The acceptance probability of a non-adaptive coherent tester on the input `ν`:
`E_{ψ ∼ ν^{⊗m}} Tr[E · ⊗_i (|ψ_i⟩⟨ψ_i|)^{⊗q}]`, the samples `ψ_1, …, ψ_m` being independent draws from
`ν` (STOC 2027 submission (sha256 e2f0a429…), Definition 3.5, p.15; §3.2.4, p.16). The real part is
taken; the trace is real and in `[0, 1]` for an effect and a state. -/
noncomputable def NACTester.acceptProb {d m q : ℕ} (T : NACTester d m q)
    (ν : Measure (PureVec d)) : ℝ :=
  ∫ ψ, (Matrix.trace (T.E * copies q ψ)).re ∂(Measure.pi fun _ : Fin m => ν)

end DesignTest



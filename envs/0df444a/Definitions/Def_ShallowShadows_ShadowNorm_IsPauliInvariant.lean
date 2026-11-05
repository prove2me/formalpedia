-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_IsPauliInvariant
-- name    : ShallowShadows_ShadowNorm_IsPauliInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:56.472036+00:00
-- url     : https://prove2.me/theorems/7c419338-5771-4303-b830-c89f85f94112
-- title:
--   Pauli invariant ensemble: $\mu(PU) = \mu(UP) = \mu(U)$
-- statement:
--   A finite ensemble $\mathcal U$ of unitaries is **Pauli invariant** when multiplying the random unitary by a Pauli string on either side does not change its law: for every Pauli string $P$, the conjugation maps $X \mapsto (PU)X(PU)^\dagger$ and $X\mapsto (UP)X(UP)^\dagger$, with $U \sim\mathcal U$, have the same distribution as $X \mapsto UXU^\dagger$. Equivalently, for every function $F$ of the conjugation map,
--
--   $$
--   \sum_i w_i F\big(\mathrm{conj}_{PU_i}\big) = \sum_i w_i F\big(\mathrm{conj}_{U_i}\big) = \sum_i w_i F\big(\mathrm{conj}_{U_iP}\big).
--   $$
--
--   **Formalization Note** The paper writes $\mu_d(PU) = \mu_d(UP) = \mu_d(U)$ for a measure on Cliffords modulo phase; comparing laws of conjugation maps is that statement and does not depend on representatives.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Appendix A, p. 10 (unnumbered)

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_pauli

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Appendix A, p. 10
(unnumbered): an ensemble is Pauli invariant "in the sense that for any Pauli `S ∈ 𝒫_n`, and any
Clifford `U ∈ 𝕌_d`, we have `μ_d(PU) = μ_d(UP) = μ_d(U)`".

Here: for every Pauli string `P = P^λ`, the law of the conjugation map `X ↦ (PU) X (PU)†`, and
the law of `X ↦ (UP) X (UP)†`, under `U ∼ 𝒰`, equal the law of `X ↦ U X U†`; that is, for every
function `F` of the conjugation map, `Σ_i w_i F(conj(P U_i)) = Σ_i w_i F(conj(U_i)) =
Σ_i w_i F(conj(U_i P))`.

**Formalization Note.** The paper's ensembles are uniform over Cliffords modulo global phase, so
the weight of a unitary is the weight of its conjugation action; the statement compares laws of
conjugation maps, which do not depend on representatives. The display writes "for any Pauli
`S`" and then uses `P`; `S = P` is read. -/
def IsPauliInvariant {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) : Prop :=
  ∀ (lam : Bits n × Bits n) (F : (Op n → Op n) → ℂ),
    (∑ i, (E.w.prob i : ℂ) * F (fun X => (pauli lam * E.mat i) * X * star (pauli lam * E.mat i)) =
        ∑ i, (E.w.prob i : ℂ) * F (fun X => E.mat i * X * star (E.mat i))) ∧
      (∑ i, (E.w.prob i : ℂ) * F (fun X => (E.mat i * pauli lam) * X * star (E.mat i * pauli lam)) =
        ∑ i, (E.w.prob i : ℂ) * F (fun X => E.mat i * X * star (E.mat i)))

end ShallowShadows.ShadowNorm



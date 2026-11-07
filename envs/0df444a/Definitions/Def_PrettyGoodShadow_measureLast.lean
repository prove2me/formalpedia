-- Prove2me | Definitions.Def_PrettyGoodShadow_measureLast
-- name    : PrettyGoodShadow_measureLast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:22:31.404441+00:00
-- url     : https://prove2.me/theorems/dfa0acc9-a9f8-4f48-a8b8-03677f69b835
-- title:
--   The map measuring the last $k$ copies with $\{A,I-A\}$
-- statement:
--   Given $s+k$ copies, this map $\mathcal R$ measures the last $k$ with the POVM $\{A,I-A\}$ and keeps the outcomes in a classical register:
--
--   $$
--   \mathcal R(X)=\sum_{z\in\{0,1\}^k}\operatorname{Tr}_{\text{last }k}\big[(I\otimes E_z)X\big]\otimes|z\rangle\langle z|,\qquad E_z=\bigotimes_j E_{z_j},\quad E_1=A,\ E_0=I-A.
--   $$
--
--   On $\rho^{\otimes(s+k)}$ the result is $\rho^{\otimes s}\otimes B^{\otimes k}$ with $B$ the Bernoulli state of $\operatorname{tr}(A\rho)$, as in Remark 4.5.
--
--   **Formalization Note** The space of $s+k$ copies is indexed by $\mathrm{Fin}(s+k)\to d$, and the two blocks of coordinates are glued by `Fin.append`.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Remark 4.5, p.20; proof of Lemma 4.10, p.26

import Mathlib

namespace PrettyGoodShadow

/-- **The map `R`** that measures the last `k` of `s + k` copies with the POVM `{A, I − A}` (arXiv:2610.06781,
sha256 bd055b7d…, Remark 4.5, p.20, and proof of Lemma 4.10, p.26), with the outcomes kept in a classical
register `z : Fin k → Fin 2`:
`R(X) = Σ_z Tr_{last k}[(I ⊗ E_z) X] ⊗ |z⟩⟨z|`, where `E_z = ⨂_j E_{z_j}`, `E_1 = A` and `E_0 = I − A`.

**Formalization Note** The space of `s + k` copies is indexed by `Fin (s + k) → d`, and `Fin.append a c` glues
the first `s` and the last `k` coordinates. Outcome `1` has probability `tr(A ρ)`, which matches the diagonal
state `bern` of Definition 4.4. -/
noncomputable def measureLast {d : Type} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) (s k : ℕ)
    (X : Matrix (Fin (s + k) → d) (Fin (s + k) → d) ℂ) :
    Matrix ((Fin s → d) × (Fin k → Fin 2)) ((Fin s → d) × (Fin k → Fin 2)) ℂ :=
  fun u v =>
    if u.2 = v.2 then
      ∑ c : Fin k → d, ∑ c' : Fin k → d,
        (∏ j, (if u.2 j = 1 then A else 1 - A) (c j) (c' j)) *
          X (Fin.append u.1 c') (Fin.append v.1 c)
    else 0

end PrettyGoodShadow



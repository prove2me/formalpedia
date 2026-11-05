-- Prove2me | Definitions.Def_Chi2QEC_lossError
-- name    : Chi2QEC_lossError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:26.393698+00:00
-- url     : https://prove2.me/theorems/12e43761-b309-47d4-bf1c-f73768919c7c
-- title:
--   The $1+3n$ single-photon-loss errors
-- statement:
--   For $n$ physical qudits the single-photon-loss errors are the identity $\hat I$ (no error) together with the $3n$ annihilation operators $\hat a_{\ell,k}$, one for a photon lost from each of the signal, idler and pump modes of each qudit.
--
--   To lowest order in the loss probability $\gamma$, the paper's Kraus operators are $\hat E_0\approx\hat I-\sum_\ell\gamma\hat a^\dagger_{k_\ell}\hat a_{k_\ell}/2$ and $\hat E_\ell\approx\sqrt\gamma\,\hat a_{k_\ell}$. This family is what Theorem 5 counts when it writes $1+3n$.
--
--   **Formalization Note** The family is indexed by `Option (Fin n × Fin 3)`: `none` is the identity and `some (ℓ, k)` is $\hat a_{\ell,k}$. The nonzero scalar $\sqrt\gamma$ is dropped, which does not change the error-correction condition (23).
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, (20)–(21), p.7; Sec. V B, p.16; (112), p.17

import Mathlib
import Definitions.Def_Chi2QEC_annihilation

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, (20)–(21), p.7, and Sec. V B, p.16 ("There are three possible
single-photon-loss errors for each qutrit: a single photon may be lost from either the signal,
idler, or pump modes"): the `1 + 3n` error operators of Theorem 5, the identity (no error, index
`none`) and the annihilation operator `â_{ℓ,k}` of each of the `3n` modes (index `some (ℓ, k)`).

**Formalization Note.** (20)–(21) give, to lowest order in `γ`, `Ê_0 ≈ Î - Σ γ â†â/2` and
`Ê_ℓ ≈ √γ â_{k_ℓ}`. This family is that lowest order: the identity and the `â_{ℓ,k}`, with the
nonzero scalar `√γ` dropped, which does not change condition (23) (`SatisfiesKL`). -/
noncomputable def lossError (n q : ℕ) : Option (Fin n × Fin 3) → Matrix (FockIdx n q) (FockIdx n q) ℂ
  | none => 1
  | some (ℓ, k) => annihilation n q ℓ k

end Chi2QEC



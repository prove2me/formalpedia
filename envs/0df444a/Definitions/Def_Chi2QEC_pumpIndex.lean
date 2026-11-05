-- Prove2me | Definitions.Def_Chi2QEC_pumpIndex
-- name    : Chi2QEC_pumpIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:35.125955+00:00
-- url     : https://prove2.me/theorems/d1efd396-deef-452e-b793-de98ae3a8e47
-- title:
--   Fock indices of the product states of $\mathcal H_{q-1}^{\otimes n}$
-- statement:
--   This is the set of Fock-basis indices in which every qudit $\ell$ is in a state of the form $|j_\ell,j_\ell,q-1-j_\ell\rangle$ with $0\le j_\ell\le q-1$: the signal and idler photon numbers are equal, and the signal and pump photon numbers add up to $q-1$.
--
--   These indices label the basis of the space $\mathcal H_{q-1}^{\otimes n}$ in which the $\chi^{(2)}$ codes lie.
--
--   **Formalization Note** Modes are numbered signal, idler, pump $=0,1,2$. The natural-number subtraction $q-1$ is exact whenever a qudit exists, because a photon number in `Fin q` forces $q\ge1$.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Sec. III A, p.5; proof of Theorem 5, p.17

import Mathlib
import Definitions.Def_Chi2QEC_FockIdx

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. III A, p.5, and proof of Theorem 5, p.17
(`H_{q-1} = Span{|j, j, q - 1 - j⟩ : 0 ≤ j ≤ q - 1}`): the Fock indices in which every qudit `ℓ`
is in a state `|j_ℓ, j_ℓ, q - 1 - j_ℓ⟩`, i.e. has as many signal as idler photons, and signal plus
pump photon number `q - 1`.

**Formalization Note.** Modes are signal, idler, pump = `0, 1, 2`. The truncated subtraction
`q - 1` is exact whenever a qudit exists: `x ℓ 0 : Fin q` forces `q ≥ 1`. -/
def pumpIndex (n q : ℕ) : Set (FockIdx n q) :=
  {x | ∀ ℓ, x ℓ 0 = x ℓ 1 ∧ (x ℓ 0 : ℕ) + (x ℓ 2 : ℕ) = q - 1}

end Chi2QEC



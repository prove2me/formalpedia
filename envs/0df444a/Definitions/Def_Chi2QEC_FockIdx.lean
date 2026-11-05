-- Prove2me | Definitions.Def_Chi2QEC_FockIdx
-- name    : Chi2QEC_FockIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:47.337143+00:00
-- url     : https://prove2.me/theorems/63f4ea7a-1a02-473c-bd86-a8021e4e7d12
-- title:
--   Fock-basis index of $n$ physical qudits of dimension $q$
-- statement:
--   A physical qudit of the $\chi^{(2)}$ codes consists of three bosonic modes: signal $s$, idler $i$ and pump $p$. Its Fock states are $|n_s,n_i,n_p\rangle$, where $n_s$, $n_i$, $n_p$ are the photon numbers of the three modes.
--
--   For $n$ physical qudits of dimension $q$, a Fock-basis index assigns to each qudit $\ell\in\{1,\dots,n\}$ and each mode $k\in\{s,i,p\}$ a photon number in $\{0,\dots,q-1\}$.
--
--   This index set carries the Hilbert space on which the code, its errors and its corrupted subspace live.
--
--   **Formalization Note** The type is `Fin n → Fin 3 → Fin q`, with modes signal, idler, pump numbered $0,1,2$. The truncation at $q-1$ photons per mode is the smallest one containing $\mathcal H_{q-1}$. Annihilation never raises a photon number, so the truncation changes no vector, inner product or dimension that occurs in the mission's statements.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Sec. III A, p.5; proof of Theorem 5, p.17

import Mathlib

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. III A, p.5 ("|n_s, n_i, n_p⟩ denoting a Fock state having n_s photons in
the signal mode, n_i photons in the idler mode, and n_p photons in the pump mode"), and proof of
Theorem 5, p.17. The Fock-basis index of `n` physical qudits of dimension `q`: `x ℓ k` is the
photon number of mode `k` of qudit `ℓ`.

**Formalization Note.** Modes are ordered signal, idler, pump, i.e. `k = 0, 1, 2`. Photon numbers
are truncated at `q - 1`, the largest number occurring in `H_{q-1}`. Annihilation never raises a
photon number, so this truncation keeps every vector of `H_{q-1}^{⊗n}` and all its single-loss
images, and every inner product between them. For `q = 0` and `n ≥ 1` the type is empty. -/
abbrev FockIdx (n q : ℕ) := Fin n → Fin 3 → Fin q

end Chi2QEC



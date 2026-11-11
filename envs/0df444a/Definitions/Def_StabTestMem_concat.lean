-- Prove2me | Definitions.Def_StabTestMem_concat
-- name    : StabTestMem_concat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:28.282003+00:00
-- url     : https://prove2.me/theorems/31092069-9509-4381-bb9a-b93cd50bc443
-- title:
--   Completed label $(a_Xr,\,a_Zt)$ on $k+m$ qubits
-- statement:
--   Split $n=k+m$ qubits into a prefix (the first $k$ qubits) and a suffix (the last $m$). For a prefix label $a=(a_X,a_Z)\in\mathbb F_2^{2k}$ and $r,t\in\mathbb F_2^m$, the completed label
--
--   $$(a_Xr,\;a_Zt)\in\mathbb F_2^{2(k+m)}$$
--
--   has X-part $a_X$ followed by $r$ and Z-part $a_Z$ followed by $t$. A partial Bell sample returns the pair $(a,r)$; the completions $t$ range over all Z-parts on the suffix.
--
--   **Formalization Note** The prefix occupies wires $0,\dots,k-1$ and the suffix wires $k,\dots,k+m-1$ (`Fin.append`); the paper's $m=n-k$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 3.2, p. 17; Eqs. (59)–(60), p. 32

import Definitions.Def_CutRankSched_Pauli

namespace StabTestMem

/-- **The completed label `(a_X r, a_Z t)` of a prefix `(a, r)` and a Z-completion `t`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026),
§3.1, Lemma 3.2, p. 17 (`q_ψ(a_X r, a_Z t)`), and §4.5, Eqs. (59)–(60), p. 32.

For `a = (a_X, a_Z) ∈ F₂^{2k}` and `r, t ∈ F₂^m`, the label on `k + m` qubits whose X-part is
`a_X` followed by `r` and whose Z-part is `a_Z` followed by `t`.

**Formalization Note.** `Fin.append` puts `a_X` (resp. `a_Z`) on wires `0, …, k − 1` (the first
`k` qubits, the paper's prefix) and `r` (resp. `t`) on wires `k, …, k + m − 1` (the last `m`
qubits). The paper's `m = n − k`; here `n = k + m`. -/
def concat {k m : ℕ} (a : CutRankSched.Pauli k) (r t : Fin m → ZMod 2) : CutRankSched.Pauli (k + m) :=
  (Fin.append a.1 r, Fin.append a.2 t)

end StabTestMem



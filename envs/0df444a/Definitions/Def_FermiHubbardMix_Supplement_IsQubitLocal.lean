-- Prove2me | Definitions.Def_FermiHubbardMix_Supplement_IsQubitLocal
-- name    : FermiHubbardMix_Supplement_IsQubitLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:01:34.001479+00:00
-- url     : https://prove2.me/theorems/6c94fa39-9657-462f-8045-a3e99edbf36b
-- title:
--   Local $n$-qubit Hamiltonian $H=V+W$ with arbitrary external field
-- statement:
--   An $n$-qubit Hamiltonian with external field is a decomposition
--   $$
--   H=V+W,\qquad V=\sum_{i\in[n]}v_i,\qquad W=\sum_{a}h_a,
--   $$
--   where
--
--   1. each onsite term $v_i$ is Hermitian and supported on qubit $i$ (no bound on its size);
--   2. each interaction term $h_a$ is Hermitian and supported on a set $Z_a$ with $|Z_a|\ge2$;
--   3. terms with the same support are combined, and $\mathrm{supp}(h_a)=Z_a$ exactly when $h_a\ne0$.
--
--   The hyperedges $E_H=\{Z_a\}$, the local interaction strength $\zeta=\max_i\sum_{a:\,i\in Z_a}|Z_a|\,\|h_a\|$, the interaction-truncated Hamiltonians $H^{\mathrm{int}}_\Omega=V+\sum_{Z_a\subseteq\Omega}h_a$ and the bounded $L$-local degree-$D$ condition ($\|h_a\|\le1$, $|Z_a|\le L$, every site in at most $D$ hyperedges, $L\ge2$, $D\ge1$) are those of Definitions 4.1 and 4.4.
--
--   This is the class of Hamiltonians of Theorems 6.4, 7.3, 8.6 and 9.1.
--
--   **Formalization Note** The data is the published generic `FermiHubbardMix.HamData (Fin n) n` (onsite terms `v i`, interaction terms `w Z` indexed by their support; `w Z` with `|Z|<2` is ignored), and $\zeta$, $E_H$, $H^{\mathrm{int}}_\Omega$ and bounded couplings are its published `zeta`, `edges`, `trunc`, `BoundedCouplings`. The predicate here replaces the base mission's fermionic `HamData.IsLocal` by qubit support.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 4.1, p.15; Definition 4.4, p.16; Definition 5.4, p.17

import Mathlib
import Definitions.Def_FermiHubbardMix_Supplement_IsSuppOn
import Definitions.Def_FermiHubbardMix_HamData
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- **Definitions 4.1 and 5.4 (Local `n`-qubit Hamiltonian with arbitrary external field)**
(Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version,
sha256 055b8f8f…), p.15 and p.17): `H = V + W` with `V = ∑_i v_i`, each `v_i` Hermitian and supported on
qubit `i`, and `W = ∑_a h_a`, each `h_a` Hermitian with support `Z_a`, `|Z_a| ≥ 2`, terms with the same
support combined. The data is the published generic `FermiHubbardMix.HamData (Fin n) n`
(`v i = v_i`, `w Z = h_a` for `Z = Z_a`, `w Z = 0` for every other `Z` with `|Z| ≥ 2`; `w Z` with
`|Z| < 2` is ignored by every construction): (1) `v_i` is supported on `{i}` and Hermitian; (2) `w_Z` is
supported on `Z` and Hermitian; (3) `supp(w_Z) = Z` whenever `w_Z ≠ 0`.

**Formalization Note** No bound is imposed on the `v_i` (the external field is arbitrary). Since terms
with equal support are combined, the hyperedges `E_H = {Z : |Z| ≥ 2, w_Z ≠ 0}` (published
`HamData.edges`) are the distinct supports `Z_a`, and `ζ`, the truncations `H^int_Ω` and bounded
couplings are the published `HamData.zeta`, `HamData.trunc`, `HamData.BoundedCouplings`. The base
mission's `HamData.IsLocal` is the fermionic version and is not used for qubits. -/
def IsQubitLocal {n : ℕ} (H : HamData (Fin n) n) : Prop :=
  (∀ i, IsSuppOn (H.v i) {i} ∧ (H.v i).IsHermitian) ∧
  (∀ Z : Finset (Fin n), 2 ≤ Z.card → IsSuppOn (H.w Z) (Z : Set (Fin n)) ∧ (H.w Z).IsHermitian) ∧
  (∀ Z : Finset (Fin n), 2 ≤ Z.card → H.w Z ≠ 0 →
    ∀ S : Set (Fin n), IsSuppOn (H.w Z) S → (Z : Set (Fin n)) ⊆ S)

end FermiHubbardMix.Supplement



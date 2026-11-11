-- Prove2me | Definitions.Def_StabTestMem_goodPrefixes
-- name    : StabTestMem_goodPrefixes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:22.043711+00:00
-- url     : https://prove2.me/theorems/52ec941c-0ca9-4e7e-8f32-c43b8ceb95c0
-- title:
--   Prefix subspace $H_M$ ($M$-good prefixes)
-- statement:
--   For a set $M$ of labels on $k+m$ qubits, a prefix $(a,r)\in\mathbb F_2^{2k}\times\mathbb F_2^m$ is **$M$-good** if some completion lies in $M$, and **$M$-bad** otherwise:
--
--   $$H_M=\{(a,r)\;:\;\exists t\in\mathbb F_2^m,\ (a_Xr,\,a_Zt)\in M\}.$$
--
--   For a Lagrangian $M$ this is a subspace, the prefix subspace of $M$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Definition 4.7 and Eq. (60), p. 32

import Definitions.Def_StabTestMem_concat

namespace StabTestMem

/-- **The prefix subspace `H_M` (the `M`-good prefixes).** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Definition 4.7 and Eq. (60),
p. 32: "We say that a prefix (a, r) ∈ F_2^{2k} × F_2^{n−k} is M-good if there exists
t ∈ F_2^{n−k} such that (a_X r, a_Z t) ∈ M. Otherwise, (a, r) is M-bad." and
"H_M = {(a, r) ∈ F_2^{2k} × F_2^m | ∃t ∈ F_2^m : (a_X r, a_Z t) ∈ M}".

Defined for any set `M` of labels on `k + m` qubits (Definition 4.7 allows any subset). -/
def goodPrefixes {k m : ℕ} (M : Set (CutRankSched.Pauli (k + m))) : Set (CutRankSched.Pauli k × (Fin m → ZMod 2)) :=
  {p | ∃ t : Fin m → ZMod 2, concat p.1 p.2 t ∈ M}

end StabTestMem



-- Prove2me | Definitions.Def_PPSLattice_dmax
-- name    : PPSLattice_dmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:00.355081+00:00
-- url     : https://prove2.me/theorems/304e7dbe-7eaa-4c70-abdf-727d0f6cee7c
-- title:
--   Largest depth $d_f$ of the circuits $f_S$, $S\subseteq[N]$
-- statement:
--   $d_{\max}(N)=\max_{S\subseteq[N]}\operatorname{depth}(f_S)$, the depth that governs the noise bound $\|\mathbf H_{S,i}\|\le m^{O(d_f)}$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Claim 4.10, p.23; correctness analysis, p.22

import Mathlib
import Definitions.Def_PPSLattice_memCircuit
import Definitions.Def_PPSLattice_circDepth
set_option autoImplicit false

namespace PPSLattice

/-- The **largest depth `d_f`** of the set membership circuits `f_S`, `S ⊆ [N]`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), proof of Claim 4.10, p.23 ("As |S| ≤ N, the bound on d_f holds for every S ⊆ [N]"); correctness
analysis, p.22 ("‖H_{S,i}‖ ≤ m^{O(d_f)} where d_f is the depth of f_S"). -/
def dmax (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).powerset.sup fun S => circDepth (Nat.clog 2 N) (memCircuit N S)

end PPSLattice



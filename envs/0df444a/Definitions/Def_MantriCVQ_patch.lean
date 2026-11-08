-- Prove2me | Definitions.Def_MantriCVQ_patch
-- name    : MantriCVQ_patch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:15.201629+00:00
-- url     : https://prove2.me/theorems/f24f68c4-bb6b-47eb-bc6d-90e7001ac2b2
-- title:
--   An oracle overwritten on a finite set
-- statement:
--   The oracle with the answers $a$ on a finite set $S$ of strings and the answers of $O_0$ elsewhere. Fixing $O_0$ and varying $a$ is the paper's "fix the oracle answers on all strings other than the leaves".
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claims 7.1, 7.2, p. 38 (PDF p. 40)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The oracle with the answers `a` on the finite set `S` of strings and the answers of `O₀` elsewhere
(Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claims 7.1, 7.2, p. 38 (PDF p. 40): "Fix … the
oracle answers on all strings other than the leaves of the instance of size `n`"). -/
def patch (O₀ : Oracle) (S : Finset Str) (a : S → Bool) : Oracle :=
  fun x => if h : x ∈ S then a ⟨x, h⟩ else O₀ x

end MantriCVQ



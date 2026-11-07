-- Prove2me | Definitions.Def_PRUPermLayer_haar
-- name    : PRUPermLayer_haar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:49.25484+00:00
-- url     : https://prove2.me/theorems/033011d3-1e55-4386-ae7b-0b36b1e29c89
-- title:
--   Haar measure on $U(N)$, $N = 2^n$
-- statement:
--   Let $n \ge 0$ and $N = 2^n$. **Haar** denotes the Haar probability measure on the unitary group $U(N)$: the unique probability measure on $U(N)$ invariant under multiplication by fixed unitaries. A **Haar-random unitary** is a sample from it.
--
--   It is the reference ensemble against which every advantage in the paper is measured.
--
--   **Formalization Note** $U(N)$ is the group of unitary $N\times N$ matrices indexed by $\{0,\dots,N-1\}$; label $x$ is identified with the $n$-bit string whose binary value is $x$ (most significant bit first). The measure is the published Haar probability measure on $U(N)$ with its Borel $\sigma$-algebra.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
open MeasureTheory

namespace PRUPermLayer

/-- The Haar probability measure on `U(N)`, `N = 2ⁿ` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11): "We write Haar
for the Haar measure on U(N)").

**Formalization Note** `U(N)` is `Matrix.unitaryGroup (Fin (2 ^ n)) ℂ`, and the measure is the
published `QAlgorithms.Schur.unitaryHaar (2 ^ n)`, normalized to total mass one on the compact
group, with the published Borel σ-algebra. The label `x : Fin (2 ^ n)` is the bit string
`(QAlgorithms.bitsEquivFin n).symm x` (most significant bit on wire 0), which identifies `[N]`
with `{0,1}ⁿ` as on p.8. -/
noncomputable def haar (n : ℕ) : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :=
  QAlgorithms.Schur.unitaryHaar (2 ^ n)

end PRUPermLayer



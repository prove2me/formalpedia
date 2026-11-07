-- Prove2me | Definitions.Def_ShadowBootstrap_suffixEnsemble
-- name    : ShadowBootstrap_suffixEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:49.114068+00:00
-- url     : https://prove2.me/theorems/4cc1c7fe-3579-40ec-a71b-dbbaec450c07
-- title:
--   The suffix ensembles $E_\ell = E_{2L}(km) \otimes \mathrm{Cl}(r)$ of Lemma A.2
-- statement:
--   Fix the number of qubits $n$ and the block size $k := \max\{8, 2\lceil\log_2 n\rceil\}$. For a suffix of $j = n - \ell$ qubits write $j = mk + r$ with $m = \lfloor j/k\rfloor$ and $0 \le r \le k-1$. The **suffix ensemble** (Lemma A.2, p.34) is
--   $$E_\ell := E_{2L}(km) \otimes \mathrm{Cl}(r),$$
--   the two-layer Clifford ensemble with block size $k$ on the first $km$ suffix qubits and a uniformly random $r$-qubit Clifford on the last $r$ qubits.
--
--   At level $\ell$ of the initialization the paper measures with $I_{2^\ell} \otimes U$, $U \sim E_\ell$ (§5.2, p.17); the bootstrapping stages use $E_0$.
--
--   **Formalization Note** The ensemble is indexed by the suffix size $j = n - \ell$. The paper omits factors on zero qubits ($m = 0$ or $r = 0$); here such a factor is a one-label ensemble whose unitary is a global phase, which changes no outcome probability, shadow channel or shadow.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma A.2, p.34; Lemma 5.4, p.17

import Mathlib
import Definitions.Def_ShadowBootstrap_tensorEnsemble
import Definitions.Def_ShadowBootstrap_twoLayer
import Definitions.Def_ShallowShadows_ShadowNorm_globalClifford

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- The block size `k := max{8, 2⌈log₂ n⌉}` of Lemma A.2 (p.34). `Nat.clog 2 n = ⌈log₂ n⌉` for
`n ≥ 1`. -/
def blockSize (n : ℕ) : ℕ := max 8 (2 * Nat.clog 2 n)

/-- The labels of the suffix ensemble on `j` qubits: a two-layer label on the first
`k⌊j/k⌋` qubits and a global Clifford label on the last `j mod k` qubits. -/
abbrev SuffixLabel (n j : ℕ) : Type :=
  ((Fin (j / blockSize n) → CliffordLabel (blockSize n)) ×
    (Fin (j / blockSize n) → CliffordLabel (blockSize n))) × CliffordLabel (j % blockSize n)

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma A.2, p.34 (and Lemma 5.4, p.17): for an `n`-qubit problem and a suffix of `j = n − ℓ`
qubits, write `j = mk + r` with `k = max{8, 2⌈log₂ n⌉}`, `m = ⌊j/k⌋`, `0 ≤ r ≤ k − 1`; the
suffix ensemble is `E_ℓ := E2L(km) ⊗ Cl(r)`, the cyclic two-layer Clifford ensemble with block size
`k` on the first `km` suffix qubits and a uniformly random global Clifford on the last `r`.

**Formalization Note** The ensemble is indexed by the suffix size `j = n − ℓ` rather than by the
level `ℓ`; level `ℓ` uses `suffixEnsemble n (n − ℓ)`, and the refinement stages use
`suffixEnsemble n n` (`ℓ = 0`). The paper omits factors on zero qubits (`m = 0` or `r = 0`). Here
such a factor is the one-label ensemble on `{0,1}⁰` whose unitary is a `1 × 1` unitary, i.e. a
global phase, so the product is the paper's ensemble up to a global phase of each unitary, which
changes no outcome probability, shadow channel or shadow. The register `{0,1}^{km+r}` is
identified with `{0,1}^j` along `km + r = j`. -/
noncomputable def suffixEnsemble (n j : ℕ) [∀ k, Fintype (CliffordLabel k)] :
    Primitive j (SuffixLabel n j) :=
  castQubits (Nat.div_add_mod j (blockSize n))
    (tensorEnsemble (twoLayer (blockSize n) (j / blockSize n))
      (globalClifford (j % blockSize n)))

end ShadowBootstrap



-- Prove2me | Definitions.Def_BBPSSW_Distill_pairsState
-- name    : BBPSSW_Distill_pairsState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:30.489497+00:00
-- url     : https://prove2.me/theorems/49f00c5c-e864-48ea-888d-b81b2f49fd57
-- title:
--   Joint state $\rho_0\otimes\cdots\otimes\rho_{k-1}$ of $k$ shared pairs
-- statement:
--   Given two-spin states $\rho_0,\dots,\rho_{k-1}$, their tensor product is regarded as a bipartite state between Alice, who holds the first spin of every pair, and Bob, who holds the second. With Alice's basis states the bit strings $a\in\{0,1\}^k$ and Bob's $b\in\{0,1\}^k$,
--
--   $$\Big(\bigotimes_j\rho_j\Big)_{(a,b),(a',b')}=\prod_{j}(\rho_j)_{(a_j,b_j),(a'_j,b'_j)},$$
--
--   so Alice's spin $j$ and Bob's spin $j$ form pair $j$. In particular $M^{\otimes n}$ is `pairsState (fun _ => M)`.
--
--   **Formalization Note** Each register $\{0,1\}^k$ is encoded as $\{0,\dots,2^k-1\}$ by `finFunctionFinEquiv`, the form on which the LOCC class acts. For $k=0$ the state is the $1\times1$ matrix $1$.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 1 and pp. 2–3 (n shared pairs, n copies of M)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **The joint state of `k` shared pairs, `ρ₀ ⊗ ρ₁ ⊗ ⋯ ⊗ ρ_{k−1}`, as a bipartite state.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 1 ("Alice and Bob share … pairs"); pp. 2–3 (n impure pairs; n copies of M).

Alice holds spin `j` of every pair `j`, Bob the other spin. A basis state of Alice's `k`
spins is a bit string `Fin k → Fin 2`, encoded as an element of `Fin (2^k)` by
`finFunctionFinEquiv`; likewise for Bob. The entry is
`(a, b), (a', b') ↦ ∏ j, ρ j (a_j, b_j) (a'_j, b'_j)`
where `a_j` is bit `j` of `a`: Alice's spin `j` and Bob's spin `j` form pair `j`.

**Formalization Note.** The bipartite form `Fin (2^k) × Fin (2^k)` (Alice's register first) is
the one on which `FiniteLOCC` acts. For `k = 0` it is the `1 × 1` matrix `1`. -/
noncomputable def pairsState {k : ℕ} (ρ : Fin k → Matrix QQ QQ ℂ) :
    Matrix (Fin (2 ^ k) × Fin (2 ^ k)) (Fin (2 ^ k) × Fin (2 ^ k)) ℂ :=
  Matrix.of fun x y => ∏ j, ρ j
    ((finFunctionFinEquiv.symm x.1) j, (finFunctionFinEquiv.symm x.2) j)
    ((finFunctionFinEquiv.symm y.1) j, (finFunctionFinEquiv.symm y.2) j)

end BBPSSW.Distill



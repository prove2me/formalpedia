-- Prove2me | Definitions.Def_QPSpinProfile_pauliPOVM
-- name    : QPSpinProfile_pauliPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:03.67847+00:00
-- url     : https://prove2.me/theorems/1fe97e90-8dca-4696-8618-b7a4708ad1a2
-- title:
--   The Pauli POVM $E_{a,s}=\tfrac16(I+sa)$
-- statement:
--   For each axis $a\in\{X,Y,Z\}$ and sign $s\in\{+1,-1\}$, let
--   $$
--   E_{a,s}=\tfrac13|a,s\rangle\langle a,s|=\tfrac16(I+s\,a).
--   $$
--   For each axis $E_{a,+1}+E_{a,-1}=\tfrac13I$, and summing over the three axes gives $\sum_{a,s}E_{a,s}=I$: the six operators form a POVM with outcomes $(a,s)$. Its measurement map is $\mathcal M_{\mathrm{Pauli}}(X)=\sum_{a,s}\operatorname{Tr}(E_{a,s}X)\,|a,s\rangle\langle a,s|_{\mathrm{cl}}$ (display (10)), with six orthonormal classical labels.
--
--   **Formalization Note** Outcomes are $k\in\mathrm{Fin}\,6$: $k=0,1$ is axis $X$, $2,3$ is $Y$, $4,5$ is $Z$; even $k$ has $s=+1$, odd $k$ has $s=-1$.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §2.1.2, p.15–16 (PDF p.18–19), display (10)

import Mathlib
import Definitions.Def_QPSpinProfile_PauliString

namespace QPSpinProfile

/-- The Pauli POVM (arXiv:2610.02166, held version sha256 a0a1ec89…, §2.1.2, p.15–16,
PDF p.18–19): the six effects `E_{a,s} := (1/3)|a,s⟩⟨a,s| = (1/6)(I + s a)`, `a ∈ {X, Y, Z}`,
`s ∈ {+1, −1}`.

**Formalization Note** The outcome `(a, s)` is encoded as `k : Fin 6` with axis
`a = pauliMat (k / 2 + 1)` (`k = 0,1 ↦ X`, `2,3 ↦ Y`, `4,5 ↦ Z`) and sign `s = +1` for even `k`,
`s = −1` for odd `k`. The measurement map `M_Pauli` of (10) is `DeFinettiSDP.Hierarchy.measB
pauliPOVM`, whose six classical labels are orthonormal. -/
noncomputable def pauliPOVM (k : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 6 : ℂ) • (1 + (if k.val % 2 = 0 then (1 : ℂ) else -1) •
    pauliMat ⟨k.val / 2 + 1, by omega⟩)

end QPSpinProfile



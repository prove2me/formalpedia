-- Prove2me | Definitions.Def_CEPolytopeHard_gtilde
-- name    : CEPolytopeHard_gtilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:58.504731+00:00
-- url     : https://prove2.me/theorems/528974d3-968f-42f2-afa1-20866f8ae676
-- title:
--   Copy evaluation $\tilde f$ and copy map $\tilde g$
-- statement:
--   With $q = 2p + 1$ copies $z^{(1)}, \dots, z^{(q)}$ of a point of $[0,1]^{dr}$:
--
--   1. coordinate $i$ of the **copy evaluation** is
--   $$
--   \tilde f_i(z^{(1)}, \dots, z^{(2p)}) = \mathbb E\, h_i\Big(\frac1p\sum_{j=1}^p \xi_j,\ \frac1p\sum_{j=p+1}^{2p}\xi_j\Big),
--   $$
--   with independent Bernoulli $\xi_j$ of success probability $z^{(j)}_{a_i}$ for $j \le p$ and $z^{(j)}_{b_i}$ otherwise, a multilinear polynomial in the copies;
--   2. the **copy map** is, layer by layer,
--   $$
--   \tilde g^{(\ell)}(z^{(1)}, \dots, z^{(q)}) = (1 - b^{-\ell}) z^{(q,\ell)} + b^{-\ell}\, \tilde f(z^{(1,\ell)}, \dots, z^{(2p,\ell)}),
--   $$
--   where $z^{(j,\ell)}$ is the $\ell$-th $d$-dimensional block of copy $j$.
--
--   It evaluates the lift $g$ through a multilinear game with copy players (Eq. (14)).
--
--   **Formalization Note** Copies are 0-based; the last copy is the paper's copy $q$. The expectation is the finite sum over outcomes $\xi \in \{0,1\}^{2p}$. Layers are 0-based as in the lift.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), "Evaluating the map with copies", p.22

import Mathlib
import Definitions.Def_CEPolytopeHard_GCircuit
import Definitions.Def_CEPolytopeHard_gateMap
import Definitions.Def_CEPolytopeHard_liftG

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **multilinear copy evaluation `f̃_i`** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, p.22: "f̃_i(z^{(1)}, . . . , z^{(2p)}) =
E h_i((1/p)∑_{j=1}^p ξ_j, (1/p)∑_{j=p+1}^{2p} ξ_j), where the ξ_j are independent, with success
probabilities z^{(j)}_{a_i} for j ≤ p and z^{(j)}_{b_i} otherwise"), written as the finite sum over
outcomes `ξ ∈ {0, 1}^{2p}`.

**Formalization Note** Copies `j = 0, …, 2p − 1` (0-based); copies `j < p` read the first input
`a_i`, the others the second input `b_i` (`0` if the gate has none, ignored by its gate map). -/
noncomputable def ftilde (τ : ℝ) (p : ℕ) (C : GCircuit) (z : Fin (2 * p) → Fin C.d → ℝ)
    (i : Fin C.d) : ℝ :=
  ∑ ξ : Fin (2 * p) → Bool,
    (∏ j : Fin (2 * p),
      (if ξ j then (if j.val < p then C.valO (z j) (C.gates.get i).argA
          else C.valO (z j) (C.gates.get i).argB)
        else 1 - (if j.val < p then C.valO (z j) (C.gates.get i).argA
          else C.valO (z j) (C.gates.get i).argB))) *
    gateMap τ (C.gates.get i)
      (((Finset.univ.filter fun j : Fin (2 * p) => j.val < p ∧ ξ j = true).card : ℝ) / p)
      (((Finset.univ.filter fun j : Fin (2 * p) => p ≤ j.val ∧ ξ j = true).card : ℝ) / p)

/-- The **copy map `g̃`** (p.22: "we use one more copy for the retained coordinate in each layer of
g, for a total of q = 2p + 1 copies. Writing z^{(j,ℓ)} for the ℓth d-dimensional block of copy j,
we define g̃^{(ℓ)}(z^{(1)}, . . . , z^{(q)}) = (1 − b^{−ℓ})z^{(q,ℓ)} + b^{−ℓ}f̃(z^{(1,ℓ)}, . . . , z^{(2p,ℓ)})").

**Formalization Note** Copies are indexed by `Fin (2p + 1)`; the last one (`Fin.last (2p)`) is the
paper's copy `q`. Layers are 0-based with weight `b^{−(ℓ+1)}`, as in `liftG`. -/
noncomputable def gtilde (τ : ℝ) (p : ℕ) (C : GCircuit) (b : ℕ) {r : ℕ}
    (z : Fin (2 * p + 1) → Fin r × Fin C.d → ℝ) : Fin r × Fin C.d → ℝ :=
  fun ℓi => (1 - (b : ℝ) ^ (-((ℓi.1.val : ℤ) + 1))) * z (Fin.last (2 * p)) ℓi +
    (b : ℝ) ^ (-((ℓi.1.val : ℤ) + 1)) *
      ftilde τ p C (fun j => layer (z (Fin.castSucc j)) ℓi.1) ℓi.2

end CEPolytopeHard



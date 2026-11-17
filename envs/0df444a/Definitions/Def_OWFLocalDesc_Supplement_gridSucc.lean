-- Prove2me | Definitions.Def_OWFLocalDesc_Supplement_gridSucc
-- name    : OWFLocalDesc_Supplement_gridSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T16:57:40.059837+00:00
-- url     : https://prove2.me/theorems/1a284c5c-07bc-4c94-a822-45d08451fb07
-- title:
--   The random-threshold grid and exact-recovery success (Theorem A.2)
-- statement:
--   Fix a PAC-style sampler $D$ with concept-seed length $q(n)$, a coding header $\sigma_Q$ of length $c_Q$, a sample-size schedule $m$ and an integer schedule $P$. Put
--   $$c'(n)=\lceil\log(m(n)+1)\rceil+c_Q+3,\qquad L(n)=q(n)+c'(n),$$
--   let $G(n)$ be the least power of two with $G(n)\ge 8P(n)(L(n)+1)$, and for $0\le j<G(n)$ put
--   $$\theta_j=\frac12+\frac{2j+1}{8G(n)} .$$
--
--   The **exact-recovery success** of a PPT algorithm $B$ is
--   $$\Pr_{(x,y)\sim D_n,\ j,\ B}\Big[B(1^n,x,y,j)=\mathrm{pSC}^{t(n)}_{\theta_j}(x,y)\Big],$$
--   where $j$ is uniform on $\{0,\dots,G(n)-1\}$ and independent of the dataset and of the coins of $B$. Equality holds in $\mathbb Z\cup\{\infty\}$, so $\infty$ must be reproduced exactly.
--
--   **Formalization Note** $G(n)=2^{\lceil\log_2 8P(n)(L(n)+1)\rceil}$. The index $j$ is given to $B$ in binary after the dataset code, the dataset mass is the published `OWFLocalDesc.datasetMass`, and the quantile is the published `OWFLocalDesc.pSC` at the original clock $t(n)$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem A.2, p.35

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_PPT
import Definitions.Def_OWFLocalDesc_PACSampler
import Definitions.Def_OWFLocalDesc_pSC
import Definitions.Def_OWFLocalDesc_decodeOut
import Definitions.Def_OWFLocalDesc_InInterval
import Definitions.Def_OWFLocalDesc_intervalSucc
import Definitions.Def_OWFLocalDesc_datasetMass
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

open OWFLocalDesc

/-- The integer price cutoff `L(n) = q(n) + c′(n)`, `c′(n) = ⌈log(m(n)+1)⌉ + c_Q + 3`, with
`c_Q = |σ_Q|` (Theorem A.2, p.35, "as in the proof of Theorem 5.1"). -/
def priceCutoff (D : PACSampler) (m : ℕ → ℕ) (σQ : List Bool) (n : ℕ) : ℕ :=
  D.q n + (Nat.clog 2 (m n + 1) + σQ.length + 3)

/-- `G(n)`: the least power of two with `G(n) ≥ 8P(n)(L(n)+1)` (Theorem A.2, p.35). -/
def gridSize (D : PACSampler) (m : ℕ → ℕ) (σQ : List Bool) (P : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 ^ Nat.clog 2 (8 * P n * (priceCutoff D m σQ n + 1))

/-- The grid threshold `θ_j = 1/2 + (2j+1)/(8G(n))` (Theorem A.2, p.35). -/
noncomputable def gridTheta (D : PACSampler) (m : ℕ → ℕ) (σQ : List Bool) (P : ℕ → ℕ) (n j : ℕ) :
    ℝ :=
  1 / 2 + (2 * (j : ℝ) + 1) / (8 * (gridSize D m σQ P n : ℝ))

/-- The input `(1ⁿ, x, y, j)`: the dataset code followed by the grid index in binary. -/
def gridInput {m n : ℕ} (x : Fin m → Fin n → Bool) (y : Fin m → Bool) (j : ℕ) : List Bool :=
  QuantumPRC.tupleCode [datasetCode x y, Nat.bits j]

/-- **Exact-recovery success at a uniform grid threshold (Theorem A.2).** Myrisiotis, *One-Way
Functions and Local Descriptions of Random Data*, STOC 2027 submission (held manuscript, sha256
d818fa43…4c4e), Theorem A.2, p.35:
"Pr_{(x,y)∼D_n,j,B}[B(1^n,x,y,j) = pSC^t_{θj}(x,y)] … The grid index is uniform on
{0,...,G(n)−1} and independent of the dataset and the algorithm's coins. The decoder inside every
certificate is run for the original t(n) steps."

`gridSucc U D t m σQ P B n` averages, uniformly over `j < G(n)`, over `(x, y) ∼ D_n` (published
`OWFLocalDesc.datasetMass`, `m(n)` points) and over the coins of `B`, the event that the output
of `B` on `(1ⁿ, x, y, j)` is well formed and equals `pSC^{t(n)}_{θ_j}(x,y)` (including `∞`).

**Formalization Note.** Equality is in `ℤ ∪ {∞}` after `OWFLocalDesc.decodeOut`; the quantile is
the published `OWFLocalDesc.pSC` at the original clock `t(n)`. -/
noncomputable def gridSucc (U : Decoder) (D : PACSampler) (t m : ℕ → ℕ) (σQ : List Bool)
    (P : ℕ → ℕ) (B : PPT) (n : ℕ) : ℝ :=
  (∑ j : Fin (gridSize D m σQ P n), ∑ x : Fin (m n) → Fin n → Bool, ∑ y : Fin (m n) → Bool,
      datasetMass D x y *
        B.prob (gridInput x y j) fun out =>
          decodeOut out = some (toWT (pSC U (t n) (gridTheta D m σQ P n j) x y))) /
    (gridSize D m σQ P n : ℝ)

end OWFLocalDesc.Supplement



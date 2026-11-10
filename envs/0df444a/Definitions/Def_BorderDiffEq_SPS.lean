-- Prove2me | Definitions.Def_BorderDiffEq_SPS
-- name    : BorderDiffEq_SPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:14.730115+00:00
-- url     : https://prove2.me/theorems/c0c46b55-6bc5-4676-abc1-b30e927d75bc
-- title:
--   Depth-3 $\Sigma\Pi\Sigma$ circuits, their top fan-in and size
-- statement:
--   A **depth-3 circuit** with top fan-in $t$ over a commutative ring $K$ computes
--   $$
--   \sum_{i=1}^{t}\prod_{j=1}^{d_i}\ell_{ij}(x),
--   $$
--   where the $\ell_{ij}$ are affine linear polynomials over $K$. Its **top fan-in** is $t$, and its **formal degree** is $\max_i d_i$.
--
--   Its **size** is
--   $$
--   \mathrm{size}=\sum_{i=1}^{t}\Big(1+\sum_{j=1}^{d_i}\big(1+|\mathrm{supp}(\ell_{ij})|\big)\Big):
--   $$
--   one for each product gate, and for each factor (counted with multiplicity) one plus the number of variables it uses.
--
--   **Formalization Note** The paper does not define the size of a $\Sigma\Pi\Sigma$ circuit; it uses only that the formal degree, the top fan-in and the number of variables are at most the size (pp.5, 44). The count above is at most the usual number of gates plus wires and bounds all three. Counting factors with multiplicity is essential: a size that counts a repeated factor once does not bound the formal degree, and Kumar's theorem shows that top fan-in 2 with unbounded formal degree approximates every polynomial.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.1, p.5, display (2) and the sentence after it; size convention per the proof of Theorem 2.1, p.44

import Mathlib
import Definitions.Def_BorderDiffEq_AffineForm

namespace BorderDiffEq

/-- **Depth-3 (ΣΠΣ) circuits** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission),
§2.1, p.5, display (2)): a depth-3 circuit with top fan-in `t` computes
`∑_{i=1}^{t} ∏_{j=1}^{dᵢ} ℓᵢⱼ(x)` with affine linear `ℓᵢⱼ` over the commutative ring `K`.

**Formalization Note.** `t` is the number of product gates (the top fan-in), `deg i = dᵢ` the
fan-in of the `i`-th product gate, and `form i j = ℓᵢⱼ`. The paper does not define the size of a
ΣΠΣ circuit; it uses only that the formal degree `maxᵢ dᵢ`, the top fan-in and the number of
variables are at most the size (p.5, p.44). Here
`size = ∑ᵢ (1 + ∑ⱼ (1 + #{l : coefficient of xₗ in ℓᵢⱼ is nonzero}))`: one for each product gate,
and one for each factor **counted with multiplicity** plus one for each variable it uses. This is at
most the usual count of gates and wires, and it bounds `t`, every `dᵢ` and the number of variables
used. -/
structure SPS (K : Type) (σ : Type) where
  /-- the number of product gates (top fan-in) -/
  t : ℕ
  /-- the fan-in of each product gate -/
  deg : Fin t → ℕ
  /-- the affine factors of each product gate -/
  form : (i : Fin t) → Fin (deg i) → AffineForm K σ

namespace SPS

variable {K σ : Type}

/-- The polynomial `∑ᵢ ∏ⱼ ℓᵢⱼ` computed by the circuit. -/
noncomputable def eval [CommRing K] [Fintype σ] (Φ : SPS K σ) : MvPolynomial σ K :=
  ∑ i, ∏ j, (Φ.form i j).toPoly

/-- The top fan-in (number of product gates). -/
def topFanIn (Φ : SPS K σ) : ℕ := Φ.t

/-- The size: every product gate counts `1`, every factor counts `1` plus the number of variables
it uses, factors counted with multiplicity. -/
noncomputable def size [Zero K] [Fintype σ] (Φ : SPS K σ) : ℕ :=
  ∑ i, (1 + ∑ j, (1 + (Φ.form i j).supportCard))

end SPS

end BorderDiffEq



-- Prove2me | Definitions.Def_FourierRankQLB_HasFourierRankCost
-- name    : FourierRankQLB_HasFourierRankCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:43:08.65349+00:00
-- url     : https://prove2.me/theorems/1c84d682-c8a2-44f9-9763-787b30a3bcf3
-- title:
--   Fourier-rank cost of a query family
-- statement:
--   A family of unitaries $\{O_Q:Q\in O(n)\}$ on a Hilbert space $H$ has **Fourier-rank cost at most $s$** if, for every $r\ge0$, both the query and its inverse map
--   $$
--   V_r^{(n)}\mathbin{\widehat\otimes}H\quad\text{into}\quad V_{r+s}^{(n)}\mathbin{\widehat\otimes}H .
--   $$
--   Here a query acts fibrewise: $\Psi$ goes to $Q\mapsto O_Q\Psi(Q)$.
--
--   This single number is all the method needs to know about an oracle.
--
--   **Formalization Note** The definition asks for a class in the target space that agrees almost everywhere with the fibrewise image.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.1, p.17

import Mathlib
import Definitions.Def_FourierRankQLB_VH

open MeasureTheory

namespace FourierRankQLB

/-- A family of query oracles `{O_Q}` on `H` has Fourier-rank cost at most `s`: for every `r`, the
query and its inverse, applied fibrewise in `Q`, map `V_r ⊗̂ H` into `V_{r+s} ⊗̂ H`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.1, "Fourier-rank cost of a query", p. 17.

**Formalization Note.** The image of `Ψ` is the function `Q ↦ O_Q Ψ(Q)`. The definition asks that
its class exists in `V_{r+s} ⊗̂ H`, which includes the measurability of the image. -/
def HasFourierRankCost {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : Od n → (H ≃ₗᵢ[ℂ] H)) (s : ℕ) : Prop :=
  ∀ (r : ℕ), ∀ Ψ ∈ VH n r H,
    (∃ Φ ∈ VH n (r + s) H, Φ =ᵐ[haarO n] fun Q => O Q (Ψ Q)) ∧
    (∃ Φ ∈ VH n (r + s) H, Φ =ᵐ[haarO n] fun Q => (O Q).symm (Ψ Q))

end FourierRankQLB



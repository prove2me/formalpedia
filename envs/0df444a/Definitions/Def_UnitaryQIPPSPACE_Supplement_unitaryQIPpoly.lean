-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Supplement_unitaryQIPpoly
-- name    : UnitaryQIPPSPACE_Supplement_unitaryQIPpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:44:52.018664+00:00
-- url     : https://prove2.me/theorems/8df29e57-c194-43b4-a6a0-b549b621f9ec
-- title:
--   The class $\mathsf{unitaryQIP}^{(\mathrm{poly})}_{c,s,\delta}[\ell]$
-- statement:
--   For $\ell\in\mathbb N$ and $c,s,\delta:\mathbb N\to\mathbb R$,
--   $$\mathsf{unitaryQIP}^{(\mathrm{poly})}_{c,s,\delta}[\ell]=\bigcup_{m}\mathsf{unitaryQIP}^{(m)}_{c,s,\delta}[\ell],$$
--   the union over all copy numbers $m:\mathbb N\to\mathbb N$ that are polynomially bounded ($m(n)\le p(n)$ for a polynomial $p$ and all $n$). The verifier may receive polynomially many copies of the input state.
--
--   **Formalization Note** The copy number is chosen per unitary family.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 1.4 (notation), p.4 (PDF p.6), restated p.38 (PDF p.40)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_Supplement_unitaryQIPm

namespace UnitaryQIPPSPACE

namespace Supplement

/-- **The class `unitaryQIP^{(poly)}_{c,s,δ}[ℓ]`** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, Theorem 1.4, p. 4 (PDF p. 6), restated p. 38
(PDF p. 40)): the union, over all polynomially bounded copy numbers `m : ℕ → ℕ`, of the
multi-copy classes `unitaryQIP^{(m)}_{c,s,δ}[ℓ]` (`unitaryQIPm`).

**Formalization Note** The copy number is chosen per family: `U` is in the class when some
`m` with `m(n) ≤ p(n)` for a polynomial `p ∈ ℕ[X]` and every `n` has `U ∈ unitaryQIPm m ℓ c s δ`. -/
def unitaryQIPpoly (ℓ : ℕ) (c s δ : ℕ → ℝ) : Set UFam :=
  {U | ∃ m : ℕ → ℕ, (∃ p : Polynomial ℕ, ∀ n, m n ≤ p.eval n) ∧ U ∈ unitaryQIPm m ℓ c s δ}

end Supplement

end UnitaryQIPPSPACE



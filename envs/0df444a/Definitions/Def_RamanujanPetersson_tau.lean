-- Prove2me | Definitions.Def_RamanujanPetersson_tau
-- name    : RamanujanPetersson_tau
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T16:09:57.53757+00:00
-- url     : https://prove2.me/theorems/67896fa5-a9ed-4d8c-94a5-5f11c3914f84
-- title:
--   Ramanujan's tau function $\tau(n)$
-- statement:
--   Let $q=e^{2\pi i z}$ for $z$ in the upper half-plane $\mathbb H$, and let $\Delta(z)=\eta(z)^{24}=q\prod_{n>0}(1-q^n)^{24}$ be the discriminant modular form, a holomorphic cusp form of weight $12$ and level $1$. **Ramanujan's tau function** $\tau:\mathbb N\to\mathbb C$ is defined by the Fourier expansion of $\Delta$ at $i\infty$:
--
--   $$\Delta(z)=\sum_{n=0}^{\infty}\tau(n)\,q^n .$$
--
--   Since $\Delta$ is a cusp form, $\tau(0)=0$, so the sum starts at $n=1$ as in the source. This is the arithmetic function behind all of the mission's statements about $\tau$ and its $L$-function $L(s,\tau)=\sum_{n\ge1}\tau(n)n^{-s}$.
--
--   **Formalization Note** $\tau(n)$ is the $n$-th coefficient of Mathlib's `UpperHalfPlane.qExpansion 1` of `ModularForm.discriminant` (which is defined as $\eta^{24}$), as a complex number. Integrality of $\tau$ is not built into the definition.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan conjecture", displayed definitions of $\Delta(z)$ and of $\tau(n)$ via $\Delta(z)=\sum_{n\ge1}\tau(n)q^n$

import Mathlib

open UpperHalfPlane

namespace RamanujanPetersson

/-- Ramanujan's tau function: `tau n` is the `n`-th Fourier coefficient, in the variable
`q = exp(2πiz)`, of the discriminant modular form `Δ(z) = η(z)^24`. -/
noncomputable def tau (n : ℕ) : ℂ :=
  (qExpansion 1 ModularForm.discriminant).coeff n

end RamanujanPetersson



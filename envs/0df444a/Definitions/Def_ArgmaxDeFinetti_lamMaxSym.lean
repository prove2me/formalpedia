-- Prove2me | Definitions.Def_ArgmaxDeFinetti_lamMaxSym
-- name    : ArgmaxDeFinetti_lamMaxSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:57.952317+00:00
-- url     : https://prove2.me/theorems/d96ddb26-836a-41c0-a437-67c1671c5fca
-- title:
--   Top eigenvalue $\lambda_{\max}(M^{[N]})$ on $\mathrm{Sym}^N$
-- statement:
--   For a two-site operator $M$,
--   $$
--   \lambda_{\max}(M^{[N]})=\sup\{\langle\psi,M^{[N]}\psi\rangle:\ \psi\in\mathrm{Sym}^N(\mathbb C^d),\ \|\psi\|=1\},
--   $$
--   the largest eigenvalue of the lift $M^{[N]}$ as an operator on $\mathrm{Sym}^N(\mathbb C^d)$, written as its largest Rayleigh quotient.
--
--   **Formalization Note** (3.4) defines $M^{[N]}$ on $\mathrm{Sym}^N$, so the supremum runs over unit symmetric vectors only; the top eigenvalue on the whole of $(\mathbb C^d)^{\otimes N}$ can be larger. The real part of the Rayleigh quotient is taken.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1, pp.22–23, eqs. (3.4)–(3.5)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_IsSym
import Definitions.Def_ArgmaxDeFinetti_liftN

open Matrix

namespace ArgmaxDeFinetti

/-- `λ_max(M^{[N]})`: the largest eigenvalue of the lift `M^{[N]}` as an operator on `Sym^N(ℂ^d)`, written as
its largest Rayleigh quotient `sup { ⟨ψ, M^{[N]} ψ⟩ : ψ ∈ Sym^N(ℂ^d), ∥ψ∥ = 1 }`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eqs. (3.4)–(3.5),
pp.22–23.

**Formalization Note** (3.4) defines `M^{[N]}` "on Sym^N(H)", so the supremum is over unit symmetric vectors
only, not over all of `(ℂ^d)^{⊗N}`. For Hermitian `M^{[N]}` preserving `Sym^N`, this is its top eigenvalue
there. The real part of the Rayleigh quotient is taken. -/
noncomputable def lamMaxSym (N : ℕ) {d : ℕ} (M : Op 2 d) : ℝ :=
  sSup {r | ∃ ψ : Vec N d, IsSym ψ ∧ vnorm ψ = 1 ∧ r = (vinner ψ (liftN N M *ᵥ ψ)).re}

end ArgmaxDeFinetti



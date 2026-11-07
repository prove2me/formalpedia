-- Prove2me | Definitions.Def_ArgmaxDeFinetti_liftN
-- name    : ArgmaxDeFinetti_liftN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:24.351422+00:00
-- url     : https://prove2.me/theorems/ef6d66ee-f34a-4c87-bed8-09af92ce19d8
-- title:
--   Normalized $N$-site lift $M^{[N]}=\binom N2^{-1}\sum_{i<j}M_{ij}$
-- statement:
--   For a two-site operator $M$ and sites $i\ne j$, $M_{ij}$ acts as $M$ on sites $i,j$ and as the identity on the others. The normalized $N$-site lift is
--   $$
--   M^{[N]}=\binom N2^{-1}\sum_{1\le i<j\le N}M_{ij}.
--   $$
--   Its top eigenvalue on $\mathrm{Sym}^N$ is the maximum of $\operatorname{Tr}(M\rho)$ over bosonic two-site marginals.
--
--   **Formalization Note** The lift is written on all of $(\mathbb C^d)^{\otimes N}$; the paper uses it on $\mathrm{Sym}^N$, which it preserves for witnesses $M\in\mathrm{Herm}(\mathrm{Sym}^2)$. Sites are $0$-based.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1, p.22, eq. (3.4)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_tensorPow

open Matrix

namespace ArgmaxDeFinetti

/-- `M_{ij}`: the operator on `N` sites acting as the two-site operator `M` on sites `i, j` (in this
order) and as the identity elsewhere, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1, p.22 (after (3.4)). -/
def siteOp {N d : ℕ} (M : Op 2 d) (i j : Fin N) : Op N d :=
  fun a b => M ![a i, a j] ![b i, b j] *
    ∏ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), (if a k = b k then (1 : ℂ) else 0)

/-- The normalized `N`-site lift `M^{[N]} = (N choose 2)^{-1} Σ_{1≤i<j≤N} M_{ij}`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (3.4), p.22.

**Formalization Note** The lift is written on all of `(ℂ^d)^{⊗N}`; the paper uses it on `Sym^N(H)`, which it
preserves when `M` is a witness (`IsSymWitness`). Its top eigenvalue on `Sym^N` is `lamMaxSym`. Sites are
`Fin N` (0-based), so `1 ≤ i < j ≤ N` is `i < j` in `Fin N`. -/
noncomputable def liftN (N : ℕ) {d : ℕ} (M : Op 2 d) : Op N d :=
  ((N.choose 2 : ℂ))⁻¹ •
    ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), siteOp M p.1 p.2

end ArgmaxDeFinetti



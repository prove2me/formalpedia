-- Prove2me | Definitions.Def_ArgmaxDeFinetti_IsSymWitness
-- name    : ArgmaxDeFinetti_IsSymWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:18.280198+00:00
-- url     : https://prove2.me/theorems/29338459-7fbe-46b2-a558-33f5b17c04cf
-- title:
--   Witnesses $M\in\mathrm{Herm}(\mathrm{Sym}^2(\mathbb C^d))$
-- statement:
--   A Hermitian operator on the symmetric subspace $\mathrm{Sym}^2(\mathbb C^d)$, represented by the Hermitian matrix on $\mathbb C^d\otimes\mathbb C^d$ that vanishes off $\mathrm{Sym}^2$:
--   $$
--   M=M^\dagger,\qquad U_\pi M=M\,U_\pi=M\quad(\pi\in S_2).
--   $$
--   These are the witnesses of the exact duality (3.5) and of Proposition 3.5.
--
--   **Formalization Note** On two sites $\mathrm{Sym}^2$ is the $+1$ eigenspace of the swap, so the two conditions say that $M$ maps into $\mathrm{Sym}^2$ and annihilates its orthogonal complement. Under this extension by zero, $\|M\|_\infty$, $a_M$, $h(M)$, $M^{[N]}$ on $\mathrm{Sym}^N$ and $\tau(M)$ coincide with those of the operator on $\mathrm{Sym}^2$.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1, p.22

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_IsSym

open Matrix

namespace ArgmaxDeFinetti

/-- `M ∈ Herm(Sym²(ℂ^d))`: a Hermitian operator on the symmetric subspace `Sym²(ℂ^d)`, represented as the
Hermitian matrix on `ℂ^d ⊗ ℂ^d` that vanishes off `Sym²`: `U_π M = M U_π = M` for both `π ∈ S₂`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1, p.22 ("associate with each M ∈ Herm(Sym²(H))").

**Formalization Note** For two sites `Sym²` is the `+1` eigenspace of the swap and its complement the `−1`
eigenspace, so `U_π M = M` says that `M` has range in `Sym²` and `M U_π = M` that it kills the complement.
Under this extension by zero the operator norm `∥M∥_∞`, `a_M`, `h(M)`, `M^{[N]}` on `Sym^N` and `τ(M)` are those of
the operator on `Sym²`. -/
def IsSymWitness {d : ℕ} (M : Op 2 d) : Prop :=
  M.IsHermitian ∧ ∀ π : Equiv.Perm (Fin 2),
    OptimalSpectrum.Entangled.permOp (ι := Fin d) π * M = M ∧ M * OptimalSpectrum.Entangled.permOp (ι := Fin d) π = M

end ArgmaxDeFinetti



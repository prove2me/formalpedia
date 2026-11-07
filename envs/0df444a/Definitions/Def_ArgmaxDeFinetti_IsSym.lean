-- Prove2me | Definitions.Def_ArgmaxDeFinetti_IsSym
-- name    : ArgmaxDeFinetti_IsSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:17.497642+00:00
-- url     : https://prove2.me/theorems/68fd611f-9f65-4acc-8958-f37e40cf48b2
-- title:
--   The symmetric subspace $\mathrm{Sym}^n(\mathbb C^d)$
-- statement:
--   For $\pi\in S_n$, the operator $U_\pi$ on $(\mathbb C^d)^{\otimes n}$ permutes the tensor factors: $(U_\pi\Psi)(i_1,\dots,i_n)=\Psi(i_{\pi(1)},\dots,i_{\pi(n)})$. The symmetric tensor power is
--   $$
--   \mathrm{Sym}^n(\mathbb C^d)=\{\Psi\in(\mathbb C^d)^{\otimes n}:\ U_\pi\Psi=\Psi\ \text{for every }\pi\in S_n\}.
--   $$
--   Bosonic states, the witnesses $\mathrm{Herm}(\mathrm{Sym}^2)$ and the eigenvalue $\lambda_{\max}(M^{[N]})$ are all defined through this subspace.
--
--   **Formalization Note** $U_\pi$ is the published `OptimalSpectrum.Entangled.permOp`, which maps $|v\rangle$ to $|v\circ\pi^{-1}\rangle$. Whether this is the paper's $U_\pi$ or $U_{\pi^{-1}}$ is a convention the paper does not fix; every statement quantifies over all $\pi$, so both readings agree.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18 (definition of Sym^k H)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_ArgmaxDeFinetti_tensorPow

open Matrix

namespace ArgmaxDeFinetti

/-- `Ψ ∈ Sym^n(ℂ^d)`: the vector is invariant under every permutation of the tensor factors, `U_π Ψ = Ψ` for
every `π ∈ S_n`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18 (definition of the symmetric tensor power).

**Formalization Note** `U_π` is the published `OptimalSpectrum.Entangled.permOp π` on `(ℂ^d)^{⊗n}`, which
maps `|v⟩` to `|v ∘ π⁻¹⟩`. Whether this is the paper's `U_π` or `U_{π⁻¹}` is a convention the paper does not
fix; every use quantifies over all `π`, so both readings give the same statements. -/
def IsSym {n d : ℕ} (ψ : Vec n d) : Prop :=
  ∀ π : Equiv.Perm (Fin n), OptimalSpectrum.Entangled.permOp (ι := Fin d) π *ᵥ ψ = ψ

end ArgmaxDeFinetti



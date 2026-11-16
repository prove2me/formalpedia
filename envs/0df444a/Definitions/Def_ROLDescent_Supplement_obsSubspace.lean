-- Prove2me | Definitions.Def_ROLDescent_Supplement_obsSubspace
-- name    : ROLDescent_Supplement_obsSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:56:17.860087+00:00
-- url     : https://prove2.me/theorems/35848f2e-2d9e-4aef-8129-745398115997
-- title:
--   Observable hierarchy $I_S=\{f:\mathbb E_\mu[f\mid X_S]=0\}$ in $L^2(\mu)$, eq. (108)
-- statement:
--   Let $\mu$ be a full-support law on $\{0,1\}^V$ and $K=L^2(\mu)$ the space of complex functions on configurations with $\langle f,g\rangle_\mu=\sum_x\mu(x)\overline{f(x)}g(x)$. For $S\subseteq V$, the **observable hierarchy** assigns to $S$ the orthogonal complement of the observables supported on $S$:
--
--   $$I_S=A_S^{\perp}=\{f\in L^2(\mu):\ \mathbb E_\mu[f\mid X_S]=0\},\qquad A_S=\{g(X_S)\}.$$
--
--   The removed space at $S$ and $i\notin S$ is $U_{S,i}=I_S\cap I_{S\cup\{i\}}^{\perp}$, and the Gram norms of this hierarchy are the overlap quantities of Theorem 6.4.
--
--   **Formalization Note** $L^2(\mu)$ is represented isometrically in `EuclideanSpace ℂ (V → Bool)` by the unitary map $f\mapsto\sqrt{\mu}\,f$. Under this transport the condition $\mathbb E_\mu[f\mid X_S]=0$ becomes $\sum_{x:\,x_S=s}\sqrt{\mu(x)}\,\psi(x)=0$ for every $s\in\{0,1\}^S$, and orthogonal projections and operator norms are those of $L^2(\mu)$.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.1, eq. (108), p.47, specialized to binary spins in Section 6.2.2, p.50 (PDF 47, 50)

import Mathlib

namespace ROLDescent.Supplement

/-- **Observable hierarchy** `I_S = A_S^⊥` in `K = L²(µ)`, eq. (108).
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.1, eq. (108), p.47 (PDF 47): "node : S ⊆ V, K = L²(µ),
A_S = {g(X_S) : g : ∏_{i∈S} X_i → ℂ}, Π^obs_S f = E_µ[f | X_S], I_S = A_S^⊥ = {f : E_µ[f | X_S] = 0}".
Specialized to binary spins `X_i = {0, 1}` (Section 6.2.2, p.50).

**Formalization Note** `L²(µ)` (ℂ-valued `f` on `{0,1}^V` with `⟨f, g⟩_µ = Σ_x µ(x) conj(f x) g x`)
is represented isometrically in `EuclideanSpace ℂ (V → Bool)` by the unitary `f ↦ ψ = √µ · f`
(full support makes it bijective). Under this transport, `E_µ[f | X_S] = 0` means
`Σ_{x : x_S = s} µ(x) f(x) = 0` for every `s ∈ {0,1}^S`, i.e. `Σ_{x : x_S = s} √µ(x) ψ(x) = 0`; the
subspace is the intersection of the kernels of these functionals. Orthogonal projections and
operator norms in the transported space are those of `L²(µ)`. -/
noncomputable def obsSubspace {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (S : Finset V) : Submodule ℂ (EuclideanSpace ℂ (V → Bool)) :=
  ⨅ s : S → Bool, LinearMap.ker
    ((∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i : S, x i = s i),
      ((Real.sqrt (μ x) : ℝ) : ℂ) • EuclideanSpace.proj (𝕜 := ℂ) x :
        EuclideanSpace ℂ (V → Bool) →L[ℂ] ℂ) : EuclideanSpace ℂ (V → Bool) →ₗ[ℂ] ℂ)

end ROLDescent.Supplement



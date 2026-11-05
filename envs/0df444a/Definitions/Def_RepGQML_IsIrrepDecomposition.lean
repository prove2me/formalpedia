-- Prove2me | Definitions.Def_RepGQML_IsIrrepDecomposition
-- name    : RepGQML_IsIrrepDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:25.351737+00:00
-- url     : https://prove2.me/theorems/c6261e76-631e-49fc-839e-57a281015b0f
-- title:
--   Decomposition $U=\bigoplus_k\mathbb 1_{m_k}\otimes U_k$ into irreps
-- statement:
--   Let $U$ be a representation of $G$ on $H$. A linear isomorphism $\Phi:H\to\bigoplus_k\mathbb C^{m_k}\otimes V_k$, together with representations $\rho_k$ of $G$ on the inner product spaces $V_k$, is a **decomposition of $U$ into irreps** when:
--
--   1. each $\rho_k$ is irreducible and unitary;
--   2. $\rho_k$ and $\rho_l$ are inequivalent for $k\ne l$;
--   3. $\Phi$ carries $U_g$ to $\mathbb 1_{m_k}\otimes(\rho_k)_g$ on the $k$-th summand, that is,
--   $$
--   \Phi(U_g x)_k=(\mathbb 1_{m_k}\otimes(\rho_k)_g)\,\Phi(x)_k .
--   $$
--
--   The integer $m_k$ is the multiplicity of the irrep $\rho_k$.
--
--   **Formalization Note** The source writes "$U=\bigoplus_k\mathbb 1_{m_k}\otimes U_k$", an equality after an identification of spaces; $\Phi$ is that identification, and here it is only required to be linear, which covers the isometric case. Condition 2 is not printed in Theorem 7; it is how the source uses the word multiplicity, and the theorem is false without it. The value $m_k=0$ is allowed.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Theorem 7, p.28, with p.23, (31) on p.29, and footnote 20, p.28

import Mathlib
import Definitions.Def_RepGQML_IsUnitaryRep
import Definitions.Def_RepGQML_AreEquivalent
import Definitions.Def_RepGQML_IrrepSum

namespace RepGQML

/-- `Φ` exhibits `U = ⨁_k 𝟙_{m_k} ⊗ ρ_k`, the decomposition into irreps of Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Theorem 7, p.28:
each `ρ_k` is an irreducible unitary representation, different `k` carry inequivalent `ρ_k`, and `Φ`
carries `U_g` to `𝟙 ⊗ (ρ_k)_g` on the `k`-th summand.

**Formalization Note** (1) The "=" of the page holds after identifying `H` with the direct sum (p.23,
(31) on p.29); `Φ` is that identification. It is only linear here, which covers the isometric case.
(2) Inequivalence is the reading of "the multiplicity of the irrep `U_k`" (see p.30, "`K` distinct
irreducible invariant subspaces", and footnote 20, p.28); the page's (30) is false without it.
(3) `m k = 0` is allowed. A zero `V k` is impossible, since `Representation.IsIrreducible` requires a
nonzero space. -/
structure IsIrrepDecomposition {G H K : Type*} [Group G] [AddCommGroup H] [Module ℂ H] [Fintype K]
    (U : Representation ℂ G H) (m : K → ℕ) (V : K → Type*) [∀ k, NormedAddCommGroup (V k)]
    [∀ k, InnerProductSpace ℂ (V k)] (ρ : ∀ k, Representation ℂ G (V k))
    (Φ : H ≃ₗ[ℂ] IrrepSum m V) : Prop where
  /-- Each `ρ_k` is irreducible. -/
  irreducible : ∀ k, (ρ k).IsIrreducible
  /-- Each `ρ_k` is unitary. -/
  unitary : ∀ k, IsUnitaryRep (ρ k)
  /-- Different `k` carry inequivalent irreps. -/
  inequivalent : ∀ k l, k ≠ l → ¬ AreEquivalent (ρ k) (ρ l)
  /-- `Φ` carries `U_g` to `𝟙 ⊗ (ρ_k)_g` on the `k`-th summand. -/
  intertwines : ∀ (g : G) (x : H) (k : K),
    Φ (U g x) k = TensorProduct.map LinearMap.id (ρ k g) (Φ x k)

end RepGQML



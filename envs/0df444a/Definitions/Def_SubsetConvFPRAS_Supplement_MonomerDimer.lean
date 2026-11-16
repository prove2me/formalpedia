-- Prove2me | Definitions.Def_SubsetConvFPRAS_Supplement_MonomerDimer
-- name    : SubsetConvFPRAS_Supplement_MonomerDimer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:48:18.366035+00:00
-- url     : https://prove2.me/theorems/a5546491-70ed-45b1-99d5-b21cbf41fbcf
-- title:
--   The monomer-dimer law $\mu_\lambda$ on common independent sets and its heat-bath Glauber dynamics $P_\lambda$
-- statement:
--   Let $M,N$ be matroids on a common ground set $U$ with $|U|=n$, and let $\Omega=\mathcal I(M)\cap\mathcal I(N)$ be the family of their common independent sets. For $\lambda\ge0$ the **monomer-dimer law** is
--   $$\mu_\lambda(S)=\frac{\lambda^{|S|}}{\sum_{T\in\Omega}\lambda^{|T|}},\qquad S\in\Omega,$$
--   with the convention $0^0=1$, so that $\mu_0$ is the point mass at $\emptyset$.
--
--   The **heat-bath Glauber dynamics** picks a uniformly random $u\in U$ and resamples its membership conditioned on the rest. Its transition matrix $P_\lambda$ has off-diagonal entries
--   $$P_\lambda(S,S-u)=\frac{1}{n(1+\lambda)}\ (u\in S),\qquad P_\lambda(S,S+u)=\frac{\lambda}{n(1+\lambda)}\ (u\notin S,\ S+u\in\Omega),$$
--   and every other off-diagonal entry is $0$. These objects are the subject of the spectral-gap bound Theorem D.1.
--
--   **Formalization Note** The diagonal of $P_\lambda$ (the holding probability) is stored as $0$: the Dirichlet form $\langle f,(I-P_\lambda)f\rangle_{\mu_\lambda}=\sum_{S}\mu_\lambda(S)\sum_{T}P_\lambda(S,T)(f(S)-f(T))f(S)$ does not depend on it.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Appendix D.1, p.64

import Mathlib

open scoped Classical

namespace SubsetConvFPRAS.Supplement

/-!
# The matroid-intersection monomer-dimer law and its heat-bath Glauber dynamics

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), Appendix D.1, p.64.

**Formalization Note.**
* The matroids are Mathlib `Matroid (Fin n)`; the theorems using this file assume ground set
  `Set.univ`. A set is common independent when it is independent in both.
* `monomerDimerLaw M N λ S = λ^|S| / ∑_T λ^|T|`, the sum over common independent `T`. Lean's `0^0 = 1`,
  so at `λ = 0` this is the point mass at `∅` (always common independent), as on p.64.
* `glauberKernel M N λ` is the transition matrix `P_λ` off the diagonal: deleting an element has
  probability `1/(n(1+λ))` (choose `u` uniformly, then delete with probability `1/(1+λ)`), adding an
  element to give a common independent set has probability `λ/(n(1+λ))`, and every other off-diagonal
  entry is `0`. The diagonal (the holding probability) is set to `0`: it does not enter the Dirichlet
  form `⟨f, (I − P_λ) f⟩`, which the published `dirichlet` computes from the off-diagonal entries.
-/

variable {n : ℕ}

/-- The common independent sets `I(M) ∩ I(N)` of two matroids on `Fin n`, as a finite type. -/
abbrev CommonIndep (M N : Matroid (Fin n)) : Type :=
  {S : Finset (Fin n) // M.Indep (S : Set (Fin n)) ∧ N.Indep (S : Set (Fin n))}

/-- The monomer-dimer law `μ_λ(S) ∝ λ^|S|` on the common independent sets, p.64. -/
noncomputable def monomerDimerLaw (M N : Matroid (Fin n)) (lam : ℝ) : CommonIndep M N → ℝ :=
  fun S => lam ^ S.1.card / ∑ T : CommonIndep M N, lam ^ T.1.card

/-- The heat-bath Glauber dynamics `P_λ` on common independent sets, p.64, off the diagonal:
`P_λ(S, S − u) = 1/(n(1+λ))` for `u ∈ S`, `P_λ(S, S + u) = λ/(n(1+λ))` for `u ∉ S` (the target is common
independent because it is a state), and `0` otherwise. -/
noncomputable def glauberKernel (M N : Matroid (Fin n)) (lam : ℝ) :
    CommonIndep M N → CommonIndep M N → ℝ :=
  fun S T =>
    if ∃ u ∈ S.1, T.1 = S.1.erase u then 1 / ((n : ℝ) * (1 + lam))
    else if ∃ u, u ∉ S.1 ∧ T.1 = insert u S.1 then lam / ((n : ℝ) * (1 + lam))
    else 0

end SubsetConvFPRAS.Supplement



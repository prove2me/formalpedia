-- Prove2me | Definitions.Def_TreeCoverLB_IsAgreementIndexMap
-- name    : TreeCoverLB_IsAgreementIndexMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:52.116332+00:00
-- url     : https://prove2.me/theorems/a20b4d52-9f2b-4cc9-b6cc-a061c7c82421
-- title:
--   Continuous $\mathbb Z_p$-equivariant map $|I_{p,k}|\to|E_d\mathbb Z_p|$
-- statement:
--   A map $\psi : |I_{p,k}|\to|E_d\mathbb Z_p|$ is a **continuous $\mathbb Z_p$-equivariant map** if it is continuous on $|I_{p,k}|$, takes values in $|E_d\mathbb Z_p|$, and satisfies
--   $$
--   \psi(g\cdot\mu)=g\cdot\psi(\mu)\qquad(g\in\mathbb Z_p,\ \mu\in|I_{p,k}|),
--   $$
--   with the diagonal action on words and the layerwise action on $E_d\mathbb Z_p$. The topological index (Definition 4.2) satisfies $\operatorname{ind}_{\mathbb Z_p}(|I_{p,k}|)\le d$ exactly when such a map exists.
--
--   **Formalization Note** $\psi$ is a function on the ambient space $\mathbb R^{\mathbb Z_p^k}$; only its values on $|I_{p,k}|$ matter. The index itself is never used as a value.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Definition 4.2, p.11 (PDF p.13), and §4, p.11: fix a G-equivariant map ψ : |I_{p,k}| → |E_dG|

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_agreementComplex

namespace TreeCoverLB

/-- `ψ` is a **continuous `ℤ_p`-equivariant map `|I_{p,k}| → |E_dℤ_p|`** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 4.2,
p.11 (PDF p.13): `ind_{ℤ_p}(|I_{p,k}|) ≤ d` iff such a map exists; §4, p.11: "fix a G-equivariant
map ψ : |I_{p,k}| → |E_dG|").

The three clauses: `ψ` is continuous on `|I_{p,k}|`, maps `|I_{p,k}|` into `|E_dℤ_p|`, and
`ψ(g · µ) = g · ψ(µ)` for every `g ∈ ℤ_p` and every `µ ∈ |I_{p,k}|` (diagonal action on words,
layerwise action `(i, h) ↦ (i, g + h)` on `E_dℤ_p`).

**Formalization Note** `ψ` is a function on the ambient space `ℝ^{ℤ_p^k}`; only its values on
`|I_{p,k}|` matter. The index itself (an `inf` with value `+∞` on the empty set) is never used: a
statement "`ind ≤ d`" is written as the existence of such a `ψ`. -/
def IsAgreementIndexMap (p k d : ℕ) [NeZero p]
    (ψ : ((Fin k → ZMod p) → ℝ) → (Fin (d + 1) × ZMod p → ℝ)) : Prop :=
  ContinuousOn ψ (realization (agreementComplex p k)) ∧
    Set.MapsTo ψ (realization (agreementComplex p k)) (realization (EJoin d (ZMod p))) ∧
    ∀ g : ZMod p, ∀ μ ∈ realization (agreementComplex p k),
      ψ (wordAct g μ) = ejoinAct g (ψ μ)

end TreeCoverLB



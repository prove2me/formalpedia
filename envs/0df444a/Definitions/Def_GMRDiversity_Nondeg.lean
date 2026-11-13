-- Prove2me | Definitions.Def_GMRDiversity_Nondeg
-- name    : GMRDiversity_Nondeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:24.950424+00:00
-- url     : https://prove2.me/theorems/758bca4d-9bf8-4cdb-b05c-270de3d78da2
-- title:
--   Nondegenerate subspaces of $\mathbb F_2^n$: $S\cap S^\perp=\{0\}$
-- statement:
--   Equip $\mathbb F_2^n$ with the dot product $a\cdot b=\sum_k a_kb_k \bmod 2$ and, for a subspace $S$, let $S^\perp=\{v : s\cdot v=0 \text{ for all } s\in S\}$. The subspace $S$ is **nondegenerate** if
--   $$
--   S\cap S^\perp=\{0\}.
--   $$
--   Over $\mathbb F_2$ the dot product is not an inner product: a nonzero vector can be orthogonal to itself, and, for instance, the span of $(1,1)$ in $\mathbb F_2^2$ is degenerate. The upper-bound policy keeps a basis of a nondegenerate subspace, which is what makes the stored equations determine a unique partial solution.
--
--   **Formalization Note** $S^\perp$ is `orth S` from the published definition `ExtremalForrelation_Nonadaptive_Basic`, and $\{0\}$ is the zero submodule.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, Step (i), p.10

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Basic

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Nondegenerate subspace** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of Lemma 2,
Step (i), p.10): a subspace `S ≤ 𝔽₂ⁿ` is nondegenerate if `S ∩ S^⊥ = {0}`, where `S^⊥` is the
orthogonal complement for the dot product `a · b = ∑ₖ aₖ bₖ mod 2`.

**Formalization Note.** `S^⊥` is the published `orth S` of `ExtremalForrelation_Nonadaptive_Basic`
(`{y | ∀ s ∈ S, s · y = 0}`); `{0}` is the zero submodule `⊥`. Over `𝔽₂` the dot product is not an
inner product, so many subspaces are degenerate (for instance the span of `(1,1)` in `𝔽₂²`). -/
def Nondeg {n : ℕ} (S : Submodule (ZMod 2) (V n)) : Prop := S ⊓ orth S = ⊥

end GMRDiversity



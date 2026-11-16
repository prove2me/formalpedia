-- Prove2me | Definitions.Def_LowErrExt_Supplement_IsAffinePartition
-- name    : LowErrExt_Supplement_IsAffinePartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:57.787435+00:00
-- url     : https://prove2.me/theorems/2845376e-83e6-4bbe-a6c9-e3d56dc7e179
-- title:
--   Affine partition $\Gamma:\mathbb F_2^n\to\Sigma$
-- statement:
--   A function $\Gamma:\mathbb F_2^n\to\Sigma$ is an **affine partition** if every fiber of $\Gamma$, that is, every preimage $\Gamma^{-1}(\gamma)$ of an element $\gamma$ of the image $\Gamma(\mathbb F_2^n)$, is an affine subspace of $\mathbb F_2^n$.
--
--   Viewing $\Gamma$ as a partition of $\mathbb F_2^n$ into its fibers, an affine partition cuts the space into affine pieces; conditioning an affine source on a fiber leaves an affine source. It is the partition type of the regularity lemma for quadratics (Theorem 4.2).
--
--   **Formalization Note** Fibers are the nonempty preimages; affine subspaces are cosets (published `IsCoset`).
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 2.20, p.19

import Mathlib
import Definitions.Def_LowErrExt_IsCoset

namespace LowErrExt.Supplement

open LowErrExt

/-- **Affine partition.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 2.20, p.19: "We say that a function Γ : F₂ⁿ → Σ is an affine partition if every fiber of
Γ is an affine subspace V ⊆ F₂ⁿ", where "a fiber of a function Γ : X → Σ is a preimage of a single
element in Γ(X)" (p.19).

**Formalization Note.** Fibers are preimages of elements of the image, i.e. the nonempty preimages;
affine subspaces of `𝔽₂ⁿ` are the cosets (published `IsCoset`). -/
def IsAffinePartition {n : ℕ} {Sig : Type*} (Γ : (Fin n → ZMod 2) → Sig) : Prop :=
  ∀ γ : Sig, (Γ ⁻¹' {γ}).Nonempty → IsCoset (Γ ⁻¹' {γ})

end LowErrExt.Supplement



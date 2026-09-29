-- Prove2me | Definitions.Def_ModularSchurBasic
-- name    : ModularSchurBasic
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-19T22:32:35.387875+00:00
-- url     : https://prove2.me/theorems/6d055b61-2a07-4348-a9ac-065cc26f74f4
-- title:
--   $\ell$-sum-free sets modulo $m$
-- statement:
--   This bundle introduces the residue-level notion of sum-freeness on which the whole modular Schur development rests.
--
--   Fix a modulus $m \ge 2$ and a number of summands $\ell \ge 2$, and work in the cyclic group $\mathbb{Z}/m$. A finite subset $C \subseteq \mathbb{Z}/m$ is **$\ell$-sum-free modulo $m$** when no $\ell$ of its elements, repetitions allowed, sum to an element of $C$:
--
--   $$ x_1 + \cdots + x_\ell \ne y \quad \text{for all } x_1, \dots, x_\ell \in C \text{ and all } y \in C, $$
--
--   the sum and the inequality both taken in $\mathbb{Z}/m$.
--
--   For $\ell = 2$ this is the classical sum-free condition behind the Schur numbers; letting $\ell$ vary gives the modular generalisation studied here. Every later definition and theorem in this mission is phrased in terms of this single predicate, so it is the shared vocabulary of the whole tree.
--
--   **Formalization Note** The $\ell$-tuple is a function $f : \mathrm{Fin}\ \ell \to \mathbb{Z}/m$ taking values in $C$, which builds in *repetitions allowed* automatically, and the sum is the Finset sum over $\mathrm{Fin}\ \ell$.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Definition 1.1 (residue form). Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/Basic.lean#L25-L28

-- Generated from lean/ModularSchur/Basic.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Mathlib

namespace ModularSchur

open Finset

/-- A subset `C ⊆ ZMod m` is **ℓ-sum-free mod m** iff no `(ℓ+1)`-tuple
    from `C` (with repetitions) satisfies `x₁ + ⋯ + x_ℓ = y`. -/
def IsEllSumFree (m : ℕ) (ℓ : ℕ) (C : Finset (ZMod m)) : Prop :=
  ∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ C) → ∀ y ∈ C, (∑ i, f i) ≠ y

end ModularSchur



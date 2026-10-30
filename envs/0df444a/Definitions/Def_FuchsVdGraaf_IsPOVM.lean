-- Prove2me | Definitions.Def_FuchsVdGraaf_IsPOVM
-- name    : FuchsVdGraaf_IsPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:16.661036+00:00
-- url     : https://prove2.me/theorems/f935abcd-7cad-4797-8077-3d633ece6c0b
-- title:
--   Positive operator-valued measure (Definition 2)
-- statement:
--   Let $\mathcal H = \mathbb C^N$ with $N$ finite. An ordered collection $E = \langle E_1,\dots,E_m\rangle$ of $N\times N$ complex matrices is a **POVM** (positive operator-valued measure) if
--
--   1. every $E_x$ is positive semidefinite, and
--   2. $\sum_{x} E_x = \mathrm{Id}$.
--
--   POVMs are the most general measurements of a quantum system; the number $m$ of outcomes is arbitrary and may exceed $N$. The set $\mathcal M$ of all POVMs is the range of the optimisations that define the quantum distinguishability measures.
--
--   **Formalization Note** Matrices are indexed by an arbitrary finite type; outcomes are indexed by $\mathrm{Fin}\,m = \{0,\dots,m-1\}$ for an arbitrary $m\in\mathbb N$.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 2, p.7

import Mathlib

open scoped ComplexOrder

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 2, p.7: a collection
(ordered set) `E = ⟨E₁, …, E_m⟩` of operators is a POVM if (1) every `E_x` is positive
semidefinite and (2) `∑_x E_x = Id`.

**Formalization Note.** Operators on the `N`-dimensional Hilbert space (`N` finite, p.5) are
matrices over an arbitrary finite index type `n`. The outcomes are `Fin m` (0-based) for an
arbitrary `m : ℕ`, which covers every finite ordered outcome set `⟨E₁, …, E_m⟩`. -/
def IsPOVM {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} (E : Fin m → Matrix n n ℂ) : Prop :=
  (∀ x, (E x).PosSemidef) ∧ ∑ x, E x = 1

end FuchsVdGraaf



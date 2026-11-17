-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_RepModel
-- name    : TwoFoldOPI_Supplement_RepModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:01:31.420758+00:00
-- url     : https://prove2.me/theorems/9924a2f3-4d31-46a1-88d4-60c41c7e4c47
-- title:
--   Represented code-intersection instances with a translation action
-- statement:
--   An **instance representation** $I$ consists of public classical data and access to fixed classical function oracles; it specifies a target set $A(I)\subseteq\mathbb F_q^M$. A **translation action** assigns a representation $I+v$ to each $I$ and $v\in\mathbb F_q^M$ with
--   $$A(I+v)=A(I)+v,\qquad (I+v)+w=I+(v+w),\qquad I+0=I .$$
--
--   This is the instance model of the average-case reduction (Theorem 5.28).
--
--   **Formalization Note** Algorithms see the public data and query the oracles (reversible evaluation); they never see $I$ itself. The cost clause of Definition 5.27 is stated in Theorem 5.28.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definitions 5.26–5.27, p. 27

import Mathlib
import Definitions.Def_TwoFoldOPI_Supplement_fnOracle

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **Represented code-intersection instances with a translation action.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definition 5.26, p.27: "An instance representation I consists of public classical data
and, optionally, access to fixed classical function oracles; it specifies a target set
A(I) ⊆ F_q^M"; Definition 5.27, p.27: "A translation action assigns a representation I + v to each I
and v ∈ F_q^M, with A(I + v) = A(I) + v, (I + v) + w = I + (v + w), I + 0 = I."; "Computational
conventions", p.26: "Classical function oracles use reversible evaluation, |x, z⟩ ↦ |x, z ⊕ H(x)⟩".

A model over `K^M` has a type `Rep` of representations, the public data `pub I`, `r` classical
function oracles `fn I k : {0,1}^{inW k} → {0,1}^{outW k}`, the target set `target I ⊆ K^M`, and a
translation action `shift I v = I + v` with the three laws.
`oracles I k` is the reversible evaluation of `fn I k` on `inW k + outW k` qubits.

**Formalization Note.** Algorithms see `pub I` (a program may be chosen as a function of it) and
query `oracles I`; they never see `I` itself. The cost clause of Definition 5.27 ("public data and
oracle access for I + v can be constructed or simulated from I, v") is stated where the model is
used: decoders and preparations for `I + v` are given as functions of `(pub I, v)` querying the
oracles of `I`. The module holds the structure with its oracle matrices. -/
structure RepModel (K : Type) [AddCommGroup K] [DecidableEq K] (M : ℕ) where
  /-- The representations. -/
  Rep : Type
  /-- The type of public data. -/
  Pub : Type
  /-- The public data of a representation. -/
  pub : Rep → Pub
  /-- The number of oracles. -/
  r : ℕ
  /-- Input width of each oracle. -/
  inW : Fin r → ℕ
  /-- Output width of each oracle. -/
  outW : Fin r → ℕ
  /-- The classical functions behind the oracles. -/
  fn : Rep → (k : Fin r) → (Fin (inW k) → Bool) → (Fin (outW k) → Bool)
  /-- The target set `A(I)`. -/
  target : Rep → Finset (Fin M → K)
  /-- The translation action `I + v`. -/
  shift : Rep → (Fin M → K) → Rep
  target_shift : ∀ I v, target (shift I v) = (target I).image fun x => x + v
  shift_shift : ∀ I v w, shift (shift I v) w = shift I (v + w)
  shift_zero : ∀ I, shift I 0 = I

/-- The oracle matrices of a representation: reversible evaluation of each `fn I k`. -/
noncomputable def RepModel.oracles {K : Type} [AddCommGroup K] [DecidableEq K] {M : ℕ}
    (Mo : RepModel K M) (I : Mo.Rep) (k : Fin Mo.r) :
    Matrix (Qubits (Mo.inW k + Mo.outW k)) (Qubits (Mo.inW k + Mo.outW k)) ℂ :=
  fnOracle (Mo.inW k + Mo.outW k) (Mo.inW k) (Mo.outW k) (Mo.fn I k)

end Supplement

end TwoFoldOPI



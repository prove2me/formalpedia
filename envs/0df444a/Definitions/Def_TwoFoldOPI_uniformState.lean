-- Prove2me | Definitions.Def_TwoFoldOPI_uniformState
-- name    : TwoFoldOPI_uniformState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:47.901906+00:00
-- url     : https://prove2.me/theorems/5f5fefc5-8660-477c-a12d-0306c4e60e1c
-- title:
--   The uniform superposition $|S\rangle$
-- statement:
--   For a finite set $S$, the uniform superposition
--   $$|S\rangle=|S|^{-1/2}\sum_{x\in S}|x\rangle .$$
--   The states $|A\rangle$ and $|A_i\rangle$ of Definition 7.1 and Lemma 7.2 are of this form.
--
--   **Formalization Note** For $S=\emptyset$ the vector is $0$; this case is never used.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7, Definition 7.1, p. 37; proof of Lemma 7.2, p. 38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace TwoFoldOPI

/-- **The uniform superposition `|S⟩` over a finite set.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7, Definition 7.1, p.37: "let |A⟩ be the uniform superposition over A"; proof of Lemma 7.2,
p.38: `|A_i⟩ = |A_i|^{−1/2} Σ_{y ∈ A_i} |y⟩`.

**Formalization Note.** `|S⟩ = |S|^{−1/2} Σ_{x ∈ S} |x⟩`; it is the zero vector for `S = ∅`
(never used). -/
noncomputable def uniformState {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    EuclideanSpace ℂ ι :=
  ∑ x ∈ S, ((Real.sqrt (S.card : ℝ))⁻¹ : ℂ) • QAlgorithms.ket x

end TwoFoldOPI



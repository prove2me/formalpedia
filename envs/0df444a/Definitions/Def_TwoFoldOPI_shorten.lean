-- Prove2me | Definitions.Def_TwoFoldOPI_shorten
-- name    : TwoFoldOPI_shorten
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:21.500633+00:00
-- url     : https://prove2.me/theorems/74d65de2-f5a8-4736-973f-c0a7a5cd5a14
-- title:
--   The shortened code $C[S]$
-- statement:
--   For a linear code $C\subseteq\mathbb F_q^M$ and a set $S\subseteq[M]$ of coordinates, the shortened code is
--   $$C[S]=\{c\in C: c_i=0\ \text{for all } i\in S\},$$
--   a linear subcode of $C$.
--
--   **Formalization Note** $C[S]$ is kept inside $\mathbb F_q^M$. The paper sometimes deletes the coordinates in $S$; this does not change the dimension, which is the only quantity the mission uses.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.19, p. 25

import Mathlib

namespace TwoFoldOPI

/-- **The shortened code `C[S]`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.19, p.25: "For a linear code C ⊆ F_q^M and a subset S ⊆ [M], we define
the shortened code C[S] to be: {c ∈ C : c_i = 0 ∀i ∈ S}."

**Formalization Note.** `C[S]` is kept inside `K^M`. The page's "abuse of notation" of deleting
the coordinates in `S` is a linear isomorphism onto its image (those coordinates are zero), so the
dimension, the only quantity used, is the same. -/
def shorten {K : Type*} [Field K] {M : ℕ} (C : Submodule K (Fin M → K)) (S : Finset (Fin M)) :
    Submodule K (Fin M → K) where
  carrier := {c | c ∈ C ∧ ∀ i ∈ S, c i = 0}
  add_mem' := by
    rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
    exact ⟨C.add_mem ha hb, fun i hi => by simp [ha0 i hi, hb0 i hi]⟩
  zero_mem' := ⟨C.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro t a ⟨ha, ha0⟩
    exact ⟨C.smul_mem t ha, fun i hi => by simp [ha0 i hi]⟩

end TwoFoldOPI



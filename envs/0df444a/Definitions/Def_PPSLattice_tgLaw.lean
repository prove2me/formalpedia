-- Prove2me | Definitions.Def_PPSLattice_tgLaw
-- name    : PPSLattice_tgLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:34:07.815082+00:00
-- url     : https://prove2.me/theorems/7f28e83c-7234-4f8a-ac35-4714f52ab0b3
-- title:
--   Law of an entry of $tg$ in skEnc
-- statement:
--   Uniform on the residues of $\mathbb Z_q$ outside $[-\lfloor q/4\rfloor-B,-\lfloor q/4\rfloor+B]\cup[\lfloor q/4\rfloor-B,\lfloor q/4\rfloor+B]$ (integers modulo $q$).
--
--   **Formalization Note** If no residue is allowed (only when $q\le4B+2$, excluded for large $\lambda$ by valid parameters), the law is the point mass at $0$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, skEnc Step 1, p.21

import Mathlib
import Definitions.Def_MinSumClust_pexp
set_option autoImplicit false

namespace PPSLattice

/-- The law of one entry of `tg` in skEnc: uniform on the residues of `Z_q` that are not inside
`[−⌊q/4⌋ − B, −⌊q/4⌋ + B] ∪ [⌊q/4⌋ − B, ⌊q/4⌋ + B]` (as integers modulo `q`).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, skEnc Step 1, p.21 ("sample tg ← Z_q^λ subject to the constraint that each entry
of tg is not inside [−⌊q/4⌋−B, −⌊q/4⌋+B] ∪ [⌊q/4⌋−B, ⌊q/4⌋+B]. As q > λ^{ω(1)}B, the set of valid tg is
non-empty").

**Formalization Note.** If no residue is allowed (possible only when `q ≤ 4B + 2`, which valid parameters
exclude for all large `λ`), the law is the point mass at `0`. -/
noncomputable def tgLaw (q B : ℕ) : PMF (ZMod q) :=
  (MinSumClust.unifOr ((Finset.range q).filter fun v : ℕ =>
      ∀ z ∈ Finset.Icc (-((q / 4 : ℕ) : ℤ) - B) (-((q / 4 : ℕ) : ℤ) + B) ∪
          Finset.Icc (((q / 4 : ℕ) : ℤ) - B) (((q / 4 : ℕ) : ℤ) + B),
        z % (q : ℤ) ≠ (v : ℤ)) (0 : ℕ)).map fun v : ℕ => (v : ZMod q)

end PPSLattice



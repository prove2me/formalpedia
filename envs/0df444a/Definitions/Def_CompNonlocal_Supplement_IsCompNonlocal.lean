-- Prove2me | Definitions.Def_CompNonlocal_Supplement_IsCompNonlocal
-- name    : CompNonlocal_Supplement_IsCompNonlocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:07:38.506208+00:00
-- url     : https://prove2.me/theorems/39f4a0b2-b2f5-4e90-b284-8dc80aceb600
-- title:
--   Computationally nonlocal states (Definition 10)
-- statement:
--   A state $\omega$ is **computationally nonlocal** if it is $(c,s)$-computationally nonlocal for some $c,s:\mathbb N\to[0,1]$: some game is a $(c,s)$-certificate for $\omega$, with inverse-polynomial gap.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 10, p.25

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_IsCertificateK

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- Computationally nonlocal states. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 10, p.25: `ω` is `(c, s)`-computationally
nonlocal for some `c, s : ℕ → [0, 1]`, i.e. some game certifies it (`IsCertificateK`), with an
inverse-polynomial gap. -/
def IsCompNonlocal {nA nB : ℕ} (ω : Matrix (Bits nA × Bits nB) (Bits nA × Bits nB) ℂ) : Prop :=
  ∃ (G : Game) (cc s : ℕ → ℝ), IsCertificateK G ω cc s

end CompNonlocal.Supplement



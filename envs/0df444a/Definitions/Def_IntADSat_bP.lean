-- Prove2me | Definitions.Def_IntADSat_bP
-- name    : IntADSat_bP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:49.061556+00:00
-- url     : https://prove2.me/theorems/2eddc0ab-ebab-4699-b077-2f79b5cab498
-- title:
--   Class-size bound $b_p=\lceil 32(n/p+\sqrt n)\rceil$
-- statement:
--   For $n,p\in\mathbb N$,
--
--   $$
--   b_p=\Big\lceil 32\Big(\frac np+\sqrt n\Big)\Big\rceil ,
--   $$
--
--   the bound on degree-residue class sizes in Lemma S3.3 and in the proof of Theorem S3.1.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S3.3, p.36 (PDF 37) (also restated in the proof of Theorem S3.1, p.38)

import Mathlib

set_option autoImplicit false

namespace IntADSat

/-- The class-size bound `b_p = ⌈32(n/p + √n)⌉` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S3.3, p.36 (PDF 37)). -/
noncomputable def bP (n p : ℕ) : ℕ :=
  ⌈32 * ((n : ℝ) / p + Real.sqrt n)⌉₊

end IntADSat



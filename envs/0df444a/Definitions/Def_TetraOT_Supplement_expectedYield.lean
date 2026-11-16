-- Prove2me | Definitions.Def_TetraOT_Supplement_expectedYield
-- name    : TetraOT_Supplement_expectedYield
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:41:53.013226+00:00
-- url     : https://prove2.me/theorems/f142883b-fd1f-4b64-91f3-3bb9841c4de8
-- title:
--   The expected yield $\mathbb E[g(\rho)]$ of the Multi Tetrahedral Protocol
-- statement:
--   For $\rho$ uniform on $S_{4m}$ and hands of sizes $n_A, n_B$, the expected number of oblivious transfers produced is
--   $$\mathbb E[g(\rho)] = \frac{1}{(4m)!}\sum_{\rho\in S_{4m}} g(\rho),$$
--   where $g(\rho)$ is the size of the good set $G(\rho)$ of the Multi Tetrahedral Protocol.
--
--   **Formalization Note** A real number.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), §10.1, p.12; proof of Theorem 10.1, p.13; App. B, pp.16–17 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Supplement_multiRun

set_option autoImplicit false

namespace TetraOT.Supplement

/-- **The expected yield `𝔼[g(ρ)]` of the Multi Tetrahedral Protocol** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), §10.1, p.12, proof of
Theorem 10.1, p.13, and App. B, pp.16–17; p. = PDF page, the PDF has no printed page numbers): the
expected number `𝔼[g(ρ)]` of ½ROT instances produced when `ρ` is uniform on `S_n`, `n = 4m`, Alice holds
`nA` cards and Bob `nB` cards:
$$\mathbb E[g(\rho)] = \frac{1}{(4m)!}\sum_{\rho\in S_{4m}} g(\rho).$$

**Formalization Note.** A real number; `goodCount` is `g(ρ) = |G(ρ)|`, and `(4m)! = |S_{4m}|`. -/
noncomputable def expectedYield (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) : ℝ :=
  (∑ ρ : Equiv.Perm (Fin (4 * m)), (goodCount m nA nB h ρ : ℝ)) / (Nat.factorial (4 * m) : ℝ)

end TetraOT.Supplement



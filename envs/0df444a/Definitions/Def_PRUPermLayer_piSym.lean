-- Prove2me | Definitions.Def_PRUPermLayer_piSym
-- name    : PRUPermLayer_piSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:06.289512+00:00
-- url     : https://prove2.me/theorems/3a30d43e-7368-4282-8a87-42c07db2784c
-- title:
--   Symmetric-subspace projector $\Pi_{\mathrm{sym}} = (I + \mathrm{SWAP})/2$
-- statement:
--   On two registers with $N$ basis labels, $\Pi_{\mathrm{sym}} = \tfrac12(I + \mathrm{SWAP})$, with $\mathrm{SWAP}|x,y\rangle = |y,x\rangle$, is the orthogonal projector onto the symmetric subspace.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 2.7, p.11 (PDF p.13)

import Mathlib

namespace PRUPermLayer

/-- The projector `Π_sym = (I + SWAP)/2` onto the symmetric subspace of two registers with `N`
labels (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 2.7, p.11 (PDF p.13)), where `SWAP |x, y⟩ = |y, x⟩`. -/
noncomputable def piSym (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  (1 / 2 : ℂ) • (1 + Matrix.of fun p q => if p = (q.2, q.1) then 1 else 0)

end PRUPermLayer



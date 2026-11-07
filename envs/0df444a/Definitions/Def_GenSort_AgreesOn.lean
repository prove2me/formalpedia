-- Prove2me | Definitions.Def_GenSort_AgreesOn
-- name    : GenSort_AgreesOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:42.310137+00:00
-- url     : https://prove2.me/theorems/9df2fc1a-3c25-4309-a504-6a9ef898a63f
-- title:
--   A permutation agrees with the reported orientation of an edge
-- statement:
--   A permutation $\sigma$ **agrees with the reported orientation** of an edge $\{u, v\}$ if it orders $u, v$ as the hidden order $\pi$ does: $u \prec_\pi v$ implies $u \prec_\sigma v$. The coarse predictor $\sigma$ of §3.1 is any permutation that agrees with every sampled edge; one exists, since $\pi$ itself does.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.1, p.5 (PDF p.7)

import Mathlib

namespace GenSort

/-- **`σ` agrees with the reported orientation of the edge `e`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.1, p.5 (PDF p.7): "let σ
be any permutation of the vertices V which agrees with the reported orientation of every sampled
edge". The reported orientation of `e = {u, v}` is its orientation in the hidden order `π`. -/
def AgreesOn {n : ℕ} (π σ : Equiv.Perm (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ∀ u v : Fin n, e = s(u, v) → π.symm u < π.symm v → σ.symm u < σ.symm v

end GenSort



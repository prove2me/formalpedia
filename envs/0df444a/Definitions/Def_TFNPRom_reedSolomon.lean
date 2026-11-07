-- Prove2me | Definitions.Def_TFNPRom_reedSolomon
-- name    : TFNPRom_reedSolomon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:07.72793+00:00
-- url     : https://prove2.me/theorems/5cf8f106-19af-4581-bd3c-f3896db29f4f
-- title:
--   The Reed-Solomon code
-- statement:
--   For a finite field $F$ with $|F|=n+1$, an element $\gamma$ and $d\in\mathbb N$,
--   $$
--   \mathrm{ReedSolomon}_{F,\gamma,d}=\{c\in F^n : c_i=f(\gamma^{i-1}),\ f\in F[x],\ \deg f\le d\}.
--   $$
--
--   **Formalization Note** Coordinates are 0-based, so the paper's $\gamma^{i-1}$ is $\gamma^i$. The bound $\deg f\le d$ includes the zero polynomial.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…), §3.3, p.17

import Mathlib

namespace TFNPRom

open Classical in
/-- The Reed-Solomon code (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §3.3, p.17: "`ReedSolomon_{F,γ,d} := {c ∈ F^n | c_i = f(γ^{i-1}) where
`f ∈ F[x]` with `deg(f) ≤ d`}`", `|F| = n + 1`).

**Formalization Note** Coordinates are `Fin n` (0-based), so the paper's `γ^{i-1}` is `γ ^ i`.
`f.natDegree ≤ d` includes the zero polynomial, and is `deg f ≤ d` for every `d : ℕ`. -/
noncomputable def reedSolomon {F : Type} [Field F] [Fintype F] (γ : F) (d : ℕ) :
    Finset (Fin (Fintype.card F - 1) → F) :=
  Finset.univ.filter fun c =>
    ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ i : Fin (Fintype.card F - 1), c i = f.eval (γ ^ (i : ℕ))

end TFNPRom



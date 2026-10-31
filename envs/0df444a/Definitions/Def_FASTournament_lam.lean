-- Prove2me | Definitions.Def_FASTournament_lam
-- name    : FASTournament_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:21.816022+00:00
-- url     : https://prove2.me/theorems/ec4ef9fc-5fc2-4e4c-ac04-9cc8c1aaaf46
-- title:
--   $\lambda_w(G)$: maximum size of an FAS packing
-- statement:
--   Let $G=(V,A)$ be a digraph with a nonnegative integral weight $w(e)$ on each arc $e$. A collection $\mathcal F$ of FASs, **with repetition allowed**, is an **FAS packing** if each arc $e$ is used at most $w(e)$ times by the members of $\mathcal F$. Then
--   $$
--   \lambda_w(G)=\max\{|\mathcal F| : \mathcal F \text{ an FAS packing of } G\}.
--   $$
--   Always $\lambda_w(G)\le\mu_w(G)$.
--
--   **Formalization Note** A packing is a list of FASs (so members may repeat), and the number of members containing $e$ is counted with multiplicity. The value lies in $\mathbb N\cup\{\infty\}$ (`ℕ∞`): if $G$ has no directed cycle, $\emptyset$ is an FAS, arbitrarily many copies of it form a packing, and $\lambda_w(G)=\infty$.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsFAS

open Classical

namespace FASTournament

/-- **`λ_w(G)`, the maximum size of an FAS packing.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3: "A collection F of FAS's (with repetition allowed) is called an FAS packing of G if
each arc e is used at most w(e) times by the members of F. Let λw(G) be the maximum size of an
FAS packing".

An FAS packing is a finite list `F₁, …, F_r` of FASs of `G` (repetition allowed) such that every
arc `e` lies in at most `w(e)` of them, counted with multiplicity; `λ_w(G)` is the supremum of
`r` over all FAS packings.

**Formalization Note.** The value is in `ℕ∞`. If `G` has no directed cycle then `∅` is an FAS,
any number of copies of it is a packing, and `λ_w(G) = ⊤`. -/
noncomputable def lam {V : Type*} (G : Digraph V) (w : Arc G → ℕ) : ℕ∞ :=
  ⨆ (Fs : List (Finset (Arc G)))
    (_ : (∀ F ∈ Fs, IsFAS G F) ∧ ∀ e, Fs.countP (fun F => decide (e ∈ F)) ≤ w e),
    (Fs.length : ℕ∞)

end FASTournament



-- Prove2me | Definitions.Def_SmolenskyAC_UComplete
-- name    : SmolenskyAC_UComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:46.600107+00:00
-- url     : https://prove2.me/theorems/28c19948-86cf-4e4b-9eb9-2b1ca064b783
-- title:
--   $U^n_F$-complete elements and sets
-- statement:
--   Let $F$ be a field. A finite family $v_1,\dots,v_s\in U^n_F$ is **$U^n_F$-complete** if for every algebra $A\in\Omega^n_F$ and every $u\in U^n_F$
--
--   $$\deg_A(u)\le \frac n2+\max_i \deg_A(v_i).$$
--
--   A single element $v$ is complete when the one-element family is.
--
--   Complete families have low degree only in algebras of dimension about $2^{n-1}$ or less (Lemma 4), which is the paper's source of lower bounds.
--
--   **Formalization Note** Algebras are erased sets $E$, and the bound is stated as $2\deg_A(u)\le n+2\max_i\deg_A(v_i)$ in the natural numbers. An empty family has maximum $0$.
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, U^n_F-complete elements and sets, Definition, p.80 (pdf 4)

import Mathlib
import Definitions.Def_SmolenskyAC_CubeAlgebra

namespace SmolenskyAC

/-- A finite family `v_1, …, v_s ∈ U^n_F` is **`U^n_F`-complete** (Smolensky, STOC 1987,
Definition, p.80) if for every algebra `A ∈ Ω^n_F` and every `u ∈ U^n_F`,
`deg_A(u) ≤ n/2 + max_i deg_A(v_i)`. A single element `v` is the family indexed by `Unit`.

**Formalization Note.** Algebras are erased sets `E` (see `degOff`). The bound is stated as
`2 · deg_A(u) ≤ n + 2 · max_i deg_A(v_i)` in `ℕ`, which is the page's inequality with `n/2` a
rational number. Every `u ∈ U^n_F` is a polynomial (Proposition 1), so "any polynomial `u`" is
every function `u`. -/
def IsUComplete {F : Type*} [Field F] {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Cube n → F) :
    Prop :=
  ∀ (E : Finset (Cube n)) (u : Cube n → F),
    2 * degOff E u ≤ n + 2 * Finset.univ.sup (fun i => degOff E (v i))

end SmolenskyAC



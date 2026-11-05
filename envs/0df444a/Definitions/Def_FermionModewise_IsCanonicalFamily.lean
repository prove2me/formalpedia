-- Prove2me | Definitions.Def_FermionModewise_IsCanonicalFamily
-- name    : FermionModewise_IsCanonicalFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:08.357953+00:00
-- url     : https://prove2.me/theorems/f012eb2c-e567-412c-a1a7-4ec214e96795
-- title:
--   Canonical (Bogoliubov) family of modes obtained from $b$
-- statement:
--   Let $(b_j)_{j\in\mu}$ be a family of modes. A family $(c_i)_{i\in\mu}$ is a **canonical family obtained from $b$** if there are complex matrices $u,v$ with
--   $$c_i=\sum_{j\in\mu}\big(u_{ij}\,b_j+v_{ij}\,b_j^\dagger\big)\quad\text{for every } i,$$
--   and the $c_i$ again satisfy the canonical anticommutation relations.
--
--   This is the paper's "choice of mode basis $\tilde b_i=u_{ij}b_j+v_{ij}b_j^\dagger$ preserving the fermion anticommutation algebra". Applied to the modes of one side of a bipartition only, it expresses that a transformation is **local**.
--
--   **Formalization Note.** The new family has as many modes as the old one. Improper transformations (determinant $-1$ on the quadratures, e.g. $c=b^\dagger$) are allowed, as on p.4. The page prints $u_{ij}b_i$; the summation index is read as $j$.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, p.3 (mode basis before (4)); improper transformations p.4

import Mathlib
import Definitions.Def_FermionModewise_IsCAR

open Matrix

namespace FermionModewise

/-- **Canonical family of modes** (Botero–Reznik, arXiv:quant-ph/0404176v3, p.3: "a certain choice
of mode basis `b̃_i = u_ij b_j + v_ij b_j†` preserving the fermion anticommutation algebra"):
`c` is a canonical family obtained from `b` if every `c_i` is a linear combination of the
`b_j` and `b_j†`, and the `c_i` again satisfy the canonical anticommutation relations.

**Formalization Note.** The new family is indexed by the same mode type `μ` as the old one (as many
new modes as old). No restriction to proper (determinant `+1`) transformations is made: p.4 of the
paper admits improper ones. The page prints `u_ij b_i`; the summation index is read as `j`. -/
def IsCanonicalFamily {ι μ : Type} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    (b c : μ → Matrix ι ι ℂ) : Prop :=
  IsCAR c ∧ ∃ u v : Matrix μ μ ℂ, ∀ i, c i = ∑ j, (u i j • b j + v i j • (b j)ᴴ)

end FermionModewise



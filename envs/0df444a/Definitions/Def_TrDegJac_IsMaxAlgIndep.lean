-- Prove2me | Definitions.Def_TrDegJac_IsMaxAlgIndep
-- name    : TrDegJac_IsMaxAlgIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:30.835006+00:00
-- url     : https://prove2.me/theorems/37ab45f4-be0a-4783-be03-e6685ef2fd72
-- title:
--   Maximally algebraically independent subfamily
-- statement:
--   Let $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$. Polynomials $g_1,\dots,g_r$ are **algebraically dependent** over $\mathbb F$ if some non-zero $A\in\mathbb F[y_1,\dots,y_r]$ satisfies $A(g_1,\dots,g_r)=0$, and **algebraically independent** otherwise.
--
--   An index set $S\subseteq\{1,\dots,m\}$ is **maximally algebraically independent** for $f$ if the polynomials $(f_i)_{i\in S}$ are algebraically independent over $\mathbb F$ and no index set $T\supsetneq S$ has this property.
--
--   Maximality is with respect to inclusion, not size; that the two notions give subfamilies of the same size is Lemma 2.7. This is the "maximally algebraically independent subset" of Definition 2.6 and Theorem 4.12.
--
--   **Formalization Note** A subfamily is an index set `S : Finset (Fin m)`. If two entries of $f$ coincide, any index set containing both is dependent, so index sets and sets of polynomials define the same notion.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Definitions 2.3, 2.5, 2.6, pp.7–8; Theorem 4.12, p.29

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **Maximally algebraically independent subfamily** — Forbes and Staicu, *Approximating
Transcendence Degree in Medium Characteristic*, STOC 2027 submission (manuscript sha256
3ab72a42…), Definitions 2.3, 2.5 and 2.6, pp.7–8, and Theorem 4.12, p.29 ("any maximally
algebraically independent subset of f").

`IsMaxAlgIndep f S` says that the polynomials `(f i)_{i ∈ S}` are algebraically independent over
`F` (Definition 2.3: they have no non-zero annihilator in `F[y]`), and that no strictly larger index
set has this property.

**Formalization Note.** A family `f₁, …, f_m` is `f : Fin m → MvPolynomial (Fin n) F` and a
subfamily is an index set `S : Finset (Fin m)`. "Maximally" is maximality under inclusion, not
maximum size. If `f` has two equal entries, an index set containing both is dependent, so index
sets and sets of polynomials give the same notion. -/
def IsMaxAlgIndep {F : Type*} [Field F] {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) F)
    (S : Finset (Fin m)) : Prop :=
  AlgebraicIndependent F (fun i : S => f i) ∧
    ∀ T : Finset (Fin m), S ⊂ T → ¬ AlgebraicIndependent F (fun i : T => f i)

end TrDegJac



-- Prove2me | Definitions.Def_DiagLinesLDT_labelMap
-- name    : DiagLinesLDT_labelMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:52:51.660648+00:00
-- url     : https://prove2.me/theorems/d7a11379-c2e0-44bb-bd13-bbecee5badc6
-- title:
--   Label map $w(x,y)$, line-label space $S_\ell$, induced answers $h^\ell_\lambda$
-- statement:
--   For $(x,y)\in\mathbb F_q^2$ the **label map** is
--
--   $$w(x,y):=\big(1,y,y^2;\ xy^2,-2xy,x\big)\in\mathbb F_q^3\oplus\mathbb F_q^3.$$
--
--   For an axis-parallel line $\ell\subseteq\mathbb F_q^2$, the **line-label space** is $S_\ell:=\operatorname{span}_{\mathbb F_q}\{w(u):u\in\ell\}$, and each linear functional $\lambda\in S_\ell^*$ induces the line answer
--
--   $$h^\ell_\lambda:\ell\to\mathbb F_q,\qquad h^\ell_\lambda(u):=\lambda(w(u)).$$
--
--   The label is the new ingredient of the construction: points on a common axis-parallel line have labels with zero symplectic product, while points differing in both coordinates do not.
--
--   **Formalization Note** One map serves every characteristic: in characteristic two $-2xy=0$, which is the map of §7.2.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §4.2, p.6, §4.3, p.9, and §7.2, p.23

import Mathlib
import Definitions.Def_DiagLinesLDT_AxisLine
import Definitions.Def_DiagLinesLDT_Weyl

namespace DiagLinesLDT

variable {F : Type*} [Field F]

/-- The label map `w(x, y) := (1, y, y²; xy², -2xy, x)` with `x = u 0`, `y = u 1`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §4.2, p.6.

**Formalization Note** One map serves every characteristic: at characteristic two `-2xy = 0`, which is
§7.2's `w(x, y) = (1, y, y²; xy², 0, x)`. -/
def w (u : Fin 2 → F) : PS F :=
  (![1, u 1, u 1 ^ 2], ![u 0 * u 1 ^ 2, -2 * u 0 * u 1, u 0])

/-- The line-label space `S_ℓ := span_{𝔽_q} {w(u) : u ∈ ℓ}` (§4.3, p.9). -/
def lineSpan (ℓ : AxisLine F 2) : Submodule F (PS F) :=
  Submodule.span F (w '' ℓ.1)

/-- The label `w(u)` of a point of `ℓ`, as an element of `S_ℓ`. -/
def labelIn (ℓ : AxisLine F 2) (u : ℓ.1) : lineSpan ℓ :=
  ⟨w u.1, Submodule.subset_span ⟨u.1, u.2, rfl⟩⟩

/-- The induced line answer `h^ℓ_λ : ℓ → 𝔽_q`, `h^ℓ_λ(u) := λ(w(u))` (§4.3, p.9). -/
def inducedAnswer (ℓ : AxisLine F 2) (lam : Module.Dual F (lineSpan ℓ)) (u : ℓ.1) : F :=
  lam (labelIn ℓ u)

noncomputable instance [Fintype F] (ℓ : AxisLine F 2) : Fintype (lineSpan ℓ) :=
  Fintype.ofFinite _

noncomputable instance [Fintype F] (ℓ : AxisLine F 2) :
    Fintype (Module.Dual F (lineSpan ℓ)) :=
  have : Finite (Module.Dual F (lineSpan ℓ)) := Module.finite_of_finite F
  Fintype.ofFinite _

end DiagLinesLDT



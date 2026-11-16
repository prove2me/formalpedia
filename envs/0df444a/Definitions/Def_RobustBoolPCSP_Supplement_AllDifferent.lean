-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_AllDifferent
-- name    : RobustBoolPCSP_Supplement_AllDifferent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:22:45.62837+00:00
-- url     : https://prove2.me/theorems/f0c26e27-88e7-493a-9deb-fa8d84b0ab23
-- title:
--   The template $T_{\mathrm{AD}}$ and its soft-equality expansion
-- statement:
--   On $D_3=\{0,1,2\}$ let $\mathrm{AD}_3$ be the triples of pairwise distinct labels and $\mathrm{NAE}_3=D_3^3\setminus\{000,111,222\}$. The template is
--
--   $$T_{\mathrm{AD}}=(D_3,D_3;\mathrm{AD}_3,\mathrm{NAE}_3),$$
--
--   and $T_{\mathrm{AD}}^{=}$ adds soft equality.
--
--   The pair $T_{\mathrm{AD}}$, $T_{\mathrm{AD}}^{=}$ shows that soft equality changes the robustness exponent (Theorem 2.9).
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §2.3, p.11

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_Classes

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- `AD3`: triples over `D3 = {0,1,2}` (`Fin 3`) with pairwise distinct labels (p.11). -/
def AD3 : Set (Fin 3 → Fin 3) := {x | Function.Injective x}

/-- `NAE3 = D3³ \ {000, 111, 222}` (p.11): the triples that are not constant. -/
def NAE3 : Set (Fin 3 → Fin 3) := {x | ∃ i j, x i ≠ x j}

/-- The template **`T_AD = (D3, D3; AD3, NAE3)`**.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §2.3, p.11: "On D3 = {0, 1, 2}, let AD3 consist of triples of pairwise distinct labels
and NAE3 = D3³ \ {000, 111, 222}, and put TAD = (D3, D3; AD3, NAE3)."

**Formalization Note.** One ternary relation pair, index type `Unit`; `D3` is `Fin 3`. -/
def TAD : Template Unit (Fin 3) (Fin 3) := Template.single (k := 3) AD3 NAE3

/-- The soft-equality expansion `T_AD^=` (p.11), `withEq TAD`. -/
def TADEq : Template (Option Unit) (Fin 3) (Fin 3) := withEq TAD

end RobustBoolPCSP.Supplement



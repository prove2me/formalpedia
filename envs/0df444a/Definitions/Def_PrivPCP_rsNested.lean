-- Prove2me | Definitions.Def_PrivPCP_rsNested
-- name    : PrivPCP_rsNested
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:28.185216+00:00
-- url     : https://prove2.me/theorems/c70d4428-38f3-441d-9c17-6b4356b13247
-- title:
--   The punctured Reed–Solomon nested codes of §4.1
-- statement:
--   Given evaluation sets $S_i\subseteq\mathbb F_q$, constraint sets $H_i\subseteq\mathbb F_q$ and a degree profile $a=(a_1,\dots,a_k)$, the nested codes of §4.1 are
--   $$V_i=\mathrm{RS}(S_i,a_i+1),\qquad K_i=\{\mathrm{ev}_{S_i}(p):\ \deg p\le a_i,\ p|_{H_i}=0\},$$
--   and $U_i,W_i,C,E_i,K,B,D_i,D$ are formed from them as in the general set-up. By (4), $C$ is the evaluation code of the polynomials of individual degree at most $a$ and $K$ that of those vanishing on $D=\prod_i H_i$.
--
--   **Formalization Note** The standing assumptions of §4.1 ($|H_i|\ge 1$, $H_i\cap S_i=\emptyset$, $|H_i|\le a_i<|S_i|$) are hypotheses of the theorems that use these codes.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §4.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_GoodQLTC_rsCode
import Definitions.Def_PrivPCP_NestedCodes

namespace PrivPCP

/-- The code `K_i = {ev_{S_i}(p) : deg p ⩽ a_i, p|_{H_i} = 0} ⊆ F^{S_i}` of §4.1 (Bafna, Vyas, *Private PCPs
from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), §4.1, p.13): evaluations on `S` of
the polynomials of degree at most `a` vanishing on `H`. -/
noncomputable def vanishCode {F : Type} [Field F] (S H : Finset F) (a : ℕ) :
    Submodule F (↥(S : Set F) → F) :=
  (Polynomial.degreeLT F (a + 1) ⊓ ⨅ c ∈ H, LinearMap.ker (Polynomial.leval c)).map
    (GoodQLTC.evalOn (S : Set F))

/-- The **punctured Reed–Solomon nested codes of §4.1** (p.13): on the evaluation sets `S_i ⊆ F` with
constraint sets `H_i ⊆ F` and degree profile `a`, `V_i = RS(S_i, a_i + 1)` and
`K_i = {ev_{S_i}(p) : deg p ⩽ a_i, p|_{H_i} = 0}`. The spaces `U_i, W_i, C, E_i, K, B, D_i, D` are those of
`NestedCodes`.

**Formalization Note** §4.1's standing assumptions (`h_i = |H_i| ⩾ 1`, `H_i ∩ S_i = ∅`, `h_i ⩽ a_i < s_i`) are
hypotheses of the theorems that use this set-up; under them `0 ≠ K_i ⊊ V_i`. -/
noncomputable def rsNested {F : Type} [Field F] {k : ℕ} (S H : Fin k → Finset F) (a : Fin k → ℕ) :
    NestedCodes F (Fin k) (fun i => ↥((S i : Finset F) : Set F)) :=
  ⟨fun i => vanishCode (S i) (H i) (a i), fun i => GoodQLTC.rsCode ((S i : Finset F) : Set F) (a i + 1)⟩

end PrivPCP



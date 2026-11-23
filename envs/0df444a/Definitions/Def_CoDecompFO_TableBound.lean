-- Prove2me | Definitions.Def_CoDecompFO_TableBound
-- name    : CoDecompFO_TableBound
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:03:11.9648+00:00
-- url     : https://prove2.me/theorems/6eacb899-cf5f-4c95-97c8-8aaa74de28af
-- title:
--   Primitive recursive table bounds and canonical ranks of finite hypotheticals
-- statement:
--   For a finite relational signature σ, this module records the explicit table bound appearing in ¶5.82 and a canonical rank for finite hypotheticals.
--
--   The atom count is
--   $$q_\sigma(k)=\sum_{R\in\sigma}k^{\operatorname{ar}(R)},$$
--   and `tableBound σ w ℓ` is the published tower evaluated at $q_{\sigma^\circ}(2\ell)$. For a hypothetical H over Fin n, `hthCode H` is its position in the canonical finite enumeration of its type. Thus ranks are determined entirely by the hypothetical, independently of any input list.
--
--   **Formalization Note** These are the data for the numeric representation of reduced hypotheticals; proof that the tower is primitive recursive and bounds all the ranks uses Lemma 5.81 separately.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 5.81 and ¶5.82, p.41 (PDF p.43); proof of Theorem 1.16, p.41

import Mathlib
import Definitions.Def_CoDecompFO_HTh
import Definitions.Def_CoDecompFO_Codes
import Definitions.Def_CoDecompFO_Sig
set_option autoImplicit false
namespace CoDecompFO

/-- The number of atomic statements on `k` positions. -/
def atomCount (σ : Sig) (k : ℕ) : ℕ := ∑ i, k ^ σ.ar i

/-- The explicit bound of Lemma 5.81 on reduced `ℓ`-hypotheticals over a bag of width `w`. -/
def tableBound (σ : Sig) (w ℓ : ℕ) : ℕ := tower w (atomCount (sigmaEq σ) (2 * ℓ)) ℓ

open Classical in
/-- The rank of a hypothetical in the canonical finite enumeration of its finite type. -/
noncomputable def hthCode {σ : Sig} {n k m : ℕ} [Finite (HTh σ (Fin n) k m)]
    (H : HTh σ (Fin n) k m) : ℕ :=
  letI := Fintype.ofFinite (HTh σ (Fin n) k m)
  ((Fintype.equivFin (HTh σ (Fin n) k m)) H).val

end CoDecompFO



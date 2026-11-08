-- Prove2me | Definitions.Def_MaxCompForest_encOptIn
-- name    : MaxCompForest_encOptIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:30.7652+00:00
-- url     : https://prove2.me/theorems/1254bf05-08bd-46b0-9fcd-e20409e5680d
-- title:
--   Input of the physical mass-support optimizer
-- statement:
--   The input word of the optimizer of Lemma 3.5: the labelled graph with its conductances, $q$, $\gamma$, the rational factor $\mathbf F$, $\varepsilon_0$, $k$, $j$, in binary. Its length is the input length $L_F$ of (3.28).
--
--   **Formalization Note** The paper's $L_F$ also counts the actual degrees. They are sums of the conductances, of polynomially bounded length, and are not written separately.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.5, p.23

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_graphWords
import Definitions.Def_MaxCompForest_matWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The input word of Lemma 3.5**: the labelled quotient, `q`, `γ`, the factor (`r` and its entries),
`ε₀`, `k`, `j`, in binary. Its length is `L_F`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 3.5, p.23.

**Formalization Note.** The paper's `L_F` also counts the actual degrees. They are not written here: they
are sums of the conductances, of polynomially bounded length, and a machine reads them off the graph. -/
def encOptIn (I : RInst) (q : ℕ) (γ : ℚ) (r : ℕ) (F : Fin r → Fin I.n → ℚ) (ε₀ : ℚ) (k j : ℕ) :
    List Sym :=
  encWords (graphWords I ++ [encNat q, encRat γ, encNat r] ++ matWords F ++
    [encRat ε₀, encNat k, encNat j])

end MaxCompForest



-- Prove2me | Definitions.Def_MaxCompForest_physNode__7b4b7e
-- name    : MaxCompForest_physNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:09.450535+00:00
-- url     : https://prove2.me/theorems/7b4b7e3b-2c4c-4cd7-96c3-71d1cbc030dd
-- title:
--   One step of the physical recursion
-- statement:
--   One node of the physical recursion, at the forest $S$ of labels already included. Put $H=G/S$, $j=k-|S|$, $p_e=K^{(H)}_{ee}$ and $p_{\max}=\max_e p_e$. Then:
--
--   1. if $j=0$, return $S$;
--   2. if $j>|V(H)|-1$ or fewer than $j$ labels remain, discard the branch;
--   3. if at most $M_0$ labels remain, enumerate all $j$-subsets $J$, each giving the candidate $S\cup J$;
--   4. if $p_{\max}<\alpha$, stop at an all-low node; but if moreover $|V(H)|\le q$, enumerate its residual forests exactly;
--   5. otherwise let $\mathcal H=\{e:p_e\ge p_{\max}/j^2\}$. If $|\mathcal H|<M_0$, branch on the labels of $\mathcal H$; otherwise enumerate the $j$-subsets of the top $M_0$ labels by $p_e$.
--
--   **Formalization Note** Lemma E.2 is the procedure with $q=0$, and Lemma E.5 adds the small-quotient exit. The dependence on a fixed label order is only through ties in the prefix.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), proof of Lemma E.2, pp.38–39; Lemma E.5, p.40

import Mathlib
import Definitions.Def_MaxCompForest_PhysNode
import Definitions.Def_MaxCompForest_K
import Definitions.Def_MaxCompForest_topPrefix
import Definitions.Def_MaxCompForest_liftLabels
import Definitions.Def_MaxCompForest_IsForest
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

open Classical in
/-- **One node of the physical recursion at the included forest `S`**: the procedure in the proof of
Lemma E.2 (pp.38–39), with the small-quotient exit of Lemma E.5 (p.40). With `H = G/S`, `j = k − |S|`,
`p_e = K^(H)_ee`, `p_max = max_e p_e`:

* `j = 0`: return `S`;
* `j > |V(H)| − 1` or fewer than `j` labels remain: discard;
* at most `M0` labels remain: enumerate all `j`-subsets;
* `p_max < α`: an all-low node; but when `|V(H)| ≤ q`, enumerate its residual forests exactly (Lemma E.5);
* otherwise, with `𝓗 = {e : p_e ≥ p_max / j²}` (E.4): branch on `𝓗` if `|𝓗| < M0`, else enumerate the
  `j`-subsets of the top `M0` labels.

Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2).

**Formalization Note.** Lemma E.2 is this procedure at `q = 0`: no quotient has at most `0` vertices. The
statements are about this defined procedure, not about "some procedure". -/
noncomputable def physNode (G : WGraph V E) (k : ℕ) (α : ℝ) (M0 q : ℕ) (S : Finset E) :
    PhysNode E :=
  let H := contract G S
  let j := k - S.card
  let p : ContractE G S → ℝ := fun e => K H e e
  let pmax := ⨆ e, p e
  let out (A : Finset (Finset (ContractE G S))) : Finset (Finset E) :=
    A.image fun J => S ∪ liftLabels G S J
  if j = 0 then .terminal {S}
  else if Fintype.card (ContractV G S) - 1 < j ∨ Fintype.card (ContractE G S) < j then
    .terminal ∅
  else if Fintype.card (ContractE G S) ≤ M0 then
    .terminal (out (Finset.powersetCard j Finset.univ))
  else if pmax < α then
    if Fintype.card (ContractV G S) ≤ q then
      .terminal (out ((Finset.powersetCard j Finset.univ).filter (IsForest H)))
    else .allLow
  else if (Finset.univ.filter fun e => pmax / (j : ℝ) ^ 2 ≤ p e).card < M0 then
    .branch (liftLabels G S (Finset.univ.filter fun e => pmax / (j : ℝ) ^ 2 ≤ p e))
  else
    .terminal (out (Finset.powersetCard j (topPrefix p M0)))

end MaxCompForest



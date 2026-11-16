-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_wP
-- name    : AgnosticTNS_Supplement_wP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:33:18.846801+00:00
-- url     : https://prove2.me/theorems/58231cfc-5f4c-46a3-871f-4b9384e22e23
-- title:
--   MPS edge weights $w_P(\{v_i,v_{i+1}\})=\prod_{e\in\mathrm{cut}_G(\{v_1,\dots,v_i\})}w(e)$
-- statement:
--   For a graph $G$ with edge dimensions $w$ and a linear ordering $\pi$ with $v_i=\pi^{-1}(i)$, the labelled path $P^\pi_n$ carries the edge weights
--   $$
--   w_P(\{v_i,v_{i+1}\}) = \prod_{e\in\mathrm{cut}_G(\{v_1,\dots,v_i\})} w(e),\qquad i\in[n-1],
--   $$
--   with the empty product equal to $1$: the path bond between positions $i$ and $i+1$ carries the virtual indices of all original edges crossing the prefix cut.
--
--   **Formalization Note** With $0$-based positions, the path edge between positions $j$ and $j+1$ uses the prefix $\{v:\pi(v)\le j\}$, $j$ the smaller of its two endpoint positions.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.11, Eq. (6.14), p.52

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_pathOrd
import Definitions.Def_AgnosticTNS_cut

namespace AgnosticTNS.Supplement

/-- **The MPS edge weights** `w_P({v_i, v_{i+1}}) = ∏_{e ∈ cut_G({v_1, …, v_i})} w(e)`, Eq. (6.14),
p.52 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)); the empty product is `1`.

**Formalization Note** With 0-based positions, the path edge between positions `j` and `j + 1`
gets the product over the cut of the prefix `{v : π v ≤ j}`, `j` the smaller endpoint position. -/
noncomputable def wP {n : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ) (π : Equiv.Perm (Fin n)) :
    (pathOrd π).edgeSet → ℕ := fun f =>
  ∏ e ∈ cut G (Finset.univ.filter fun v =>
      π v ≤ Sym2.lift ⟨fun a b => min (π a) (π b), fun _ _ => min_comm _ _⟩ f.1), w e

end AgnosticTNS.Supplement



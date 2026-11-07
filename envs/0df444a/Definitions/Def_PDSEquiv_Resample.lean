-- Prove2me | Definitions.Def_PDSEquiv_Resample
-- name    : PDSEquiv_Resample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:36.581449+00:00
-- url     : https://prove2.me/theorems/c25db5e7-6840-4524-bca2-2cb3dcf8a8ce
-- title:
--   The vertex-resampling procedure $M_s$ and the noise operator $T_s$
-- statement:
--   For a graph $G$ on $[n]$ and $s\in[0,1]$, $H\sim M_s(G)$ is obtained by sampling $R\sim\mathrm{Bin}([n],s)$ and setting $H_{ij}=G_{ij}$ if $i,j\in R$ and $H_{ij}\sim\mathrm{Ber}(q)$ independently otherwise. For $w:\mathcal G_n\to[0,1]$,
--   $$(T_sw)(G)=\mathbb E_{H\sim M_s(G)}[w(H)].$$
--
--   This is the noise operator of the amplification step, Lemma 6.2.
--
--   **Formalization Note** Written as a finite sum over the retained sets $R$, with weight $s^{|R|}(1-s)^{n-|R|}$.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), §6.1, p.18

import Mathlib
import Definitions.Def_PDSEquiv_Laws

set_option autoImplicit false

namespace PDSEquiv

noncomputable section

/-!
# The vertex-resampling procedure `M_s` and the operator `T_s`

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), §6.1, p.18: `R ∼ Bin([n], s)`, `H_{ij} = G_{ij}` if `i, j ∈ R`, and
otherwise `H_{ij} ∼ Ber(q)` fresh. Written as a finite sum over `R`.
-/

/-- The mass of `H ∼ M_s(G)`, §6.1, p.18. -/
def resampleMass {n : ℕ} (q s : ℝ) (G H : Graph n) : ℝ :=
  ∑ R : Finset (Fin n), s ^ R.card * (1 - s) ^ (n - R.card) *
    ∏ e : Pair n,
      if e.1.1 ∈ R ∧ e.1.2 ∈ R then (if H e = G e then 1 else 0) else ber q (H e)

/-- `(T_s w)(G) = E_{H∼M_s(G)}[w(H)]`, §6.1, p.18. -/
def resampleT {n : ℕ} (q s : ℝ) (w : Graph n → ℝ) (G : Graph n) : ℝ :=
  ∑ H, resampleMass q s G H * w H

end

end PDSEquiv



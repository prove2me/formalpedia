-- Prove2me | Definitions.Def_DivideChooseBayes_qOfP
-- name    : DivideChooseBayes_qOfP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:21.487541+00:00
-- url     : https://prove2.me/theorems/9a728b53-5dde-45d5-a16d-3a2bda2f2a8f
-- title:
--   Auxiliary variables of a division: $q_i = 2p_i - 1$ (Eq. (1))
-- statement:
--   For a division $p\in[0,1]^n$ the auxiliary variables are
--
--   $$q_i := 2p_i-1 = p_i-(1-p_i),$$
--
--   the difference between the shares of good $i$ in pile 1 and in pile 2.
--
--   **Formalization Note** Used to read the output $p$ of Algorithm 1 in the variables $q$, on which the utilities of this development are defined.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, §3.1, p.6, Eq. (1)

import Mathlib

namespace DivideChooseBayes

/-- **Auxiliary variables of a division (Eq. (1)).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, §3.1, p.6, Eq. (1): `qᵢ := 2pᵢ − 1 = pᵢ − (1 − pᵢ)`.

**Formalization Note.** Used to read the output `p` of Algorithm 1 as a vector `q`, on which the
utilities of this development are defined. -/
noncomputable def qOfP {ι : Type*} (p : ι → ℝ) : ι → ℝ := fun i => 2 * p i - 1

end DivideChooseBayes



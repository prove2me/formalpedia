-- Prove2me | Definitions.Def_AgnosticTNS_TTN_state
-- name    : AgnosticTNS_TTN_state
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:17.381222+00:00
-- url     : https://prove2.me/theorems/0f5c006b-dad3-4684-81b4-e726cbc5aca8
-- title:
--   State of a tree tensor network
-- statement:
--   The state of a TTN description is the contraction
--   $$
--   \psi(x)=\sum_{j}\prod_{k}T_k\big(x|_{\text{qudits at }k},\,j_k,\,(j_c)_{c\text{ child of }k}\big),
--   $$
--   where each bond index $j_k$ is shared by node $k$ and its parent — the contraction (2.2) on the tree.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Eq. (2.2), p.12; Proposition 3.8, p.24

import Mathlib
import Definitions.Def_AgnosticTNS_TTN

namespace AgnosticTNS

/-- **The state of a tree tensor network**, the contraction (2.2), p.12, specialised to the TTN of
Proposition 3.8, p.24 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `ψ(x) = Σ_j Π_k T_k(x|_{site⁻¹ k}, j_k, (j_c)_{c child of k})`,
each bond index `j_k` shared by node `k` and its parent. -/
noncomputable def TTN.state {m n d : ℕ} (D : TTN m n d) : (Fin n → Fin d) → ℂ := fun x =>
  ∑ j : (k : Fin m) → Fin (D.bond k), ∏ k, D.tensor k (fun v => x v.1) (j k) (fun c => j c.1)

end AgnosticTNS



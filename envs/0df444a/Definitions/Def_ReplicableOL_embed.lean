-- Prove2me | Definitions.Def_ReplicableOL_embed
-- name    : ReplicableOL_embed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:21.368273+00:00
-- url     : https://prove2.me/theorems/17c27e16-4c85-402a-80da-e38f71c19ab9
-- title:
--   From bits to the loss sequence
-- statement:
--   The map from the block sequence to the loss sequence of Construction C: each of the first $kL$ rounds has $\ell_t=(B_t,1-B_t)$, and each trailing round has $\ell_t=(1/2,1/2)$. Under $P_\theta$ every loss sequence is almost surely of this form.
--
--   **Formalization Note** Round `t` (0-based) carries the bit `S (t / L) (t % L)` when `t / L < k`. The second conjunct of the guard only provides `L > 0`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_Bits

namespace ReplicableOL

/-- **From bits to the loss sequence.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. `ℓ_t := (B_t, 1 − B_t)` on the first `kL` rounds; the trailing rounds have `ℓ_t := (1/2, 1/2)`.

**Formalization Note.** Round `t` (0-based) carries the bit `S (t / L) (t % L)` when `t / L < k`. The second conjunct of the guard only provides `L > 0`. -/
noncomputable def embed (T k L : ℕ) (S : Bits k L) : Fin T → Fin 2 → ℝ :=
  fun t =>
    if h : t.val / L < k ∧ t.val % L < L then
      let B : ℝ := if S ⟨t.val / L, h.1⟩ ⟨t.val % L, h.2⟩ then 1 else 0
      ![B, 1 - B]
    else ![1 / 2, 1 / 2]

end ReplicableOL



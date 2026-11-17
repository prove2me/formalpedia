-- Prove2me | Definitions.Def_ReplicableOL_Supplement_anchorVal
-- name    : ReplicableOL_Supplement_anchorVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:17:47.962654+00:00
-- url     : https://prove2.me/theorems/ff1d12ab-cec6-48b7-9c00-d9fd46fc58fc
-- title:
--   Anchor values $\hat D^{(i)}_q$ of DALR
-- statement:
--   Let $(A_i)$ be a DALR chain and write $q_i(\tau)=\lfloor \tau/A_i\rfloor$. Put $\hat D^{(0)}\equiv0$. At the level-$i$ anchor $\tau=qA_i$, let $\pi=A_{i-1}q_{i-1}(\tau)$ be its parent (the current level-$(i-1)$ anchor) and set
--
--   $$
--   u^{(i)}_q=\hat D^{(i-1)}_{q_{i-1}(\tau)}+D_\tau-D_\pi,\qquad \hat D^{(i)}_q=r_{A_i,\omega_{i,q}}\big(u^{(i)}_q\big),
--   $$
--
--   computed for $i=1,\dots,K$ in turn. So each anchor rounds its parent's value plus the increment of the gap since the parent anchor, using its own fresh offset.
--
--   **Formalization Note** The level index is the paper's; the gap enters as a function $s\mapsto D_s$. The module also proves joint measurability in the gap function and the seed.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.1, p.18

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_roundTo
import Definitions.Def_ReplicableOL_Supplement_offset

namespace ReplicableOL.Supplement

/-- **Anchor values $\hat D^{(i)}_q$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.1, p.18. "put D̂^{(0)} :≡ 0. At the level-i anchor τ = qA_i, let π := A_{i−1}q_{i−1}(τ) be the current level-(i − 1) anchor (its parent) and set u^{(i)}_q := D̂^{(i−1)}_{q_{i−1}(τ)} + D_τ − D_π, D̂^{(i)}_q := r_{A_i,ω_{i,q}}(u^{(i)}_q)", with `q_i(τ) := ⌊τ/A_i⌋`.

**Formalization Note.** `anchorVal C D r i q` is `D̂^{(i)}_q` for the gap function `D` (`D s` = the paper's `D_s`) and the seed `r`; the level index `i` is the paper's. -/
noncomputable def anchorVal {T : ℕ} (C : Chain T) (D : ℕ → ℝ) (r : Seed C) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | i + 1, q =>
    roundTo (C.A (i + 1)) (offset C r i q)
      (anchorVal C D r i (q * C.A (i + 1) / C.A i) + D (q * C.A (i + 1))
        - D (C.A i * (q * C.A (i + 1) / C.A i)))

/-- Anchor values are jointly measurable in the gap function and the seed. -/
theorem measurable_anchorVal {T : ℕ} (C : Chain T) (i q : ℕ) :
    Measurable fun p : (ℕ → ℝ) × Seed C => anchorVal C p.1 p.2 i q := by
  induction i generalizing q with
  | zero => simp only [anchorVal]; exact measurable_const
  | succ i ih =>
    simp only [anchorVal, roundTo]
    have ho : Measurable fun p : (ℕ → ℝ) × Seed C => offset C p.2 i q :=
      (measurable_offset C i q).comp measurable_snd
    have hu : Measurable fun p : (ℕ → ℝ) × Seed C =>
        anchorVal C p.1 p.2 i (q * C.A (i + 1) / C.A i) + p.1 (q * C.A (i + 1))
          - p.1 (C.A i * (q * C.A (i + 1) / C.A i)) :=
      ((ih _).add ((measurable_pi_apply _).comp measurable_fst)).sub
        ((measurable_pi_apply _).comp measurable_fst)
    refine ho.add (measurable_const.mul ?_)
    have hf : Measurable fun p : (ℕ → ℝ) × Seed C =>
        ⌊(anchorVal C p.1 p.2 i (q * C.A (i + 1) / C.A i) + p.1 (q * C.A (i + 1))
          - p.1 (C.A i * (q * C.A (i + 1) / C.A i)) - offset C p.2 i q) / (C.A (i + 1) : ℝ)
          + 1 / 2⌋ :=
      Int.measurable_floor.comp (((hu.sub ho).div_const _).add_const _)
    exact (measurable_from_top (f := (Int.cast : ℤ → ℝ))).comp hf

end ReplicableOL.Supplement



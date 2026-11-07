-- Prove2me | Definitions.Def_GyoriLovasz_ShiftChain
-- name    : GyoriLovasz_ShiftChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:32.899736+00:00
-- url     : https://prove2.me/theorems/e0902c48-aaf2-44bb-97ab-d050cacce707
-- title:
--   Runs of the while loop of ShiftAssignment (Algorithm 3)
-- statement:
--   Fix $G$, $T$ and secondary edges $e_t$. A **shift chain** of length $n$ from $\varphi$ to $\varphi_1$ records $n$ iterations of the while loop of Algorithm 3: in each iteration every $e_t$ is critical for assigning some non-terminal $v_t$ to $\varphi(v_t)$ (so the exit test of line 4 fails), the labels $v_t$ are chosen (line 9), a directed cycle $\mathcal C$ of the reassignment graph is chosen (line 11), and $\varphi$ is shifted along $\mathcal C$ (line 12).
--
--   **Formalization Note** Every choice left free by the algorithm is an argument of the chain, so a statement over all chains covers every execution. The exit of lines 4–6 is used separately in `GLRun`.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Algorithm 3, p.25

import Mathlib
import Definitions.Def_GyoriLovasz_IsCritical
import Definitions.Def_GyoriLovasz_IsShift

namespace GyoriLovasz

/-- **The while loop of Algorithm 3 (ShiftAssignment).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Algorithm 3, lines 3–13, p.25.
`ShiftChain G T sec φ n φ₁`: starting from `φ`, the loop performs `n` shifts and reaches `φ₁`, with `G`, `T` and
the secondary edges `sec` fixed. Each shift records every free choice of the printed loop: the labels `v_t` of
line 9 (critical for assigning `v_t` to `φ(v_t)`, which also says that line 4's test failed), the cycle `C` of
line 11 and the shifted assignment of line 12.

**Formalization Note.** Stopping is not part of this relation: the exit of lines 4–6 is `IsNonCritical`, used in
`GLRun`. Hence `lemma_4_5_run` can bound every partial chain, on every sequence of choices. -/
inductive ShiftChain {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (sec : V → V × V) :
    (V → V) → ℕ → (V → V) → Prop
  | refl (φ : V → V) : ShiftChain G T sec φ 0 φ
  | step {φ φ' φ₁ : V → V} {n : ℕ} (v : V → V) (C : List V)
      (hv : ∀ t ∈ T, v t ∈ G.verts \ T ∧ IsCritical G T (sec t) (v t) (φ (v t)))
      (hC : IsShiftCycle T φ v C) (hs : IsShift φ v C φ')
      (h : ShiftChain G T sec φ' n φ₁) : ShiftChain G T sec φ (n + 1) φ₁

end GyoriLovasz



-- Prove2me | Definitions.Def_PopRAM_Meeting
-- name    : PopRAM_Meeting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:19.911456+00:00
-- url     : https://prove2.me/theorems/9f26d856-042b-4896-ac68-b27bd6cf1f3a
-- title:
--   Meetings of two agents under the random scheduler
-- statement:
--   Two agents $A$ and $x$ **meet** at step $t$ if the scheduled pair $\omega_t$ is $(A,x)$ or $(x,A)$. The **meeting time** of distinct agents $a,b$ is the number of interactions up to and including their first meeting ($\infty$ if they never meet). For agents $A$, $H$, $b$ and $m\in\mathbb N$, the event $\mathrm{HelperFirst}(A,H,b,m)$ holds when $A$ meets $H$ at least $m$ times before its first meeting with $b$.
--
--   These are the waiting events of the backup simulation: the leader $A$ waits for the agent holding a requested bit, and a helper $H$ counts its meetings with the leader to decide when input reading ends.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §C.2, p.33 (PDF p.34); proof of Lemma 10, p.34 (PDF p.35)

import Mathlib
import Definitions.Def_PopRAM_Protocol

set_option autoImplicit false

namespace PopRAM

/-! # Meetings of two agents on the bare scheduler

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), §C.2, p.33 (PDF p.34), before Fact 4, and the
proof of Lemma 10, p.34 (PDF p.35).

**Formalization Note** Agents `A` and `x` **meet** at step `t` when the scheduled pair `ω t` is
`(A, x)` or `(x, A)`: both orientations count, as the backup's leader rules "apply in both
interaction orientations" (p.30). `meetTime a b ω` is the number of interactions up to and including
the first meeting of `a` and `b` (`⊤` if they never meet). `HelperFirst A H b m ω` is the event that
`A` meets `H` at least `m` times before it first meets `b`. -/

/-- `A` and `x` interact (in either orientation) in the scheduled pair `p`. -/
def meets {n : ℕ} (A x : Fin n) (p : Pair n) : Bool :=
  decide (p.1 = (A, x) ∨ p.1 = (x, A))

/-- The number of interactions up to and including the first meeting of `a` and `b`. -/
noncomputable def meetTime {n : ℕ} (a b : Fin n) (ω : ℕ → Pair n) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : meets a b (ω t) = true), ((t + 1 : ℕ) : ℕ∞)

/-- `A` meets `H` `m` times before its first meeting with `b`: there is a time `t` such that among
the first `t` interactions exactly `m` are meetings of `A` and `H` and none is a meeting of `A` and
`b`. -/
def HelperFirst {n : ℕ} (A H b : Fin n) (m : ℕ) (ω : ℕ → Pair n) : Prop :=
  ∃ t : ℕ, ((Finset.range t).filter (fun s => meets A H (ω s) = true)).card = m ∧
    ∀ s < t, meets A b (ω s) = false

end PopRAM



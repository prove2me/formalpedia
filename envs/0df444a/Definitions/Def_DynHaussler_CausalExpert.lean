-- Prove2me | Definitions.Def_DynHaussler_CausalExpert
-- name    : DynHaussler_CausalExpert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:39.009772+00:00
-- url     : https://prove2.me/theorems/93ac2bca-03c8-4614-bc4f-ccedd61c2961
-- title:
--   Deterministic causal expert $g=(g_t)_{t=1}^T$, $g_t:X^t\to[0,1]$
-- statement:
--   A **deterministic causal expert** at horizon $T$ is a tuple $g=(g_t)_{t=1}^T$ of maps
--   $$
--   g_t:X^t\to[0,1].
--   $$
--   The prediction $g_t(x_{1:t})$ may use the current instance $x_t$ and all preceding instances; the expert receives no target values. For a fixed sequence $x_{1:T}$ write $g[x_{1:T}]=(g_t(x_{1:t}))_{t=1}^T$. No computability or measurability is imposed.
--
--   Finite families of such experts are the covers counted by the global dynamic covering number $N^{\mathrm{dyn}}_p$.
--
--   **Formalization Note** Rounds are 0-based: round $t$ (`t : Fin T`) is the paper's round $t+1$, and its prediction reads the first $t+1$ instances, given as a map `Fin (t + 1) → X`. The values are bundled in `Set.Icc 0 1`. The companion `CausalExpert.run g x` is the prediction vector $g[x_{1:T}]$.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Section 3.2, p.14 (PDF p.16)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- A **deterministic causal expert** at horizon `T`: a tuple `g = (g_t)_{t=1}^T` with
`g_t : X^t → [0, 1]`; the prediction `g_t(x_{1:t})` may use the current instance `x_t` and all
preceding instances, and receives no target values.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Section 3.2, p.14 (PDF p.16). No measurability is imposed (Section 3, p.13).

**Formalization Note** Rounds are 0-based: round `t : Fin T` is the paper's round `t + 1`, and
its prediction reads the first `t + 1` instances `x_{1:t+1}` (in the paper's indexing, `x_{1:t}`
at round `t`), given as a map `Fin (t + 1) → X`. The values are bundled in `Set.Icc 0 1`. -/
def CausalExpert (X : Type*) (T : ℕ) : Type _ :=
  (t : Fin T) → (Fin (t + 1) → X) → Set.Icc (0 : ℝ) 1

/-- The prediction vector `g[x_{1:T}] = (g_t(x_{1:t}))_{t=1}^T` of a causal expert on an instance
sequence `x`. -/
def CausalExpert.run {X : Type*} {T : ℕ} (g : CausalExpert X T) (x : Fin T → X) : Fin T → ℝ :=
  fun t => (g t (fun i => x (Fin.castLE (Nat.succ_le_of_lt t.isLt) i)) : ℝ)

end DynHaussler



-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_qKtChargeRho
-- name    : QuantumKtSoI_Supplement_qKtChargeRho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:38:25.657738+00:00
-- url     : https://prove2.me/theorems/01198130-adea-4eca-89eb-1ee07677efa2
-- title:
--   The charged measure $\mathrm{qKt}^{(c)}_\varrho$ at a general threshold (Definition 4.2)
-- statement:
--   For a real $c>0$, a real $\varrho\in(0,1]$ and strings $x,y$,
--   $$\mathrm{qKt}^{(c)}_\varrho(y|x)=\min_{e,t}\{|e|+c\lceil\log t\rceil : e\in\mathcal E,\ t\ge1,\ P_e(x;t,y)\ge\varrho\},$$
--   with $\mathrm{qKt}^{(c)}=\mathrm{qKt}^{(c)}_{2/3}$. The minimum exists, since below any feasible cost the costs take finitely many values.
--
--   The threshold form is needed for Definition 4.11 with $\mathrm{qKt}^{(c)}$ in place of $\mathrm{qKt}$, which Theorem F.3(a) uses through Corollary 4.15.
--
--   **Formalization Note** The base mission publishes the case $\varrho=2/3$ as `qKtCharge`; this is the same infimum with the threshold as a parameter, and the two agree at $2/3$ by definition.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 4.2, p.41

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- **Definition 4.2** (Charge `c`, p.41 of Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…) at a general threshold `ϱ ∈ (0, 1]`:
`qKt^{(c)}_ϱ(y | x) = min_{e,t} { |e| + c⌈log t⌉ : e ∈ E, t ≥ 1, P_e(x; t, y) ≥ ϱ }` for real `c > 0`.
The published `qKtCharge G c` is the case `ϱ = 2/3`.

**Formalization Note** As for the published `qKtCharge`: the minimum is the `sInf` of a set of reals
that is nonempty (by `LIT(y)`) and bounded below by `0`, and it is attained (p.41). -/
def qKtChargeRho (G : GlueRoutines) (c ϱ : ℝ) (y x : List Bool) : ℝ :=
  sInf {v : ℝ | ∃ e : Desc, ∃ t : ℕ, 1 ≤ t ∧ ϱ ≤ e.prob G x t y ∧
    v = (e.bits.length : ℝ) + c * (Nat.clog 2 t : ℝ)}

end QuantumKtSoI.Supplement



-- Prove2me | Definitions.Def_QIndInf_successProb
-- name    : QIndInf_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:29:03.509095+00:00
-- url     : https://prove2.me/theorems/3d05fe80-caab-436e-a619-07d0087b4731
-- title:
--   Success probability $\Pr_{i,x<i}[\mathrm{TD}(\mathcal L(\dots),\tau_{\le i|h<i})\le\epsilon]$
-- statement:
--   For a learner $\mathcal L$, parameters $s,t$, $\epsilon=1/a$, $\delta=1/b$, a source $\rho$ and instruments $\mathcal I_1,\dots,\mathcal I_m$, the **success probability** is the left-hand side of Eq. (56):
--
--   $$
--   \Pr_{\substack{i\leftarrow[m]\\ x_{<i}\leftarrow D^{\mathcal I,\rho}_{<i}}}\Big[\mathrm{TD}\big(\mathcal L(\mathsf{param},h_{<i},\mathcal I_i,\rho_{<i|h<i}),\tau_{\le i|h<i}\big)\le\epsilon\Big]
--   =\frac1m\sum_{i=1}^m\sum_{x_{<i}}D^{\mathcal I,\rho}_{<i}(x_{<i})\,\mathbf 1\big[\mathrm{TD}(\cdots)\le\epsilon\big],
--   $$
--
--   with $\mathrm{TD}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$: the round $i$ is uniform in $[m]$ and the past outcomes follow their law under the source.
--
--   **Formalization Note** Round $i$ is the index $i-1$ of `Fin m`; `prefK`, `prefI` extract the first $i$ instruments and their outcome counts. $\mathrm{TD}$ is $\tfrac12$ times the published `WildeQIT.traceDist` (which is the unnormalized $\|\cdot\|_1$). Histories of probability zero contribute zero. For $m=0$ the value is $0$.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), Definition 4.1, Eq. (56), p.19; notation p.14

import Mathlib
import Definitions.Def_QIndInf_Learner
import Definitions.Def_QIndInf_target
import Definitions.Def_WildeQIT_traceDist

set_option autoImplicit false

namespace QIndInf

open QAlgorithms QAlgorithms.CopyMeasurements

/-- Outcome counts of the first `j + 1` instruments of a sequence of `m` instruments. -/
def prefK {m : ℕ} (k : Fin m → ℕ) (j : Fin m) : Fin (j.val + 1) → ℕ :=
  fun l => k (Fin.castLE (Nat.succ_le_of_lt j.isLt) l)

/-- The first `j + 1` instruments `(I₁, …, I_{j+1})` of a sequence `(I₁, …, I_m)`. -/
def prefI {n m : ℕ} {k : Fin m → ℕ} (I : (j : Fin m) → QuantumInstrument (Reg n) (Fin (k j)))
    (j : Fin m) : (l : Fin (j.val + 1)) → QuantumInstrument (Reg n) (Fin (prefK k j l)) :=
  fun l => I (Fin.castLE (Nat.succ_le_of_lt j.isLt) l)

/-- **Success probability of a learner** (the left side of Eq. (56)):
`Pr_{i ← [m], x<i ← D^{I,ρ}_{<i}} [ TD(L(param, h<i, I_i, ρ_{<i|h<i}), τ_{≤i|h<i}) ≤ ε ]`, with
`i` uniform in `[m]` and the past outcomes distributed as `D^{I,ρ}_{<i}` (Eq. (52)).

arXiv:2609.36912 (PDF of 2026-11-02), Definition 4.1, Eq. (56), p.19; notation p.14
(`TD(ρ,σ) := ½‖ρ − σ‖₁`).

**Formalization Note.**
* Round `i ∈ [m]` of the paper is `j = i − 1 : Fin m`; its past outcomes range over
  `(l : Fin j) → Fin (k l)`, each weighted by `outcomeProb` (Eq. (52)), and the rounds are
  weighted `1/m`.
* `TD = ½ · WildeQIT.traceDist` (the published `traceDist` is the unnormalized `‖·‖₁`).
* `ε = 1/a`; the parameters `s, t, n, a, b` are passed to the learner (`δ = 1/b`).
* The learner's input is `condPast` (Eq. (53)) and the target is `target` (Eq. (55)). Histories
  of probability zero contribute zero. -/
noncomputable def successProb (L : Learner) (s t a b : ℕ) {n m : ℕ} (ρ : QuantumProcess n)
    (k : Fin m → ℕ) (I : (j : Fin m) → QuantumInstrument (Reg n) (Fin (k j))) : ℝ :=
  (1 / (m : ℝ)) * ∑ j : Fin m, ∑ x : (l : Fin j.val) → Fin (prefK k j l.castSucc),
    outcomeProb ρ.state (pastInstr (prefI I j)) x *
      (if (1 / 2 : ℝ) * WildeQIT.traceDist
            (L.run s t n a b j.val (prefK k j) (prefI I j) x
              (condPast ρ.state (pastInstr (prefI I j)) x))
            (target ρ.state (prefI I j) x) ≤ 1 / (a : ℝ)
        then 1 else 0)

end QIndInf



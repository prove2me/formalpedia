-- Prove2me | Definitions.Def_TorchFire_CGS_telegraphWinProb
-- name    : TorchFire_CGS_telegraphWinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:43:37.411422+00:00
-- url     : https://prove2.me/theorems/d70d5803-9b9f-40b4-9f7a-bb3b17f6cc34
-- title:
--   CGS fire: verification and cloning correctness (16)–(17) and the game $\mathrm{TELEGRAPH}^{\mathrm{Fire}}$
-- statement:
--   The experiments of Definitions 4.16 and 4.17 for Construction 4.22 at security parameter $\mu$.
--
--   1. **Verification correctness** (16): sample the oracles, $pk=s\leftarrow\{0,1\}^\mu$, a flame $|K\rangle\langle K|$, and run $\mathrm{Fire.Ver}^O(pk,s,F)$.
--   2. **Cloning correctness** (17): after spark, execute $(F_{i-1},F_i)\leftarrow\mathrm{Fire.Clone}^O(pk,s,F_{i-1})$ for $i=1,\dots,q$ and check all $q+1$ flames.
--   3. **$\mathrm{TELEGRAPH}^{\mathrm{Fire}}$** (Definition 4.17), in normal form: shared classical randomness $r$ with an adversary-chosen distribution, independent of the oracles and setup; $A_1$ receives $v$ spark flames; $A_2$ (on input $pk,r$) measures and sends a classical $M$; $A_1$ (on $M$, its flames) sends a classical $L$; $A_2$ outputs a serial $s^*$ and a flame $F^*$; the challenger accepts iff $\mathrm{Fire.Ver}^O(pk,s^*,F^*)=1$. All parties query the public collection (26), and the total number of queries is bounded.
--
--   **Formalization Note** Each party starts from $|0\rangle$ and prepares its initial state from $r$, so the joint initial state is a finite mixture of product states, i.e. separable with shared classical randomness (paper.md decision 5). Issuing the $v$ spark flames at the start simulates any adaptive schedule.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Definition 4.16 (16)–(17) p.25; Definition 4.17 (18) pp.25–26

import Mathlib
import Definitions.Def_TorchFire_CGS_verEffect
import Definitions.Def_TorchFire_CGS_cloneChan
import Definitions.Def_TorchFire_Model_OracleAlg
import Definitions.Def_TorchFire_Model_thresholdEffect

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.CGS

/-- **Verification correctness probability** (16), Definition 4.16, p.25 (Chatterjee–Mukherjee–
Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256
4e43d2f2…afd593): sample `O ← Fire.GenOracles(1^µ)` (Construction 4.18), `(pk, sk) ←
Fire.Setup^O(1^µ)` (`pk = s ← {0,1}^µ`), `(s, F) ← Fire.Spark^O(sk)` (the flame `|K⟩⟨K|`) and run
`Fire.Ver^O(pk, s, F)`. -/
noncomputable def verCorr (mu : ℕ) : ℝ :=
  avg (Sample mu) fun ω => avg (Bits (hl mu)) fun pk => accProb (verEffectKey ω pk pk) (flame ω)

/-- **Cloning correctness probability** (17), Definition 4.16, p.25: after `(s, F_0) ←
Fire.Spark^O(sk)`, execute `(F_{i−1}, F_i) ← Fire.Clone^O(pk, s, F_{i−1})` for `i = 1, …, q` (the
first returned flame replaces the input register), and check `Fire.Ver^O(pk, s, F_i)` for
`i = 0, …, q`. The probability that all `q + 1` checks accept. -/
noncomputable def cloneCorr (mu q : ℕ) : ℝ :=
  avg (Sample mu) fun ω => avg (Bits (hl mu)) fun pk =>
    accProb
      (Matrix.of fun (x y : (Fin q → KReg mu) × KReg mu) =>
        (∏ i, verEffectKey ω pk pk (x.1 i) (y.1 i)) * verEffectKey ω pk pk x.2 y.2)
      (chain (cloneKey ω pk pk) (flame ω) q)

/-- **An adversary pair for `TELEGRAPH^Fire`** (Definition 4.17, pp.25–26), in the normal form of
paper.md decision 5. `Rnd` is the shared classical randomness, with distribution `dist`, sampled
independently of the oracles and setup; each party starts from `|0⟩` and prepares its own initial
state from it, so the initial joint state is separable (a finite mixture of product states). With
`v` spark flames (all issued to `A_1` at the start):

* `A2a`: `A_2` on input `pk, r`; it measures its message `M` and keeps a register `Ret2`;
* `A1`: `A_1` on input `pk, r`, the serials, and `M`, acting on the `v` flames; it outputs `L`;
* `A2b`: `A_2` on input `pk, r, M, L`, acting on `Ret2`; it outputs a serial `s*` and a flame `F*`.

All three query the public collection (26). No quantum register passes between the parties. -/
structure TelegraphAdv (mu v : ℕ) where
  Rnd : Type
  [instFRnd : Fintype Rnd]
  dist : Rnd → ℝ
  dist_nonneg : ∀ x, 0 ≤ dist x
  dist_sum : ∑ x, dist x = 1
  Msg1 : Type
  [instFMsg1 : Fintype Msg1]
  [instDMsg1 : DecidableEq Msg1]
  Msg2 : Type
  [instFMsg2 : Fintype Msg2]
  [instDMsg2 : DecidableEq Msg2]
  Ret2 : Type
  [instFRet2 : Fintype Ret2]
  [instDRet2 : DecidableEq Ret2]
  A2a : Bits (hl mu) → Rnd → OracleAlg Unit (Msg1 × Ret2) (PubDom mu) (PubAns mu)
  A1 : Bits (hl mu) → Rnd → (Fin v → Bits (hl mu)) → Msg1 →
    OracleAlg (Fin v → KReg mu) Msg2 (PubDom mu) (PubAns mu)
  A2b : Bits (hl mu) → Rnd → Msg1 → Msg2 →
    OracleAlg Ret2 (Bits (hl mu) × KReg mu) (PubDom mu) (PubAns mu)

attribute [instance] TelegraphAdv.instFRnd TelegraphAdv.instFMsg1 TelegraphAdv.instDMsg1
  TelegraphAdv.instFMsg2 TelegraphAdv.instDMsg2 TelegraphAdv.instFRet2 TelegraphAdv.instDRet2

variable {mu v : ℕ}

/-- The total number of queries of both parties over the whole experiment, for every value of their
classical inputs, is at most `Q` (Definition 4.17: "polynomially many queries to `O` in total, across
both parties and the entire experiment"). -/
def TelegraphAdv.QueryBounded (A : TelegraphAdv mu v) (Q : ℕ) : Prop :=
  ∀ pk x ser m l, (A.A2a pk x).T + (A.A1 pk x ser m).T + (A.A2b pk x m l).T ≤ Q

/-- **`Pr[TELEGRAPH^Fire_{A^O}(1^µ) = 1]`** (Definition 4.17, (18)): the challenger samples the
oracles and `pk`; `A_1` receives `v` spark flames `(s, |K⟩⟨K|)` (with `s = pk`); `A_2` sends `M`, `A_1`
sends `L`, `A_2` outputs `(s*, F*)`; the challenger accepts iff `Fire.Ver^O(pk, s*, F*) = 1`. -/
noncomputable def telegraphWinProb (A : TelegraphAdv mu v) : ℝ :=
  avg (Sample mu) fun ω => avg (Bits (hl mu)) fun pk =>
    ∑ x : A.Rnd, A.dist x *
      let O := pubOracle ω
      let σ2 := (A.A2a pk x).run O (1 : Matrix Unit Unit ℂ)
      ∑ m : A.Msg1, ∑ l : A.Msg2,
        ((A.A1 pk x (fun _ => pk) m).run O (piKron fun _ => flame ω) l l).re *
          ∑ s : Bits (hl mu),
            accProb (verEffectKey ω pk s) (block ((A.A2b pk x m l).run O (block σ2 m)) s)

end TorchFire.CGS



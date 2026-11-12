-- Prove2me | Definitions.Def_TorchFire_TF_telegraphWinProb
-- name    : TorchFire_TF_telegraphWinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:47:23.472198+00:00
-- url     : https://prove2.me/theorems/991da1e5-75c7-46dc-a2a0-4e2a0aaf12f6
-- title:
--   The untelegraphability game $\mathrm{TELEGRAPH}^{\mathrm{TF}}$ (Definition 6.4)
-- statement:
--   **Definition 6.4** in normal form. Shared classical randomness $r$ (an adversary-chosen distribution, independent of the oracles and setup) fixes disjoint torch sets $J_1(r),J_2(r)\subseteq[R]$. $A_1$ receives $(T_j)_{j\in J_1}$ and $v$ spark flames; $A_2$ receives $(T_j)_{j\in J_2}$. $A_2$ measures and sends a classical message $M$; $A_1$, using $M$ and its state, sends a classical $L$; $A_2$, using $L$ and its retained state, outputs a serial $s^*$ and a flame $F^*$. The challenger outputs $\mathrm{TF.Ver}^O(pk,s^*,F^*)$; a setup abort counts as $0$. Both parties query the full public collection (47); the total number of queries over both parties and the whole experiment is bounded.
--
--   **Formalization Note** Each party starts from $|0\rangle$ and prepares its initial state from $r$; a finite separable state is a finite mixture of product states, so this realizes every separable initial state with shared classical randomness (paper.md decision 5). Nothing quantum passes between the parties.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Definition 6.4 (35) pp.46–47; Theorem 7.8 (59) p.57

import Mathlib
import Definitions.Def_TorchFire_TF_cloneTF
import Definitions.Def_TorchFire_Model_OracleAlg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- **An adversary pair `A^O = (A^O_1, A^O_2)` for `TELEGRAPH^TF`** (Definition 6.4, pp.46–47), in the
normal form of paper.md decision 5, with `v` spark flames. `Rnd` is the shared classical randomness
(distribution `dist`), independent of the oracles and setup; each party starts from `|0⟩` and prepares
its own initial state from it, so the initial joint state is separable. The disjoint torch sets
`J_1(r), J_2(r) ⊆ [R]` are chosen from it.

* `A2a`: `A_2` on `T_{J_2}`; it measures its message `M` and keeps `Ret2`;
* `A1`: `A_1` on `T_{J_1}` and the `v` flames (classical input: `r`, the serials, `M`); it outputs `L`;
* `A2b`: `A_2` on `Ret2` (classical input `r, M, L`); it outputs a serial `s*` and a flame `F*`.

All three query the full public collection (47). No quantum register passes between the parties.
`pk = R` is a constant. -/
structure TelegraphAdv (lam R v : ℕ) where
  Rnd : Type
  [instFRnd : Fintype Rnd]
  dist : Rnd → ℝ
  dist_nonneg : ∀ x, 0 ≤ dist x
  dist_sum : ∑ x, dist x = 1
  J1 : Rnd → Finset (Fin R)
  J2 : Rnd → Finset (Fin R)
  disjoint : ∀ x, Disjoint (J1 x) (J2 x)
  Msg1 : Type
  [instFMsg1 : Fintype Msg1]
  [instDMsg1 : DecidableEq Msg1]
  Msg2 : Type
  [instFMsg2 : Fintype Msg2]
  [instDMsg2 : DecidableEq Msg2]
  Ret2 : Type
  [instFRet2 : Fintype Ret2]
  [instDRet2 : DecidableEq Ret2]
  A2a : (x : Rnd) →
    OracleAlg (Fin (J2 x).card → AReg lam) (Msg1 × Ret2) (PubDom lam R) (PubAns lam)
  A1 : (x : Rnd) → (Fin v → Serial lam) → Msg1 →
    OracleAlg ((Fin (J1 x).card → AReg lam) × (Fin v → Flame lam)) Msg2 (PubDom lam R)
      (PubAns lam)
  A2b : Rnd → Msg1 → Msg2 →
    OracleAlg Ret2 (Serial lam × Flame lam) (PubDom lam R) (PubAns lam)

attribute [instance] TelegraphAdv.instFRnd TelegraphAdv.instFMsg1 TelegraphAdv.instDMsg1
  TelegraphAdv.instFMsg2 TelegraphAdv.instDMsg2 TelegraphAdv.instFRet2 TelegraphAdv.instDRet2

variable {lam R v : ℕ}

/-- The total number of queries over both parties and the whole experiment is at most `Q`, for every
value of the classical inputs (Definition 6.4: "polynomially many queries to `O` in total"). -/
def TelegraphAdv.QueryBounded (A : TelegraphAdv lam R v) (Q : ℕ) : Prop :=
  ∀ x ss m l, (A.A2a x).T + (A.A1 x ss m).T + (A.A2b x m l).T ≤ Q

/-- **`Pr[TELEGRAPH^TF_{A^O}(1^λ, 1^R) = 1]`** (Definition 6.4, (35); (59), p.57): setup (an abort
counts as output `0`); `A_1` gets `T_{J_1}` and `v` spark flames, `A_2` gets `T_{J_2}`; `A_2` sends `M`,
`A_1` sends `L`, `A_2` outputs `(s*, F*)`; the challenger accepts iff `TF.Ver^O(pk, s*, F*) = 1`. -/
noncomputable def telegraphWinProb (A : TelegraphAdv lam R v) : ℝ :=
  avg (Sample lam R) fun ω =>
    if SetupOK ω then
      ∑ x : A.Rnd, A.dist x *
        let O := pubOracle ω
        let σ2 := (A.A2a x).run O (torchesOf ω (A.J2 x) rfl)
        ∑ ss : Fin v → Serial lam, ∑ mm : A.Msg1, ∑ ll : A.Msg2,
          ((A.A1 x ss mm).run O
              (Matrix.of fun p q => torchesOf ω (A.J1 x) rfl p.1 q.1 *
                piKron (fun j => block (sparkCQ ω) (ss j)) p.2 q.2) ll ll).re *
            ∑ s : Serial lam,
              accProb (verEff ω s) (block ((A.A2b x mm ll).run O (block σ2 mm)) s)
    else 0

end TorchFire.TF



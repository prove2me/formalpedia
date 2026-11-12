-- Prove2me | Definitions.Def_TorchFire_TF_splitWinProb
-- name    : TorchFire_TF_splitWinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:46:41.9673+00:00
-- url     : https://prove2.me/theorems/37d06788-8388-4245-9ab6-b3a247abada1
-- title:
--   The global non-proliferation game $\mathrm{SPLIT}^{\mathrm{TF}}$ (Definition 6.2), its ideal version, and $\varepsilon_\beta$
-- statement:
--   **Definition 6.2** in normal form. An adversary $(A_0,A_1,\dots,A_N)$ with $v$ pre-split sparks consists of: a first stage of $A_0$ on the $v$ flames (with their serials) that measures a torch request $J\subseteq[R]$, $|J|=m$; a second stage of $A_0$ on its retained register and $(T_j)_{j\in J}$ that outputs registers $B_1,\dots,B_N$ whose joint state may be arbitrarily entangled; and parties $A_i$ that act on $B_i$ and the challenge flame $F_i$ (with the challenge serials as classical input) and return two flames. All stages and parties query the full public collection (47).
--
--   The challenger checks $b_{i,a}\leftarrow\mathrm{TF.Ver}^O(pk,s_i,F'_{i,a})$, sets $X_i=b_{i,0}b_{i,1}$, and the game outputs $1$ iff $\sum_iX_i\ge m+1$. Because the parties act on disjoint registers,
--   $$\Pr[\mathrm{SPLIT}=1]=\mathbb E\,\mathrm{Tr}\big(T_{m+1}(Z_1,\dots,Z_N)\,\rho\big),$$
--   with $Z_i$ the local acceptance effect of party $i$ and $\rho$ the joint input after challenge issuance. A setup abort counts as output $0$. The **ideal** experiment also declares failure if two of the $v+N$ labels coincide (62).
--
--   The module also defines, for §8.2, the computation at each location built from party $i$, the witness-sampler effect $E_i$ for a common bound $q$ on the query positions (padding positions contribute $0$), and
--   $$\varepsilon_\beta=\sum_{i=1}^N\mathbb E\big[\mathrm{Tr}(C_iL_i\rho_iL_iC_i^\dagger)\big],\qquad L_i=(I-E_i)^\beta,$$
--   with $C_i^\dagger C_i$ the acceptance effect of party $i$ with $\Gamma$ replaced by $\Gamma^0_i$ (71).
--
--   **Formalization Note** Issuing all $v$ flames at the start simulates any adaptive schedule of at most $v$ spark queries, and the torch request "at any one point" becomes the measured $J$ between the two stages (paper.md decision 4). $pk=R$ is a constant.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Definition 6.2 pp.45–46; §8 p.58, (62); §8.2 pp.69–71, (71)

import Mathlib
import Definitions.Def_TorchFire_TF_cloneTF
import Definitions.Def_TorchFire_Model_OracleAlg
import Definitions.Def_TorchFire_Model_LocalComp

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- A torch request `J ⊆ [R]` with `|J| = m` (Definition 6.2 step 2, p.45). -/
abbrev TorchSet (R m : ℕ) : Type := {J : Finset (Fin R) // J.card = m}

/-- **An adversary `A^O = (A^O_0, A^O_1, …, A^O_N)` for `SPLIT^TF`** (Definition 6.2, pp.45–46), in
the normal form of paper.md decision 4, with `v` pre-split spark flames:

* `st1`: the first stage of `A_0`, with classical input the `v` serials and quantum input the `v`
  flames; it measures a torch request `J` (`|J| = m`) and keeps a register `Ret1`;
* `st2`: the second stage of `A_0`, depending on the serials and `J`, acting on `Ret1` and the torches
  `(T_j)_{j ∈ J}`; it outputs the registers `B_1, …, B_N`, whose joint state may be arbitrarily
  entangled;
* `party i`: the party `A_i`, with classical input the challenge serials `(s_1, …, s_N)` and quantum
  input `B_i` and its challenge flame `F_i`; it returns two flame registers `(F′_{i,0}, F′_{i,1})`.

All stages and parties query the full public collection (47), including `Γ`. No other torch or flame
is supplied, and the parties act on disjoint registers (no communication after the split).

**Formalization Note** Spark answers do not depend on the adversary, so issuing the `v` flames at the
start simulates any adaptive schedule of at most `v` spark queries, and the torch request "at any one
point" becomes the single measured `J` between the two stages (paper.md decision 4). `pk = R` is a
constant and is not passed explicitly. -/
structure SplitAdv (lam R m N v : ℕ) where
  Ret1 : Type
  [instFRet1 : Fintype Ret1]
  [instDRet1 : DecidableEq Ret1]
  B : Fin N → Type
  [instFB : ∀ i, Fintype (B i)]
  [instDB : ∀ i, DecidableEq (B i)]
  st1 : (Fin v → Serial lam) →
    OracleAlg (Fin v → Flame lam) (TorchSet R m × Ret1) (PubDom lam R) (PubAns lam)
  st2 : (Fin v → Serial lam) → TorchSet R m →
    OracleAlg (Ret1 × (Fin m → AReg lam)) ((i : Fin N) → B i) (PubDom lam R) (PubAns lam)
  party : (i : Fin N) → (Fin N → Serial lam) →
    OracleAlg (B i × Flame lam) (Flame lam × Flame lam) (PubDom lam R) (PubAns lam)

attribute [instance] SplitAdv.instFRet1 SplitAdv.instDRet1 SplitAdv.instFB SplitAdv.instDB

variable {lam R m N v : ℕ}

/-- Every stage of `A_0` and every party makes at most `Q` queries, for every value of its classical
input. -/
def SplitAdv.QueryBounded (A : SplitAdv lam R m N v) (Q : ℕ) : Prop :=
  (∀ ss, (A.st1 ss).T ≤ Q) ∧ (∀ ss J, (A.st2 ss J).T ≤ Q) ∧ (∀ i ss', (A.party i ss').T ≤ Q)

/-- The pre-split computation `A_0` makes at most `Q_pre` queries in total (§8, p.58). -/
def SplitAdv.PreBounded (A : SplitAdv lam R m N v) (Qpre : ℕ) : Prop :=
  ∀ ss J, (A.st1 ss).T + (A.st2 ss J).T ≤ Qpre

/-- **The joint input `ρ` of the parties after challenge issuance**, for fixed oracles, pre-split
serials `ss` and challenge serials `ss'` (the unnormalized branch, carrying the spark
probabilities): `A_0` runs on the `v` flames with the oracle `preO` (the public collection, or a
modified one in Lemma 8.3), measures `J`, receives `(T_j)_{j ∈ J}`, outputs `B_1 ⋯ B_N`; then party `i`
receives its challenge flame `F_i`. The state lives on `⨂_i (B_i ⊗ F_i)`. -/
noncomputable def splitInput (A : SplitAdv lam R m N v) (ω : Sample lam R)
    (preO : PubDom lam R → PubAns lam) (ss : Fin v → Serial lam) (ss' : Fin N → Serial lam) :
    Matrix ((i : Fin N) → A.B i × Flame lam) ((i : Fin N) → A.B i × Flame lam) ℂ :=
  let ρF : Matrix (Fin v → Flame lam) (Fin v → Flame lam) ℂ :=
    piKron fun j => block (sparkCQ ω) (ss j)
  let σ1 := (A.st1 ss).run preO ρF
  let σB : Matrix ((i : Fin N) → A.B i) ((i : Fin N) → A.B i) ℂ :=
    ∑ J : TorchSet R m, (A.st2 ss J).run preO
      (Matrix.of fun x y => block σ1 J x.1 y.1 * torchesOf ω J.1 J.2 x.2 y.2)
  Matrix.of fun x y =>
    σB (fun i => (x i).1) (fun i => (y i).1) * ∏ i, block (sparkCQ ω) (ss' i) (x i).2 (y i).2

/-- The labels of the `v` pre-split and `N` challenge flames are pairwise distinct (§8, p.58). -/
def DistinctLabels (ss : Fin v → Serial lam) (ss' : Fin N → Serial lam) : Prop :=
  Function.Injective (Fin.append (fun j => (ss j).1) (fun i => (ss' i).1))

noncomputable instance (ss : Fin v → Serial lam) (ss' : Fin N → Serial lam) :
    Decidable (DistinctLabels ss ss') := Classical.dec _

/-- **The joint input of the real (`ideal = false`) or ideal (`ideal = true`) experiment** for fixed
oracles and challenge serials, summed over the pre-split serials: zero on a setup abort (p.69: "Due to
setup aborts and label collisions, assume `ρ` may be subnormalized"); the ideal experiment also
declares failure on a label collision ((62), p.58). -/
noncomputable def splitRho (A : SplitAdv lam R m N v) (ω : Sample lam R)
    (preO : PubDom lam R → PubAns lam) (ss' : Fin N → Serial lam) (ideal : Bool) :
    Matrix ((i : Fin N) → A.B i × Flame lam) ((i : Fin N) → A.B i × Flame lam) ℂ :=
  if SetupOK ω then
    ∑ ss : Fin v → Serial lam,
      if ideal = true ∧ ¬ DistinctLabels ss ss' then 0 else splitInput A ω preO ss ss'
  else 0

/-- **The local acceptance effect `Z_i`** of party `i` (p.69): run `A^O_i` (with oracle `O`) on
`B_i F_i`, then `TF.Ver^O(pk, s_i, ·)` on both output flames; `X_i = b_{i,0} b_{i,1}`. -/
noncomputable def partyEff (A : SplitAdv lam R m N v) (ω : Sample lam R)
    (O : PubDom lam R → PubAns lam) (ss' : Fin N → Serial lam) (i : Fin N) :
    Matrix (A.B i × Flame lam) (A.B i × Flame lam) ℂ :=
  heis ((A.party i ss').run O)
    (Matrix.of fun x y => verEff ω (ss' i) x.1 y.1 * verEff ω (ss' i) x.2 y.2)

/-- **`Pr[SPLIT^TF_{A^O}(1^λ, 1^R, m, N) = 1]`** (Definition 6.2 step 6, p.46, (34)): the game outputs
`1` iff `Σ_i X_i ≥ m + 1`. Because the parties act on disjoint registers, the probability is
`Tr(T_{m+1}(Z_1, …, Z_N) ρ)` with the threshold effect (83) (paper.md decision 4), averaged over the
oracles and keys and summed over the challenge serials. -/
noncomputable def splitWinProb (A : SplitAdv lam R m N v) : ℝ :=
  avg (Sample lam R) fun ω => ∑ ss' : Fin N → Serial lam,
    accProb (thresholdEffect (m + 1) fun i => partyEff A ω (pubOracle ω) ss' i)
      (splitRho A ω (pubOracle ω) ss' false)

/-- **The ideal winning probability `p_ideal`** of (62), p.58: failure is also declared if two of the
`v + N` labels coincide. -/
noncomputable def splitWinProbIdeal (A : SplitAdv lam R m N v) : ℝ :=
  avg (Sample lam R) fun ω => ∑ ss' : Fin N → Serial lam,
    accProb (thresholdEffect (m + 1) fun i => partyEff A ω (pubOracle ω) ss' i)
      (splitRho A ω (pubOracle ω) ss' true)

/-- **The computation at location `i`** in the setting of §8.1, built from party `i` (§8.2, pp.69–70):
input `H_i = B_i F_i`, workspace the party's query, answer and work registers; the original queries
use the public collection, the modified ones `O⁰_i` (`Γ` replaced by `Γ⁰_i`, (85)); the witness
predicate is (86) on the query register. (The acceptance projector is not used here; acceptance enters
through `partyEff`.) -/
noncomputable def partyComp (A : SplitAdv lam R m N v) (ω : Sample lam R)
    (ss' : Fin N → Serial lam) (i : Fin N) : LocalComp (A.B i × Flame lam) where
  W := (PubDom lam R × PubAns lam) × (A.party i ss').W
  w0 := (A.party i ss').init
  G := (A.party i ss').Gseq
  O1 := fun _ => (A.party i ss').queryMat (pubOracle ω)
  O0 := fun _ => (A.party i ss').queryMat (modOracle ω (ss' i).1)
  Pi := 1
  wit := fun s => decide (IsWitness ω (ss' i).1 s.2.1.1)

/-- **The witness-sampler effect `E_i`** of §8.2 (p.70) for a common bound `q` on the query
positions: `E_i = (1/q) Σ_{j=1}^q V_{i,j}† Q_i V_{i,j}`, where positions beyond party `i`'s queries are
padding queries with invalid inputs and contribute `0`. -/
noncomputable def partyE (A : SplitAdv lam R m N v) (ω : Sample lam R) (ss' : Fin N → Serial lam)
    (i : Fin N) (q : ℕ) : Matrix (A.B i × Flame lam) (A.B i × Flame lam) ℂ :=
  ((q : ℂ))⁻¹ • ∑ j ∈ Finset.range (A.party i ss').T,
    ((partyComp A ω ss' i).V j)ᴴ * (partyComp A ω ss' i).Qmat * (partyComp A ω ss' i).V j

/-- **`ε_β` of the torch-fire experiment** ((71), p.60; (90), p.72; paper.md decision 13):
`Σ_{i=1}^N E[Tr(C_i L_i ρ_i L_i C_i†)]` with `L_i = (I − E_i)^β`, `ρ` the joint input of the ideal
experiment, and `C_i†C_i` the acceptance effect of the modified computation (party `i` with `O⁰_i`,
then verification of both flames). -/
noncomputable def epsSplit (A : SplitAdv lam R m N v) (q β : ℕ) : ℝ :=
  avg (Sample lam R) fun ω => ∑ ss' : Fin N → Serial lam, ∑ i : Fin N,
    let Li := (1 - partyE A ω ss' i q) ^ β
    accProb (Li * partyEff A ω (modOracle ω (ss' i).1) ss' i * Li)
      (reducedAt (splitRho A ω (pubOracle ω) ss' true) i)

end TorchFire.TF



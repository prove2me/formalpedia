-- Prove2me | Definitions.Def_InfoSharing_Shared_IsSequentialSPE
-- name    : InfoSharing_Shared_IsSequentialSPE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:50:48.004232+00:00
-- url     : https://prove2.me/theorems/311ce611-6a77-45f8-86b4-0c7ec748c3d6
-- title:
--   Sequential information contracting and its subgame-perfect equilibria, §5.2.2
-- statement:
--   Given a payoff table and a first manufacturer $k$ (the other is $j$), the game proceeds as follows:
--
--   1. the retailer offers $k$ a payment $T_f \ge 0$;
--   2. $k$ accepts ($X_k = I$) or rejects;
--   3. having seen $T_f$ and $k$'s decision, the retailer offers $j$ a payment $T_s \ge 0$ (she cannot commit to $T_s = T_f$);
--   4. $j$, having observed everything, accepts or rejects.
--
--   Each manufacturer receives his ex ante profit minus his payment if he accepted; the retailer receives her ex ante profit plus the payments received. A strategy profile is a **subgame-perfect equilibrium** if every player's choice is optimal at every history with nonnegative offers, given the continuation strategies. The set of values of $n$ on the paths of SPEs is the set of possible $n_d^S$; the retailer's and manufacturers' profits along the path are after the side payments.
--
--   **Formalization Note.** Strategies depend on the full history. The acceptance rule at indifference is not fixed in advance: subgame perfection determines it wherever the retailer's optimum requires it.
--
--   **Formalization Note (production economy).** A manufacturer who rejects stays uninformed: the absence of a free-sharing move is the retailer's commitment of §6.2 (p. 256).
--
--   This is a shared definition of the series, reviewed once for both missions: `01-diseconomy-sequential` (production diseconomy, §5; Shang, Ha & Tong 2016, p. 253, §5.2.2; p. 260, proof of Proposition 3) and `02-economy-sequential` (production economy, §6; p. 253, §5.2.2; p. 256, §6.2; pp. 260–261, proofs of Propositions 3 and 7). The cost parameter $c$ is a plain real; the missions differ only in the hypotheses their theorems put on it: $c > 0$ in the first, $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ in the second.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 253, §5.2.2; p. 260, proof of Proposition 3; p. 256, §6.2; p. 261, proof of Proposition 7

import Mathlib
import Definitions.Def_InfoSharing_Shared_PayoffTable

namespace InfoSharing.Shared

/-- A strategy profile of the sequential contracting game (§5.2.2, p. 253; §6.2, p. 256) with first mover
`k`: the retailer's first offer `Tf`; the first manufacturer's decision rule `accF` (given the
offer); the retailer's second offer `Ts` (given `Tf` and the first decision; she cannot commit
to `Ts = Tf`); and the second manufacturer's decision rule `accS` (given the whole history).
A decision `informed` means "accepts the offer and pays". A manufacturer who rejects stays
uninformed: there is no free-sharing move, which is the retailer's commitment of §6.2
(p. 256) not to share information for free after a rejection. -/
structure SeqStrategy where
  Tf : ℝ
  accF : ℝ → Status
  Ts : ℝ → Status → ℝ
  accS : ℝ → Status → ℝ → Status

/-- The status profile when the first mover `k` decides `dk` and the other decides `ds`. -/
def seqProfile (k : Fin 2) (dk ds : Status) : Fin 2 → Status :=
  fun i => if i = k then dk else ds

/-- Manufacturer `i`'s payoff after the history `(Tf, dk, Ts, ds)`: ex ante profit minus his own
payment, if he accepted. -/
def seqMfrPayoff (P : PayoffTable) (k : Fin 2) (Tf : ℝ) (dk : Status) (Ts : ℝ) (ds : Status)
    (i : Fin 2) : ℝ :=
  P.M (seqProfile k dk ds) i -
    if i = k then (if dk = Status.informed then Tf else 0)
    else (if ds = Status.informed then Ts else 0)

/-- The retailer's payoff after the history `(Tf, dk, Ts, ds)`: ex ante profit plus the
payments received. -/
def seqRetPayoff (P : PayoffTable) (k : Fin 2) (Tf : ℝ) (dk : Status) (Ts : ℝ) (ds : Status) :
    ℝ :=
  P.R (seqProfile k dk ds) + (if dk = Status.informed then Tf else 0) +
    (if ds = Status.informed then Ts else 0)

/-- Subgame-perfect equilibrium of the sequential contracting game with first mover `k`
(§5.2.2, p. 253; §6.2, p. 256; proofs of Propositions 3 and 7, pp. 260–261). All offers are nonnegative. Optimality holds
at every history: the second manufacturer's decision for every `(Tf, dk, Ts)`; the retailer's
second offer for every `(Tf, dk)`; the first manufacturer's decision for every `Tf`, anticipating
the continuation; and the retailer's first offer. -/
def IsSequentialSPE (P : PayoffTable) (k : Fin 2) (s : SeqStrategy) : Prop :=
  -- the second manufacturer
  (∀ (Tf : ℝ) (dk : Status) (Ts : ℝ) (d : Status), 0 ≤ Tf → 0 ≤ Ts →
    seqMfrPayoff P k Tf dk Ts d (other k) ≤
      seqMfrPayoff P k Tf dk Ts (s.accS Tf dk Ts) (other k)) ∧
  -- the retailer's second offer
  (∀ (Tf : ℝ) (dk : Status), 0 ≤ Tf →
    0 ≤ s.Ts Tf dk ∧
    ∀ Ts' : ℝ, 0 ≤ Ts' →
      seqRetPayoff P k Tf dk Ts' (s.accS Tf dk Ts') ≤
        seqRetPayoff P k Tf dk (s.Ts Tf dk) (s.accS Tf dk (s.Ts Tf dk))) ∧
  -- the first manufacturer
  (∀ (Tf : ℝ) (d : Status), 0 ≤ Tf →
    seqMfrPayoff P k Tf d (s.Ts Tf d) (s.accS Tf d (s.Ts Tf d)) k ≤
      seqMfrPayoff P k Tf (s.accF Tf) (s.Ts Tf (s.accF Tf))
        (s.accS Tf (s.accF Tf) (s.Ts Tf (s.accF Tf))) k) ∧
  -- the retailer's first offer
  0 ≤ s.Tf ∧
  ∀ Tf' : ℝ, 0 ≤ Tf' →
    seqRetPayoff P k Tf' (s.accF Tf') (s.Ts Tf' (s.accF Tf'))
        (s.accS Tf' (s.accF Tf') (s.Ts Tf' (s.accF Tf'))) ≤
      seqRetPayoff P k s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf))
        (s.accS s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf)))

/-- The status profile on the equilibrium path of `s`. -/
def seqPath (k : Fin 2) (s : SeqStrategy) : Fin 2 → Status :=
  seqProfile k (s.accF s.Tf) (s.accS s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf)))

/-- The retailer's profit on the path of `s`, after the side payments. -/
def seqRetailer (P : PayoffTable) (k : Fin 2) (s : SeqStrategy) : ℝ :=
  seqRetPayoff P k s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf))
    (s.accS s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf)))

/-- The manufacturers' total profit on the path of `s`, net of the side payments. -/
def seqManufacturersTotal (P : PayoffTable) (k : Fin 2) (s : SeqStrategy) : ℝ :=
  ∑ i : Fin 2, seqMfrPayoff P k s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf))
    (s.accS s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf))) i

/-- The set of numbers of informed manufacturers attained by SPEs with first mover `k` (the
possible values of the paper's `n_d^S` in §5 and `n_e^S` in §6). -/
def SeqOptN (P : PayoffTable) (k : Fin 2) : Set ℕ :=
  {n | ∃ s : SeqStrategy, IsSequentialSPE P k s ∧ numInformed (seqPath k s) = n}

end InfoSharing.Shared



-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Protocol
-- name    : RelativisticZK205_ThreeCol_Supplement_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:31:03.738357+00:00
-- url     : https://prove2.me/theorems/f9fcdc2a-b9ba-4ab9-b6f5-835ccb66d08c
-- title:
--   The real Γ_LHV strategy and its explicit PR-box simulator
-- statement:
--   The real strategy samples one uniform vertex permutation $\Pi$ and an independent uniform full matrix $A$. With $D$ the adjacency matrix of $\Pi(G)$, Alice answers $Y=DX+A$, entrywise. Bob reveals $(\Pi,D,A)$ on challenge zero; on challenge one he reveals $\Pi(C)$ and exactly the masks on that cycle. Both interfaces use the same initial draw.
--
--   The simulator reserves independent instances of the published PR-box, indexed by $(i,j,t)$, with
--   $$N_{\mathrm{PR}}=n^2\ell.$$
--   Alice supplies only $X_{ij,t}$ to her interface of instance $(i,j,t)$ and returns the resulting $Y$. Bob subsequently samples a uniform permutation on challenge zero and inputs its adjacency bits, or a uniform complete-graph Hamiltonian cycle on challenge one and inputs one on its edges. The two outputs from each indexed box satisfy $Y_{ij,t}\oplus A_{ij,t}=D_{ij}X_{ij,t}$. Cycle openings omit all other masks. Fixed dummy zero inputs on unused Bob interfaces are marginalized.
--
--   Bob's permutation or cycle is sampled by a local independent probability bind only after his challenge. Alice's commitment can finish while all Bob interfaces remain unused. The simulator takes $G$ and $\ell$, never the witness $C$. An empty cycle sampling set yields a total abort default on no-instances; any valid witness implies that this branch is unreachable. Malformed inputs abort locally. These are operational definitions, rather than definitions by the intended real output law.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.12, §5.2, Protocol Γ_LHV and simulators; p.13, proof of Theorem 2

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_PRBox
import Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Hamiltonian
import Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Async

namespace RelativisticZK205.ThreeCol.Supplement

/-- Γ_LHV's real device, p.12: one common uniform permutation and matrix A,
independent of all verifier resources and coins. -/
noncomputable def realDevice {n : ℕ} (G : SimpleGraph (Vertex n))
    (C : EdgeSet n) (ℓ : ℕ) :
    Device (AliceQuery n ℓ) BobQuery (AliceReply n ℓ) (BobReply n ℓ) where
  State := Equiv.Perm (Vertex n) × MatrixBits n ℓ
  initial := (PMF.uniformOfFintype (Equiv.Perm (Vertex n))).bind fun p =>
    (PMF.uniformOfFintype (MatrixBits n ℓ)).map fun A => (p, A)
  alice s q := PMF.pure (q.map (fun X => commit (adjacency G s.1) X s.2), s)
  bob s q := PMF.pure (q.map (fun c => if c then cycleOpening (relabelCycle s.1 C) s.2
    else Opening.graph s.1 (adjacency G s.1) s.2), s)

inductive RevealChoice (n : ℕ) where
  | graph : Equiv.Perm (Vertex n) → RevealChoice n
  | cycle : EdgeSet n → RevealChoice n

/-- Bob samples only after his challenge. The cycle is uniform over the complete
graph's cycle edge sets, never over cycles of G and never from a search oracle.
The empty-set branch makes the device total even on no-instances. -/
noncomputable def revealLaw (n : ℕ) (c : Bool) : PMF (Option (RevealChoice n)) := by
  classical
  exact if c then
    if h : (allCycles n).Nonempty then
      (PMF.uniformOfFinset (allCycles n) h).map (fun K => some (.cycle K))
    else PMF.pure none
  else (PMF.uniformOfFintype (Equiv.Perm (Vertex n))).map (fun p => some (.graph p))

/-- Bob's local inputs to the indexed PR bank. Outside a revealed cycle the
fixed dummy 0 is supplied and the outputs are marginalized. -/
noncomputable def choiceBits {n : ℕ} (G : SimpleGraph (Vertex n))
    (r : RevealChoice n) : BooleanMatrix n := by
  classical
  exact match r with
  | .graph p => adjacency G p
  | .cycle K => fun e => decide (e ∈ K)

noncomputable def unveil {n ℓ : ℕ} (G : SimpleGraph (Vertex n))
    (r : RevealChoice n) (A : MatrixBits n ℓ) : Opening n ℓ :=
  match r with
  | .graph p => .graph p (adjacency G p) A
  | .cycle K => cycleOpening K A

abbrev PRMemory (n ℓ : ℕ) := BoxIndex n ℓ → Half Bool Bool Bool Bool

/-- Alice's PR calls depend only on X. All n²ℓ instances are reserved by index;
no Bob input, choice, cycle or witness occurs in this local interface. -/
noncomputable def prCommit {n ℓ : ℕ} (bank : PRMemory n ℓ)
    (X : MatrixBits n ℓ) : PMF (MatrixBits n ℓ × PRMemory n ℓ) :=
  (independent (fun i : BoxIndex n ℓ => leftStep prBox (bank i) (X i.1 i.2))).map
    fun f => ((fun e t => (f (e,t)).1), fun i => (f i).2)

/-- Bob's PR calls depend only on his locally computed D. The joint evaluator
internally retains first-interface history; that history is never exposed to Bob. -/
noncomputable def prOpen {n ℓ : ℕ} (bank : PRMemory n ℓ)
    (D : BooleanMatrix n) : PMF (MatrixBits n ℓ × PRMemory n ℓ) :=
  (independent (fun i : BoxIndex n ℓ => rightStep prBox (bank i) (D i.1))).map
    fun f => ((fun e t => (f (e,t)).1), fun i => (f i).2)

/-- The explicit pp.12–13 simulator. Alice can finish and return Y with every
Bob interface still unused. The only other sampling is Bob's local PMF bind.
No Hamiltonian witness is an argument. Both malformed-query aborts are local. -/
noncomputable def simDevice {n : ℕ} (G : SimpleGraph (Vertex n)) (ℓ : ℕ) :
    Device (AliceQuery n ℓ) BobQuery (AliceReply n ℓ) (BobReply n ℓ) where
  State := PRMemory n ℓ
  initial := PMF.pure (fun _ => .empty)
  alice bank q := match q with
    | none => PMF.pure (none, bank)
    | some X => (prCommit bank X).map fun ys => (some ys.1, ys.2)
  bob bank q := match q with
    | none => PMF.pure (none, bank)
    | some c => (revealLaw n c).bind fun r => match r with
      | none => PMF.pure (none, bank)
      | some r => (prOpen bank (choiceBits G r)).map fun a => (some (unveil G r a.1), a.2)

/-- Exactly one PR instance for every ordered matrix position and coordinate. -/
def reservedPR (n ℓ : ℕ) : ℕ := Fintype.card (BoxIndex n ℓ)

end RelativisticZK205.ThreeCol.Supplement



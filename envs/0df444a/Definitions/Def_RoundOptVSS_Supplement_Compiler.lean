-- Prove2me | Definitions.Def_RoundOptVSS_Supplement_Compiler
-- name    : RoundOptVSS_Supplement_Compiler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:12:48.567064+00:00
-- url     : https://prove2.me/theorems/36793287-0dfe-4435-a2f7-368d8421a203
-- title:
--   The VSS compiler of §8.2 (Protocols 8 and 9) built from a broadcast-then-decode WSS, and the good event of Theorem 8.7
-- statement:
--   Let $\mathsf{kuWSS}$ be a scheme of broadcast-then-decode type with key length $\ell=\ell(n,t,\kappa)$ and a key search, and fix $\lambda\in\mathbb E$ at each parameter set. Put $m=(n+1)\ell$. The **protocol of §8.2** runs $n+1$ instances of $\mathsf{kuWSS}$ concurrently: $O_0$ with dealer $D$ and input $x\in\mathbb E^h$, and, for each $a\in[n]$, $O_a$ with dealer $P_a$ and input a uniform mask $R_a\in\mathbb E^m$.
--
--   1. *Sharing (Protocol 8).* In each of the three sharing rounds every party runs its $n+1$ instance parties; each instance message is delivered through that instance's own message cap. In round 2 each $P_i$ also broadcasts $C_i=X_i+\lambda R_i$, where $X_i=(\kappa^{(0)}_i,\dots,\kappa^{(n)}_i)\in\mathbb E^m$ are its round-one verification vectors.
--   2. *Reconstruction (Protocol 9).* Each $P_i$ broadcasts its openings in all $n+1$ instances and its mask $\hat R_i$; verification vectors are not broadcast. With $D_{a,i}(k)=\mathrm{Out}_a(\sigma^{(a)}_i,(k^{(a)}_j)_j;\tau_a)$, $\mathrm{Key}(C,r)=C-\lambda r$, the domains $\mathcal D_j$, the sets $\mathcal K(Z,c)$ and the searches $\mathrm{Search}_a$ run with free set $Z\setminus B_{\mathrm{bad}}$ and lifted as on p.28, $P_i$ runs Initialize, Close, Recover and Restart (the base mission's `protocol9Assign`) to obtain $k^\star$ and outputs $D_{0,i}(k^\star)$.
--
--   The compiled protocol is considered at the parameter sets where $\mathsf{kuWSS}$ is admissible at the root and at every mask instance, and $\lambda\ne0$ has algebraic degree over $\mathbb F$ larger than $nm$.
--
--   The **good event** of Theorem 8.7 is the hypothesis: for every admissible valid parameter set, corrupt set with $|C|\le t$, input and sharing adversary of the composed protocol, there are values $\rho_0\in\mathbb E^h$ and $\rho_a\in\mathbb E^m$ that are functions of the honest view at the end of the composed sharing phase, such that for every reconstruction adversary, with probability at least $1-\varepsilon$, every one of the $n+1$ instances satisfies (a) and (b) of Definition 6.2 for every honest-consistent assignment, with the openings actually broadcast (the input of $O_a$ being its dealer's mask $R_a$).
--
--   These are the protocol and the hypothesis of Theorem 8.7.
--
--   **Formalization Note** Instances are indexed by `Option (Fin n)` (`none` is $O_0$). Party $P_a$ draws $R_a$ in round 1 together with the coins of its own instance's first round, whose request may depend on $R_a$: these coins are drawn as one uniform value modulo a common multiple of the request products over all possible inputs and split into mixed-radix digits, which gives exactly independent uniform coins for the actual request. The compiled protocol has no message cap of its own. The layout of the compiled protocol for the cost model lists the parameter layouts of $O_0$ and of every $O_a$, $\lambda$ and $\ell$.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), §8.2 notation, Protocols 8 and 9 (pp.27–28), Theorem 8.7 (p.30)

import Mathlib
import Definitions.Def_RoundOptVSS_Model
import Definitions.Def_RoundOptVSS_Recovery
import Definitions.Def_RoundOptVSS_Supplement_Cost
import Definitions.Def_RoundOptVSS_Supplement_KeyUniform

open scoped ENNReal
open Classical

namespace RoundOptVSS

namespace Supplement

/-!
# The VSS compiler of §8.2 (Protocols 8 and 9) built from a broadcast-then-decode WSS

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…), §8.2 (pp.27–28): notation,
`D_{a,i}`, `Key`, `D_j`, `𝒦(Z, c)`, `B_bad`, the lifted `Search_a`, Protocol 8 and Protocol 9; the
good event of Theorem 8.7 (p.30).

**Formalization Note.**
* Built from any `S : BTD` (Definition 6.1) with a key search `Search`, and `λ : Params → 𝔼`. The
  key length `ℓ` depends on `(n, t, κ)` only, so all `n + 1` instances share it; `m = (n + 1)ℓ`.
  Instance `O_0` runs `S` at `P` (dealer `D`, input `x ∈ 𝔼^h`); instance `O_b` (`b ∈ [n]`) runs `S`
  at `maskParams P m b` (dealer `P_b`, secret length `m`, input `R_b`). Instances are indexed by
  `Option (Fin n)` (`none` = `O_0`) and stored in the order `O_0, O_1, …, O_n`.
* Rounds `0, 1, 2`: each party runs its `n + 1` instance parties concurrently; a compiled message
  carries one instance message per instance (missing = missing), and each instance message is
  delivered through that instance's own cap, as in a standalone run of `S`. In round `1` each `P_i`
  also broadcasts `C_i = X_i + λR_i`, `X_i = (κ^{(0)}_i, …, κ^{(n)}_i)` from its round-one states.
* `P_a` samples `R_a ← 𝔼^m` in round `0`, together with the coins of its own instance's round `0`,
  whose request may depend on the input `R_a`. These coins are drawn as one uniform value modulo a
  common multiple of the request products over all inputs and split into digits: this gives exactly
  the law of independent uniform coins for the actual request.
* Reconstruction: each party broadcasts its openings in all `n + 1` instances and its mask `R̂_i`
  (verification vectors are not broadcast); the output is Protocol 9's local computation, the
  published `protocol9Assign` with `D_{b,i}(k) = Out_b(σ^{(b)}_i, (k^{(b)}_j)_j; τ_b)` and the lifted
  searches of p.28, followed by `D_{0,i}(k⋆)`. A list of the wrong length reads as malformed / bad.
  A compiled state without exactly `n + 1` instance states (unreachable for an honest party) outputs
  `⊥`.
* The compiled protocol imposes no message cap of its own (`msgLen = 0`); Theorem 8.7 claims nothing
  about communication.
-/

/-- The parameters of the mask instance `O_b`: secret length `m`, dealer `P_b`. -/
def maskParams (P : Params) (m : ℕ) (b : Fin P.n) : Params := ⟨P.n, P.t, P.κ, m, b⟩

variable {𝔼 Msg St Op : Type}

/-- `m = (n + 1)ℓ`. -/
def BTD.mlen (S : BTD 𝔼 Msg St Op) (P : Params) : ℕ := (P.n + 1) * S.ℓ P

/-- The parameters of instance `a` (`none` = `O_0`: `P` itself; `some b`: `maskParams P m b`). -/
def BTD.instParams (S : BTD 𝔼 Msg St Op) (P : Params) (a : Option (Fin P.n)) : Params :=
  ⟨P.n, P.t, P.κ, a.elim P.h (fun _ => S.mlen P), a.elim P.dealer id⟩

/-- The instances in order `O_0, O_1, …, O_n`. -/
def instList (n : ℕ) : List (Option (Fin n)) := none :: (List.finRange n).map some

/-- The position of an instance in that order. -/
def instPos {n : ℕ} : Option (Fin n) → ℕ
  | none => 0
  | some b => (b : ℕ) + 1

/-- A compiled message: one instance message per instance, the deposit `C_i`, the openings and the
announced mask. -/
structure CMsg (Msg Op 𝔼 : Type) where
  inst : List Msg
  dep : List 𝔼
  opens : List Op
  mask : List 𝔼

/-- A compiled state: the root input, the own mask `R_i`, the `n + 1` instance states, the received
deposits and the received reconstruction broadcasts. -/
structure CSt (St Msg Op 𝔼 : Type) where
  input : Option (List 𝔼)
  R : List 𝔼
  inst : List St
  dep : List (Option (List 𝔼))
  recon : List (Option (CMsg Msg Op 𝔼))

/-- A state of `S` (used as the default of a missing instance state). -/
def BTD.defaultSt (S : BTD 𝔼 Msg St Op) : St := S.prot.init ⟨1, 0, 0, 0, 0⟩ 0 none

/-- The state of instance `a` stored in a compiled state. -/
def BTD.instSt (S : BTD 𝔼 Msg St Op) {n : ℕ} (st : CSt St Msg Op 𝔼) (a : Option (Fin n)) : St :=
  st.inst.getD (instPos a) S.defaultSt

/-- A vector of length `k` from a list (`none` if the length is wrong). -/
def vecOfListE [Zero 𝔼] (k : ℕ) (l : List 𝔼) : Option (Fin k → 𝔼) :=
  if l.length = k then some (fun r => l.getD r 0) else none

/-- The own mask `R_i` stored in a compiled state. -/
def maskOf [Zero 𝔼] {m : ℕ} (st : CSt St Msg Op 𝔼) : Fin m → 𝔼 := fun k => st.R.getD k 0

/-- The block `k^{(a)} ∈ 𝔼^ℓ` of instance `a` in `k ∈ 𝔼^m`. -/
def block [Zero 𝔼] {n ℓ m : ℕ} (a : Option (Fin n)) (k : Fin m → 𝔼) : Fin ℓ → 𝔼 :=
  fun r => if h : instPos a * ℓ + r < m then k ⟨instPos a * ℓ + r, h⟩ else 0

/-- The vector of `𝔼^m` with block `x` in the slot of instance `a` and zeros elsewhere. -/
def embedBlock [Zero 𝔼] {n ℓ m : ℕ} (a : Option (Fin n)) (x : Fin ℓ → 𝔼) : Fin m → 𝔼 :=
  fun k => if h : (k : ℕ) / ℓ = instPos a ∧ (k : ℕ) % ℓ < ℓ then x ⟨(k : ℕ) % ℓ, h.2⟩ else 0

/-- Mixed-radix digits of `v` for the moduli `Ns` (a modulus `N` read as `max N 1`). -/
def digits : List ℕ → ℕ → List ℕ
  | [], _ => []
  | N :: Ns, v => v % max N 1 :: digits Ns (v / max N 1)

/-- The number of outcomes of a coin request. -/
def reqProd (l : List ℕ) : ℕ := (l.map fun N => max N 1).prod

/-- Cut a list into consecutive pieces of the given lengths. -/
def splitBy : List ℕ → List ℕ → List (List ℕ)
  | [], _ => []
  | k :: ks, l => l.take k :: splitBy ks (l.drop k)

variable [Field 𝔼] [Fintype 𝔼]

/-- The `v`-th element of `𝔼` in a fixed enumeration (a uniform coin of modulus `|𝔼|`). -/
noncomputable def elemOf (v : ℕ) : 𝔼 :=
  if h : v < Fintype.card 𝔼 then (Fintype.equivFin 𝔼).symm ⟨v, h⟩ else 0

section Compiled

variable (S : BTD 𝔼 Msg St Op) (Search : SearchFn S) (lam : Params → 𝔼)

/-- The mask `R_i` drawn from the first `m` coins of round `0`. -/
noncomputable def drawnMask (P : Params) (c : List ℕ) : Fin (S.mlen P) → 𝔼 :=
  fun k => elemOf (c.getD k 0)

/-- The initial state of instance `a` at party `i` (root input from the compiled state, own mask
`R` for the own mask instance). -/
def instInit (P : Params) (i : Fin P.n) (st : CSt St Msg Op 𝔼) (R : Fin (S.mlen P) → 𝔼) :
    Option (Fin P.n) → St
  | none => S.prot.init P i (st.input.map fun l r => l.getD r 0)
  | some b => S.prot.init (maskParams P (S.mlen P) b) i (if b = i then some R else none)

/-- The common multiple of the request products of the own instance's round-`0` coins over all
possible inputs `R`. -/
noncomputable def bigModulus (P : Params) (i : Fin P.n) : ℕ :=
  ∏ R : Fin (S.mlen P) → 𝔼, reqProd (S.prot.coins (maskParams P (S.mlen P) i) i 0
    (S.prot.init (maskParams P (S.mlen P) i) i (some R)))

/-- The instance states of party `i` before round `r` (round `0`: initial states, with the mask
drawn from the round-`0` coins `c`). -/
noncomputable def instStates (P : Params) (i : Fin P.n) (r : Fin 4) (st : CSt St Msg Op 𝔼)
    (c : List ℕ) : Option (Fin P.n) → St :=
  if r.val = 0 then instInit S P i st (drawnMask S P c) else fun a => S.instSt st a

/-- The compiled coin request of party `i` in round `r`. -/
noncomputable def compCoins (P : Params) (i : Fin P.n) (r : Fin 4) (st : CSt St Msg Op 𝔼) :
    List ℕ :=
  if r.val = 0 then
    List.replicate (S.mlen P) (Fintype.card 𝔼) ++ [bigModulus S P i] ++
      (instList P.n).flatMap fun a =>
        if a = some i then [] else S.prot.coins (S.instParams P a) i 0 (instInit S P i st 0 a)
  else if r.val < 3 then
    (instList P.n).flatMap fun a => S.prot.coins (S.instParams P a) i r (S.instSt st a)
  else []

/-- The coins of instance `a` at party `i` in round `r`, cut from the compiled coins `c`. -/
noncomputable def instCoins (P : Params) (i : Fin P.n) (r : Fin 4) (st : CSt St Msg Op 𝔼)
    (c : List ℕ) (a : Option (Fin P.n)) : List ℕ :=
  if r.val = 0 then
    if a = some i then
      digits (S.prot.coins (maskParams P (S.mlen P) i) i 0
        (S.prot.init (maskParams P (S.mlen P) i) i (some (drawnMask S P c)))) (c.getD (S.mlen P) 0)
    else
      let others := (instList P.n).filter fun a' => a' ≠ some i
      (splitBy (others.map fun a' => (S.prot.coins (S.instParams P a') i 0
          (instInit S P i st 0 a')).length) (c.drop (S.mlen P + 1))).getD (others.idxOf a) []
  else
    (splitBy ((instList P.n).map fun a' => (S.prot.coins (S.instParams P a') i r
        (S.instSt st a')).length) c).getD (instPos a) []

/-- `C_i = X_i + λR_i`, `X_i = (κ^{(0)}_i, …, κ^{(n)}_i)` from the round-one instance states. -/
noncomputable def deposit (P : Params) (i : Fin P.n) (st : CSt St Msg Op 𝔼) : List 𝔼 :=
  List.zipWith (fun x r => x + lam P * r)
    ((instList P.n).flatMap fun a => List.ofFn (S.vkey1 (S.instParams P a) i (S.instSt st a)))
    st.R

/-- An instance message from a compiled message, through the instance's cap. -/
def instIn (P : Params) (a : Option (Fin P.n)) (m : Option (CMsg Msg Op 𝔼)) : Option Msg :=
  capped S.prot (S.instParams P a) (m.bind fun cm => cm.inst[instPos a]?)

/-- The empty compiled message. -/
def emptyC : CMsg Msg Op 𝔼 := ⟨[], [], [], []⟩

/-- The decoders `D_{b,i}` of the mask instances and the lifted searches `Search_b`, and the local
computation of Protocol 9 at party `i` from its final compiled state. A compiled state that does not
hold exactly `n + 1` instance states (never the case for an honest party after round `0`) outputs
`⊥`, so that the output never reads the default instance state. -/
noncomputable def protocol9Output (P : Params) (i : Fin P.n) (st : CSt St Msg Op 𝔼) :
    Option (Fin P.h → 𝔼) :=
  let m := S.mlen P
  let ℓ := S.ℓ P
  let σ : Option (Fin P.n) → St := fun a => S.instSt st a
  let Cdep : Fin P.n → Option (Fin m → 𝔼) := fun j => (st.dep.getD j none).bind (vecOfListE m)
  let Rhat : Fin P.n → Option (Fin m → 𝔼) := fun j =>
    (st.recon.getD j none).bind fun cm => vecOfListE m cm.mask
  let τ : Option (Fin P.n) → Fin P.n → Option Op := fun a j =>
    (st.recon.getD j none).bind fun cm => cm.opens[instPos a]?
  let bk : Option (Fin P.n) → KeyAssign 𝔼 P.n m → Fin P.n → Option (Fin ℓ → 𝔼) :=
    fun a k j => (k j).map (block (ℓ := ℓ) a)
  let Dm : Fin P.n → KeyAssign 𝔼 P.n m → Option (Fin m → 𝔼) := fun b k =>
    S.Out (maskParams P m b) i (σ (some b)) (bk (some b) k) (τ (some b))
  let Bbad : Finset (Fin P.n) := Finset.univ.filter fun j => Cdep j = none
  let Srch : Fin P.n → Finset (Fin P.n) → KeyAssign 𝔼 P.n m → SearchMode →
      Option (KeyAssign 𝔼 P.n m) := fun b Z c mode =>
    (Search (maskParams P m b) i (σ (some b)) (τ (some b)) (Z \ Bbad)
        (fun j => if j ∈ Bbad then none else (c j).map (block (ℓ := ℓ) (some b))) mode).map
      fun kt j => if j ∉ Z then c j else if j ∈ Bbad then none
        else (kt j).map (embedBlock (ℓ := ℓ) (m := m) (some b))
  let kstar := protocol9Assign (lam P) Cdep Dm Srch Rhat
  if st.inst.length = P.n + 1 then S.Out P i (σ none) (bk none kstar) (τ none) else none

/-- **The protocol of §8.2** built from `S`, `Search` and `λ` (Protocols 8 and 9). -/
noncomputable def compiled : Protocol (CMsg Msg Op 𝔼) (CSt St Msg Op 𝔼) 𝔼 where
  init _ _ x := ⟨x.map List.ofFn, [], [], [], []⟩
  coins P i r st := compCoins S P i r st
  send P i r st c :=
    if r.val < 3 then
      let σ := instStates S P i r st c
      let out : Option (Fin P.n) → (Fin P.n → Msg) × Msg := fun a =>
        S.prot.send (S.instParams P a) i r (σ a) (instCoins S P i r st c a)
      (fun j => ⟨(instList P.n).map fun a => (out a).1 j, [], [], []⟩,
        ⟨(instList P.n).map fun a => (out a).2,
          if r.val = 1 then deposit S lam P i st else [], [], []⟩)
    else
      (fun _ => emptyC,
        ⟨[], [], (instList P.n).map fun a => S.opening (S.instParams P a) i (S.instSt st a), st.R⟩)
  recv P i r st c pr bc :=
    if r.val < 3 then
      let σ := instStates S P i r st c
      { input := st.input
        R := if r.val = 0 then List.ofFn (drawnMask S P c) else st.R
        inst := (instList P.n).map fun a =>
          S.prot.recv (S.instParams P a) i r (σ a) (instCoins S P i r st c a)
            (fun j => instIn S P a (pr j)) (fun j => instIn S P a (bc j))
        dep := if r.val = 1 then List.ofFn fun j => (bc j).map CMsg.dep else st.dep
        recon := st.recon }
    else { st with recon := List.ofFn bc }
  output P i st := protocol9Output S Search lam P i st
  msgLen _ := 0
  msgCap _ := 0

end Compiled

/-- The parameter sets at which the compiled protocol is considered: `S`'s admissibility holds at
`P` and at every mask instance's parameters, and `λ ≠ 0` has algebraic degree over `𝔽` larger than
`nm` (§8.2). -/
def compAdm (𝔽 : Type) [Field 𝔽] [Algebra 𝔽 𝔼] (S : BTD 𝔼 Msg St Op) (AdmK : Params → Prop)
    (lam : Params → 𝔼) (P : Params) : Prop :=
  AdmK P ∧ (∀ b, AdmK (maskParams P (S.mlen P) b)) ∧ lam P ≠ 0 ∧
    P.n * S.mlen P < (minpoly 𝔽 (lam P)).natDegree

/-- The openings `τ_a` actually delivered in the compiled reconstruction round. -/
def compOpenings {P : Params} (bc : Fin P.n → Option (CMsg Msg Op 𝔼)) (a : Option (Fin P.n)) :
    Fin P.n → Option Op :=
  fun j => (bc j).bind fun cm => cm.opens[instPos a]?

/-- **The hypothesis of Theorem 8.7**: in the composed execution, for every admissible valid
parameter set, corrupt set, input and sharing adversary there are committed values `ρ_0` (in
`𝔼^h`) and `ρ_b` (in `𝔼^m`), functions of the honest view at the end of sharing, such that against
every reconstruction adversary, with probability at least `1 − ε`, all `n + 1` instances satisfy
(a) and (b) of Definition 6.2 for every honest-consistent assignment, with the actual openings
(the input of `O_b` is the mask `R_b` of its dealer). -/
def CompGood (S : BTD 𝔼 Msg St Op) (Search : SearchFn S) (lam : Params → 𝔼)
    (Adm : Params → Prop) (ε : Params → ℝ≥0∞) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ C : Finset (Fin P.n), C.card ≤ P.t →
    ∀ (x : Fin P.h → 𝔼) (A : ShareAdv P (CMsg Msg Op 𝔼) 𝔼),
      ∃ (ρ0 : HonestView P C (CMsg Msg Op 𝔼) 𝔼 → (Fin P.h → 𝔼))
        (ρm : Fin P.n → HonestView P C (CMsg Msg Op 𝔼) 𝔼 → (Fin (S.mlen P) → 𝔼)),
        ∀ B : RecAdv A,
          1 - ε P ≤ (exec (compiled S Search lam) P C x A B).toOuterMeasure
            {o | KUEvent S P C (fun j => S.instSt (n := P.n) (o.share.states 3 j) none)
                  (ρ0 (Outcome.view (C := C) o)) x (compOpenings o.recon.bcast none) ∧
                ∀ b : Fin P.n, KUEvent S (maskParams P (S.mlen P) b) C
                  (fun j => S.instSt (n := P.n) (o.share.states 3 j) (some b))
                  (ρm b (Outcome.view (C := C) o)) (maskOf (o.share.states 3 b))
                  (compOpenings o.recon.bcast (some b))}

/-! ## Layout of the compiled protocol -/

/-- Layout of a list of field elements. -/
def layFlE (l : List 𝔼) : MVal 𝔼 := layList MVal.fld l

/-- Layout of a compiled message. -/
def layCMsg (L : BTDLayout 𝔼 Msg St Op) (cm : CMsg Msg Op 𝔼) : MVal 𝔼 :=
  MVal.ofList [layList L.msg cm.inst, layFlE cm.dep, layList L.op cm.opens, layFlE cm.mask]

/-- Layout of a compiled state. -/
def layCSt (L : BTDLayout 𝔼 Msg St Op) (st : CSt St Msg Op 𝔼) : MVal 𝔼 :=
  MVal.ofList [layOpt layFlE st.input, layFlE st.R, layList L.st st.inst,
    layList (layOpt layFlE) st.dep, layList (layOpt (layCMsg L)) st.recon]

/-- The layout of the compiled protocol: parameters (those of `O_0`, of every `O_b`, `λ` and `ℓ`),
states and messages; coins are laid out as integers (not used by the local computation). -/
def compLayout (S : BTD 𝔼 Msg St Op) (L : BTDLayout 𝔼 Msg St Op) (lam : Params → 𝔼) :
    Layout 𝔼 (CMsg Msg Op 𝔼) (CSt St Msg Op 𝔼) where
  par P := MVal.ofList [L.par P,
    MVal.ofList (List.ofFn fun b : Fin P.n => L.par (maskParams P (S.mlen P) b)), MVal.fld (lam P),
    layNat (S.ℓ P)]
  st := layCSt L
  msg := layCMsg L
  coin _ _ _ _ c := layList layNat c

/-- **Polynomial local computation**: the program `code` computes the output map (the local
computation of the reconstruction phase) within `p(N(P) + input size)` steps on every input, for all
valid parameters with `Adm P`. -/
def LocalComputation (𝔽 : Type) [Field 𝔽] [Algebra 𝔽 𝔼] {M T : Type} (Adm : Params → Prop)
    (L : Layout 𝔼 M T) (prot : Protocol M T 𝔼) (N : Params → ℕ) (p : Polynomial ℕ)
    (code : Program) : Prop :=
  ∀ P : Params, P.Valid → Adm P → ∀ i st,
    RunsWithin 𝔽 code (outputIn L P i st) (layOpt layVec (prot.output P i st))
      (p.eval (N P + valSize (outputIn L P i st)))

end Supplement

end RoundOptVSS



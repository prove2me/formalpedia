-- Prove2me | Definitions.Def_QuantumBA_PackedShares_Protocol
-- name    : QuantumBA_PackedShares_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:49.079807+00:00
-- url     : https://prove2.me/theorems/a2e2a2ee-c683-40da-b701-c32006bd99d1
-- title:
--   The algorithm QBA:PackedShares (Algorithms 1–5, §2.4, §3, §5.2) and the parameters (11)
-- statement:
--   **Symbolic parameters.** A parameter record fixes $\varepsilon$, $t$, $b$, $w$, the number of levels $h$, committee sizes $k_\ell$, public committees $C_{(\ell,i)}$, public forwarding graphs, out-degrees $D_\ell$, the in-degree bound $J$ ($p_1=1$, $p_\ell=J$), and the public choices $\alpha$, $\psi$ and the bit representation of field elements; $\sigma(m)=\lfloor\theta m\rfloor$ with $\theta=1/3-\varepsilon/4$. There are $N=wb^h$ arrays; node $(\ell,i)$ has leaf interval $\{iwb^\ell+1,\dots,(i+1)wb^\ell\}$; $\mathrm{dealer}(x)=1+((x-1)\bmod n)$; an array has words $(\mathrm{bin},\ell)$, $(\mathrm{coin},\ell)$ for $\ell\in[h]$ and $(\mathrm{final})$.
--
--   **One epoch** ($1+h(4bw+3)+4(w+1)$ rounds). Distribution: every active dealer applies $V_{k_1,\sigma(k_1),1}$ to a fresh $|+_q\rangle$ for every word of its arrays and sends output $i$ to the $i$-th member of the first committee ($P$ if $h=0$). Level $\ell$: members accept child lists by strict majority of the child's committee and normalize them (frozen provider list $Y$); in the bin round holders open the level's bin words of $Y$ and members request them, in the next round holders reply and members decode the bins; then $r=bw$ phases of ByzantineAgreementWithCommonCoin on the $u$ bits of the identifier/bin pairs (estimates; proposals, $v$ if at least $|C|-a_C$ estimates equal $v$; forced values with $a_C+1$; at the proposal deadline holders open the coin word of position $j$ of their own list and members request it; reply, decode, update), normalization and lightest-bin selection; delivery of the output list to the parent committee and Algorithm 2: each holder applies $V_{D_\ell,\sigma(D_\ell),p_\ell}$ to its registers of each unopened word of the arrays of its own list, in incoming-edge order padded with $|0\rangle$, and sends one output along each forwarding edge (shares stop moving once committees are $P$). Final agreement: $w+1$ phases with $k=n$, $a=t$, coin of phase $j\le w$ from the final word of position $j$ of the local root list, coin $0$ in phase $w+1$; an undecided process decides $v$ at the proposal deadline if at least $n-t$ proposals equal $v$, and halts at the end of the first final phase at whose start it had decided. Requests name whole words; holders reply once per authorized request, subject to the stage, opening and quota rules, with address–value pairs of their measured stored registers; requesters decode backward through the public circuit, replacing missing values by $0$. For $n=1$ the process decides its input at once.
--
--   **Parameters (11)** ($c=1$): $b=2^{\lceil\log_2(10/\varepsilon)\rceil}$, $H=\lceil\log_b(10n)\rceil$, $\beta=\eta=1/(20H)$, $\tau=1/(100H)$, $\rho=\varepsilon/10$, $A=10^6(c+2)\varepsilon^{-2}$, $w=2^{\lceil\log_2(AH^2L)\rceil}$, $h=\max\{0,\lceil\log_b(10n/w)\rceil\}$, $k_\ell=\kappa b^{\ell-1}$ if $\kappa b^{\ell-1}\le n/b$ and $n$ otherwise, $\kappa=\lceil K(m_1)\rceil$, $C_\varepsilon=\lceil2/\rho^3\rceil$, $D_\ell=\lceil C_\varepsilon Lk_{\ell+1}/k_\ell\rceil$, $J=\lceil6C_\varepsilon L\rceil$, $L=\lceil\log_2 n\rceil$, $d=\lceil\log_2(n+1)\rceil$, $q=2^d$; committees and graphs are the first valid tables of Lemmas 4.4 and 5.3.
--
--   **Formalization Note** The local state of a process is its complete local log, and every action is a function of it. Classical messages are structured values with explicit bit lengths.
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, pp. 7–14 and 18–25: Algorithms 1–5 (PDF pp. 8, 10, 17, 20, 22), §2.4, §3.1–3.2, §4.2, §4.4, §5.2; parameters (11), p. 32 (PDF 33)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Model
import Definitions.Def_QuantumBA_PackedShares_Encoder
import Definitions.Def_QuantumBA_PackedShares_Tables

set_option autoImplicit false

open scoped BigOperators

namespace QuantumBA.PackedShares

attribute [local instance] Classical.propDecidable

/-! # The algorithm QBA:PackedShares (Algorithms 1–5, §2.4, §3, §4, §5.2, parameters (11))

All quantities below are defined for the failure exponent `c = 1` used by Theorem 1. -/

section Parameters

variable (ε : ℝ) (n : ℕ)

/-- `b = 2^⌈log₂(10/ε)⌉` -/
noncomputable def parB : ℕ := 2 ^ ⌈Real.logb 2 (10 / ε)⌉₊
/-- `H = ⌈log_b(10n)⌉` -/
noncomputable def parH : ℕ := ⌈Real.logb (parB ε) (10 * n)⌉₊
/-- `β = η = 1/(20H)` -/
noncomputable def parBeta : ℝ := 1 / (20 * (parH ε n : ℝ))
/-- `η = 1/(20H)` -/
noncomputable def parEta : ℝ := 1 / (20 * (parH ε n : ℝ))
/-- `τ = 1/(100H)` -/
noncomputable def parTau : ℝ := 1 / (100 * (parH ε n : ℝ))
/-- `ρ = ε/10` -/
noncomputable def parRho : ℝ := ε / 10
/-- `A = 10⁶(c+2)ε⁻²` with `c = 1` -/
noncomputable def parA : ℝ := 10 ^ 6 * (1 + 2) / ε ^ 2
/-- `w = 2^⌈log₂(A H² L)⌉` -/
noncomputable def parW : ℕ := 2 ^ ⌈Real.logb 2 (parA ε * (parH ε n : ℝ) ^ 2 * (logL n : ℝ))⌉₊
/-- `h = max{0, ⌈log_b(10n/w)⌉}` (number of levels) -/
noncomputable def parh : ℕ := ⌈Real.logb (parB ε) (10 * (n : ℝ) / (parW ε n : ℝ))⌉₊
/-- `N = w bʰ` (number of arrays) -/
noncomputable def parN : ℕ := parW ε n * parB ε ^ parh ε n
/-- `r = bw` (input slots of an election) -/
noncomputable def parR : ℕ := parB ε * parW ε n
/-- `m_ℓ = N/(w b^ℓ)` nodes at level `ℓ` -/
noncomputable def parM (ℓ : ℕ) : ℕ := parB ε ^ (parh ε n - ℓ)
/-- `κ = ⌈K(m₁)⌉` -/
noncomputable def parKappa : ℕ := ⌈Kbound ε (parBeta ε n) n (parM ε n 1)⌉₊
/-- committee size `k_ℓ = κ b^{ℓ-1}` if `κ b^{ℓ-1} ≤ n/b`, else `n`; `k₁ = n` if `h = 0` -/
noncomputable def parK (ℓ : ℕ) : ℕ :=
  if parh ε n = 0 then n else
    if ((parKappa ε n * parB ε ^ (ℓ - 1) : ℕ) : ℝ) ≤ (n : ℝ) / (parB ε : ℝ)
    then parKappa ε n * parB ε ^ (ℓ - 1) else n
/-- `C_ε = ⌈2/ρ³⌉` -/
noncomputable def parCeps : ℕ := ⌈2 / parRho ε ^ 3⌉₊
/-- `D_ℓ = ⌈C_ε L k_{ℓ+1}/k_ℓ⌉` (forwarding out-degree at level `ℓ`) -/
noncomputable def parD (ℓ : ℕ) : ℕ :=
  ⌈(parCeps ε : ℝ) * (logL n : ℝ) * (parK ε n (ℓ + 1) : ℝ) / (parK ε n ℓ : ℝ)⌉₊
/-- `J = ⌈6 C_ε L⌉` -/
noncomputable def parJ : ℕ := ⌈6 * (parCeps ε : ℝ) * (logL n : ℝ)⌉₊
/-- `p₁ = 1`, `p_ℓ = J` for `ℓ ≥ 2` (inputs of a block applied at level `ℓ`) -/
noncomputable def parP (ℓ : ℕ) : ℕ := if ℓ ≤ 1 then 1 else parJ ε n
/-- `γ = 1/3 - ε/2` -/
noncomputable def parGamma : ℝ := 1 / 3 - ε / 2
/-- `θ = 1/3 - ε/4` -/
noncomputable def parTheta : ℝ := 1 / 3 - ε / 4
/-- `σ(m) = ⌊θ m⌋` -/
noncomputable def parSigma (m : ℕ) : ℕ := ⌊parTheta ε * (m : ℝ)⌋₊
/-- `d = ⌈log₂(n+1)⌉`, `q = 2^d` -/
def parDbits : ℕ := Nat.clog 2 (n + 1)
/-- `ι = ⌈log₂(N+1)⌉` -/
noncomputable def parIota : ℕ := Nat.clog 2 (parN ε n + 1)
/-- `log₂ b` -/
noncomputable def parLogB : ℕ := Nat.log 2 (parB ε)
/-- `u = r(ι + log₂ b)` -/
noncomputable def parU : ℕ := parR ε n * (parIota ε n + parLogB ε)
/-- Rounds of one epoch: `1 + h(4bw + 3) + 4(w + 1)`. -/
noncomputable def epochLen : ℕ := 1 + parh ε n * (4 * parR ε n + 3) + 4 * (parW ε n + 1)

end Parameters

/-! ## Words, messages -/

/-- Public word labels: `(bin, ℓ)`, `(coin, ℓ)`, `(final)`. -/
inductive Lbl where
  | bin : ℕ → Lbl
  | coin : ℕ → Lbl
  | final : Lbl
  deriving DecidableEq

/-- Self-delimiting binary length of a natural number. -/
def natBits (k : ℕ) : ℕ := 2 * Nat.size k + 1

/-- Bit length of a label. -/
def Lbl.bits : Lbl → ℕ
  | .bin l => 2 + natBits l
  | .coin l => 2 + natBits l
  | .final => 2

/-- Classical messages of QBA:PackedShares.  `node l i` tags identify the committee (level `l`,
index `i`); the epoch and round are implicit.  Final agreement uses the tag `l = 0`. -/
inductive Msg (F : Type) where
  /-- a child committee member's output list -/
  | childList : ℕ → ℕ → List ℕ → Msg F
  /-- estimate vector of phase `j` -/
  | est : ℕ → ℕ → ℕ → List Bool → Msg F
  /-- proposal vector of phase `j` -/
  | prop : ℕ → ℕ → ℕ → List (Option Bool) → Msg F
  /-- whole-word reconstruction request for word `(x, λ)` -/
  | req : ℕ → ℕ → ℕ → Lbl → Msg F
  /-- reply: address–value pairs; an address `(j, s)` names the block (level `j`, holder `s`;
  `j = 0` is the dealer block) whose output was stored at the replying holder -/
  | reply : ℕ → ℕ → ℕ → Lbl → List ((ℕ × ℕ) × F) → Msg F

/-- Bit length of a message (`fb` bits per field element). -/
def Msg.bits {F : Type} (fb : ℕ) : Msg F → ℕ
  | .childList l i ids => 3 + natBits l + natBits i + natBits ids.length + (ids.map natBits).sum
  | .est l i j v => 3 + natBits l + natBits i + natBits j + natBits v.length + v.length
  | .prop l i j v => 3 + natBits l + natBits i + natBits j + natBits v.length + 2 * v.length
  | .req l i x lb => 3 + natBits l + natBits i + natBits x + lb.bits
  | .reply l i x lb ps => 3 + natBits l + natBits i + natBits x + lb.bits + natBits ps.length +
      (ps.map (fun e => natBits e.1.1 + natBits e.1.2 + fb)).sum

/-- Classical header of a transferred register: array identifier and word label. -/
abbrev Hd := ℕ × Lbl

/-- The local state of an honest process: its identity, its input and its complete local log:
for every completed round, the registers it allocated (per operation) and its measurement
outcomes, and the classical and quantum messages it received. -/
structure View (n : ℕ) (F : Type) where
  me : Fin n
  input : Bool
  outs : List (List (List ℕ) × List (ℕ × F))
  ins : List (List (Fin n × Msg F) × List (Fin n × List (Hd × ℕ)))

/-- The arbitrary public choices of the paper: distinct nonzero evaluation points, a nonzero
`𝔽₂`-linear `ψ : 𝔽_q → 𝔽₂`, and the fixed `𝔽₂`-basis representing field elements by `d` bits. -/
structure Choices (n : ℕ) (F : Type) [Field F] where
  α : Fin n → F
  ψ : F →+ ZMod 2
  bitsOf : F ≃+ (Fin (parDbits n) → ZMod 2)


/-- The symbolic parameters and public data of QBA:PackedShares (§3.1, §5.2; Sections 3–5 keep
them symbolic, Section 6 fixes them by (11)): slack `ε` (giving `θ = 1/3 - ε/4`), corruption
bound `t`, `b`, `w`, number of levels `h`, committee sizes `k_ℓ`, the public committees
`C_{(ℓ,i)}` (0-based node index `i`), the public forwarding graphs (`fwd ℓ i s` is the ordered
list of forwarding neighbours of `s ∈ C_{(ℓ,i)}` in the parent committee), the forwarding
out-degrees `D_ℓ` (used only in hypotheses of the analysis; the protocol follows `fwd`), the
in-degree bound
`J` (`p₁ = 1`, `p_ℓ = J` for `ℓ ≥ 2`), and the public choices. -/
structure Ctx (n : ℕ) (F : Type) [Field F] where
  ε : ℝ
  t : ℕ
  b : ℕ
  w : ℕ
  h : ℕ
  k : ℕ → ℕ
  comm : ℕ → ℕ → Finset (Fin n)
  fwd : ℕ → ℕ → Fin n → List (Fin n)
  D : ℕ → ℕ
  J : ℕ
  cf : Choices n F

namespace Ctx

variable {n : ℕ} {F : Type} [Field F] (X : Ctx n F)

/-- `N = w bʰ` -/
def N : ℕ := X.w * X.b ^ X.h
/-- `r = bw` -/
def r : ℕ := X.b * X.w
/-- `m_ℓ = N/(w b^ℓ)` -/
def m (ℓ : ℕ) : ℕ := X.b ^ (X.h - ℓ)
/-- `p₁ = 1`, `p_ℓ = J` -/
def p (ℓ : ℕ) : ℕ := if ℓ ≤ 1 then 1 else X.J
/-- `ι = ⌈log₂(N+1)⌉` -/
def iota : ℕ := Nat.clog 2 (X.N + 1)
/-- `log₂ b` -/
def logb : ℕ := Nat.log 2 X.b
/-- `u = r(ι + log₂ b)` -/
def u : ℕ := X.r * (X.iota + X.logb)
/-- rounds of an epoch `1 + h(4bw+3) + 4(w+1)` -/
def epochLen : ℕ := 1 + X.h * (4 * X.r + 3) + 4 * (X.w + 1)
/-- `σ(m) = ⌊θ m⌋`, `θ = 1/3 - ε/4` -/
noncomputable def sigma (m : ℕ) : ℕ := ⌊(1 / 3 - X.ε / 4) * (m : ℝ)⌋₊

end Ctx

/-- `dealer(x) = 1 + ((x - 1) mod n)`, as a 0-based process index. -/
def dealer (n x : ℕ) : ℕ := (x - 1) % n

section Helpers

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Members of a committee in increasing identifier order. -/
def sortedMembers (C : Finset (Fin n)) : List (Fin n) := C.sort (· ≤ ·)

/-- Classical messages received at the end of global round `R`. -/
def View.cin (V : View n F) (R : ℕ) : List (Fin n × Msg F) := (V.ins.getD R ([], [])).1
/-- Quantum messages received at the end of global round `R`. -/
def View.qin (V : View n F) (R : ℕ) : List (Fin n × List (Hd × ℕ)) := (V.ins.getD R ([], [])).2
/-- Register lists allocated by the operations of global round `R`. -/
def View.allocs (V : View n F) (R : ℕ) : List (List ℕ) := (V.outs.getD R ([], [])).1
/-- Outcome of the (first) measurement of register `reg`, if any. -/
def View.readout (V : View n F) (reg : ℕ) : Option F :=
  ((V.outs.flatMap (fun o => o.2)).find? (fun e => e.1 = reg)).map Prod.snd

/-- Convert a bit list (least significant first) to a number. -/
def bitsToNat (l : List Bool) : ℕ := l.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0

/-- Little-endian `k`-bit representation. -/
def natToBits (k v : ℕ) : List Bool := (List.range k).map (fun i => v.testBit i)

/-! ### Thresholds of ByzantineAgreementWithCommonCoin -/

/-- Voting threshold `a_C = ⌊(|C| - 1)/3⌋`. -/
def aThr (k : ℕ) : ℕ := (k - 1) / 3

/-- First message from each sender satisfying a predicate, as a function of the sender. -/
noncomputable def firstFrom {α : Type} (ms : List (Fin n × Msg F)) (f : Msg F → Option α) (s : Fin n) :
    Option α :=
  (ms.filterMap (fun m => if m.1 = s then f m.2 else none)).head?

/-- Per-component threshold vote: `some v` if at least `thr` of the votes for component `c`
equal `v` (checking `0` first, so ties choose `0`), else `none` (`⊥`). -/
noncomputable def thrVote (votes : List (List (Option Bool))) (thr : ℕ) (c : ℕ) : Option Bool :=
  let cnt : Bool → ℕ := fun v => (votes.filter (fun l => l.getD c none = some v)).length
  if thr ≤ cnt false then some false else if thr ≤ cnt true then some true else none

/-- The register this process keeps for itself among the outputs of its own operation number
`k` at global round `R`, when it is the receiver of output position `o`. -/
def ownOutput (V : View n F) (R k o : ℕ) : Option ℕ := ((V.allocs R).getD k [])[o]?

/-- The first register with header `(x, λ)` received from `s` at global round `R`. -/
def recvFrom (V : View n F) (R : ℕ) (s : Fin n) (x : ℕ) (lb : Lbl) : Option ℕ :=
  ((V.qin R).filter (fun m => m.1 = s)).head? >>= fun m =>
    (m.2.find? (fun e => e.1 = (x, lb))).map Prod.snd

variable (cf : Choices n F)

/-- Evaluation points of a block with `D` outputs: `α_1, …, α_D` (zero beyond `n`, never used). -/
def evalPts (D : ℕ) : Fin D → F := fun i => if h : i.1 < n then cf.α ⟨i.1, h⟩ else 0

/-! ### Encoder blocks as local operations -/

/-- A transfer block `V_{D,σ,p}` on `D` slots: the first `p` slots are the inputs (missing inputs
and padding are fresh `|0⟩` registers), the remaining `D - p` slots are fresh `|0⟩` ancillas
(the encoder prepares `σ` of them in `|+_q⟩`).  As an operator on the `D` slots it maps
`|s⟩ ⊗ |0⟩` to `V_{D,σ,p}|s⟩` (and annihilates basis states whose ancillas are not `0`). -/
noncomputable def blockOp (slots : List (Option ℕ)) (σ p : ℕ) : HOp F where
  slots := slots
  op := fun y z =>
    if ∀ i : Fin slots.length, p ≤ i.1 → z i = 0 then
      encoder slots.length σ p (evalPts cf slots.length) y
        (fun j : Fin p => if h : j.1 < slots.length then z ⟨j.1, h⟩ else 0)
    else 0

/-- The dealer block: `V_{D,σ,1}` applied to a fresh `|+_q⟩` (all `D` slots fresh). -/
noncomputable def dealerOp (D σ : ℕ) : HOp F where
  slots := List.replicate D none
  op := fun y z =>
    if z = 0 then
      ∑ s : Fin 1 → F, ((((Fintype.card F : ℝ) ^ (-(1 : ℝ) / 2)) : ℝ) : ℂ) *
        encoder (List.replicate D (none : Option ℕ)).length σ 1
          (evalPts cf (List.replicate D (none : Option ℕ)).length) y s
    else 0

/-- Coin bit `ψ(v)`. -/
def coinOf (v : F) : Bool := cf.ψ v = 1

end Helpers

section Algorithm

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)

/-! ### Tree, committees, forwarding graphs -/

/-- Index (0-based) of the level-`ℓ` ancestor of array `x ∈ [N]` (`ℓ = 0`: its level-0 list). -/
noncomputable def anc (ℓ x : ℕ) : ℕ := (x - 1) / (X.w * X.b ^ ℓ)

/-- `x` lies in the leaf interval of node `(ℓ, i)`. -/
noncomputable def inInterval (ℓ i x : ℕ) : Prop := 1 ≤ x ∧ x ≤ X.N ∧ anc X ℓ x = i

/-- The committee `C_v` of node `v = (ℓ, i)` (0-based index `i`), `1 ≤ ℓ ≤ h`. -/
noncomputable def comm (ℓ i : ℕ) : Finset (Fin n) :=
  X.comm ℓ i

/-- First level `ℓ ∈ [1, h]` with `k_ℓ = n` (`h` if there is none). Shares stop moving there. -/
noncomputable def lstar : ℕ :=
  if h : ∃ j, (1 ≤ j ∧ j ≤ X.h ∧ X.k j = n) then Nat.find h else X.h

/-- Level at which a word is used. -/
noncomputable def Lbl.lev : Lbl → ℕ → ℕ
  | .bin l, _ => l
  | .coin l, _ => l
  | .final, hh => hh

/-- The stage (level of the committee storing it) of a word with label `λ` when it is used. -/
noncomputable def sstage (lb : Lbl) : ℕ :=
  if X.h = 0 then 1 else min (lb.lev (X.h)) (lstar X)

/-- Committee storing the words of array `x` at stage `j` (`P` if `h = 0`). -/
noncomputable def stageComm (x j : ℕ) : Finset (Fin n) :=
  if X.h = 0 then Finset.univ else comm X j (anc X j x)

/-- Words of an array: `(bin, ℓ)`, `(coin, ℓ)` for `ℓ ∈ [h]` and `(final)`. -/
noncomputable def arrayLabels : List Lbl :=
  (List.range (X.h)).map (fun l => Lbl.bin (l + 1)) ++
  (List.range (X.h)).map (fun l => Lbl.coin (l + 1)) ++ [Lbl.final]

/-- Is there a transfer out of level `ℓ` (i.e. `1 ≤ ℓ < h` and `k_ℓ < n`)? -/
noncomputable def hasTransfer (ℓ : ℕ) : Prop := 1 ≤ ℓ ∧ ℓ < X.h ∧ X.k ℓ < n


/-- Forwarding neighbours of `s ∈ C_ℓ(x)` in `C_{ℓ+1}(x)`, in increasing order: the public graph
of Lemma 5.3 on committee positions, with out-degree `D_ℓ`. -/
noncomputable def nbrs (ℓ x : ℕ) (s : Fin n) : List (Fin n) := X.fwd ℓ (anc X ℓ x) s

/-- In-neighbours of `u ∈ C_{ℓ+1}(x)` in `C_ℓ(x)`, in increasing order (incoming-edge order). -/
noncomputable def inNbrs (ℓ x : ℕ) (u : Fin n) : List (Fin n) :=
  (sortedMembers (stageComm X x ℓ)).filter (fun s => u ∈ nbrs X ℓ x s)

/-! ### Reading the local log -/

/-- Global round index of round `ρ` of epoch `e`. -/
noncomputable def gRound (e ρ : ℕ) : ℕ := e * X.epochLen + ρ

/-- Start (round within the epoch) of the level-`ℓ` election, `1 ≤ ℓ ≤ h`. -/
noncomputable def lvlStart (ℓ : ℕ) : ℕ := 1 + (ℓ - 1) * (4 * X.r + 3)

/-- Delivery round (within the epoch) of level `ℓ`. -/
noncomputable def deliveryRound (ℓ : ℕ) : ℕ := lvlStart X ℓ + 2 + 4 * X.r

/-- Start (round within the epoch) of final phase `j ≥ 1`. -/
noncomputable def finStart (j : ℕ) : ℕ := 1 + X.h * (4 * X.r + 3) + 4 * (j - 1)

/-- The bin of a word value: the number formed by its first `log₂ b` bits. -/
noncomputable def binOf (v : F) : ℕ :=
  bitsToNat ((List.range (X.logb)).map (fun i =>
    if h : i < parDbits n then (X.cf.bitsOf v ⟨i, h⟩ = 1) else false))

/-! ### Normalization and lightest bin -/

/-- Normalization of the concatenated child lists of node `(ℓ, i)` (§3.2): a position coming
from child `c` keeps its identifier only if it lies in `I_c` and did not occur at an earlier kept
position; otherwise it becomes `0`.  Returns the kept flags. -/
noncomputable def normFlags (ℓ i : ℕ) (ys : List ℕ) : List Bool :=
  (List.range ys.length).map (fun j =>
    let y := ys.getD j 0
    let c := j / X.w
    decide (y ≠ 0 ∧ inInterval X (ℓ - 1) (i * X.b + c) y ∧
      ∀ j' < j, ¬ (ys.getD j' 0 = y ∧ inInterval X (ℓ - 1) (i * X.b + j' / X.w) y)))

/-- Normalized identifier list. -/
noncomputable def normalize (ℓ i : ℕ) (ys : List ℕ) : List ℕ :=
  (List.zip ys (normFlags X ℓ i ys)).map (fun e => if e.2 then e.1 else 0)

/-- Normalized identifier/bin pairs (rejected positions become `(0, 0)`). -/
noncomputable def normalizePairs (ℓ i : ℕ) (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.zip ps (normFlags X ℓ i (ps.map Prod.fst))).map (fun e => if e.2 then e.1 else (0, 0))

/-- Lightest-bin selection (Algorithm 4, lines 6–8): `S` = positions of a lightest bin (smallest
index among lightest), `T` = the first `w - |S|` remaining positions; output the identifiers at
`S` followed by those at `T`, each in increasing position order. -/
noncomputable def lightestBin (ps : List (ℕ × ℕ)) : List ℕ :=
  let cnt : ℕ → ℕ := fun z => (ps.filter (fun e => e.2 = z)).length
  let bins := List.range (X.b)
  let mn := (bins.map cnt).min?.getD 0
  let zstar := (bins.find? (fun z => cnt z = mn)).getD 0
  let idx := List.range ps.length
  let S := idx.filter (fun j => (ps.getD j (0, 0)).2 = zstar)
  let T := (idx.filter (fun j => (ps.getD j (0, 0)).2 ≠ zstar)).take (X.w - S.length)
  (S ++ T).map (fun j => (ps.getD j (0, 0)).1)

/-- Encode identifier/bin pairs as `u` bits (`ι` bits per identifier, `log₂ b` per bin). -/
noncomputable def encodePairs (ps : List (ℕ × ℕ)) : List Bool :=
  ps.flatMap (fun e => natToBits (X.iota) e.1 ++ natToBits (X.logb) e.2)

/-- Decode `u` bits into `r` identifier/bin pairs. -/
noncomputable def decodePairs (v : List Bool) : List (ℕ × ℕ) :=
  let s := X.iota + X.logb
  (List.range (X.r)).map (fun j =>
    (bitsToNat ((v.drop (j * s)).take (X.iota)),
     bitsToNat ((v.drop (j * s + X.iota)).take (X.logb))))

/-! ### Words: holdings, decoding -/

/-- Expected addresses held by holder `u` of a word of array `x` stored at stage `j`:
`(0, dealer(x))` for `j = 1`, and `(j-1, s)` for the in-neighbours `s` of `u` for `j ≥ 2`. -/
noncomputable def expectedAddrs (x j : ℕ) (u : Fin n) : List (ℕ × ℕ) :=
  if j ≤ 1 then [(0, dealer n x)] else
    (inNbrs X (j - 1) x u).map (fun s => (j - 1, s.1))

/-- Recursive decoding through the public circuit (§2.5, §5.3) of a word of array `x` stored at
stage `j*`, from readouts `rd u a` (readout reported by holder `u` at address `a`; missing values
are `0`).  Blocks at level `j` (holder `s`) have `D_j` outputs to `nbrs j x s` and `p_j` inputs
(their in-neighbours in order); the dealer block has `k₁` outputs to `C₁(x)`.  Decoding a block
returns the first `p` coefficients of `Dec_{p+σ-1}` of its outputs; the word value is the
constant coefficient decoded at the dealer block. -/
noncomputable def recDecode (x jstar : ℕ) (rd : Fin n → (ℕ × ℕ) → F) : F :=
  -- `inputsAt m s` = decoded inputs of the block of holder `s` at level `jstar - 1 - m`
  let blockIn : ℕ → (Fin n → List F) := fun m0 =>
    Nat.rec (motive := fun _ => Fin n → List F)
      (fun s =>
        let j := jstar - 1
        let outs := (nbrs X j x s).map (fun u => rd u (j, s.1))
        let D := outs.length
        let c := rsDecode (X.p j + X.sigma D - 1) (evalPts X.cf D) (fun i => outs.getD i.1 0)
        (List.range (X.p j)).map (fun i => if h : i < X.p j + X.sigma D - 1 + 1 then c ⟨i, h⟩ else 0))
      (fun m prev s =>
        let j := jstar - 1 - (m + 1)
        let outs := (nbrs X j x s).map (fun u =>
          let ins := inNbrs X j x u
          (prev u).getD (ins.idxOf s) 0)
        let D := outs.length
        let c := rsDecode (X.p j + X.sigma D - 1) (evalPts X.cf D) (fun i => outs.getD i.1 0)
        (List.range (X.p j)).map (fun i => if h : i < X.p j + X.sigma D - 1 + 1 then c ⟨i, h⟩ else 0))
      m0
  let C1 := sortedMembers (stageComm X x 1)
  let douts : List F := C1.map (fun u =>
    if jstar ≤ 1 then rd u (0, dealer n x) else (blockIn (jstar - 2) u).getD 0 0)
  let D := douts.length
  rsDecode (X.sigma D) (evalPts X.cf D) (fun i => douts.getD i.1 0) ⟨0, Nat.succ_pos _⟩

/-! ### The protocol, read off the local log -/

variable (V : View n F)

/-- Classical messages received at round `ρ` of epoch `e`. -/
noncomputable def cinAt (e ρ : ℕ) : List (Fin n × Msg F) := V.cin (gRound X e ρ)

/-- Accepted child lists of node `(ℓ, i)` in epoch `e`, concatenated (not yet normalized):
level 1 uses the public level-0 lists; for `ℓ ≥ 2` a list is accepted only if a strict majority of
the child's committee sent exactly that list (well-formed: `w` entries) in the delivery round of
level `ℓ - 1`; otherwise `w` zeros.  The process's own list counts if it is a child member. -/
noncomputable def childLists (ownOut : ℕ → ℕ → List ℕ) (e ℓ i : ℕ) : List ℕ :=
  (List.range (X.b)).flatMap (fun c =>
    let ci := i * X.b + c
    if ℓ ≤ 1 then (List.range (X.w)).map (fun j => ci * X.w + j + 1)
    else
      let C := comm X (ℓ - 1) ci
      let ms := cinAt X V e (deliveryRound X (ℓ - 1))
      let sent : Fin n → Option (List ℕ) := fun s =>
        if s = V.me then (if V.me ∈ C then some (ownOut (ℓ - 1) ci) else none)
        else firstFrom ms (fun m => match m with
          | .childList l i' ids => if l = ℓ - 1 ∧ i' = ci then some ids else none
          | _ => none) s
      let cands := (sortedMembers C).filterMap sent
      match cands.find? (fun L => L.length = X.w ∧
          2 * ((sortedMembers C).filter (fun s => sent s = some L)).length > C.card) with
      | some L => L
      | none => List.replicate (X.w) 0)

/-- Readouts (address ↦ value) a requester obtains for word `(x, λ)` from the replies received at
round `R` (tag `(l, i)`), for holder `u`: at most one value per expected address (the first),
missing ones `0`; its own stored registers are read locally. -/
noncomputable def readoutsFrom (ownPairs : List ((ℕ × ℕ) × F)) (R l i x : ℕ) (lb : Lbl) (jstar : ℕ) :
    Fin n → (ℕ × ℕ) → F := fun u a =>
  let pairs : List ((ℕ × ℕ) × F) :=
    if u = V.me then ownPairs else
      (firstFrom (V.cin R) (fun m => match m with
        |   .reply l' i' x' lb' ps => if l' = l ∧ i' = i ∧ x' = x ∧ lb' = lb then some ps else none
        | _ => none) u).getD []
  if a ∈ expectedAddrs X x jstar u then ((pairs.find? (fun e => e.1 = a)).map Prod.snd).getD 0 else 0

/-- Nodes of level `ℓ` whose committee contains this process. -/
noncomputable def myNodes (ℓ : ℕ) : List ℕ :=
  (List.range (X.m ℓ)).filter (fun i => V.me ∈ comm X ℓ i)

/-- Words dealt by this process in an epoch: its arrays `x ∈ [N]` with `dealer(x) = p`, each
with its `M` labels, in a fixed order (the order of its distribution operations). -/
noncomputable def distWords : List (ℕ × Lbl) :=
  ((List.range (X.N)).map (· + 1)).filter (fun x => dealer n x = V.me.1) |>.flatMap
    (fun x => (arrayLabels X).map (fun lb => (x, lb)))

end Algorithm

/-! ### Elections, root list and final agreement, read off the log

The level-by-level recursion needs the transfer descriptors, so the remaining definitions are
stated as one block. -/

section Run

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F) (V : View n F)

/-- Descriptors (word, in-edge list) of this process's transfer operations in the delivery round
of level `ℓ` of epoch `e`, given its election outputs `out` at level `ℓ`: for each node of level
`ℓ` containing it (increasing index), each nonzero array of its own output list, each unopened
word label (level `> ℓ`). -/
noncomputable def transferWords (out : ℕ → List ℕ) (ℓ : ℕ) : List (ℕ × Lbl) :=
  if hasTransfer X ℓ then
    (myNodes X V ℓ).flatMap (fun i =>
      ((out i).filter (· ≠ 0)).dedup.flatMap (fun x =>
        ((arrayLabels X).filter (fun lb => ℓ < lb.lev (X.h))).map (fun lb => (x, lb))))
  else []

/-- Registers this process stores for word `(x, λ)` at stage `j` of epoch `e`, with their
addresses, given its election outputs `outs ℓ i` (used to locate its own self-addressed transfer
outputs).  Stage 1: the register received from (or, for its own arrays, kept by) the dealer in
the distribution round.  Stage `j ≥ 2`: for each in-neighbour `s ∈ C_{j-1}(x)`, the register
received from `s` (or its own output if `s` is itself) in the delivery round of level `j - 1`.
At most one register per word and incoming edge is accepted. -/
noncomputable def stored (outs : ℕ → ℕ → List ℕ) (e x : ℕ) (lb : Lbl) (j : ℕ) : List ((ℕ × ℕ) × ℕ) :=
  if j ≤ 1 then
    if V.me ∈ stageComm X x 1 then
      let R0 := gRound X e 0
      let d : ℕ := dealer n x
      let reg : Option ℕ :=
        if d = V.me.1 then
          ownOutput V R0 ((distWords X V).idxOf (x, lb))
            ((sortedMembers (stageComm X x 1)).idxOf V.me)
        else if hd : d < n then recvFrom V R0 ⟨d, hd⟩ x lb else none
      match reg with
      | some r => [((0, d), r)]
      | none => []
    else []
  else
    if V.me ∈ stageComm X x j then
      let R := gRound X e (deliveryRound X (j - 1))
      (inNbrs X (j - 1) x V.me).filterMap (fun s =>
        let reg : Option ℕ :=
          if s = V.me then
            ownOutput V R ((transferWords X V (outs (j - 1)) (j - 1)).idxOf (x, lb))
              ((nbrs X (j - 1) x V.me).idxOf V.me)
          else recvFrom V R s x lb
        reg.map (fun r => ((j - 1, s.1), r)))
    else []

/-- Stored registers of a word at the stage where it is used (shares stop moving at the first
committee equal to `P`). -/
noncomputable def storedUse (outs : ℕ → ℕ → List ℕ) (e x : ℕ) (lb : Lbl) : List ((ℕ × ℕ) × ℕ) :=
  stored X V outs e x lb (sstage X lb)

/-- Address–value pairs of this holder's measured stored registers of word `(x, λ)`. -/
noncomputable def ownPairs (outs : ℕ → ℕ → List ℕ) (e x : ℕ) (lb : Lbl) : List ((ℕ × ℕ) × F) :=
  (storedUse X V outs e x lb).filterMap (fun a => (V.readout a.2).map (fun v => (a.1, v)))

/-- Reconstructed value of word `(x, λ)` from the replies received at global round `R` with tag
`(l, i)` (identifier `0`: value `0`, no request). -/
noncomputable def reconstruct (outs : ℕ → ℕ → List ℕ) (e R l i x : ℕ) (lb : Lbl) : F :=
  if x = 0 then 0 else
    recDecode X x (sstage X lb)
      (readoutsFrom X V (ownPairs X V outs e x lb) R l i x lb (sstage X lb))

/-- One election of node `(ℓ, i)` in epoch `e` (Algorithm 4 with Algorithm 3 inside), given the
process's outputs `prev` at level `ℓ - 1` and its outputs `outs` (for its stored registers).
Returns the frozen provider list `Y`, the estimate vector after each phase, and the proposals. -/
noncomputable def elect (outs : ℕ → ℕ → List ℕ) (prev : ℕ → ℕ → List ℕ) (e ℓ i : ℕ) :
    List ℕ × (ℕ → List Bool) × (ℕ → List (Option Bool)) :=
  let Y := normalize X ℓ i (childLists X V prev e ℓ i)
  let C := comm X ℓ i
  let a := aThr C.card
  let u := X.u
  let others := (sortedMembers C).filter (· ≠ V.me)
  let Rb := gRound X e (lvlStart X ℓ + 1)
  let z : List ℕ := Y.map (fun x => if x = 0 then 0 else binOf X (reconstruct X V outs e Rb ℓ i x (.bin ℓ)))
  let est0 := encodePairs X (List.zip Y z)
  let R1 : ℕ → ℕ := fun j => gRound X e (lvlStart X ℓ + 2 + 4 * (j - 1))
  -- proposal vector of phase `j` given the estimate at its start
  let propOf : ℕ → List Bool → List (Option Bool) := fun j x =>
    let votes := (x.map some) :: others.map (fun m =>
      ((firstFrom (V.cin (R1 j)) (fun msg => match msg with
        | .est l i' j' v => if l = ℓ ∧ i' = i ∧ j' = j ∧ v.length = u then some (v.map some) else none
        | _ => none) m).getD []))
    (List.range u).map (thrVote votes (C.card - a))
  let step : ℕ → List Bool → List Bool := fun j x =>
    let y := propOf j x
    let votes := y :: others.map (fun m =>
      ((firstFrom (V.cin (R1 j + 1)) (fun msg => match msg with
        | .prop l i' j' v => if l = ℓ ∧ i' = i ∧ j' = j ∧ v.length = u then some v else none
        | _ => none) m).getD []))
    let f := (List.range u).map (thrVote votes (a + 1))
    let c := coinOf X.cf (reconstruct X V outs e (R1 j + 3) ℓ i (Y.getD (j - 1) 0) (.coin ℓ))
    f.map (fun fc => fc.getD c)
  let estAfter : ℕ → List Bool := fun j0 =>
    Nat.rec (motive := fun _ => List Bool) est0 (fun j x => step (j + 1) x) j0
  (Y, estAfter, fun j => propOf j (estAfter (j - 1)))

/-- The process's output lists `A_v` of all levels `≤ L` in epoch `e` (`allOuts e L l i` is the
output of node `(l, i)` for `1 ≤ l ≤ L`, empty otherwise), computed level by level. -/
noncomputable def allOuts (e : ℕ) : ℕ → ℕ → ℕ → List ℕ :=
  fun L0 =>
    Nat.rec (motive := fun _ => ℕ → ℕ → List ℕ) (fun _ _ => [])
      (fun L prev l i =>
        if l = L + 1 then
          let r := elect X V prev prev e (L + 1) i
          lightestBin X (normalizePairs X (L + 1) i (decodePairs X (r.2.1 (X.r))))
        else prev l i)
      L0

/-- The process's output lists of epoch `e`, all levels. -/
noncomputable def outsE (e : ℕ) : ℕ → ℕ → List ℕ := allOuts X V e (X.h)

/-- The frozen provider list of node `(ℓ, i)` in epoch `e`. -/
noncomputable def provList (e ℓ i : ℕ) : List ℕ := (elect X V (outsE X V e) (outsE X V e) e ℓ i).1

/-- The local root list of epoch `e`: the public level-0 list if `h = 0`, otherwise the process's
output at the root node. -/
noncomputable def rootList (e : ℕ) : List ℕ :=
  if X.h = 0 then (List.range (X.w)).map (· + 1)
  else if V.me ∈ comm X (X.h) 0 then outsE X V e (X.h) 0
  else List.replicate (X.w) 0

/-- Final agreement (Algorithm 5), final phase number `g` (0-based, across epochs): phase
`j = g mod (w+1) + 1` of epoch `g / (w+1)`.  From the state `(estimate, decision)` at its start,
returns the state at its end; the decision is updated at the proposal deadline (end of round 2):
an undecided process decides `v` if at least `n - t` proposals equal `v`. -/
noncomputable def finalPhase (g : ℕ) (st : Bool × Option Bool) : Bool × Option Bool :=
  let e := g / (X.w + 1)
  let j := g % (X.w + 1) + 1
  let R1 := gRound X e (finStart X j)
  let others := (List.finRange n).filter (· ≠ V.me)
  let votesE := [some st.1] :: others.map (fun m =>
    ((firstFrom (V.cin R1) (fun msg => match msg with
      | .est l i j' v => if l = 0 ∧ i = 0 ∧ j' = j ∧ v.length = 1 then some (v.map some) else none
      | _ => none) m).getD []))
  let y := thrVote votesE (n - X.t) 0
  let votesP := [y] :: others.map (fun m =>
    ((firstFrom (V.cin (R1 + 1)) (fun msg => match msg with
      | .prop l i j' v => if l = 0 ∧ i = 0 ∧ j' = j ∧ v.length = 1 then some v else none
      | _ => none) m).getD []))
  let dec := match st.2 with
    | some v => some v
    | none => thrVote votesP (n - X.t) 0
  let f := thrVote votesP (X.t + 1) 0
  let x := (rootList X V e).getD (j - 1) 0
  let c := if j ≤ X.w then coinOf X.cf (reconstruct X V (outsE X V e) e (R1 + 3) 0 0 x .final) else false
  (f.getD c, dec)

/-- State `(estimate, decision)` after `g` final phases. -/
noncomputable def finalRun (g : ℕ) : Bool × Option Bool :=
  Nat.rec (motive := fun _ => Bool × Option Bool) (V.input, none)
    (fun g' st => finalPhase X V g' st) g

/-- Global round at which final phase `g` starts. -/
noncomputable def finalPhaseRound (g : ℕ) : ℕ :=
  gRound X (g / (X.w + 1)) (finStart X (g % (X.w + 1) + 1))

/-- Number of final phases whose proposal round has been completed. -/
noncomputable def finalPhasesDecidable : ℕ :=
  ((List.range (V.ins.length + 1)).filter (fun g => finalPhaseRound X g + 1 < V.ins.length)).length

/-- Position of global round `R` inside the level loop: `some (ℓ, o)` for offset `o` of the
level-`ℓ` election. -/
noncomputable def lvlPos (R : ℕ) : Option (ℕ × ℕ) :=
  let ρ := R % X.epochLen
  let B := 4 * X.r + 3
  if 1 ≤ ρ ∧ ρ < 1 + X.h * B then some ((ρ - 1) / B + 1, (ρ - 1) % B) else none

/-- Position of global round `R` inside final agreement: `some (j, sub)` for round `sub + 1` of
final phase `j`. -/
noncomputable def finPos (R : ℕ) : Option (ℕ × ℕ) :=
  let ρ := R % X.epochLen
  let s0 := 1 + X.h * (4 * X.r + 3)
  if s0 ≤ ρ then some ((ρ - s0) / 4 + 1, (ρ - s0) % 4) else none

/-- Current global round (number of completed rounds) and epoch. -/
def View.round (V : View n F) : ℕ := V.ins.length

/-- Current epoch. -/
noncomputable def curEpoch : ℕ := V.round / X.epochLen

/-- Input slots of this process's transfer block for word `(x, λ)` at level `ℓ`: its stored
registers in incoming-edge order (missing ones fresh `|0⟩`), padded to `p_ℓ` fresh `|0⟩`
registers, followed by `D_ℓ - p_ℓ` fresh ancillas. -/
noncomputable def transferSlots (e ℓ x : ℕ) (lb : Lbl) : List (Option ℕ) :=
  let outs := outsE X V e
  let st := stored X V outs e x lb ℓ
  let ins : List (ℕ × ℕ) :=
    if ℓ ≤ 1 then [(0, dealer n x)] else (inNbrs X (ℓ - 1) x V.me).map (fun s => (ℓ - 1, s.1))
  let pl := X.p ℓ
  let inp : List (Option ℕ) := (ins.map (fun a => (st.find? (fun e => e.1 = a)).map Prod.snd)).take pl
  let D := (nbrs X ℓ x V.me).length
  inp ++ List.replicate (pl - inp.length) none ++ List.replicate (D - pl) none

/-- Quantum operations of this process in the current round: dealer blocks in the distribution
round, transfer blocks (Algorithm 2) in a delivery round with transfer. -/
noncomputable def qbaOps : List (HOp F) :=
  let R := V.round
  let e := curEpoch X V
  if R % X.epochLen = 0 then
    (distWords X V).map (fun w =>
      let D := (sortedMembers (stageComm X w.1 1)).length
      dealerOp X.cf D (X.sigma D))
  else match lvlPos X R with
    | some (ℓ, o) =>
      if o = 2 + 4 * X.r then
        (transferWords X V (outsE X V e ℓ) ℓ).map (fun w =>
          let D := (nbrs X ℓ w.1 V.me).length
          blockOp X.cf (transferSlots X V e ℓ w.1 w.2) (X.sigma D) (X.p ℓ))
      else []
    | none => []

/-- Registers this process measures (opens) in the current round: the level's bin words of its
provider list in the bin round; the coin word of position `j` of its provider list in round 3 of
phase `j`; the final word of position `j` of its root list in round 3 of final phase `j ≤ w`. -/
noncomputable def qbaMeas : List ℕ :=
  let R := V.round
  let e := curEpoch X V
  let outs := outsE X V e
  let regsOf : ℕ → Lbl → List ℕ := fun x lb =>
    if x = 0 then [] else (storedUse X V outs e x lb).map Prod.snd
  match lvlPos X R with
  | some (ℓ, o) =>
    if o = 0 then
      (myNodes X V ℓ).flatMap (fun i => (provList X V e ℓ i).flatMap (fun x => regsOf x (.bin ℓ)))
    else if 2 ≤ o ∧ o < 2 + 4 * X.r ∧ (o - 2) % 4 = 2 then
      (myNodes X V ℓ).flatMap (fun i =>
        regsOf ((provList X V e ℓ i).getD ((o - 2) / 4) 0) (.coin ℓ))
    else []
  | none => match finPos X R with
    | some (j, sub) =>
      if sub = 2 ∧ j ≤ X.w then regsOf ((rootList X V e).getD (j - 1) 0) .final else []
    | none => []

/-- Proposal bit of final phase `g` (Algorithm 5, line 5). -/
noncomputable def finalY (g : ℕ) : Option Bool :=
  let e := g / (X.w + 1)
  let j := g % (X.w + 1) + 1
  let R1 := gRound X e (finStart X j)
  let others := (List.finRange n).filter (· ≠ V.me)
  let votesE := [some (finalRun X V g).1] :: others.map (fun m =>
    ((firstFrom (V.cin R1) (fun msg => match msg with
      | .est l i j' v => if l = 0 ∧ i = 0 ∧ j' = j ∧ v.length = 1 then some (v.map some) else none
      | _ => none) m).getD []))
  thrVote votesE (n - X.t) 0

/-- Replies to the whole-word requests received in the previous round, subject to the
authorization, stage, opening and per-requester quota rules of §3.2: at most `r` bin requests per
requester and node, one coin request per requester, node and phase, one final-word request per
requester and final phase; only for words already opened under the holder's own frozen list. -/
noncomputable def qbaReplies : List (Fin n × Msg F) :=
  let R := V.round
  let e := curEpoch X V
  let outs := outsE X V e
  let reqs := V.cin (R - 1)
  let reqOf : Msg F → Option (ℕ × ℕ × ℕ × Lbl) := fun m => match m with
    | .req l i x lb => some (l, i, x, lb)
    | _ => none
  let senders := (List.finRange n).filter (· ≠ V.me)
  if R = 0 then [] else
  senders.flatMap (fun q =>
    let qs := (reqs.filter (fun m => m.1 = q)).filterMap (fun m => reqOf m.2)
    -- position of a request among the requests of the same category from `q`
    let ok : ℕ → (ℕ × ℕ × ℕ × Lbl) → Prop := fun pos rq =>
      let same := (qs.take pos).filter (fun r' => r'.1 = rq.1 ∧ r'.2.1 = rq.2.1 ∧
        (match r'.2.2.2, rq.2.2.2 with
          | .bin _, .bin _ => True
          | .coin _, .coin _ => True
          | .final, .final => True
          | _, _ => False))
      match rq.2.2.2, lvlPos X R, finPos X R with
      | .bin l, some (ℓ, o), _ =>
          l = ℓ ∧ o = 1 ∧ rq.1 = l ∧ V.me ∈ comm X l rq.2.1 ∧ q ∈ comm X l rq.2.1 ∧
          rq.2.2.1 ≠ 0 ∧ rq.2.2.1 ∈ provList X V e l rq.2.1 ∧ same.length < X.r
      | .coin l, some (ℓ, o), _ =>
          l = ℓ ∧ 2 ≤ o ∧ o < 2 + 4 * X.r ∧ (o - 2) % 4 = 3 ∧ rq.1 = l ∧
          V.me ∈ comm X l rq.2.1 ∧ q ∈ comm X l rq.2.1 ∧ rq.2.2.1 ≠ 0 ∧
          rq.2.2.1 ∈ (provList X V e l rq.2.1).take ((o - 2) / 4 + 1) ∧ same.length < 1
      | .final, _, some (j, sub) =>
          sub = 3 ∧ j ≤ X.w ∧ rq.1 = 0 ∧ rq.2.1 = 0 ∧ rq.2.2.1 ≠ 0 ∧
          rq.2.2.1 ∈ (rootList X V e).take j ∧ same.length < 1
      | _, _, _ => False
    ((List.range qs.length).filter (fun pos => ok pos (qs.getD pos (0, 0, 0, .final)))).map (fun pos =>
      let rq := qs.getD pos (0, 0, 0, .final)
      (q, Msg.reply rq.1 rq.2.1 rq.2.2.1 rq.2.2.2 (ownPairs X V outs e rq.2.2.1 rq.2.2.2))))

/-- Classical messages of the current round. -/
noncomputable def qbaClassical : List (Fin n × Msg F) :=
  let R := V.round
  let e := curEpoch X V
  let outs := outsE X V e
  let holdersOf : ℕ → Lbl → List (Fin n) := fun x lb =>
    (sortedMembers (stageComm X x (sstage X lb))).filter (· ≠ V.me)
  match lvlPos X R with
  | some (ℓ, o) =>
    if o = 0 then
      (myNodes X V ℓ).flatMap (fun i => ((provList X V e ℓ i).filter (· ≠ 0)).flatMap (fun x =>
        (holdersOf x (.bin ℓ)).map (fun u => (u, Msg.req ℓ i x (.bin ℓ)))))
    else if o = 1 then qbaReplies X V
    else if o < 2 + 4 * X.r then
      let j := (o - 2) / 4 + 1
      let sub := (o - 2) % 4
      (myNodes X V ℓ).flatMap (fun i =>
        let r := elect X V outs outs e ℓ i
        let others := (sortedMembers (comm X ℓ i)).filter (· ≠ V.me)
        if sub = 0 then others.map (fun m => (m, Msg.est ℓ i j (r.2.1 (j - 1))))
        else if sub = 1 then others.map (fun m => (m, Msg.prop ℓ i j (r.2.2 j)))
        else if sub = 2 then
          (let x := r.1.getD (j - 1) 0
           if x = 0 then [] else (holdersOf x (.coin ℓ)).map (fun u => (u, Msg.req ℓ i x (.coin ℓ))))
        else []) ++ (if sub = 3 then qbaReplies X V else [])
    else
      if ℓ < X.h then
        (myNodes X V ℓ).flatMap (fun i =>
          ((sortedMembers (comm X (ℓ + 1) (i / X.b))).filter (· ≠ V.me)).map (fun m =>
            (m, Msg.childList ℓ i (outs ℓ i))))
      else []
  | none => match finPos X R with
    | some (j, sub) =>
      let g := e * (X.w + 1) + (j - 1)
      let others := (List.finRange n).filter (· ≠ V.me)
      if sub = 0 then others.map (fun m => (m, Msg.est 0 0 j [(finalRun X V g).1]))
      else if sub = 1 then others.map (fun m => (m, Msg.prop 0 0 j [finalY X V g]))
      else if sub = 2 then
        (let x := (rootList X V e).getD (j - 1) 0
         if j ≤ X.w ∧ x ≠ 0 then (holdersOf x .final).map (fun u => (u, Msg.req 0 0 x .final)) else [])
      else qbaReplies X V
    | none => []

/-- Quantum messages of the current round: output `o` of a block goes to its `o`-th recipient
(the `o`-th member of the first committee for a dealer block, the `o`-th forwarding neighbour for
a transfer block); a self-addressed output is kept.  One message per recipient. -/
noncomputable def qbaQuantum (allocs : List (List ℕ)) : List (Fin n × List (Hd × ℕ)) :=
  let R := V.round
  let e := curEpoch X V
  let entries : List (Fin n × (Hd × ℕ)) :=
    if R % X.epochLen = 0 then
      (List.range (distWords X V).length).flatMap (fun k =>
        let w := (distWords X V).getD k (0, .final)
        let rec_ := sortedMembers (stageComm X w.1 1)
        (List.range rec_.length).filterMap (fun o =>
          match rec_[o]?, (allocs.getD k [])[o]? with
          | some u, some reg => if u = V.me then none else some (u, (w, reg))
          | _, _ => none))
    else match lvlPos X R with
      | some (ℓ, o) =>
        if o = 2 + 4 * X.r then
          let ws := transferWords X V (outsE X V e ℓ) ℓ
          (List.range ws.length).flatMap (fun k =>
            let w := ws.getD k (0, .final)
            let rec_ := nbrs X ℓ w.1 V.me
            (List.range rec_.length).filterMap (fun o' =>
              match rec_[o']?, (allocs.getD k [])[o']? with
              | some u, some reg => if u = V.me then none else some (u, (w, reg))
              | _, _ => none))
        else []
      | none => []
  ((List.finRange n).filter (· ≠ V.me)).filterMap (fun u =>
    let es := (entries.filter (fun e' => e'.1 = u)).map Prod.snd
    if es = [] then none else some (u, es))

/-- Decision of the process (Algorithm 5, line 7). For `n = 1` the process decides its input at
once. -/
noncomputable def qbaDecision : Option Bool :=
  if n ≤ 1 then some V.input else (finalRun X V (finalPhasesDecidable X V)).2

/-- The delayed-halt rule (Algorithm 5, lines 3 and 12): the process halts at the end of the
first final phase at whose start it had already decided.  For `n = 1` it halts at once. -/
noncomputable def qbaHalted : Bool :=
  if n ≤ 1 then true else
    decide (∃ g < V.round + 1, finalPhaseRound X g + 3 < V.round ∧ (finalRun X V g).2.isSome)

end Run

/-- **QBA:PackedShares** (Algorithm 1 with the sharing scheme of §2.4/§5.2), as a protocol of the
model of §1.1, for `n` processes and symbolic parameters `X` (the headline algorithm uses the
parameters (11), `ctx11`). -/
noncomputable def qba {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (X : Ctx n F) : Protocol n F where
  St := View n F
  M := Msg F
  Hd := Hd
  mbits := Msg.bits (Nat.log 2 (Fintype.card F))
  hbits := fun hd => natBits hd.1 + hd.2.bits
  init := fun p b => ⟨p, b, [], []⟩
  ops := fun _ V => if n ≤ 1 then [] else qbaOps X V
  meas := fun _ V => if n ≤ 1 then [] else qbaMeas X V
  out := fun _ V allocs vals =>
    let V' : View n F := { V with outs := V.outs ++ [(allocs, vals)] }
    if n ≤ 1 then (V', [], []) else (V', qbaClassical X V, qbaQuantum X V allocs)
  recv := fun _ V cs qs => { V with ins := V.ins ++ [(cs, qs)] }
  decision := fun V => qbaDecision X V
  halted := fun V => qbaHalted X V



end QuantumBA.PackedShares

namespace QuantumBA.PackedShares

/-- The headline instance: QBA:PackedShares with the parameters (11) (`c = 1`): committees are
the first valid tables of Lemma 4.4 (`P` for capped levels), forwarding graphs the first valid
graphs of Lemma 5.3 on committee positions, `D_ℓ = ⌈C_ε L k_{ℓ+1}/k_ℓ⌉`, `J = ⌈6C_ε L⌉`. -/
noncomputable def ctx11 (ε : ℝ) (n t : ℕ) {F : Type} [Field F] (cf : Choices n F) : Ctx n F where
  ε := ε
  t := t
  b := parB ε
  w := parW ε n
  h := parh ε n
  k := parK ε n
  comm := fun ℓ i =>
    if hi : i < parM ε n ℓ then committeeTable ε (parBeta ε n) n t (parM ε n ℓ) (parK ε n ℓ) ⟨i, hi⟩
    else ∅
  fwd := fun ℓ i s =>
    let C := fun ℓ' i' => if hi : i' < parM ε n ℓ' then
      committeeTable ε (parBeta ε n) n t (parM ε n ℓ') (parK ε n ℓ') ⟨i', hi⟩ else ∅
    let rows := sortedMembers (C ℓ i)
    let cols := sortedMembers (C (ℓ + 1) (i / parB ε))
    let G := forwardingGraph (parRho ε) n (parK ε n ℓ) (parK ε n (ℓ + 1)) (parD ε n ℓ)
    if h : rows.idxOf s < parK ε n ℓ then
      ((G ⟨rows.idxOf s, h⟩).sort (· ≤ ·)).filterMap (fun c => cols[c.1]?)
    else []
  D := parD ε n
  J := parJ ε n
  cf := cf

end QuantumBA.PackedShares



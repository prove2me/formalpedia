-- Prove2me | Definitions.Def_NovyPQZK_Main_Novy
-- name    : NovyPQZK_Main_Novy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:37:44.078548+00:00
-- url     : https://prove2.me/theorems/72ec7c44-2da6-4847-9041-090be4befe71
-- title:
--   The novy interactive hashing and bit commitment scheme (p. 2, Fig. 1), its π-Bind experiment and π-binding (Experiment 8, Definition 14)
-- statement:
--   **Interactive hashing** $\Pi_{\text{int-hash}}(1^n, y)$: for $i = 1,\dots,n-1$ Rachel sends $h_i = 0^{i-1}\,\|\,1\,\|\,r$ with $r\in_R\{0,1\}^{n-i}$ and Sam answers $z_i = \langle y,h_i\rangle$ (inner product mod 2). The outputs $y_0 <_{\mathrm{lex}} y_1$ are the two strings consistent with every $(h_i,z_i)$.
--
--   **novy** instantiated with $\pi$ (Fig. 1). Committing phase on bit $b$: Sam picks $x\in_R\{0,1\}^n$, sets $y = \pi_n(x)$, runs $\Pi_{\text{int-hash}}(1^n,y)$, and announces $d = b\oplus\beta$ where $y = y_\beta$. Opening: Sam announces $b$, $x$, $y$; Rachel accepts iff there is $\beta\in\{0,1\}$ with $y = y_\beta$, $\pi_n(x) = y$ and $b = d\oplus\beta$. It has unique openings and is publicly verifiable by construction.
--
--   **$\pi$-Bind** (Exp. 8): $S_n$ runs $\Pi_{\text{int-hash}}$ with an honest Rachel (transcript $t$, outputs $y_0(t), y_1(t)$), then outputs $(x_0,x_1)$; success iff $\pi_n(x_0) = y_0(t)$ and $\pi_n(x_1) = y_1(t)$. novy is **computational $\pi$-binding** (Def. 14) if every QPT $S$ succeeds with probability $\le\mathrm{negl}(n)$.
--
--   **Formalization Note** $\mathrm{Public}_n = 1^n$ ($1^1$ at $n = 0$, where the scheme is undefined); the committing phase has $(n-1)+1$ rounds, Rachel sending the empty string in the last while Sam sends $d$; the opening is $u = \mathrm{pack}[x,y]$, $R_{open}$ also checks that the transcript has this shape. Sam's behaviour on a malformed challenge is not in the source: he aborts, sending the empty string from then on, which does not depend on $b$. In $\pi$-Bind the answer $z_i$ is the first bit of what $S_n$ outputs at round $i$.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), pp. 2–3 (box Π_int-hash, Fig. 1) and §4 pp. 27–28, Experiment 8 and Definition 14

import Mathlib
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_NovyPQZK_Main_Binding
import Definitions.Def_NovyPQZK_Main_OWP

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), pp. 2–3
(the boxed `Π_int-hash` and Fig. 1) and §4, pp. 27–28 (Experiment 8, Definition 14): the novy
interactive hashing, the novy bit commitment scheme instantiated with a permutation family `π`, and
its `π`-binding experiment.

`Π_int-hash(1^n, y)`: for `i = 1, …, n − 1`, Rachel picks `h_i = 0^{i−1} ‖ 1 ‖ r`,
`r ∈_R {0,1}^{n−i}`, and Sam answers `z_i = ⟨y, h_i⟩` (inner product mod 2); the outputs are the two
strings `y₀ <_lex y₁` consistent with every `(h_i, z_i)`.

Committing phase: Sam picks `x ∈_R {0,1}^n`, sets `y = π_n(x)`, runs `Π_int-hash`, and announces
`d = b ⊕ β` where `y = y_β`. Opening: Sam announces `b, x, y`; Rachel accepts iff there is `β`
with `y = y_β`, `π_n(x) = y` and `b = d ⊕ β`.

Encodings: `Public_n = 1^n`, except `Public_0 = 1^1` (the scheme is undefined at `n = 0`, where
`{0,1}^0` has one element; it runs as at `n = 1`); the committing phase has `(n − 1) + 1` rounds (the last one: Rachel
sends the empty string, Sam sends `d`); the opening is `u = pack [x, y]`. Sam's behaviour on a
malformed challenge (not of the form `0^{i−1} ‖ 1 ‖ r` with `|r| = n − i`), which the source does not
specify, is: abort, i.e. send the empty string from then on (independent of `b`).
-/

/-- The inner product mod 2 of two strings. -/
def ip (h y : Bits) : Bool := ((h.zip y).map fun p => p.1 && p.2).foldl xor false

/-- The `n`-bit string of `v` written most significant bit first; `v ↦ msbStr n v` lists
`{0,1}^n` in lexicographic order as `v` runs through `0, …, 2^n − 1`. -/
def msbStr (n v : ℕ) : Bits := (List.range n).map fun i => v.testBit (n - 1 - i)

/-- `h` is a legitimate round-`i` challenge `0^{i−1} ‖ 1 ‖ r` of length `n` (`i ≥ 1`). -/
def wellFormedH (n i : ℕ) (h : Bits) : Bool :=
  decide (h.length = n) && (h.take (i - 1)).all (fun b => !b) && h.getD (i - 1) false

/-- The strings of `{0,1}^n` consistent with every `(h_i, z_i)`, in lexicographic order. -/
def consistentList (n : ℕ) (hs : List Bits) (zs : List Bool) : List Bits :=
  ((List.range (2 ^ n)).map (msbStr n)).filter fun y => (hs.zip zs).all fun p => ip p.1 y == p.2

/-- Rachel (receiver of novy and of `Π_int-hash`): input `1^n`; her coins are the `r` of rounds
`1, …, n − 1`; in round `i ≤ n − 1` she sends `h_i`, afterwards the empty string. -/
def novyReceiver : Party where
  coins pub := (List.range (pub.length - 1)).map fun j => 2 ^ (pub.length - (j + 1))
  next view := match unpack view with
    | inp :: cenc :: msgs =>
        let n := inp.length
        let j := msgs.length
        if j < n - 1 then
          List.replicate j false ++ [true] ++ msbStr (n - (j + 1)) (((unpack cenc).map bitsToNat).getD j 0)
        else []
    | _ => []

/-- Sam's `x` from his coin (`x ∈_R {0,1}^n`). -/
def novyX (n : ℕ) (cenc : Bits) : Bits := msbStr n (((unpack cenc).map bitsToNat).getD 0 0)

/-- Sam (honest sender of novy instantiated with `π`): input `pack [[b], 1^n]`. -/
def novySender (π : PermFamily) : Party where
  coins inp := match unpack inp with
    | [_, pub] => [2 ^ pub.length]
    | _ => []
  next view := match unpack view with
    | inp :: cenc :: msgs => match unpack inp with
      | [m, pub] =>
          let n := pub.length
          let y := π.applyStr (novyX n cenc)
          let hs := msgs.take (n - 1)
          if ((List.range hs.length).all fun i => wellFormedH n (i + 1) (hs.getD i [])) then
            if msgs.length = 0 then []
            else if msgs.length ≤ n - 1 then [ip (msgs.getLastD []) y]
            else if msgs.length = (n - 1) + 1 then
              let ys := consistentList n hs (hs.map fun h => ip h y)
              let β : Bool := !(decide (y = ys.getD 0 []))
              [xor (m.headD false) β]
            else []
          else []
      | _ => []
    | _ => []

/-- `S_open` of novy: Sam announces `b`, and `u = pack [x, y]`. -/
def novySopen (π : PermFamily) (view : Bits) : Bits × Bits :=
  match unpack view with
  | inp :: cenc :: _ => match unpack inp with
    | [m, pub] =>
        let x := novyX pub.length cenc
        (m, pack [x, π.applyStr x])
    | _ => ([], [])
  | _ => ([], [])

/-- `R_open` of novy (Fig. 1): parse `Comm = [h₁, z₁, …, h_{n−1}, z_{n−1}, ε, d]`, check that the
challenges are legitimate and the answers are bits, and accept `(b, pack [x, y])` iff there is
`β` with `y = y_β`, `π_n(x) = y` and `b = d ⊕ β`. -/
def novyRopen (π : PermFamily) (m u : Bits) (comm : List Bits) (_privR pub : Bits) : Bool :=
  let n := pub.length
  let K := n - 1
  let hs := (List.range K).map fun i => comm.getD (2 * i) []
  let zs := (List.range K).map fun i => comm.getD (2 * i + 1) []
  let d := comm.getD (2 * K + 1) []
  let ys := consistentList n hs (zs.map fun z => z.headD false)
  match unpack u with
  | [x, y] =>
      decide (comm.length = 2 * (K + 1)) &&
        ((List.range K).all fun i => wellFormedH n (i + 1) (hs.getD i [])) &&
        zs.all (fun z => decide (z.length = 1)) && decide (d.length = 1) &&
        decide (m.length = 1) && decide (u = pack [x, y]) &&
        decide (x.length = n) && decide (y.length = n) &&
        ([false, true].any fun β =>
          decide (y = ys.getD β.toNat []) && decide (π.applyStr x = y) &&
            decide (m.headD false = xor (d.headD false) β))
  | _ => false

/-- Fig. 1 (p. 3): the novy bit commitment scheme `Π_novy` instantiated with `π`. -/
def novy (π : PermFamily) : CommitmentScheme where
  msgSpace _ := {[false], [true]}
  setup n := unary (max n 1)
  rounds n := (max n 1 - 1) + 1
  sender := novySender π
  receiver := novyReceiver
  sopen := novySopen π
  ropen := novyRopen π

/-- Experiment 8 (p. 27), `Pr[π-Bind_{novy,S}(n) = 1]`: `S n` runs `Π_int-hash` with an honest
Rachel (its answers `z_i` are the first bit of what it outputs at step `i − 1`; it receives `1^n` at
step `0`), then outputs `(x₀, x₁)` (decoded from `pack [x₀, x₁]`) at step `n − 1`; success iff
`π_n(x₀) = y₀(t)` and `π_n(x₁) = y₁(t)`. -/
noncomputable def piBindProb (π : PermFamily) (S : QStrategy) (n : ℕ) : ℝ :=
  let pub := unary n
  let K := n - 1
  avgOver (CoinSpace (novyReceiver.coins pub)) fun c =>
    ∑ o : S.Outs (K + 1),
      let os := QStrategy.outList o
      let hs := (List.range K).map fun j => novyReceiver.msg pub c (os.take j)
      let ys := consistentList n hs ((os.take K).map fun z => z.headD false)
      let s := os.getD K []
      let x0 := (unpack s).getD 0 []
      let x1 := (unpack s).getD 1 []
      let msg : List Bits → Bits := fun done =>
        if done.length < K then msgFor pub (novyReceiver.msg pub c) done else []
      if x0.length = n ∧ x1.length = n ∧ π.applyStr x0 = ys.getD 0 [] ∧ π.applyStr x1 = ys.getD 1 []
      then (S.run msg (zeroDM S.inQ) os).trace.re
      else 0

/-- Definition 14 (p. 27): novy instantiated with `π` is computational `π`-binding. -/
def IsPiBinding (π : PermFamily) : Prop :=
  ∀ S : ℕ → QStrategy, IsQPT S →
    ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧ ∀ n, piBindProb π (S n) n ≤ μ n

end NovyPQZK.Main



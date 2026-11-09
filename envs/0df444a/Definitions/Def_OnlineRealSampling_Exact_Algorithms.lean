-- Prove2me | Definitions.Def_OnlineRealSampling_Exact_Algorithms
-- name    : OnlineRealSampling_Exact_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:08:36.698104+00:00
-- url     : https://prove2.me/theorems/d523eb55-804b-4a29-a707-cac0b8ed2db2
-- title:
--   Algorithms 3–5: ApproxDivision, EstimatePMF, IntervalSample, Recycle and Sample
-- statement:
--   The algorithms of the paper as machines of the charged model.
--
--   1. **ApproxDivision$(a/b,k)$** (Algorithm 4). If $b<2^{k+1}$, return $a/b$. Otherwise let $n$ be the bit length of $b$ and $s=n-(k+1)$, and return $\lfloor a/2^s\rfloor/\lfloor b/2^s\rfloor$: the top $k+1$ aligned binary digits of $b$ and of $a$.
--   2. **EstimatePMF$(F,x,\nu)$** (Algorithm 5). For $j=0,1,\dots$ compute $u_j=F^-(x,j)-F^+(x-1,j)$ from $\phi(x,j+1)$ and $\phi(x-1,j+1)$; the second is not queried when $x=0$. Return $\hat p=u_j$ as soon as $2^{-j+1}\nu\le u_j$. If $f(x)=0$ it never returns.
--   3. **IntervalSample$(F,(Z,M))$** (Algorithm 3, lines 5–21). Start with $r=t=0$, $X^-=0$, $X^+=\infty$ and $\hat Q=0$. While $X^-<X^+$: let $X_{\rm mid}=2X^-$ if $X^+=\infty$ and $\lfloor(X^++X^-)/2\rfloor$ otherwise, and query $\phi(X_{\rm mid},t+1)$. If $F^+(X_{\rm mid},t)\le\hat Q$, set $X^-\leftarrow X_{\rm mid}+1$. Else, if $\hat Q+2^{-t+1}\le F^-(X_{\rm mid},t)$, set $X^+\leftarrow X_{\rm mid}$. Otherwise increment $t$. Then, if $t\ge 1+\lfloor\lg M\rfloor$, read a fresh bit, increment $r$ and set $\hat Q=(Z+\sum_{j\le r}B_j2^{-j})/M$; otherwise set $\hat Q=\mathrm{ApproxDivision}(Z/M,t+1)-2^{-t-1}$. Return $X=X^-$ and the bits $B_1,\dots,B_r$.
--   4. **Recycle$(F,(Z,M),\Delta,X,(B_1,\dots,B_r))$** (lines 22–33). Compute $\hat p=\mathrm{EstimatePMF}(F,X,1)$, $s=\max\{0,\lceil\lg(\Delta/(M\hat p))\rceil-2\}$ and $\kappa=s+\lceil\lg M\rceil$. Read the fresh bits $B_{r+1},\dots,B_s$ if $r<s$. Then set
--   $$U^-=\lceil 2^sMF^+(X-1,\kappa)\rceil,\qquad U^+=\lfloor 2^sMF^-(X,\kappa)\rfloor,\qquad V=2^s\Big(Z+\sum_{j\le s}B_j2^{-j}\Big).$$
--   $V$ uses exactly $s$ bits, also when $r>s$. Return $(V-U^-,U^+-U^-)$ if $U^-\le V<U^+$, and $(0,1)$ otherwise.
--   5. **Sample$(F,(Z,M),\Delta)$** runs IntervalSample and then Recycle on the bits after the $r$ consumed ones. Its outcome records $X$, $(Z',M')$, the number $T=\max\{r,s\}$ of fresh bits, the final $r$ and $t$ of IntervalSample, the values $s,U^\pm,V$ of Recycle, and the resources of the whole call. It is viewed as a random variable on the single-step space ($Z$ uniform on $\{0,\dots,M-1\}$, independent fair bits). The definitions also name the event $\{X=x\}$ and each resource as an element of $[0,\infty]$, equal to $\infty$ if the call never halts.
--
--   **Formalization Note** Rationals are pairs of integers with positive denominators, and $F^\pm$ are formed from the integer numerator of $\phi$ over $2^{k+1}$. Each IntervalSample iteration makes one oracle call, because $F^+$ and $F^-$ at $(X_{\rm mid},t)$ both come from $\phi(X_{\rm mid},t+1)$. The bits $B_1\dots B_r$ are kept as one integer. A checked simulation (module `Solutions.verification.OnlineRealSampling_Exact_Simulation`) reproduces exact output frequencies and a uniform recycled state on two toy oracles.
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Algorithm 3 (PDF 10 / printed 9), Algorithm 4 (Appendix A, PDF 19 / printed 18), Algorithm 5 (Appendix B, PDF 20 / printed 19)

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Machine

namespace OnlineRealSampling.Exact

open MeasureTheory
open scoped ENNReal

noncomputable section

section Algorithms

variable (w : ℕ)

/-! ## Algorithm 4: ApproxDivision (Appendix A, PDF 19 / printed 18) -/

/-- `ApproxDivision(a/b, k)`: if `b < 2^{k+1}` return `a/b`; otherwise, with `n` the bit length
of `b` and `s = n - (k+1)`, return `⌊a/2^s⌋ / ⌊b/2^s⌋` (the top `k+1` aligned binary digits of
`b` and of `a`, the latter padded with leading zeros). The result is the pair
(numerator, denominator). -/
def approxDivision (a b : ℤ) (k : ℕ) : Charged (ℤ × ℤ) := do
  let n ← bitLengthZ b
  if n ≤ k + 1 then
    pure (a, b)
  else
    let b' ← shrZ w b (n - (k + 1))
    let a' ← shrZ w a (n - (k + 1))
    pure (a', b')

/-! ## Algorithm 5: EstimatePMF (Appendix B, PDF 20 / printed 19) -/

/-- Program counter of EstimatePMF. -/
inductive EstPC where
  | qHi | qLo | test | done
  deriving DecidableEq

/-- State of `EstimatePMF(F, x, ν)`: the loop index `j` (the paper's `i`), the oracle answers
`aHi = φ(x, j+1)` and `aLo = φ(x-1, j+1)` (`0` when `x = 0`), and the returned numerator `u`, so
that the estimate is `p̂ = u / 2^{j+1} = F⁻(x,j) - F⁺(x-1,j)`. -/
structure EstState where
  x : ℕ
  ν : ℕ
  j : ℕ
  aHi : ℤ
  aLo : ℤ
  u : ℤ
  pc : EstPC

/-- Initial state of `EstimatePMF(F, x, ν)`. -/
def EstState.init (x ν : ℕ) : EstState := ⟨x, ν, 0, 0, 0, 0, .qHi⟩

/-- The returned estimate `p̂ = u / 2^{j+1}`. -/
def EstState.estimate (s : EstState) : ℝ := (s.u : ℝ) / 2 ^ (s.j + 1)

/-- One step of EstimatePMF. For `j = 0, 1, 2, …`: query `φ(x, j+1)` and (if `x ≥ 1`)
`φ(x-1, j+1)`, form `u = (φ(x,j+1) - 1) - (φ(x-1,j+1) + 1)`, i.e.
`u / 2^{j+1} = F⁻(x,j) - F⁺(x-1,j)`, and return as soon as `2^{-j+1} ν ≤ u / 2^{j+1}`,
i.e. `4ν ≤ u`. -/
def estStep (s : EstState) : Action EstState :=
  match s.pc with
  | .qHi => .query s.x (s.j + 1) (fun a => pure { s with aHi := a, pc := .qLo })
  | .qLo =>
      if s.x = 0 then .compute (pure { s with aLo := 0, pc := .test })
      else .query (s.x - 1) (s.j + 1) (fun a => pure { s with aLo := a, pc := .test })
  | .test => .compute (do
      let d ← subZ w s.aHi s.aLo
      let u ← subZ w d 2
      let lhs ← mulZ w 4 s.ν
      let ok ← leZ w lhs u
      pure (if ok then { s with u := u, pc := .done } else { s with j := s.j + 1, pc := .qHi }))
  | .done => .halt

/-- Storage of an EstimatePMF state. -/
def estSize (s : EstState) : ℕ :=
  bitLen s.x + bitLen s.ν + bitLen s.j + bitLen s.aHi + bitLen s.aLo + bitLen s.u + 2

/-- The EstimatePMF machine. -/
def estimatePMF : Machine EstState := ⟨estStep w, estSize⟩

/-! ## Algorithm 3, lines 5–21: IntervalSample (PDF 10 / printed 9) -/

/-- Program counter of IntervalSample: loop head, oracle query, branch, fresh bit, done. -/
inductive ISPC where
  | head | ask | decide | bit | done
  deriving DecidableEq

/-- State of `IntervalSample(F, (Z, M))`: inputs `Z, M`; the counters `r, t`; the search
interval `X⁻ = lo`, `X⁺ = hi` (`none` is `∞`); `Q̂ = qn / qd`; the bits `B₁ … B_r` read so far as
the integer `bs = ∑_{j ≤ r} B_j 2^{r-j}`; the current midpoint and the last oracle answer. -/
structure ISState where
  Z : ℕ
  M : ℕ
  r : ℕ
  t : ℕ
  lo : ℕ
  hi : Option ℕ
  qn : ℤ
  qd : ℤ
  bs : ℕ
  mid : ℕ
  ans : ℤ
  pc : ISPC

/-- Line 6: `r ← 0, t ← 0, X⁻ ← 0, X⁺ ← ∞, Q̂ ← 0`. -/
def ISState.init (Z M : ℕ) : ISState := ⟨Z, M, 0, 0, 0, none, 0, 1, 0, 0, 0, .head⟩

/-- The rational `Q̂ = qn / qd` as a real number. -/
def ISState.qhat (s : ISState) : ℝ := (s.qn : ℝ) / s.qd

/-- One step of IntervalSample.
* `head` (lines 7–8): stop if `X⁻ ≥ X⁺`; otherwise `X_mid ← 2X⁻` if `X⁺ = ∞`, else
  `⌊(X⁺ + X⁻)/2⌋`.
* `ask`: query `φ(X_mid, t+1)`, from which `F^±(X_mid, t) = (φ(X_mid,t+1) ± 1)/2^{t+1}`.
* `decide` (lines 9–20): if `F⁺(X_mid,t) ≤ Q̂` then `X⁻ ← X_mid + 1`; else if
  `Q̂ + 2^{-t+1} ≤ F⁻(X_mid,t)` then `X⁺ ← X_mid`; else `t ← t+1` and, if the new
  `t ≥ 1 + ⌊lg M⌋` (`= bitLen M`), go read a bit, otherwise
  `Q̂ ← ApproxDivision(Z/M, t+1) - 2^{-t-1}`.
* `bit` (lines 16–18): read a fresh bit `B_{r+1}`, `r ← r+1`,
  `Q̂ ← (Z + ∑_{j≤r} B_j 2^{-j}) / M = (Z 2^r + bs) / (M 2^r)`. -/
def isStep (s : ISState) : Action ISState :=
  match s.pc with
  | .head =>
      match s.hi with
      | none => .compute (do
          let m ← mulZ w 2 s.lo
          pure { s with mid := m.toNat, pc := .ask })
      | some h => .compute (do
          let go ← ltZ w s.lo h
          if go then do
            let sum ← addZ w s.lo h
            let m ← shrZ w sum 1
            pure { s with mid := m.toNat, pc := .ask }
          else pure { s with pc := .done })
  | .ask => .query s.mid (s.t + 1) (fun a => pure { s with ans := a, pc := .decide })
  | .decide => .compute (do
      let p ← pow2 w (s.t + 1)
      let a1 ← addZ w s.ans 1
      let l1 ← mulZ w a1 s.qd
      let r1 ← mulZ w s.qn p
      let c1 ← leZ w l1 r1
      if c1 then do
        let lo' ← addZ w s.mid 1
        pure { s with lo := lo'.toNat, pc := .head }
      else do
        let q4 ← mulZ w 4 s.qd
        let l2 ← addZ w r1 q4
        let a2 ← subZ w s.ans 1
        let r2 ← mulZ w a2 s.qd
        let c2 ← leZ w l2 r2
        if c2 then pure { s with hi := some s.mid, pc := .head }
        else do
          let L ← bitLengthZ s.M
          if L ≤ s.t + 1 then pure { s with t := s.t + 1, pc := .bit }
          else do
            let ab ← approxDivision w s.Z s.M (s.t + 2)
            let pa ← shlZ w ab.1 (s.t + 2)
            let num ← subZ w pa ab.2
            let den ← shlZ w ab.2 (s.t + 2)
            pure { s with t := s.t + 1, qn := num, qd := den, pc := .head })
  | .bit => .coin (fun b => do
      let b2 ← shlZ w s.bs 1
      let bs' ← addZ w b2 (if b then 1 else 0)
      let zs ← shlZ w s.Z (s.r + 1)
      let num ← addZ w zs bs'
      let den ← shlZ w s.M (s.r + 1)
      pure { s with r := s.r + 1, bs := bs'.toNat, qn := num, qd := den, pc := .head })
  | .done => .halt

/-- Storage of an IntervalSample state. -/
def isSize (s : ISState) : ℕ :=
  bitLen s.Z + bitLen s.M + bitLen s.r + bitLen s.t + bitLen s.lo +
    (match s.hi with | none => 1 | some h => bitLen h + 1) +
    bitLen s.qn + bitLen s.qd + bitLen s.bs + bitLen s.mid + bitLen s.ans + 3

/-- The IntervalSample machine. On halting, `X = lo` and the bits used are `(r, bs)`. -/
def intervalSample : Machine ISState := ⟨isStep w, isSize⟩

/-! ## Algorithm 3, lines 22–33: Recycle (PDF 10 / printed 9) -/

/-- Program counter of Recycle. -/
inductive RecPC where
  | est | setS | read | qLo | qHi | final | done
  deriving DecidableEq

/-- State of `Recycle(F, (Z, M), Δ, X, (B₁,…,B_r))`: the inputs (bits as `bs`), the embedded
EstimatePMF state, `s`, `κ = s + ⌈lg M⌉`, the answers `aLo = φ(X-1, κ+1)` (`0` if `X = 0`) and
`aHi = φ(X, κ+1)`, and `U⁻, U⁺, V, Z', M'`. -/
structure RecState where
  Z : ℕ
  M : ℕ
  Δ : ℕ
  X : ℕ
  r : ℕ
  bs : ℕ
  est : EstState
  sv : ℕ
  κ : ℕ
  aLo : ℤ
  aHi : ℤ
  Um : ℤ
  Up : ℤ
  V : ℤ
  Z' : ℕ
  M' : ℕ
  pc : RecPC

/-- Initial state of Recycle; EstimatePMF is started with `ν = 1` (line 23). -/
def RecState.init (Z M Δ X r bs : ℕ) : RecState :=
  ⟨Z, M, Δ, X, r, bs, EstState.init X 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, .est⟩

/-- One step of Recycle.
* `est` (line 23): run `p̂ ← EstimatePMF(F, X, 1)`; it never returns if `f(X) = 0`.
* `setS` (line 24): `s ← max{0, ⌈lg(Δ/(M p̂))⌉ - 2}`, computed as
  `⌈lg(Δ 2^{j+1} / (M u))⌉` for `p̂ = u/2^{j+1}`; and `κ ← s + ⌈lg M⌉`.
* `read` (lines 25–26): if `r < s`, read the `s - r` fresh bits `B_{r+1} … B_s`.
* `qLo`, `qHi`: query `φ(X-1, κ+1)` (no call if `X = 0`, as `φ(-1,·) = 0`) and `φ(X, κ+1)`.
* `final` (lines 27–33): `U⁻ ← ⌈2^s M F⁺(X-1, κ)⌉`, `U⁺ ← ⌊2^s M F⁻(X, κ)⌋`,
  `V ← 2^s (Z + ∑_{j≤s} B_j 2^{-j})` (exactly `s` bits, also when `r > s`); return
  `(V - U⁻, U⁺ - U⁻)` if `U⁻ ≤ V < U⁺`, else `(0, 1)`. -/
def recStep (s : RecState) : Action RecState :=
  match s.pc with
  | .est =>
      match estStep w s.est with
      | .halt => .compute (pure { s with pc := .setS })
      | a => a.lift (fun e => { s with est := e })
  | .setS => .compute (do
      let A ← shlZ w s.Δ (s.est.j + 1)
      let B ← mulZ w s.M s.est.u
      let e ← ceilLog2Ratio w A B
      let cm ← ceilLog2Ratio w s.M 1
      pure { s with sv := (e - 2).toNat, κ := (e - 2).toNat + cm.toNat, pc := .read })
  | .read =>
      if s.r < s.sv then
        .coins (s.sv - s.r) (fun v => do
          let b1 ← shlZ w s.bs (s.sv - s.r)
          let b2 ← addZ w b1 v
          pure { s with bs := b2.toNat, pc := .qLo })
      else .compute (pure { s with pc := .qLo })
  | .qLo =>
      if s.X = 0 then .compute (pure { s with aLo := 0, pc := .qHi })
      else .query (s.X - 1) (s.κ + 1) (fun a => pure { s with aLo := a, pc := .qHi })
  | .qHi => .query s.X (s.κ + 1) (fun a => pure { s with aHi := a, pc := .final })
  | .final => .compute (do
      let den ← pow2 w (s.κ + 1)
      let sm ← shlZ w s.M s.sv
      let lo1 ← addZ w s.aLo 1
      let nlo ← mulZ w sm lo1
      let um ← cdivZ w nlo den
      let hi1 ← subZ w s.aHi 1
      let nhi ← mulZ w sm hi1
      let up ← fdivZ w nhi den
      let zs ← shlZ w s.Z s.sv
      let low ← if s.r ≤ s.sv then pure (s.bs : ℤ) else shrZ w s.bs (s.r - s.sv)
      let v ← addZ w zs low
      let c1 ← leZ w um v
      let c2 ← ltZ w v up
      if c1 && c2 then do
        let z' ← subZ w v um
        let m' ← subZ w up um
        pure { s with Um := um, Up := up, V := v, Z' := z'.toNat, M' := m'.toNat, pc := .done }
      else pure { s with Um := um, Up := up, V := v, Z' := 0, M' := 1, pc := .done })
  | .done => .halt

/-- Storage of a Recycle state. -/
def recSize (s : RecState) : ℕ :=
  bitLen s.Z + bitLen s.M + bitLen s.Δ + bitLen s.X + bitLen s.r + bitLen s.bs + estSize s.est +
    bitLen s.sv + bitLen s.κ + bitLen s.aLo + bitLen s.aHi + bitLen s.Um + bitLen s.Up +
    bitLen s.V + bitLen s.Z' + bitLen s.M' + 3

/-- The Recycle machine. -/
def recycle : Machine RecState := ⟨recStep w, recSize⟩

/-! ## Algorithm 3, lines 1–4: Sample -/

/-- The outcome of one call `(X, (Z', M')) ← Sample(F, (Z, M), Δ)`, with the quantities the
analysis refers to: `T = max{r, s}` fresh bits, the final IntervalSample counters `r, t`, the
Recycle values `s, U⁻, U⁺, V`, and the resources of the whole call. -/
structure SampleOut where
  X : ℕ
  Z' : ℕ
  M' : ℕ
  T : ℕ
  r : ℕ
  tFinal : ℕ
  sv : ℕ
  Um : ℤ
  Up : ℤ
  V : ℤ
  usage : Usage

/-- `Sample(F, (Z, M), Δ)` on the fair-bit stream `ω`: run IntervalSample from `ω`, then
Recycle on the bits after the `r` consumed ones (Recycle sees `B₁ … B_r` through its input). The
result is `none` if either part never halts. -/
def sampleRun (O : OracleAccess) (Z M Δ : ℕ) (ω : ℕ → Bool) : Option SampleOut :=
  match (intervalSample w).run O w ω (ISState.init Z M) with
  | none => none
  | some c1 =>
    match (recycle w).run O w (fun j => ω (c1.pos + j))
        (RecState.init Z M Δ c1.st.lo c1.st.r c1.st.bs) with
    | none => none
    | some c2 => some
        { X := c1.st.lo, Z' := c2.st.Z', M' := c2.st.M', T := c1.pos + c2.pos, r := c1.st.r,
          tFinal := c1.st.t, sv := c2.st.sv, Um := c2.st.Um, Up := c2.st.Up, V := c2.st.V,
          usage := c1.usage.seq c2.usage }

/-- Sample as a random variable on the single-step space `ℕ × (ℕ → Bool)` of `stepMeasure M`
(the state `Z` is the first coordinate). -/
def sampleOn (O : OracleAccess) (M Δ : ℕ) (p : ℕ × (ℕ → Bool)) : Option SampleOut :=
  sampleRun w O p.1 M Δ p.2

/-- IntervalSample as a random variable on `ℕ × (ℕ → Bool)`: its final configuration, if it
halts. -/
def intervalSampleOn (O : OracleAccess) (M : ℕ) (p : ℕ × (ℕ → Bool)) :
    Option (Config ISState) :=
  (intervalSample w).run O w p.2 (ISState.init p.1 M)

/-- The event that `Sample(F, (Z, M), Δ)` halts with output `X = x`. -/
def sampleEvent (O : OracleAccess) (M Δ x : ℕ) : Set (ℕ × (ℕ → Bool)) :=
  {p | ∃ out, sampleOn w O M Δ p = some out ∧ out.X = x}

/-- A resource `f` of the call `Sample(F, (Z, M), Δ)` as an extended nonnegative number
(`⊤` if the call never halts). -/
def sampleRes (O : OracleAccess) (M Δ : ℕ) (f : Usage → ℕ) (p : ℕ × (ℕ → Bool)) : ℝ≥0∞ :=
  match sampleOn w O M Δ p with
  | some out => (f out.usage : ℝ≥0∞)
  | none => ⊤

/-- The event that IntervalSample halts with output `X = x`. -/
def isEvent (O : OracleAccess) (M x : ℕ) : Set (ℕ × (ℕ → Bool)) :=
  {p | ∃ c, intervalSampleOn w O M p = some c ∧ c.st.lo = x}

end Algorithms

end

end OnlineRealSampling.Exact



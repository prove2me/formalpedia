-- Prove2me | Definitions.Def_PrivOptTest_algo2
-- name    : PrivOptTest_algo2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:09.757668+00:00
-- url     : https://prove2.me/theorems/cb49369a-7bb3-41b9-a98f-c5e7d83d6c08
-- title:
--   Algorithm 1 ($\mathcal A_{\mathrm{PCF}}$) and Algorithm 2 ($\mathcal A_{\mathrm{val\text{-}thr}}$) as two-party protocols
-- statement:
--   **Algorithm 1** (p.18), on $S_A,S_B\in[m]^n$: set $R=\lceil4n^2/\beta\rceil$; if $m\le R$ use the identity, else a public uniformly random hash $g:[m]\to[R]$ (and $R:=m$ in the first case). Alice releases $\tilde A_z=|\{i:g(X_i)=z\}|+\mathrm{Lap}(2/\varepsilon)$ for every bucket $z$, Bob releases $\tilde B_z$ likewise, and the output is $\hat f=\max_z\min\{\tilde A_z,\tilde B_z\}$, an estimate of $f=\max_v\min\{A_v,B_v\}$.
--
--   **Algorithm 2** (p.20), on records in $\{0,1\}^b$ with block size $n$: $T=\lceil\log_2b\rceil$, $\varepsilon_0=\varepsilon/2T$, $\beta_0=\beta/2T$ and
--   $$\alpha=20\max\Big\{\frac{2}{\varepsilon_0}\ln\frac{4\lceil4n^2/\beta_0\rceil}{\beta_0},\ \frac{28}{\varepsilon}\ln\frac4\beta\Big\}.$$
--   A private binary search starts at $L=0$, $H=b$, $\hat F(0)=0$, $\hat F(b)=n$, and while $H-L>1$ queries $\ell=\lfloor(L+H)/2\rfloor$, runs Algorithm 1 with $(\varepsilon_0,\beta_0)$ on the depth-$\ell$ prefixes, sets $\hat F(\ell)=n-\hat f$, and moves $L$ to $\ell$ if $\hat F(\ell)<\alpha$, else $H$. If $\hat F(H)-\hat F(L)\ge\alpha/2$ each party releases its large-jump statistic plus $\mathrm{Lap}(28/\varepsilon)$, otherwise its cumulative-escape statistic plus $\mathrm{Lap}(28/\varepsilon)$, and the output is Match if $\hat V_A\ge\hat V_B$, else Far.
--
--   On a domain $\mathcal X\subset\mathbb R$ with $|\mathcal X|=m$, the tester of Theorem 3.12 ranks each record in $\mathcal X$ as a $\lceil\log_2m\rceil$-bit string, lifts Alice's ranks by $\psi_A$ and Bob's by $\psi_B$, keeps Alice's $k=\lfloor t/2\rfloor$ largest and Bob's $k$ smallest (Remark 3.6), and runs Algorithm 2 with $b=\lceil\log_2m\rceil+1$ and block size $k$.
--
--   **Formalization Note** Messages are pairs (scalar, vector), vectors padded with zeros. Each pass of the search uses fresh noise and a fresh public hash (p.21); hashes are drawn on $\{0,1\}^b$, whose restriction to depth-$\ell$ prefixes is uniform. Coins are drawn whether or not used. The arithmetic is written over an ordered field so that the same text runs over $\mathbb Q$ in tests.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Algorithm 1 and Theorem 3.11, p.18; Algorithm 2, p.20; Lemma 3.5 and Remark 3.6, p.16; §1.4.2, p.9

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivOptTest_Protocol
import Definitions.Def_PrivOptTest_Trie

open MeasureTheory

namespace PrivOptTest

/-! The arithmetic of Algorithms 1 and 2 is written over an arbitrary ordered field `K` with
floor and a logarithm `ln`, so the same text is executed on `ℚ` in the tests and is `ℝ` here. -/

section Core

variable {K : Type} [Field K] [LinearOrder K] [FloorRing K]

/-- `R` after lines 1–5 of Algorithm 1 (p.18): `m` if `m ≤ ⌈4n²/β⌉`, else `⌈4n²/β⌉`. `Rbar` is `⌈4n²/β⌉`. -/
def pcfBuckets (m Rbar : ℕ) : ℕ := if m ≤ Rbar then m else Rbar

/-- `g` after lines 1–5 of Algorithm 1 (p.18): the identity if `m ≤ Rbar`, else the public hash. -/
def pcfHash (m Rbar : ℕ) (g : ℕ → ℕ) (x : ℕ) : ℕ := if m ≤ Rbar then x else g x

/-- Lines 6–7 of Algorithm 1 (p.18): a party's release `|{i : g(X_i) = z}| + Lap(2/ε)` for `z ∈ [R]`,
written 0-based, padded with zeros from `z = R` on. -/
def pcfRelease (m Rbar : ℕ) (g : ℕ → ℕ) (recs : List ℕ) (noise : ℕ → K) (z : ℕ) : K :=
  if z < pcfBuckets m Rbar then
    ((recs.countP fun x => pcfHash m Rbar g x = z : ℕ) : K) + noise z
  else 0

/-- The maximum of a list, `0` on the empty list. -/
def listMax : List K → K
  | [] => 0
  | x :: xs => xs.foldl max x

/-- Line 8 of Algorithm 1 (p.18): `f̂ = max_{z∈[R]} min{Ã_z, B̃_z}`. -/
def pcfEstimate (m Rbar : ℕ) (a b : ℕ → K) : K :=
  listMax ((List.range (pcfBuckets m Rbar)).map fun z => min (a z) (b z))

/-- The numbers fixed by lines 1–2 of Algorithm 2 (p.20), given `T`: the bit length `b`, the block
size `k` (the algorithm's `n`), `T = ⌈log₂ b⌉`, `ε₀ = ε/2T`, `β₀ = β/2T`, `Rbar = ⌈4k²/β₀⌉` and
`α = 20 max{(2/ε₀) ln(4⌈4k²/β₀⌉/β₀), (28/ε) ln(4/β)}`. -/
structure Params (K : Type) where
  b : ℕ
  k : ℕ
  T : ℕ
  Rbar : ℕ
  ε : K
  ε₀ : K
  β₀ : K
  α : K

/-- `Params` from `b`, `k`, `T`, `ε`, `β`, by constantly many arithmetic operations. -/
def paramsOf (ln : K → K) (b k T : ℕ) (ε β : K) : Params K :=
  let ε₀ := ε / (2 * (T : K))
  let β₀ := β / (2 * (T : K))
  let Rbar := ⌈4 * (k : K) ^ 2 / β₀⌉.toNat
  { b := b, k := k, T := T, Rbar := Rbar, ε := ε, ε₀ := ε₀, β₀ := β₀,
    α := 20 * max ((2 / ε₀) * ln (4 * (Rbar : K) / β₀)) ((28 / ε) * ln (4 / β)) }

/-- The binary-search state of Algorithm 2 (p.20): `L`, `H`, `F̂(L)`, `F̂(H)`. -/
structure SearchState (K : Type) where
  L : ℕ
  H : ℕ
  FL : K
  FH : K

/-- Line 3 of Algorithm 2 (p.20): `L ← 0`, `H ← b`, `F̂(0) ← 0`, `F̂(b) ← n`. -/
def searchInit (P : Params K) : SearchState K := ⟨0, P.b, 0, (P.k : K)⟩

/-- The `F̂(ℓ) ← n − A_PCF(S^ℓ_A, S^ℓ_B; ε₀, β₀)` of line 7, from the two releases. -/
def fHat (P : Params K) (ℓ : ℕ) (a b : ℕ → K) : K :=
  (P.k : K) - pcfEstimate (2 ^ ℓ) P.Rbar a b

/-- One pass of lines 4–11 of Algorithm 2 (p.20), on the two releases `a`, `b` of that pass. A state
with `H − L ≤ 1` is left alone, since the loop has ended. -/
def searchStep (P : Params K) (s : SearchState K) (a b : ℕ → K) : SearchState K :=
  if 1 < s.H - s.L then
    let ℓ := (s.L + s.H) / 2
    let F := fHat P ℓ a b
    if F < P.α then { s with L := ℓ, FL := F } else { s with H := ℓ, FH := F }
  else s

/-- The binary-search state after `i` passes, read from the public messages: pass `i` uses messages
`2i` (Alice) and `2i + 1` (Bob). A message is `(v, a)`, with `v` the scalar of lines 14–18 and `a` the
release of lines 6–7 of Algorithm 1. -/
def searchAt (P : Params K) (m : ℕ → K × (ℕ → K)) : ℕ → SearchState K
  | 0 => searchInit P
  | i + 1 => searchStep P (searchAt P m i) (m (2 * i)).2 (m (2 * i + 1)).2

/-- The unnoised statistic of lines 13–18 of Algorithm 2 (p.20), on a party's own records. -/
def finalStat (P : Params K) (s : SearchState K) (recs : List ℕ) : K :=
  if P.α / 2 ≤ s.FH - s.FL then ((statJump P.b s.L recs : ℤ) : K)
  else ((statCum P.b s.H recs : ℤ) : K)

/-- The message of a party in pass `i` of the protocol: the release of Algorithm 1 at depth
`ℓ = ⌊(L + H)/2⌋` on the prefix dataset while `H − L > 1` (lines 5–7), else the noised statistic. Here
`recs` are the party's records, `g` the public hash of pass `i`, `noise` its noise for pass `i`, `lap`
its `Lap(28/ε)` sample. Only the party's own data and coins, and public information, enter. -/
def partyMsg (P : Params K) (recs : List ℕ) (g : ℕ → ℕ) (noise : ℕ → K) (lap : K)
    (m : ℕ → K × (ℕ → K)) (i : ℕ) : K × (ℕ → K) :=
  let s := searchAt P m i
  if 1 < s.H - s.L then
    let ℓ := (s.L + s.H) / 2
    (0, pcfRelease (2 ^ ℓ) P.Rbar g (recs.map (prefixOf P.b ℓ)) noise)
  else
    (finalStat P s recs + lap, 0)

/-- The public stopping rule. The first pass `i` with `H − L ≤ 1` carries the two `V̂`; the run stops
before round `2i + 2`, and line 19 returns Match if `V̂_A ≥ V̂_B`, otherwise Far. -/
def algo2Stop (P : Params K) (r : ℕ) (m : ℕ → K × (ℕ → K)) : Outcome ⊕ Unit :=
  if r ≠ 0 ∧ r % 2 = 0 ∧ ¬ 1 < (searchAt P m (r / 2 - 1)).H - (searchAt P m (r / 2 - 1)).L then
    Sum.inl (if (m (r - 1)).1 ≤ (m (r - 2)).1 then Outcome.matched else Outcome.far)
  else Sum.inr ()

end Core

/-- A history as a total function, with `d` beyond its length. -/
def histFn {M : Type} {r : ℕ} (d : M) (h : Fin r → M) (j : ℕ) : M :=
  if hj : j < r then h ⟨j, hj⟩ else d

/-- The numbers of lines 1–2 of Algorithm 1 for `ℝ`. -/
noncomputable def realParams (b k : ℕ) (ε β : ℝ) : Params ℝ :=
  paramsOf Real.log b k (Nat.clog 2 b) ε β

/-- A party's coins in Algorithm 2 (p.20): for each of the `T` passes a noise vector with coordinates
`Lap(2/ε₀)`, and one sample `Lap(28/ε)`. -/
abbrev Algo2Noise (P : Params ℝ) : Type := (Fin P.T → Fin P.Rbar → ℝ) × ℝ

/-- The public coins of Algorithm 2: a fresh hash for each pass. The domain `{0,1}^b` holds the
zero-padded prefixes of every depth, so that its restriction to depth-`ℓ` prefixes is uniform from
`[2^ℓ]` to `[R]`. -/
abbrev Algo2Hash (P : Params ℝ) : Type := Fin P.T → Fin (2 ^ P.b) → Fin P.Rbar

/-- The law of a party's coins in Algorithm 2. -/
noncomputable def algo2NoiseLaw (P : Params ℝ) : Measure (Algo2Noise P) :=
  (Measure.pi fun _ : Fin P.T => Measure.pi fun _ : Fin P.Rbar =>
    PrivLearn.Generic.laplace (2 / P.ε₀)).prod (PrivLearn.Generic.laplace (28 / P.ε))

/-- The noise of pass `i` as a total function. -/
def noiseAt {P : Params ℝ} (ω : Algo2Noise P) (i z : ℕ) : ℝ :=
  if h : i < P.T ∧ z < P.Rbar then ω.1 ⟨i, h.1⟩ ⟨z, h.2⟩ else 0

/-- The hash of pass `i` as a total function. -/
def hashAt {P : Params ℝ} (ω : Algo2Hash P) (i x : ℕ) : ℕ :=
  if h : i < P.T ∧ x < 2 ^ P.b then (ω ⟨i, h.1⟩ ⟨x, h.2⟩ : ℕ) else 0

/-- **Algorithm 2, `A_val-thr`, p.20**, as a two-party protocol on records `recs` that are `b`-bit
strings read as integers, with `k` the algorithm's `n`. The party's input is a list of `k` records.
Rounds alternate: in each pass Alice releases, then Bob; the last pass carries `V̂_A`, `V̂_B`.

**Formalization Note.** A message is `(v, a) : ℝ × (ℕ → ℝ)`. A pass of the search uses fresh coins
(p.21). The search has at most `T = ⌈log₂ b⌉` passes, so the guards in `noiseAt`, `hashAt` never fire. -/
noncomputable def algo2 (b k : ℕ) (ε β : ℝ) : Protocol (List ℕ) Outcome :=
  let P := realParams b k ε β
  { ΩA := Algo2Noise P
    ΩB := Algo2Noise P
    ΩP := Algo2Hash P
    Msg := ℝ × (ℕ → ℝ)
    μA := algo2NoiseLaw P
    μB := algo2NoiseLaw P
    μP := ProbabilityTheory.uniformOn Set.univ
    nextA := fun r recs ω g h =>
      partyMsg P recs (hashAt g (r / 2)) (noiseAt ω (r / 2)) ω.2 (histFn (0, 0) h) (r / 2)
    nextB := fun r recs ω g h =>
      partyMsg P recs (hashAt g (r / 2)) (noiseAt ω (r / 2)) ω.2 (histFn (0, 0) h) (r / 2)
    stop := fun r _ h => algo2Stop P r (histFn (0, 0) h) }

/-- The rank of a domain point in `{0, …, m − 1}` under the increasing enumeration of `X` ("each point's
rank in the public domain as a binary string", §1.4.2, p.9). -/
noncomputable def rankIn (X : Finset ℝ) (x : ↥X) : ℕ :=
  ((X.orderIsoOfFin rfl).symm x : ℕ)

/-- Alice's local encoding: the `k = ⌊t/2⌋` largest lifted ranks `S̃↑_{A,k}` (Remark 3.6, p.16). -/
noncomputable def encA (X : Finset ℝ) {n : ℕ} (t : ℕ) (S : Fin n → ↥X) : List ℕ :=
  blockUp (t / 2) fun i => psiA (rankIn X (S i))

/-- Bob's local encoding: the `k = ⌊t/2⌋` smallest lifted ranks `S̃↓_{B,k}` (Remark 3.6, p.16). -/
noncomputable def encB (X : Finset ℝ) {n : ℕ} (t : ℕ) (S : Fin n → ↥X) : List ℕ :=
  blockDown (t / 2) fun i => psiB (rankIn X (S i))

/-- The bit length `b = ⌈log₂ m⌉ + 1` on which Algorithm 2 runs: ranks have `⌈log₂ m⌉` bits, and the
lifting adds one. -/
def bitsOf (m : ℕ) : ℕ := Nat.clog 2 m + 1

/-- **`A_val-thr` on a domain `X ⊂ ℝ`, as Theorem 3.12 (p.21) uses it.** Each party ranks its records,
lifts them by `ψ_A`, `ψ_B`, keeps its block of `k = ⌊t/2⌋` records (Remark 3.6, p.16), and runs
Algorithm 2 with `b = ⌈log₂ m⌉ + 1` and `n := k`. -/
noncomputable def avalThr (X : Finset ℝ) (n t : ℕ) (ε β : ℝ) : Protocol (Fin n → ↥X) Outcome :=
  (algo2 (bitsOf X.card) (t / 2) ε β).precomp (encA X t) (encB X t)

/-- **Algorithm 1, `A_PCF`, p.18**, as a protocol with real output, on `S_A, S_B ∈ [m]ⁿ` (0-based).
Alice releases, Bob releases, the run stops before round 2 with the estimate `f̂` of line 8.

**Formalization Note.** Coins are drawn whether or not they are used. `R̄ = ⌈4n²/β⌉`. -/
noncomputable def apcf (m n : ℕ) (ε β : ℝ) : Protocol (Fin n → Fin m) ℝ :=
  let Rbar := ⌈4 * (n : ℝ) ^ 2 / β⌉.toNat
  let recs (S : Fin n → Fin m) : List ℕ := List.ofFn fun i => (S i : ℕ)
  let hsh (g : Fin m → Fin Rbar) (x : ℕ) : ℕ := if h : x < m then (g ⟨x, h⟩ : ℕ) else 0
  let nz (ω : Fin Rbar → ℝ) (z : ℕ) : ℝ := if h : z < Rbar then ω ⟨z, h⟩ else 0
  { ΩA := Fin Rbar → ℝ
    ΩB := Fin Rbar → ℝ
    ΩP := Fin m → Fin Rbar
    Msg := ℕ → ℝ
    μA := Measure.pi fun _ => PrivLearn.Generic.laplace (2 / ε)
    μB := Measure.pi fun _ => PrivLearn.Generic.laplace (2 / ε)
    μP := ProbabilityTheory.uniformOn Set.univ
    nextA := fun _ S ω g _ => pcfRelease m Rbar (hsh g) (recs S) (nz ω)
    nextB := fun _ S ω g _ => pcfRelease m Rbar (hsh g) (recs S) (nz ω)
    stop := fun r _ h =>
      if r = 2 then Sum.inl (pcfEstimate m Rbar (histFn 0 h 0) (histFn 0 h 1)) else Sum.inr () }

/-- The target of Algorithm 1 (p.18): `f = max_{k∈[m]} min{A_k, B_k}`, with `A_k`, `B_k` the counts of `k`. -/
def commonFreq {m n : ℕ} (SA SB : Fin n → Fin m) : ℕ :=
  Finset.univ.sup fun v : Fin m =>
    min (Finset.univ.filter fun i => SA i = v).card (Finset.univ.filter fun i => SB i = v).card

end PrivOptTest



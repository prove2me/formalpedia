-- Prove2me | Definitions.Def_QaryCVP_Supplement_alg4
-- name    : QaryCVP_Supplement_alg4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:14:24.690795+00:00
-- url     : https://prove2.me/theorems/7f198615-aa04-4756-93dd-bdbf0bbc7065
-- title:
--   A mathematical model of Algorithm 4 (SVP), its randomness, and the specifications of its subprocedures
-- statement:
--   **Algorithm 4** (p.48) takes $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ ($q\ge2$, $n\ge1$, $m\ge0$) and returns a nonzero vector of $\Lambda$:
--
--   1. if $m=0$ return $e_1$; if $n=1$ return $(q/\gcd(q,H_{11},\dots,H_{m1}))e_1$; set $\hat x=qe_1$;
--   2. if $q=2$ or $q^4\le n$, scan every nonzero $x$ with $\|x\|^2\le q^2$, replacing $\hat x$ by $x$ when $Hx=0_m$ and $\|x\|<\|\hat x\|$, and return $\hat x$;
--   3. let $u$ be the least integer with $|B_{n-1}(u)|\ge q^m2^{\lceil n^{2/3}\rceil}$ and $b=\min\{u+1,q^2\}$ (33);
--   4. if $\delta\le\delta_0$ (exactly: $q^m\le2^{\delta_0n}$) return the nonzero exact search $E^{\ne0}_0(H,0^n,b)$, or $\hat x$ on $\bot$;
--   5. otherwise let $a>0$ solve $\mu(a)=u/(n-1)$, $n_0=\lceil n/(1-\kappa)\rceil$, $t_0=\hat p+\lambda$, $t_i=c_it_0$, $a_0=2^k\lfloor t_0n_0/2^k\rfloor$ with $0\le\hat p-p_a(1)\le\min\{n^{-2},10^{-12}\}$ (34); return $\hat x$ if some $t_i\notin(0,1/2)$ or (3) fails;
--   6. for each of $n$ rounds, each $z$ satisfying (35), each $i\notin\mathrm{supp}(z)$, $\sigma\in\{\pm1\}$ and $(N_+,N_-)$ satisfying (36): with $I=[n]\setminus(\mathrm{supp}(z)\cup\{i\})$, skip if $N_++N_->|I|$ or $2a_0-N_+-N_->n_0-|I|$; form $d$ with $a_0-N_+$ ones, then $a_0-N_-$ minus ones, then zeros; sample a fresh uniform $D$; put $A=[H_I\ D]$, $t=-H(z+\sigma e_i)+Dd$; for every $v$ output by the enumeration $R(A,t)$ with $v_{|I|+1..n_0}=d$, set $x=z+\sigma e_i+e_v$ and keep it if $Hx=0_m$ and $\|x\|<\|\hat x\|$;
--   7. return $\hat x$.
--
--   Here (35) is $z_j\in\{0\}\cup\{|z_j|\ge2\}$, $\|z\|^2\le b$, $-\sum_j\log r_a(z_j)\le n(H(r_a)+\varepsilon)$, and (36) is $N_\pm\le a_0$, $|N_\pm-np_a(1)|\le\varepsilon n+1$, $1+\|z\|^2+N_++N_-\le b$ and $<q^2$; the numerical tests use outward rational intervals of width at most one (p.50). The random choices of different cases and rounds are independent. The module also states the specifications used by the theorems: the accuracy of $\hat p$, the validity of the enclosures, the output specification of the nonzero exact search, the uniform bound of Lemma 3.2 on omitting a fixed vector at the actual completion parameters, a program computing the enumeration, and a program implementing Algorithm 4.
--
--   **Formalization Note** The model is parametrized by the enumeration $R$, the exact search, $\hat p$ and the enclosures (as the published model of Algorithm 3). Finite sets are scanned in a fixed order, which changes only the choice among equally short vectors. The added matrix $D$ is the last $n_0-|I|$ columns of a uniform $m\times n_0$ sample. A program implements Algorithm 4 when there is a measurable assignment of the random choices to coin tapes under which its output on every tape equals the model's, and whose law under fair coins is within total-variation distance $2^{-n}$ of the model's law (independent uniform added matrices, fair bits for $R$).
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Algorithm 4, p.48; §5.1, pp.49–50 ((33)–(36), exact tests); Lemma 3.2 and §3.1.1, pp.20–22; Definition 3.4, p.24; Section E.6, pp.98–100

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3
import Definitions.Def_QaryCVP_Supplement_svpBasics
import Definitions.Def_QaryCVP_Supplement_thetaDist
import Definitions.Def_QaryCVP_Supplement_svpExponents

open MeasureTheory ProbabilityTheory Filter Topology TwMSOCount.Main

namespace QaryCVP.Supplement

/-- The search radius `u` of (33), p.49: the least nonnegative integer with
`|B_{n−1}(u)| ≥ qᵐ 2^{⌈n^{2/3}⌉}`.
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), (33), p.49.

**Formalization Note.** `sInf` of the qualifying radii; for `n ≥ 2` the set is nonempty
(`|B_{n−1}(u)| → ∞`), and Algorithm 4 uses `u` only for `n ≥ 2`, `m ≥ 1`. -/
noncomputable def radiusU (n m q : ℕ) : ℕ :=
  sInf {u : ℕ | q ^ m * 2 ^ ⌈(n : ℝ) ^ ((2 : ℝ) / 3)⌉₊ ≤ ballCount (n - 1) u}

/-- `b = min{u + 1, q²}` (33), p.49. -/
noncomputable def radiusB (n m q : ℕ) : ℕ := min (radiusU n m q + 1) (q ^ 2)

/-- The counting parameter `a > 0` with `µ(a) = u/(n − 1)` (p.49). -/
noncomputable def aOf (n m q : ℕ) : ℝ := aSolve ((radiusU n m q : ℝ) / ((n : ℝ) - 1))

/-- The completion dimension `n₀ = ⌈n/(1 − κ)⌉` (p.49). -/
noncomputable def n0Of (κ : ℚ) (n : ℕ) : ℕ := ⌈(n : ℚ) / (1 - κ)⌉₊

/-- The proportions (34), p.49: `t₀ = b̂p + λ`, `tᵢ = cᵢt₀` (`1 ≤ i ≤ k`), written `tᵢ = cᵢ(b̂p + λ)`
for every `i` (equal under `c₀ = 1`), with `b̂p = bp n m q` the rational upper approximation of
`p_a(1)` chosen from `(n, m, q)`. -/
def propT (P : Params) (bp : ℕ → ℕ → ℕ → ℚ) (n m q : ℕ) : ℕ → ℚ :=
  fun i => P.c i * (bp n m q + P.lam)

/-- The sign count `a₀ = 2^k ⌊t₀n₀/2^k⌋` (34), p.49 (`QaryCVP.signCount0`). -/
noncomputable def a0Of (P : Params) (bp : ℕ → ℕ → ℕ → ℚ) (n m q : ℕ) : ℕ :=
  signCount0 P.k (propT P bp n m q 0 : ℝ) (n0Of P.κ n)

/-- The accuracy of `b̂p` required by (34), p.49: `0 ≤ b̂p − p_a(1) ≤ min{n⁻², 10⁻¹²}`, with `a` the
counting parameter of the input (for every `n ≥ 2`, `m ≥ 1`, `q ≥ 2`). -/
def BpAccurate (bp : ℕ → ℕ → ℕ → ℚ) : Prop :=
  ∀ n m q : ℕ, 2 ≤ n → 1 ≤ m → 2 ≤ q →
    0 ≤ (bp n m q : ℝ) - pa (aOf n m q) 1 ∧
      (bp n m q : ℝ) - pa (aOf n m q) 1 ≤ min (1 / (n : ℝ) ^ 2) (1 / 10 ^ 12)

/-- The outward rational intervals of p.50 (Section E.6.2): an interval for the left side
`−Σⱼ log r_a(zⱼ)` of (35) (depending on `m, q, z`), one for its right side `n(H(r_a) + ε)`, and one
for `n p_a(1)` in (36). -/
structure Encl where
  lhs35 : ∀ {n : ℕ}, ℕ → ℕ → (Fin n → ℤ) → ℚ × ℚ
  rhs35 : ℕ → ℕ → ℕ → ℚ × ℚ
  np1 : ℕ → ℕ → ℕ → ℚ × ℚ

/-- A rational interval `[lo, hi]` of width at most one containing the real `x` (p.50: "enclose each
side in an interval of width at most one"). -/
def Encloses (I : ℚ × ℚ) (x : ℝ) : Prop := (I.1 : ℝ) ≤ x ∧ x ≤ I.2 ∧ I.2 - I.1 ≤ 1

/-- The enclosures are valid (p.50): for every `n ≥ 2`, `m ≥ 1`, `q ≥ 2`, with `a` the counting
parameter, they enclose `n(H(r_a) + ε)`, `n p_a(1)` and, for every `z` whose entries are `0` or of
absolute value at least two, `−Σⱼ log₂ r_a(zⱼ)`. -/
def EnclValid (P : Params) (encl : Encl) : Prop :=
  ∀ n m q : ℕ, 2 ≤ n → 1 ≤ m → 2 ≤ q →
    Encloses (encl.rhs35 n m q) (n * (entZ (ra (aOf n m q)) + P.ε)) ∧
    Encloses (encl.np1 n m q) (n * pa (aOf n m q) 1) ∧
    ∀ z : Fin n → ℤ, (∀ j, z j = 0 ∨ 2 ≤ |z j|) →
      Encloses (encl.lhs35 m q z) (-∑ j, Real.logb 2 (ra (aOf n m q) (z j)))

/-- The prescribed vectors `z` of (35), p.49, with the outward test of p.50: `zⱼ = 0` or `|zⱼ| ≥ 2`,
`‖z‖² ≤ b`, and the logarithmic budget is rejected only when the lower endpoint of the left side
exceeds the upper endpoint of the right side. -/
def Acc35 (encl : Encl) {n : ℕ} (m q : ℕ) (z : Fin n → ℤ) : Prop :=
  (∀ j, z j = 0 ∨ 2 ≤ |z j|) ∧ sqNormZ z ≤ (radiusB n m q : ℚ) ∧
    ¬ ((encl.rhs35 n m q).2 < (encl.lhs35 m q z).1)

/-- The sign-count window (36), p.49, with the widened enclosure of p.50: `N₊, N₋ ≤ a₀`,
`lo − (εn + 1) ≤ N± ≤ hi + (εn + 1)` for the enclosure `[lo, hi]` of `n p_a(1)`,
`1 + ‖z‖² + N₊ + N₋ ≤ b` and `1 + ‖z‖² + N₊ + N₋ < q²`. -/
def Win36 (P : Params) (bp : ℕ → ℕ → ℕ → ℚ) (encl : Encl) {n : ℕ} (m q : ℕ) (z : Fin n → ℤ)
    (Np Nm : ℕ) : Prop :=
  Np ≤ a0Of P bp n m q ∧ Nm ≤ a0Of P bp n m q ∧
    (encl.np1 n m q).1 - (P.ε * n + 1) ≤ Np ∧ (Np : ℚ) ≤ (encl.np1 n m q).2 + (P.ε * n + 1) ∧
    (encl.np1 n m q).1 - (P.ε * n + 1) ≤ Nm ∧ (Nm : ℚ) ≤ (encl.np1 n m q).2 + (P.ε * n + 1) ∧
    1 + sqNormZ z + Np + Nm ≤ (radiusB n m q : ℚ) ∧ 1 + sqNormZ z + Np + Nm < (q : ℚ) ^ 2

/-- The enumeration `R(A, t)` of Section 3.1 run with the proportions `t₀, …, t_k` (Algorithm 1, or
Algorithm 7 for a large modulus; p.49), as a randomized function of the proportions, the instance
`(A, t)` and its random bits `ω`, returning its output list. -/
abbrev EnumProc (Ω : Type) :=
  (ℕ → ℚ) → ∀ {m n0 q : ℕ}, Matrix (Fin m) (Fin n0) (ZMod q) → (Fin m → ZMod q) → Ω →
    List (Fin n0 → ℤ)

/-- The nonzero exact search `E^{≠0}_0(H, 0ⁿ, b)` (p.48, line 12), as a function of `(H, b)`. -/
abbrev SearchProc := ∀ {m n q : ℕ}, Matrix (Fin m) (Fin n) (ZMod q) → ℚ → Option (Fin n → ℤ)

/-- The output specification of the nonzero exact search (Definition 3.4, p.24; nonzero variant,
p.27): for `n ≥ 1`, `q ≥ 2`, `b ≥ 0`, it returns `⊥` exactly when no nonzero `x ∈ Λ` has
`‖x‖² ≤ b`, and otherwise such an `x` of minimum norm (`QaryCVP.IsSearchOutput` with target `0ⁿ`). -/
def NonzeroSearchSpec (E0 : SearchProc) : Prop :=
  ∀ (m n q : ℕ) (H : Matrix (Fin m) (Fin n) (ZMod q)) (b : ℚ), 1 ≤ n → 2 ≤ q → 0 ≤ b →
    IsSearchOutput (fun x => x ≠ 0) H 0 b (E0 H b)

/-- The index of a completion case (lines 19–20, p.48): `z ∈ {−q, …, q}ⁿ` (stored as offsets in
`Fin (2q + 1)`; every `z` of (35) has `‖z‖² ≤ b ≤ q²`), a position `i`, a sign `σ` (`true ↦ +1`),
and counts `N₊, N₋ ≤ n₀`. -/
abbrev CaseIdx (n q n0 : ℕ) :=
  (Fin n → Fin (2 * q + 1)) × Fin n × Bool × Fin (n0 + 1) × Fin (n0 + 1)

/-- The vector `z` of a case index: `zⱼ = wⱼ − q`. -/
def caseZ {n q : ℕ} (w : Fin n → Fin (2 * q + 1)) : Fin n → ℤ := fun j => ((w j : ℕ) : ℤ) - q

/-- The random choices of one case: an `m × n₀` matrix over `Z/qZ`, whose columns
`|I| + 1, …, n₀` are the added matrix `D` of line 24, and the bits `ω` of the call to `R`. -/
abbrev Alg4Sample (m n0 q : ℕ) (Ω : Type) := (Fin m → Fin n0 → ZMod q) × Ω

/-- The randomness of Algorithm 4: one sample for each of the `n` rounds and each case index. -/
abbrev Alg4Coins (κ : ℚ) (n m q : ℕ) (Ω : Type) :=
  Fin n → CaseIdx n q (n0Of κ n) → Alg4Sample m (n0Of κ n) q Ω

/-- The law of the randomness (p.49: "The random bits used to sample different added matrices and to
run different calls to R are mutually independent, including across rounds"): independent over
rounds and cases, each a uniform matrix times an independent `ω ∼ µ`. -/
noncomputable def alg4Measure (κ : ℚ) (n m q : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Measure (Alg4Coins κ n m q Ω) :=
  Measure.pi fun _ => Measure.pi fun _ =>
    (uniformOn (Set.univ : Set (Fin m → Fin (n0Of κ n) → ZMod q))).prod μ

/-- The `k`-th (0-based) element of `I` in increasing order. -/
def colIdx {n : ℕ} (I : Finset (Fin n)) (k : ℕ) : Option (Fin n) := (I.sort (· ≤ ·))[k]?

/-- Entry `k` (0-based) of `v`, zero outside the range. -/
def getZ {n0 : ℕ} (v : Fin n0 → ℤ) (k : ℕ) : ℤ := if h : k < n0 then v ⟨k, h⟩ else 0

/-- `e_v ∈ Zⁿ` (p.49): the first `|I|` entries of `v` placed on `I` in increasing order, zero
elsewhere. -/
def placeOn {n n0 : ℕ} (I : Finset (Fin n)) (v : Fin n0 → ℤ) : Fin n → ℤ :=
  fun j => if j ∈ I then getZ v (I.filter (· < j)).card else 0

/-- The padded vector `(0^{|I|}, d)` with `d` as in line 23: `a₀ − N₊` ones, then `a₀ − N₋` minus
ones, then zeros, in the last `n₀ − |I|` positions. -/
def addedVec (n0 s a0 Np Nm : ℕ) : Fin n0 → ℤ := fun k =>
  if k.val < s then 0 else
    if k.val - s < a0 - Np then 1 else if k.val - s < 2 * a0 - Np - Nm then -1 else 0

/-- The completion matrix `A = [H_I D]` (line 24): column `k < |I|` is column `(k-th element of I)`
of `H`, the other columns are those of the sampled matrix. -/
def compMatrix {m n n0 q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (I : Finset (Fin n))
    (S : Fin m → Fin n0 → ZMod q) : Matrix (Fin m) (Fin n0) (ZMod q) := fun r k =>
  if k.val < I.card then (match colIdx I k.val with | some j => H r j | none => 0) else S r k

open Classical in
/-- Scan the candidates in order, replacing the current vector `x̂` by `x` exactly when `Hx = 0ᵐ` and
`‖x‖ < ‖x̂‖` (lines 6 and 29). -/
noncomputable def bestShort {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (xhat : Fin n → ℤ)
    (L : List (Fin n → ℤ)) : Fin n → ℤ :=
  L.foldl (fun xh x => if x ∈ qaryLattice H ∧ sqNormZ x < sqNormZ xh then x else xh) xhat

/-- `gcd(q, H₁₁, …, H_{m1})` on canonical representatives (line 2; p.52). -/
def gcdCol {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) : ℕ :=
  (List.finRange m).foldl (fun g i => if h : 0 < n then Nat.gcd g (H i ⟨0, h⟩).val else g) q

/-- The integer vectors with all entries in `[−q, q]` (containing every `x` with `‖x‖² ≤ q²`). -/
noncomputable def boxQ (n q : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(q : ℤ)) q

open Classical in
/-- The candidates produced by one completion case (lines 19–29, p.48) with sample `s`: if the case
passes (35), `i ∉ supp(z)` and (36), and the count check of line 22, run `R` on
`A = [H_I D]`, `t = −H(z + σeᵢ) + Dd`, keep the outputs `v` with `v_{|I|+1..n₀} = d`, and return
`x = z + σeᵢ + e_v` for each. -/
noncomputable def caseCands {Ω : Type} (P : Params) (bp : ℕ → ℕ → ℕ → ℚ) (encl : Encl)
    (R : EnumProc Ω) {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q))
    (c : CaseIdx n q (n0Of P.κ n)) (s : Alg4Sample m (n0Of P.κ n) q Ω) : List (Fin n → ℤ) :=
  let n0 := n0Of P.κ n
  let z := caseZ c.1
  let i := c.2.1
  let σ : ℤ := if c.2.2.1 then 1 else -1
  let Np := c.2.2.2.1.val
  let Nm := c.2.2.2.2.val
  let a0 := a0Of P bp n m q
  if ¬ (Acc35 encl m q z ∧ z i = 0 ∧ Win36 P bp encl m q z Np Nm) then [] else
  let I : Finset (Fin n) := Finset.univ.filter (fun j => z j = 0 ∧ j ≠ i)
  if I.card < Np + Nm ∨ (n0 : ℤ) - I.card < 2 * (a0 : ℤ) - Np - Nm then [] else
  let dv := addedVec n0 I.card a0 Np Nm
  let A := compMatrix H I s.1
  let zi : Fin n → ℤ := z + fun j => if j = i then σ else 0
  let t : Fin m → ZMod q :=
    -(H.mulVec (fun j => (zi j : ZMod q))) + A.mulVec (fun k => (dv k : ZMod q))
  ((R (propT P bp n m q) A t s.2).filter
      (fun v => decide (∀ k : Fin n0, I.card ≤ k.val → v k = dv k))).map
    (fun v => zi + placeOn I v)

open Classical in
/-- A mathematical model of **Algorithm 4** (SVP, p.48), lines 1–34, run on `H` with the randomness
`ω`. It is parametrized by the constants `P`, the approximation `b̂p` (34), the interval enclosures
of p.50, the enumeration `R` and the nonzero exact search `E^{≠0}_0`.

Line by line: 1 return `e₁` if `m = 0`; 2 return `(q/gcd(q, H₁₁, …, H_{m1}))e₁` if `n = 1`;
3 `x̂ = qe₁`; 4–8 if `q = 2` or `q⁴ ≤ n`, scan every nonzero `x` with `‖x‖² ≤ q²`; 10 `u, b` by (33);
11–14 if `δ ≤ δ₀` (exact test `q^{m·den δ₀} ≤ 2^{num δ₀·n}`), return `E^{≠0}_0(H, 0ⁿ, b)` or `x̂` on
`⊥`; 16–17 compute `n₀`, `t₀, …, t_k`, `a₀` and return `x̂` if some `tᵢ ∉ (0, 1/2)` or (3) fails;
18–33 `n` rounds over every case `(z, i, σ, N₊, N₋)`, each with a fresh sample; 34 return `x̂`.
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Algorithm 4, p.48;
§5.1, pp.49–50.

**Formalization Note.** Finite sets are scanned in a fixed enumeration (`Finset.toList`); with the
strict improvement of lines 6 and 29 this changes only which vector is returned among equally short
candidates. The added matrix `D` is the last `n₀ − |I|` columns of a uniform `m × n₀` sample, which
is uniform. Indices are 0-based. -/
noncomputable def alg4 {Ω : Type} (P : Params) (bp : ℕ → ℕ → ℕ → ℚ) (encl : Encl)
    (R : EnumProc Ω) (E0 : SearchProc) {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q))
    (ω : Alg4Coins P.κ n m q Ω) : Fin n → ℤ :=
  if m = 0 then unitVec1 n else
  if n = 1 then (fun i => if i.val = 0 then ((q / gcdCol H : ℕ) : ℤ) else 0) else
  let xhat : Fin n → ℤ := fun i => if i.val = 0 then (q : ℤ) else 0
  if q = 2 ∨ q ^ 4 ≤ n then
    bestShort H xhat ((boxQ n q).filter (fun x => x ≠ 0 ∧ sqNormZ x ≤ (q : ℚ) ^ 2)).toList
  else
  if DensityLeQ P.δ0 q m n then
    (match E0 H (radiusB n m q : ℚ) with
      | some x => x
      | none => xhat)
  else
  if ¬ CoordCond P.k (fun i => (propT P bp n m q i : ℝ)) then xhat else
  bestShort H xhat ((List.finRange n).flatMap fun r =>
    (Finset.univ : Finset (CaseIdx n q (n0Of P.κ n))).toList.flatMap fun c =>
      caseCands P bp encl R H c (ω r c))

/-- The completion branch of Algorithm 4 (lines 16–34) on an input in the range of Theorems 5.7 and
5.8: `n ≥ 2`, `m ≥ 1`, `q ≥ 3`, `q⁴ > n`, and `δ₀ < δ ≤ D`. -/
def CompRange (P : Params) (D : ℝ) (n m q : ℕ) : Prop :=
  2 ≤ n ∧ 1 ≤ m ∧ 3 ≤ q ∧ n < q ^ 4 ∧ (P.δ0 : ℝ) < density q m n ∧ density q m n ≤ D

/-- The uniform bound of Lemma 3.2 on omitting a fixed vector (§3.1.1; used in Theorem 5.7's proof,
p.53), at the actual parameters of every completion: there are `ε(·) → 0` and `N` such that for every
input in the completion range with `n ≥ N` and every fixed `v ∈ {−1, 0, 1}^{n₀}` with `a₀` entries of
each nonzero sign, over a uniform `A ∈ (Z/qZ)^{m×n₀}` and `ω ∼ µ`,
`Pr[v is among the outputs of R(A, Av)] ≥ 1 − 2^{−(ν − ε(n₀))n₀^{2/3}}`, the events being measurable. -/
def InclusionBound {Ω : Type} [MeasurableSpace Ω] (P : Params) (bp : ℕ → ℕ → ℕ → ℚ) (D : ℝ)
    (μ : Measure Ω) (R : EnumProc Ω) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ N : ℕ, ∀ n m q : ℕ, N ≤ n → CompRange P D n m q →
    ∀ v ∈ ternarySet (n0Of P.κ n) (a0Of P bp n m q),
      (∀ A : Matrix (Fin m) (Fin (n0Of P.κ n)) (ZMod q),
        MeasurableSet {ω | v ∈ R (propT P bp n m q) A (A.mulVec (fun j => (v j : ZMod q))) ω}) ∧
      1 - (2 : ℝ) ^ (-((P.ν : ℝ) - ε (n0Of P.κ n)) * ((n0Of P.κ n : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) ≤
        matAvg q m (n0Of P.κ n) (fun A =>
          (μ {ω | v ∈ R (propT P bp n m q) A (A.mulVec (fun j => (v j : ZMod q))) ω}).toReal)

/-- The input word of a completion call `R(A, t)` with proportions `t₀, …, t_k`: the short-solution
word `(n₀, m, q, A, t)` (`QaryCVP.encShort`) followed by `t₀, …, t_k`. -/
def encComp (k : ℕ) (t : ℕ → ℚ) {m n0 q : ℕ} (A : Matrix (Fin m) (Fin n0) (ZMod q))
    (b : Fin m → ZMod q) : List ℚ :=
  encShort A b ++ (List.range (k + 1)).map t

/-- The program `Rprog` computes `R` on the completion calls of Algorithm 4: for every accurate `b̂p`,
every input in the completion range, every `(A, t)` of dimension `n₀` and every coin tape, its output
word is the concatenation of the vectors of `R(A, t)` run on that tape. -/
def ComputesEnum (P : Params) (D : ℝ) (Rprog : Program) (R : EnumProc (ℕ → Bool)) : Prop :=
  ∀ bp : ℕ → ℕ → ℕ → ℚ, BpAccurate bp → ∀ n m q : ℕ, CompRange P D n m q →
    ∀ (A : Matrix (Fin m) (Fin (n0Of P.κ n)) (ZMod q)) (b : Fin m → ZMod q) (τ : ℕ → Bool),
      callOutput Rprog (Config.init (encComp P.k (propT P bp n m q) A b)) τ =
        some ((R (propT P bp n m q) A b τ).map encZVec).flatten

/-- The program `Pr` implements Algorithm 4 (the model `alg4` with these subprocedures) on the input
`H`: there is a measurable assignment `φ` of the algorithm's random choices to coin tapes such that
(i) on every coin tape the program's output is `alg4`'s output at `φ(τ)`, and (ii) the law of `φ`
under fair coins is within total-variation distance `2^{−n}` of the law `alg4Measure` of the model's
randomness (independent uniform added matrices and fair-coin bits for `R`, p.49).

**Formalization Note.** Clause (ii) is what makes `Pr` the randomized Algorithm 4 rather than one of
its derandomized runs: without it a program could reproduce the model's output on a single unlucky
assignment of the random choices. Exact uniformity is not claimed: a program halting on every tape
reads finitely many fair bits, so it samples `Z/qZ` only up to the bounded-bit error of Section
E.6.4 (`2^{−Ω(n²)}` per sample, p.52), which is below `2^{−n}` with polynomially many bits. -/
def ImplementsAlg4 (Pr : Program) (P : Params) (bp : ℕ → ℕ → ℕ → ℚ) (encl : Encl)
    (R : EnumProc (ℕ → Bool)) (E0 : SearchProc) {m n q : ℕ}
    (H : Matrix (Fin m) (Fin n) (ZMod q)) : Prop :=
  ∃ φ : (ℕ → Bool) → Alg4Coins P.κ n m q (ℕ → Bool), Measurable φ ∧
    (∀ S : Set (Alg4Coins P.κ n m q (ℕ → Bool)), MeasurableSet S →
      |(coinTape (φ ⁻¹' S)).toReal - (@alg4Measure P.κ n m q _ _ coinTape
        (by unfold coinTape; infer_instance) S).toReal| ≤
        (2 : ℝ) ^ (-(n : ℝ))) ∧
    ∀ τ : ℕ → Bool,
      callOutput Pr (Config.init (encSVP H)) τ = some (encZVec (alg4 P bp encl R E0 H (φ τ)))

end QaryCVP.Supplement



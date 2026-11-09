-- Prove2me | Definitions.Def_RecoveryStorage3SUM_Adaptive_Construction
-- name    : RecoveryStorage3SUM_Adaptive_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:41.60445+00:00
-- url     : https://prove2.me/theorems/59016737-f0c3-462d-a22c-9ab6ecc06a28
-- title:
--   The objects of the construction: marked values, loads, the padded self-map, Recover, and $z$
-- statement:
--   Let $A,B$ be sets of $n$ integers and $\delta$ the threshold exponent. Parameters: the heavy threshold $n^\delta\log^2 n$, the number of parts $L=\lceil 6n^\delta\log^2 n\rceil$, the sample size $|R|=\min(\lceil 3n^{1-\delta}\rceil,n)$, the prime range starting at $\lceil n^{2-\delta}\log^3 n\rceil$, and the repetition counts $\lceil c\log n\rceil$.
--
--   1. $\mathrm{count}_{X\times Y}(c)=|\{(a,b)\in X\times Y:a+b=c\}|$. A value of $A+B$ is **heavy** if its count is at least the threshold.
--   2. $C^\star=R+B$ is the **marked** set.
--   3. $M_r=\{(a,b)\in A\times B: a+b\equiv_p r,\ a+b\notin C^\star\}$, and the **load** is $d_{i,r}=|M_r\cap(A_i\times B)|$ for a part $A_i$ of a partition of $A$.
--   4. The **padded self-map** $G$ of $[2p]$ for a part $A_i$: list $A_i\times B$ in lexicographic order as $(a_x,b_x)$, and set
--   $$G(x)=\begin{cases}(a_x+b_x)\bmod p,& x<|A_i\times B|\text{ and }a_x+b_x\notin C^\star,\\ p+(x\bmod p),&\text{otherwise.}\end{cases}$$
--   5. A run with prime $p$ is **clean** for $c$ if every $c'\in C^\star$ with $c'\equiv_p c$ equals $c$. The target $c$ itself may be marked.
--   6. **Recover$(r)$** (Algorithm 2). The set $\widehat A$ collects first coordinates of the points returned by the inverters at $r$, where a point is kept only if $G$ maps it to $r$. The expansion lists all $(a,b)$ with $a\in\widehat A$ and $b\in B$, $b\equiv_p r-a$. Only its first $L$ entries are processed, and an entry is output iff $a+b\notin C^\star$.
--   7. $z(c)=\mathrm{cong}(r)-|\{(a,b)\in\mathrm{out}\cap(A'\times B'):a+b\ne c\}|$ with $r=c\bmod p$ and $\mathrm{cong}(r)=|\{(a,b)\in A'\times B':a+b\equiv_p r\}|$, as an integer.
--
--   Inverter answers are an arbitrary function here, so the deterministic facts about Recover hold for all of them.
--
--   **Formalization Note** The source takes real sizes as integers and assumes $L$ divides $n$. Here sizes are rounded up. The sample size is capped at $n$ since $R\subseteq A$: the cap is inactive for $\delta>0$ and large $n$, and at $\delta=0$ it gives $R=A$. The source leaves the reading order of the expansion free; here $\widehat A$ and each bucket are read in increasing order.
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Section 2, p.6; Section 3, pp.6-9; Algorithms 1-3, pp.7-9; Section 4.1, p.10

import Mathlib

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-!
# The objects of the construction: §§3–4.1

Carmel, Kosoburd, Krauthgamer, STOC 2027 submission #561, §2, p.6; §3, pp.6–9; §4.1, p.10.

**Formalization Note.** `log` is the natural logarithm. The source sets `L := 6 n^δ log² n` "assuming
for simplicity that L divides n" and takes real sizes as integers; here every size is rounded up,
the parts of a partition may differ by one (`Laws`), and no divisibility is assumed. Because `R ⊆ A`, the
sample size `3 n^{1-δ}` is capped at `n`; for `δ > 0` the cap is inactive for large `n`, and at `δ = 0`
the sample is all of `A`. A value of the source's "Recover" depends on the iteration order only
through the reading cap; here `Â` and each bucket are read in increasing order.
-/

/-! ### Parameters -/

/-- `n^δ log² n`, the heavy threshold. -/
noncomputable def heavyThreshold (n : ℕ) (δ : ℝ) : ℝ := (n : ℝ) ^ δ * Real.log n ^ 2

/-- `L = ⌈6 n^δ log² n⌉`, the number of parts of a partition. -/
noncomputable def numParts (n : ℕ) (δ : ℝ) : ℕ := ⌈6 * heavyThreshold n δ⌉₊

/-- `|R| = min(⌈3 n^{1-δ}⌉, n)`. -/
noncomputable def sampleSize (n : ℕ) (δ : ℝ) : ℕ := min ⌈3 * (n : ℝ) ^ (1 - δ)⌉₊ n

/-- `⌈n^{2-δ} log³ n⌉`, the lower end of the prime range. -/
noncomputable def primeLow (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ (2 - δ) * Real.log n ^ 3⌉₊

/-- `⌈c log n⌉`, for the repetition counts `J = Θ(log n)` and `K = Θ(log n)`. -/
noncomputable def logCount (c n : ℕ) : ℕ := ⌈(c : ℝ) * Real.log n⌉₊

/-! ### Sums, marked values, heavy values -/

/-- `count_{X×Y}(c) = |{(a,b) ∈ X × Y : a + b = c}|`. -/
def countIn (X Y : Finset ℤ) (c : ℤ) : ℕ :=
  ((X ×ˢ Y).filter fun x => x.1 + x.2 = c).card

/-- `C⋆ = R + B`, the marked values. -/
def markedSet (R B : Finset ℤ) : Finset ℤ := (R ×ˢ B).image fun x => x.1 + x.2

/-- `c ∈ A + B` is heavy if `count(c) ≥ n^δ log² n`, for `n = |A|`. -/
def IsHeavy (A B : Finset ℤ) (δ : ℝ) (c : ℤ) : Prop :=
  0 < countIn A B c ∧ heavyThreshold A.card δ ≤ countIn A B c

/-- The check of line 2 of Algorithm 1: every heavy value is marked. -/
def HeavyCovered (A B R : Finset ℤ) (δ : ℝ) : Prop :=
  ∀ c, IsHeavy A B δ c → c ∈ markedSet R B

/-! ### Residue classes and loads -/

/-- `x mod p` as an element of `[p]`, for an integer `x` of any sign and `p > 0`. -/
def residue (p : ℕ) (x : ℤ) : ℕ := (x % (p : ℤ)).toNat

/-- `M_r = {(a,b) ∈ X × B : a + b ≡_p r, a + b ∉ C⋆}`, for `X = A`; for `X = A_i^{(k)}` this is
`M_r ∩ (A_i^{(k)} × B)`. -/
def unmarkedClass (X B R : Finset ℤ) (p r : ℕ) : Finset (ℤ × ℤ) :=
  (X ×ˢ B).filter fun x => residue p (x.1 + x.2) = r ∧ x.1 + x.2 ∉ markedSet R B

/-- The part `A_i` of the partition `π` of `A`. -/
def part {A : Finset ℤ} {L : ℕ} (π : A → Fin L) (i : Fin L) : Finset ℤ :=
  (A.attach.filter fun a => π a = i).image Subtype.val

/-- The load `d_{i,r}^{(k)} = |M_r ∩ (A_i^{(k)} × B)|` for the partition `π = π^{(k)}`. -/
def load {A : Finset ℤ} {L : ℕ} (B R : Finset ℤ) (p : ℕ) (π : A → Fin L) (i : Fin L) (r : ℕ) : ℕ :=
  (unmarkedClass (part π i) B R p r).card

/-- `∑_{i,r} (d_{i,r})²` for one partition. -/
def squaredLoad {A : Finset ℤ} {L : ℕ} (B R : Finset ℤ) (p : ℕ) (π : A → Fin L) : ℕ :=
  ∑ i : Fin L, ∑ r ∈ Finset.range p, load B R p π i r ^ 2

/-! ### The padded self-map -/

/-- `A_i × B` in lexicographic order. -/
noncomputable def partPairs (X B : Finset ℤ) : List (ℤ × ℤ) :=
  (X.sort (· ≤ ·)).flatMap fun a => (B.sort (· ≤ ·)).map fun b => (a, b)

/-- The padded self-map `G` of `[2p]` for the part `X = A_i^{(k)}`:
`G(x) = (a_x + b_x) mod p` if `x < |X × B|` and `a_x + b_x ∉ C⋆`; `G(x) = p + (x mod p)` otherwise. -/
noncomputable def paddedMap (X B R : Finset ℤ) (p : ℕ) (x : ℕ) : ℕ :=
  match (partPairs X B)[x]? with
  | some ab =>
    if ab.1 + ab.2 ∉ markedSet R B then residue p (ab.1 + ab.2) else p + x % p
  | none => p + x % p

/-! ### Clean runs -/

/-- A run with prime `p` is clean for `c`: every `c′ ∈ C⋆` with `c′ ≡_p c` is `c`. -/
def CleanFor (B R : Finset ℤ) (p : ℕ) (c : ℤ) : Prop :=
  ∀ c' ∈ markedSet R B, residue p c' = residue p c → c' = c

/-! ### Recover: Algorithm 2 -/

/-- One run: its prime and its `K` partitions of `A` into `L` parts. -/
structure Attempt (A : Finset ℤ) (K L : ℕ) where
  p : ℕ
  π : Fin K → A → Fin L

open Classical in
/-- `Â`, the discover step: the first coordinates of the points returned by the inverters at `r`
and verified by evaluating the padded map. `inv k i` is the answer function of the FN structure of
`G_i^{(k)}`; nothing about it is assumed here. -/
noncomputable def discovered {A : Finset ℤ} {K L : ℕ} (B R : Finset ℤ) (run : Attempt A K L)
    (inv : Fin K → Fin L → ℕ → Option ℕ) (r : ℕ) : Finset ℤ :=
  (Finset.univ.biUnion fun k : Fin K => Finset.univ.biUnion fun i : Fin L =>
    match inv k i r with
    | none => ∅
    | some x =>
      if paddedMap (part (run.π k) i) B R run.p x = r then
        match (partPairs (part (run.π k) i) B)[x]? with
        | some ab => {ab.1}
        | none => ∅
      else ∅)

/-- The bucket `B_{(r-a) mod p} = {b ∈ B : b ≡_p r - a}` in increasing order. -/
noncomputable def bucket (B : Finset ℤ) (p r : ℕ) (a : ℤ) : List ℤ :=
  ((B.filter fun b => residue p b = residue p ((r : ℤ) - a))).sort (· ≤ ·)

/-- The full expansion, with no cap: every pair `(a, b)` with `a ∈ Â` and `b ∈ B_{(r-a) mod p}`,
in reading order. Its length is the number of values the uncapped expansion reads. -/
noncomputable def expansion {A : Finset ℤ} {K L : ℕ} (B R : Finset ℤ) (run : Attempt A K L)
    (inv : Fin K → Fin L → ℕ → Option ℕ) (r : ℕ) : List (ℤ × ℤ) :=
  ((discovered B R run inv r).sort (· ≤ ·)).flatMap fun a =>
    (bucket B run.p r a).map fun b => (a, b)

open Classical in
/-- The output `out` of `Recover(r)`. Lines 6–8 of Algorithm 2: when more than `cap` values have been
read, return; so only the first `cap` entries of the expansion are processed, and an entry `(a, b)` is
output iff `a + b ∉ C⋆`. -/
noncomputable def recoverOutput {A : Finset ℤ} {K L : ℕ} (B R : Finset ℤ) (run : Attempt A K L)
    (inv : Fin K → Fin L → ℕ → Option ℕ) (cap r : ℕ) : Finset (ℤ × ℤ) :=
  (((expansion B R run inv r).take cap).toFinset).filter fun x => x.1 + x.2 ∉ markedSet R B

/-! ### The per-target value: Algorithm 3 -/

/-- `cong(r) = |{(a,b) ∈ A′ × B′ : a + b ≡_p r}|`. -/
def congCount (A' B' : Finset ℤ) (p r : ℕ) : ℕ :=
  ((A' ×ˢ B').filter fun x => residue p (x.1 + x.2) = r).card

/-- `z(c) = cong(r) - |{(a,b) ∈ out ∩ (A′ × B′) : a + b ≠ c}|`, for `r = c mod p`, as an integer. -/
def zValue (A' B' : Finset ℤ) (p : ℕ) (out : Finset (ℤ × ℤ)) (c : ℤ) : ℤ :=
  (congCount A' B' p (residue p c) : ℤ) -
    ((out.filter fun x => x ∈ A' ×ˢ B' ∧ x.1 + x.2 ≠ c).card : ℤ)

end RecoveryStorage3SUM.Adaptive



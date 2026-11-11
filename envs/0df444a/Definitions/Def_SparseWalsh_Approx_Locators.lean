-- Prove2me | Definitions.Def_SparseWalsh_Approx_Locators
-- name    : SparseWalsh_Approx_Locators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:02:28.397603+00:00
-- url     : https://prove2.me/theorems/a044d438-ce60-43c6-8456-ba9f23cd28f3
-- title:
--   Frequency locators: the identity locator, the degree-sensitive locator of Appendix C (Algorithm 4), amplification, binary codes, and the repetition and coding robust locators
-- statement:
--   A **frequency locator** consists of measurement shifts $y_1,\dots,y_D\in\mathbb F_2^d$ (the rows of a binary matrix $A$) and a decoder that maps every bit vector to one frequency or to failure. On a frequency $a$ the exact measurements are $Aa=(\langle y_j,a\rangle)_j$.
--
--   - **Identity locator** (Eq. (4)): $A=\mathrm{Id}$, and the decoder returns the measured bits.
--   - **Degree-sensitive locator** (Appendix C, $1\le k\le d$). If $k\ge d/256$, it is the identity locator. Otherwise put $\ell=\lceil\log_2d\rceil$, $q=2^\ell$, $J=\lceil\log_4k\rceil+1$ and $b_t=\lceil\log_2(128k/2^t)\rceil$. For each stage $t<J$ draw a uniform permutation $P_t$ of the $q$ labels; coordinate $i$ has label $i-1$. Split each permuted label into a prefix $h_t(i)\in\mathbb F_2^{b_t}$ (its bucket) and a suffix $\rho_t(i)\in\mathbb F_2^{\ell-b_t}$. Each bucket $v$ measures the parity $p_v=\sum_{h_t(i)=v}a_i$ and the suffix sum $r_v=\sum_{h_t(i)=v}a_i\rho_t(i)$. The decoder is Algorithm 4: at each stage it forms the residual measurements $z_t+A_t\tilde a_t$; for every bucket with $p_v=1$ it looks up $P_t^{-1}(v,r_v)$ and, if this is a coordinate label, flips that coordinate.
--   - **Amplification** (p. 40): take $n$ independent copies, stack their rows, and return the frequency output by a strict majority of the copies, or failure if there is none.
--   - A **binary code** is a linear map $E:\mathbb F_2^D\to\mathbb F_2^P$ (a $P\times D$ matrix) with a decoder. It corrects every pattern of at most $\beta P$ errors if it returns the message $x$ on every word within Hamming distance $\beta P$ of $Ex$.
--   - **Robust locators** for a bucket $v$ of a hash $B\in\mathbb F_2^{m\times d}$, given the bucket values $H^c_{B,y}(v)$. Write $\operatorname{sgn}(0)=1$, and let the comparison bit $z$ of two values satisfy $(-1)^z=\operatorname{sgn}(h_1)\operatorname{sgn}(h_2)$.
--     - *Repetition* (p. 40): use base shifts $x_1,\dots,x_u$. Bit $j$ is the majority over $t$ of the comparisons between $H^c_{B,x_t}(v)$ and $H^c_{B,x_t+y_j}(v)$. The locator then decodes these bits.
--     - *Coding* (Eq. (10), p. 41): use one base shift $x$, and take the rows of $EA$ as shifts. The bits are $(-1)^{z_j}=\operatorname{sgn}(H^c_{B,x}(v))\operatorname{sgn}(H^c_{B,x+(EA)_j}(v))$. The code decoder recovers the message, and the locator decodes it.
--     - In both methods a decoded $a$ is retained only if $Ba=v$ and it is allowed (the degree restriction, when imposed). Each bucket yields at most one candidate.
--
--   **Formalization Note.** Shifts are a list, and the decoder takes a list of bits and returns an `Option`. In the degree-sensitive locator, a permuted label is an $\ell$-bit number: its top $b_t$ bits are the bucket and its low $\ell-b_t$ bits the suffix. Rows are listed stage by stage and bucket by bucket, parity row first. The majority vote of the repetition locator outputs $1$ only on a strict majority of $1$s, which is a fixed tie rule. `tablePoints B Y` is the set of query points $\{y+B^\top z\}$ of the tables at the shifts $y\in Y$.
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 13 (Eq. (4)); p. 20 (§5.1); pp. 36-37 (App. C.1-C.2, Algorithm 4); pp. 40-41 (App. D.2, Eq. (10))

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-!
# Frequency locators: the identity locator (4), the degree-sensitive locator of Appendix C
(Algorithm 4), amplification by strict majority, binary codes, and the robust locators
(repetition and coding, Eq. (10))

Attias, Bshouty, Medvedev, Srebro, *Efficient Non-Adaptive Sparse Fourier Learning on the Boolean
Cube and Finite Abelian Groups*, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 13 (Eq. (4)),
p. 20 (§5.1), pp. 36–37 (App. C.1–C.2, Algorithm 4), pp. 40–41 (App. D.2, Eq. (10)).

* A **locator** is a list of measurement rows `y_1, …, y_D ∈ F_2^d` (the rows of `A`) and a
  decoder that maps every measurement vector (a list of bits) to one frequency or to failure
  (`none`) — "every decoder returns one result or failure on every input" (p. 40). `meas ℓ a` is
  `Aa = (⟨y_j, a⟩)_j`.
* `identityLocator d`: `A = Id`, decoder returns the bits (Eq. (4)).
* `degLocator d k P` (App. C): if `d ≤ 256k`, the identity; otherwise `ℓ = ⌈log₂ d⌉`, `q = 2^ℓ`,
  `J = ⌈log₄ k⌉ + 1`, `b_t = ⌈log₂(128k/2^t)⌉`, and for each stage `t < J` a permutation `P_t` of the
  `q` labels. Coordinate `i` (0-based; the paper's `i + 1`) has label `i`. The permuted label
  `P_t(i)`, an `ℓ`-bit number, splits into the prefix `h_t(i)` = its top `b_t` bits (the bucket,
  a number `< 2^{b_t}`) and the suffix `ρ_t(i)` = its low `ℓ − b_t` bits. Bucket `v` has the parity
  row `{i : h_t(i) = v}` and, for each suffix bit `j < ℓ − b_t`, the row `{i : h_t(i) = v, bit j of
  ρ_t(i) = 1}`; rows are listed stage by stage, bucket by bucket, parity row first. The decoder is
  Algorithm 4 (residual peeling over `F_2`).
* `degLocatorLaw d k`: the `P_t` independent and uniform.
* `amplify n μ`: `n` independent copies, rows stacked, decoder = the frequency returned by a strict
  majority of the copies, failure if there is none (p. 40).
* A **binary code** of message length `D`: a matrix `E ∈ F_2^{P×D}` (the linear map
  `F_2^D → F_2^P`) and a decoder `F_2^P → F_2^D ∪ {failure}`.
* `cmpBit h₁ h₂` is the bit `z` with `(−1)^z = sgn(h₁)sgn(h₂)`, `sgn(0) = 1` (Eq. (10)).
* `repLocate tab B ℓ x allowed v` (repetition, p. 40): for each row `y_j` of `A`, bit `j` is `1`
  iff strictly more than half of the comparisons `cmpBit(tab(x_t, v), tab(x_t + y_j, v))`,
  `t < u`, are `1` (ties give `0`: the fixed tie rule); the locator decodes the bits, and the
  candidate is retained iff `Ba = v` and `allowed a`. `tab y v` is the bucket value `H^c_{B,y}(v)`.
* `codeLocate tab B ℓ E x allowed v` (coding, p. 41): the rows of `EA` are the protected shifts;
  `z_j = cmpBit(tab(x, v), tab(x + (EA)_j, v))`, the code decoder recovers `Aa`, the locator decodes
  it, and the same two checks apply.
-/

/-- A frequency locator: measurement rows (the rows of `A`) and a decoder returning one frequency
or failure on every input. -/
structure Locator (d : ℕ) where
  rows : List (Cube d)
  dec : List (ZMod 2) → Option (Cube d)

/-- The exact measurements `Aa = (⟨y_j, a⟩)_j`. -/
def meas {d : ℕ} (ℓ : Locator d) (a : Cube d) : List (ZMod 2) := ℓ.rows.map fun y => dot y a

/-- The standard basis vector `e_i`. -/
def unitVec {d : ℕ} (i : Fin d) : Cube d := fun j => if j = i then 1 else 0

/-- The vector of `F_2^d` whose coordinates are the first `d` entries of a bit list (missing
entries read as `0`). -/
def ofBits {d : ℕ} (z : List (ZMod 2)) : Cube d := fun i => z.getD i 0

/-- The identity locator (Eq. (4)): rows `e_1, …, e_d`, decoder returns the measured bits. -/
def identityLocator (d : ℕ) : Locator d :=
  ⟨List.ofFn unitVec, fun z => some (ofBits z)⟩

/-! ### The degree-sensitive locator of Appendix C -/

/-- `ℓ = ⌈log₂ d⌉`. -/
def labelBits (d : ℕ) : ℕ := Nat.clog 2 d

/-- `J = ⌈log₄ k⌉ + 1`. -/
def degStages (k : ℕ) : ℕ := Nat.clog 4 k + 1

/-- `b_t = ⌈log₂(128k/2^t)⌉`, computed as `⌈log₂ ⌈128k/2^t⌉⌉` (equal, since `2^b` is an
integer). -/
def degBucketBits (k t : ℕ) : ℕ := Nat.clog 2 ((128 * k + 2 ^ t - 1) / 2 ^ t)

/-- The permuted label `P_t(i)` of coordinate `i` (label `i`), as a number below `q`. -/
def permLabel {d : ℕ} (q : ℕ) (P : Equiv.Perm (Fin q)) (i : Fin d) : ℕ :=
  if h : (i : ℕ) < q then (P ⟨i, h⟩ : ℕ) else 0

/-- The bucket `h_t(i)`: the top `b` bits of the `ℓ`-bit permuted label. -/
def degBucket {d : ℕ} (ℓ b q : ℕ) (P : Equiv.Perm (Fin q)) (i : Fin d) : ℕ :=
  permLabel q P i / 2 ^ (ℓ - b)

/-- The suffix `ρ_t(i)`: the low `ℓ − b` bits of the permuted label. -/
def degSuffix {d : ℕ} (ℓ b q : ℕ) (P : Equiv.Perm (Fin q)) (i : Fin d) : ℕ :=
  permLabel q P i % 2 ^ (ℓ - b)

/-- The rows of stage `t`: for each bucket `v < 2^b`, the parity row and then the `ℓ − b` suffix
rows. -/
def degStageRows (d ℓ b q : ℕ) (P : Equiv.Perm (Fin q)) : List (Cube d) :=
  (List.range (2 ^ b)).flatMap fun v =>
    (fun i => if degBucket ℓ b q P i = v then 1 else 0) ::
      (List.range (ℓ - b)).map fun j =>
        fun i => if degBucket ℓ b q P i = v ∧ (degSuffix ℓ b q P i).testBit j then 1 else 0

/-- One stage of Algorithm 4: from the stage's measurement block `z` and the current estimate `ã`,
form the residual measurements `z + A_t ã`; for each bucket with residual parity `1`, look up
`P_t^{−1}(v, r_v)` and, if it is the label of a coordinate `i < d`, set `(g_t)_i = 1`; return
`ã + g_t`. -/
noncomputable def degStageDecode (d ℓ b q : ℕ) (P : Equiv.Perm (Fin q)) (z : List (ZMod 2))
    (ã : Cube d) : Cube d := by
  classical exact
  let rows := degStageRows d ℓ b q P
  let res : ℕ → ZMod 2 := fun n => z.getD n 0 + dot (rows.getD n 0) ã
  let found : ℕ → Option (Fin d) := fun v =>
    if res (v * (1 + (ℓ - b))) = 1 then
      let r : ℕ := ∑ j ∈ Finset.range (ℓ - b), (res (v * (1 + (ℓ - b)) + 1 + j)).val * 2 ^ j
      let lab : ℕ := v * 2 ^ (ℓ - b) + r
      if h : lab < q then
        let i : ℕ := (P.symm ⟨lab, h⟩ : ℕ)
        if hi : i < d then some ⟨i, hi⟩ else none
      else none
    else none
  let g : Cube d := fun i =>
    if ∃ v ∈ Finset.range (2 ^ b), found v = some i then 1 else 0
  ã + g

/-- The degree-sensitive locator of Appendix C for the permutations `P_0, …, P_{J−1}`. -/
noncomputable def degLocator (d k : ℕ) (P : Fin (degStages k) → Equiv.Perm (Fin (2 ^ labelBits d))) :
    Locator d :=
  if d ≤ 256 * k then identityLocator d else
    let ℓ := labelBits d
    let q := 2 ^ ℓ
    let stageRows : ℕ → List (Cube d) := fun t =>
      if h : t < degStages k then degStageRows d ℓ (degBucketBits k t) q (P ⟨t, h⟩) else []
    let offset : ℕ → ℕ := fun t => ((List.range t).map fun t' => (stageRows t').length).sum
    ⟨(List.range (degStages k)).flatMap stageRows,
      fun z => some ((List.range (degStages k)).foldl
        (fun ã t =>
          if h : t < degStages k then
            degStageDecode d ℓ (degBucketBits k t) q (P ⟨t, h⟩)
              ((z.drop (offset t)).take (stageRows t).length) ã
          else ã)
        0)⟩

/-- The law of the degree-sensitive locator: independent uniform permutations. -/
noncomputable def degLocatorLaw (d k : ℕ) : PMF (Locator d) :=
  (PMF.uniformOfFintype (Fin (degStages k) → Equiv.Perm (Fin (2 ^ labelBits d)))).map
    (degLocator d k)

/-! ### Amplification -/

/-- Stack the rows of `n` locators and decode by strict majority of the component outputs
(failure if no frequency is returned by more than `n/2` copies). -/
noncomputable def stackLocators {d n : ℕ} (ls : Fin n → Locator d) : Locator d := by
  classical exact
    ⟨(List.ofFn ls).flatMap Locator.rows, fun z =>
      let offset : ℕ → ℕ := fun c =>
        ((List.range c).map fun c' => if h : c' < n then (ls ⟨c', h⟩).rows.length else 0).sum
      let outs : Fin n → Option (Cube d) := fun c =>
        (ls c).dec ((z.drop (offset c)).take (ls c).rows.length)
      let winners := Finset.univ.filter fun a : Cube d =>
        n < 2 * (Finset.univ.filter fun c => outs c = some a).card
      if h : winners.Nonempty then some h.choose else none⟩

/-- `n` independent draws from a law `μ` (the product law on `Fin n → α`). -/
noncomputable def iidPMF {α : Type} (μ : PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure finZeroElim
  | n + 1 => μ.bind fun x₀ => (iidPMF μ n).map fun xs => Fin.cons x₀ xs

/-- `n` independent copies of a locator law, stacked, with strict-majority decoding. -/
noncomputable def amplify {d : ℕ} (n : ℕ) (μ : PMF (Locator d)) : PMF (Locator d) :=
  (iidPMF μ n).map stackLocators

/-! ### Binary codes -/

/-- A binary linear code `E : F_2^D → F_2^P` with a decoder returning a message or failure. -/
structure BinCode (D : ℕ) where
  P : ℕ
  E : Matrix (Fin P) (Fin D) (ZMod 2)
  dec : Cube P → Option (Cube D)

/-- Hamming distance on `F_2^n`. -/
def hamming {n : ℕ} (x y : Cube n) : ℕ := (Finset.univ.filter fun i => x i ≠ y i).card

/-- The decoder corrects every pattern of at most `β P` errors. -/
def BinCode.Corrects {D : ℕ} (C : BinCode D) (β : ℝ) : Prop :=
  ∀ (msg : Cube D) (w : Cube C.P), (hamming (C.E *ᵥ msg) w : ℝ) ≤ β * C.P → C.dec w = some msg

/-! ### Robust locators -/

/-- The comparison bit `z` with `(−1)^z = sgn(h₁)·sgn(h₂)`, where `sgn(0) = 1`. -/
noncomputable def cmpBit (h₁ h₂ : ℝ) : ZMod 2 := by
  classical exact if (0 ≤ h₁ ↔ 0 ≤ h₂) then 0 else 1

/-- The retention rule: keep a decoded frequency `a` from bucket `v` only if `Ba = v` and it is
allowed (the degree restriction, when imposed). -/
noncomputable def retain {d m : ℕ} (B : Matrix (Fin m) (Fin d) (ZMod 2)) (allowed : Cube d → Prop)
    (v : Cube m) (o : Option (Cube d)) : Option (Cube d) := by
  classical exact match o with
    | some a => if B *ᵥ a = v ∧ allowed a then some a else none
    | none => none

/-- Repetition (p. 40): `tab y v` is the bucket value at shift `y`; base shifts `x_0, …, x_{u−1}`;
bit `j` is the strict majority of the `u` comparisons for row `y_j` (ties give `0`). -/
noncomputable def repLocate {d m u : ℕ} (tab : Cube d → Cube m → ℝ)
    (B : Matrix (Fin m) (Fin d) (ZMod 2)) (ℓ : Locator d) (x : Fin u → Cube d)
    (allowed : Cube d → Prop) (v : Cube m) : Option (Cube d) :=
  let bits : List (ZMod 2) := ℓ.rows.map fun y =>
    if u < 2 * (Finset.univ.filter fun t => cmpBit (tab (x t) v) (tab (x t + y) v) = 1).card
    then 1 else 0
  retain B allowed v (ℓ.dec bits)

/-- The matrix `A` of a locator with `D` rows (missing rows read as `0`). -/
def locMatrix {d : ℕ} (D : ℕ) (ℓ : Locator d) : Matrix (Fin D) (Fin d) (ZMod 2) :=
  fun j => ℓ.rows.getD j 0

/-- Coding (p. 41, Eq. (10)): the rows of `EA` are the protected shifts; one base shift `x`. -/
noncomputable def codeLocate {d m D : ℕ} (tab : Cube d → Cube m → ℝ)
    (B : Matrix (Fin m) (Fin d) (ZMod 2)) (ℓ : Locator d) (C : BinCode D) (x : Cube d)
    (allowed : Cube d → Prop) (v : Cube m) : Option (Cube d) :=
  let EA : Matrix (Fin C.P) (Fin d) (ZMod 2) := C.E * locMatrix D ℓ
  let z : Cube C.P := fun j => cmpBit (tab x v) (tab (x + EA j) v)
  retain B allowed v ((C.dec z).bind fun msg => ℓ.dec (List.ofFn msg))

/-- The query points of the tables at shifts `y ∈ Y` with hash `B`: `{y + Bᵀz}`. -/
noncomputable def tablePoints {d m : ℕ} (B : Matrix (Fin m) (Fin d) (ZMod 2))
    (Y : Finset (Cube d)) : Finset (Cube d) := by
  classical exact (Y ×ˢ (Finset.univ : Finset (Cube m))).image fun p => p.1 + Bᵀ *ᵥ p.2

end SparseWalsh.Approx



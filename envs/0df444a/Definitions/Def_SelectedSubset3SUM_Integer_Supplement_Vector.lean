-- Prove2me | Definitions.Def_SelectedSubset3SUM_Integer_Supplement_Vector
-- name    : SelectedSubset3SUM_Integer_Supplement_Vector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:49:27.290207+00:00
-- url     : https://prove2.me/theorems/d9f90acf-0c54-45ec-b991-d6e1650177fa
-- title:
--   Selected-entries convolution on $[r]^d$, its lattice counts, and a scalar machine with exact division
-- statement:
--   Fix naturals $r$ and $d$ and write $[r]=\{0,\dots,r-1\}$. A vector $x\in[r]^d$ has $L_1$ norm $\|x\|_1=\sum_j x_j$, and $H_{r,d,t}=\{x\in[r]^d:\|x\|_1=t\}$. An instance of **Problem 3.1** consists of a sparse real function $f$ on $H_{r,d,t_1}$, a sparse real function $g$ on $H_{r,d,t_2}$, each given as an arbitrary-order list of distinct (vector, weight) pairs, and a duplicate-free query list $\mathcal C\subseteq H_{r,d,t_1+t_2}$. Validity requires these norms and at most $n$ listed pairs in total; unlisted vectors have weight $0$. For each $c\in\mathcal C$ the selected value is
--
--   $$(f\star_r g)(c)=\sum_{a,b\in[r]^d,\ a+b=c} f(a)\,g(b),$$
--
--   where $a+b$ is ordinary coordinatewise addition in $\mathbb Z^d$ (no wraparound, no carries).
--
--   The two lattice counts are
--
--   $$H_r(d,\le s)=\bigl|\{x\in[r]^d:\|x\|_1\le s\}\bigr|,\qquad H_r(d,t,\ge s)=\max_{c\in H_{r,d,t}}\bigl|\{x\in[r]^d: x\le c,\ \|x\|_1\ge s\}\bigr|,$$
--
--   where $x\le c$ is coordinatewise domination and the maximum over an empty $H_{r,d,t}$ is $0$.
--
--   The machine is the mission's published scalar machine (exact real constant one, real addition, subtraction, multiplication, scalar memory access, and the word RAM) with one added instruction: divide a scalar by the integer held in a word. There are no tests on scalars and no real-to-word conversion. A run on an instance receives a word header $(n,r,d,t_1,t_2,s)$, the list lengths and all key and query coordinates, and the weights in scalar memory; a successful run accepts with every selected value in its designated scalar output cell. Its charge is input presentation, query outputs and executed instructions. The word width threshold is $b\,(d(\lfloor\lg r\rfloor+1)+\lfloor\lg\max(2,n)\rfloor+1)$.
--
--   The conditional premise used by Theorem 3.4 at base $r$ asserts one such program that solves every real-weight instance over $[r]^d$, for every $d$ and every split $t_1+t_2$, within $K\,(P(n,d,t,r)+|\mathcal C|\,Q(n,d,t,r))$, $t=t_1+t_2$, with $P,Q\ge0$. Finally $\rho(r)=r^2/(r!)^{1/r}$, and the cost of Theorem 3.4 at dimension $d$ and $t=(r-1)d/2$ is
--
--   $$\widehat n^{\,2(1-\log_\rho r)}\bigl(P(N,d,t,r)+N+|C|(Q(N,d,t,r)+1)\bigr),$$
--
--   replaced by the linear budget $|A|+|B|+|C|+1$ when a side is empty.
--
--   These objects carry the vector analogue of the mission's subset-convolution layer used by Theorems 3.3 and 3.4.
--
--   **Formalization Note** Vectors are `Fin d → Fin r`. The division instruction is needed for the factorial normalisation $(f\star_r g)(c)=(f'\star g')(c)/\prod_j c_j!$; its divisors are word values of at most $W$ bits, and division by a zero word returns $0$.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Problem 3.1, p.11; Lemma 3.2 (definitions of H_r) and footnote 10, p.12; Theorem 3.3 and its proof, p.12; Theorem 3.4 (ρ, cost), p.12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Mathlib
import Definitions.Def_SelectedSubset3SUM_Integer_AllQueries

namespace SelectedSubset3SUM.Integer.Supplement

open SelectedSubset3SUM.Integer

/-! Chan--Itakura--Ma--Yu, STOC 2027 submission #1421 (October 2026), §3, pp.11--14.
Problem 3.1: selected-entries convolution of sparse real functions on `[r]^d`, where
`[r] = {0,…,r-1}` and vector addition is ordinary coordinatewise addition in `ℤ^d`
(no wraparound, no carries). Lists are arbitrary-order presentations of finite sets. -/

/-- A vector of `[r]^d`. -/
abbrev Vec (r d : ℕ) : Type := Fin d → Fin r

/-- The `L1` norm `‖x‖₁ = ∑_j x_j` of a vector of `[r]^d`. -/
def norm1 {r d : ℕ} (x : Vec r d) : ℕ := ∑ j, (x j : ℕ)

/-- An instance of Problem 3.1: sparse `f` (left), sparse `g` (right), and the query set `𝒞`. -/
structure VecData (R : Type) (r d : ℕ) where
  left : List (Vec r d × R)
  right : List (Vec r d × R)
  queries : List (Vec r d)

/-- Validity: `f` supported on `H_{r,d,t₁}`, `g` on `H_{r,d,t₂}`, queries in `H_{r,d,t₁+t₂}`,
distinct keys and queries, and total listed support at most `n`. -/
def VecData.Valid {R : Type} {r d : ℕ} (I : VecData R r d) (n t₁ t₂ : ℕ) : Prop :=
  I.left.length + I.right.length ≤ n ∧
  (I.left.map Prod.fst).Nodup ∧ (I.right.map Prod.fst).Nodup ∧ I.queries.Nodup ∧
  (∀ u ∈ I.left, norm1 u.1 = t₁) ∧ (∀ u ∈ I.right, norm1 u.1 = t₂) ∧
  (∀ c ∈ I.queries, norm1 c = t₁ + t₂)

/-- The value of a sparse function at `x`; zero at unlisted vectors. -/
def vecValue {R : Type} [Zero R] {r d : ℕ} (rows : List (Vec r d × R)) (x : Vec r d) : R :=
  ((rows.find? (fun u => decide (u.1 = x))).map Prod.snd).getD 0

/-- `(f ⋆_r g)(c) = ∑_{a,b ∈ [r]^d, a + b = c} f(a) g(b)`, addition in `ℤ^d`. -/
def vecConvolution {R : Type} [CommRing R] {r d : ℕ} (I : VecData R r d) (c : Vec r d) : R :=
  ∑ a : Vec r d, ∑ b : Vec r d,
    if (∀ j, (a j : ℕ) + (b j : ℕ) = (c j : ℕ)) then vecValue I.left a * vecValue I.right b else 0

/-- `H_r(d, ≤ s)`: the number of vectors of `[r]^d` with `L1` norm at most `s`. -/
def lowerCount (r d s : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Vec r d => norm1 x ≤ s).card

/-- `H_r(d, t, ≥ s)`: the maximum, over `c ∈ [r]^d` with `‖c‖₁ = t`, of the number of vectors
`x ∈ [r]^d` dominated by `c` (`x_j ≤ c_j` for all `j`) with `‖x‖₁ ≥ s`; `0` if no such `c`. -/
def upperCount (r d t s : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Vec r d => norm1 c = t).sup fun c =>
    (Finset.univ.filter fun x : Vec r d => (∀ j, x j ≤ c j) ∧ s ≤ norm1 x).card

/-- `n + H_r(d, ≤ s) + q · H_r(d, t, ≥ s)`. -/
def vecCost (r d t s n q : ℕ) : ℝ :=
  n + (lowerCount r d s : ℝ) + q * (upperCount r d t s : ℝ)

/-- The coordinates of a vector, as words. -/
def coords {r d : ℕ} (x : Vec r d) : List ℤ := List.ofFn fun j => ((x j : ℕ) : ℤ)

/-- Word input: the header `n, r, d, t₁, t₂, s` and the three list lengths, then the
coordinates of every left key, every right key and every query, in list order. -/
def vecKeys {R : Type} {r d : ℕ} (n t₁ t₂ s : ℕ) (I : VecData R r d) : List ℤ :=
  ([n, r, d, t₁, t₂, s, I.left.length, I.right.length, I.queries.length].map Int.ofNat) ++
    (I.left.flatMap fun u => coords u.1) ++ (I.right.flatMap fun u => coords u.1) ++
    (I.queries.flatMap coords)

/-- Scalar input: the left weights, then the right weights. -/
def vecScalars {r d : ℕ} (I : VecData ℝ r d) : List ℝ :=
  I.left.map Prod.snd ++ I.right.map Prod.snd

/-! The machine is the published scalar machine `ScalarInstr` (exact real constant one,
`+`, `−`, `×`, scalar load/store, the word RAM) with one added instruction: exact division of
a scalar by the integer held in a word, `divw i j k : s[i] := s[j] / [k]`. It is needed for the
factorial normalisation of Theorem 3.3. Divisors are word values, so at most `W` bits;
division by a zero word gives `0` (Lean's convention). There are still no tests on scalars,
no real-to-word conversion and no transform or convolution instruction. -/

inductive VecInstr where
  | base (i : ScalarInstr)
  | divw (i j k : ℤ)

noncomputable def vecExec {W : ℕ} (P : List VecInstr) :
    ℕ → ℕ → ScalarMemory W → Option (Bool × ScalarMemory W)
  | 0, _, _ => none
  | fuel + 1, pc, m =>
    let next := vecExec P fuel (pc + 1)
    let writeWord (i : ℤ) (v : BitVec W) :=
      next { m with words := fun a => if a = i then v else m.words a }
    let writeScalar (i : ℤ) (v : ℝ) :=
      next { m with scalars := fun a => if a = i then v else m.scalars a }
    match P.getD pc (.base (.word .reject)) with
    | .divw i j k => writeScalar i (m.scalars j / ((m.words k).toInt : ℝ))
    | .base (.one i) => writeScalar i 1
    | .base (.add i j k) => writeScalar i (m.scalars j + m.scalars k)
    | .base (.sub i j k) => writeScalar i (m.scalars j - m.scalars k)
    | .base (.mul i j k) => writeScalar i (m.scalars j * m.scalars k)
    | .base (.load i j) => writeScalar i (m.scalars (m.words j).toInt)
    | .base (.store i j) => writeScalar (m.words i).toInt (m.scalars j)
    | .base (.word i) =>
      match i with
      | .one i => writeWord i 1
      | .add i j k => writeWord i (m.words j + m.words k)
      | .sub i j k => writeWord i (m.words j - m.words k)
      | .mul i j k => writeWord i (m.words j * m.words k)
      | .load i j => writeWord i (m.words (m.words j).toInt)
      | .store i j => writeWord (m.words i).toInt (m.words j)
      | .bltz i l => vecExec P fuel (if (m.words i).toInt < 0 then l else pc + 1) m
      | .accept => some (true, m)
      | .reject => some (false, m)

def vecInitial {r d : ℕ} (W n t₁ t₂ s : ℕ) (I : VecData ℝ r d) : ScalarMemory W :=
  { words := TrulySubcubicAPSP.loadWords W (vecKeys n t₁ t₂ s I)
    scalars := fun a => if a < 0 then 0 else (vecScalars I).getD a.toNat 0 }

/-- A successful run: it accepts within `fuel` steps and scalar cell `|scalars| + j` holds
`(f ⋆_r g)(c_j)` for the `j`-th query `c_j`. -/
def VecRun {r d : ℕ} (P : List VecInstr) (W n t₁ t₂ s fuel : ℕ) (I : VecData ℝ r d) : Prop :=
  ∃ m, vecExec P fuel 0 (vecInitial W n t₁ t₂ s I) = some (true, m) ∧
    ∀ j : Fin I.queries.length,
      m.scalars ((vecScalars I).length + j.val : ℕ) = vecConvolution I (I.queries.get j)

/-- Total charge: input presentation, every query output, and executed instructions. -/
def vecCharge {r d : ℕ} (n t₁ t₂ s fuel : ℕ) (I : VecData ℝ r d) : ℕ :=
  (vecKeys n t₁ t₂ s I).length + (vecScalars I).length + I.queries.length + fuel

/-- Required word width: `b (d (⌊lg r⌋ + 1) + ⌊lg max(2,n)⌋ + 1)` bits, enough to index
`[r]^d` and the support. -/
def vecWidth (b n r d : ℕ) : ℕ := b * (d * (Nat.log2 r + 1) + Nat.log2 (max 2 n) + 1)

/-- The conditional premise of Theorem 3.4 at base `r`: one uniform program solving every
real-weight instance of Problem 3.1 over `[r]^d` (every `d`, every split `t₁ + t₂`) with charge
at most `K (P(n,d,t,r) + |𝒞| Q(n,d,t,r))`, `t = t₁ + t₂`. Nothing about integer realisation
is assumed. The unused cutoff header is zero. -/
def VecSolver (r : ℕ) (P Q : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ n d t, 0 ≤ P n d t r ∧ 0 ≤ Q n d t r) ∧
  ∃ (code : List VecInstr) (b : ℕ) (K : ℝ), 0 < b ∧ 0 < K ∧
    ∀ (n d t₁ t₂ : ℕ) (I : VecData ℝ r d), I.Valid n t₁ t₂ →
      ∀ W ≥ vecWidth b n r d,
        ∃ fuel, VecRun code W n t₁ t₂ 0 fuel I ∧
          (vecCharge n t₁ t₂ 0 fuel I : ℝ) ≤
            K * (P n d (t₁ + t₂) r + I.queries.length * Q n d (t₁ + t₂) r)

/-- `ρ = r² / (r!)^{1/r}`. -/
noncomputable def rho (r : ℕ) : ℝ := (r : ℝ) ^ 2 / ((Nat.factorial r : ℝ)) ^ ((1 : ℝ) / r)

/-- The cost of Theorem 3.4 at dimension `d`, `t = (r-1)d/2`:
`n̂^{2(1 - log_ρ r)} (P(N,d,t,r) + N + |C| (Q(N,d,t,r) + 1))`; an exact linear input/output
budget when a side is empty. -/
noncomputable def vecReductionCost (r : ℕ) (P Q : ℕ → ℕ → ℕ → ℕ → ℝ) (I : SumInput) (d : ℕ) : ℝ :=
  if I.A = [] ∨ I.B = [] then (I.A.length + I.B.length + I.C.length + 1 : ℕ)
  else
    let t := (r - 1) * d / 2
    I.nhat ^ (2 * (1 - Real.logb (rho r) r)) *
      (P I.N d t r + I.N + I.C.length * (Q I.N d t r + 1))

end SelectedSubset3SUM.Integer.Supplement



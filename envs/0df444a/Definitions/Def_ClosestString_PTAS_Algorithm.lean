-- Prove2me | Definitions.Def_ClosestString_PTAS_Algorithm
-- name    : ClosestString_PTAS_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T16:18:16.088506+00:00
-- url     : https://prove2.me/theorems/5f8f8f21-1c1f-4ffb-bedb-0a3fcf14838b
-- title:
--   Figure 3 — Algorithm closestSubstring: admissible tuples, Q and P, the random multisets R, step 1(c)(i), problem (8), its solver, the candidates and the output (pp. 9–10)
-- statement:
--   This file defines Algorithm closestSubstring (Figure 3, p. 10) and its randomness.
--
--   The input is $n\ge1$ strings $s_1,\dots,s_n$ of length $m$, an integer $1\le L\le m$, an integer $r$ and a real $\varepsilon>0$.
--
--   1. **Admissible tuples** (step 1). A tuple of $r$ length-$L$ substrings $t_{i_1},\dots,t_{i_r}$, each given by its string index and start position, with repetitions allowed, but if two entries come from the same $s_i$ they are the same substring.
--   2. **$Q$ and $P$** (step 1(a)). $Q=\{j: t_{i_1}[j]=\dots=t_{i_r}[j]\}$ and $P=\{1,\dots,L\}\setminus Q$.
--   3. **The sample** (step 1(b)). $R$ is a multiset of $k=\lceil (4/\varepsilon^2)\ln(nm)\rceil$ positions drawn independently and uniformly from $P$, with replacement; one independent multiset $R_\tau$ for each admissible tuple $\tau$.
--   4. **Step 1(c)(i).** For each string $y$ of length $k$ and each $i$, $t'_i$ is a length-$L$ substring of $s_i$ minimizing
--   $$d(y,t'_i|_R)\cdot\frac{|P|}{|R|}+d(t_{i_1}|_Q,t'_i|_Q).$$
--   5. **Problem (8)** (p. 9). For strings $t'_1,\dots,t'_n$, the set $P$ and offsets $b_i=d(t'_i|_Q,t_{i_1}|_Q)$, its optimum is
--   $$d_0=\min_{x\in\Sigma^{|P|}}\ \max_i\big(d(t'_i|_P,x)+b_i\big).$$
--   A **solver** receives only $(t',P,b)$ and returns $x$. Step 1(c)(ii) asks for "the approximate solution within error $\varepsilon|P|$": $d(t'_i|_P,x)+b_i\le d_0+\varepsilon|P|$ for every $i$ (`IsApproxSolver`).
--   6. **Candidates** (steps 1(c)(iii) and 2). Each pair (tuple, $y$) gives $s'$ with $s'|_P=x$ and $s'|_Q=t_{i_1}|_Q$; each length-$L$ substring of $s_1$ is also a candidate.
--   7. **Output** (step 3). A candidate of minimum cost $c=\max_i\min_{t_i\sqsubseteq s_i}d(s',t_i)$.
--
--   The algorithm is a function of $s_1,\dots,s_n$, $L$, $r$, $\varepsilon$, the solver and the samples only; it never sees an optimal center, the optimal substrings or $d_{\mathrm{opt}}$.
--
--   **Formalization Note** Positions are 0-based and substrings are indexed by start position. $R$ is `Fin k → Fin L`; its law `sampleLaw` is the product of $k$ uniform laws on $P$, and when $P=\emptyset$ (the sample is never read: the weight $|P|/|R|$ is $0$ and (8) has no free position) it is the Dirac mass at the constant multiset $0$. The samples of different tuples are independent (`algLaw`, a product over tuples). The weight $|P|/|R|$ is a real number; for $k=0$ (which happens only when $nm=1$) Lean's $x/0=0$ makes it $0$. Ties in step 1(c)(i) go to the smallest start position (`bestStart`); the output is a minimizer of cost chosen by `Classical.choose` (every minimizer has the same cost). The solver returns a full length-$L$ string of which only the positions in $P$ are read; `opt8` takes the minimum over all length-$L$ strings, which equals the minimum over $\Sigma^{|P|}$. `Cand` is the candidate index set of step 3: (admissible tuples × $\Sigma^k$) plus the start positions of $s_1$.
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 9 (problem (8)), p. 10 (Figure 3: Algorithm closestSubstring)

import Mathlib
import Definitions.Def_ClosestString_PTAS_Basic

namespace ClosestString.PTAS

open MeasureTheory

/-!
# Algorithm closestSubstring (Figure 3, p. 10), problem (8) (p. 9) and its randomness

Li, Ma & Wang, *On the Closest String and Substring Problems*, arXiv:cs/0002012v1, pp. 9–10.

The algorithm is a function of the instance `S` (`n` strings of length `m`), the substring length
`L`, the constants `r` and `ε`, the solver of problem (8), and the random position multisets
`ω τ`, one for each admissible tuple `τ`. It never sees an optimal center, the optimal substrings or
`d_opt`.
-/

variable {A : Type*}

/-- A tuple of `r` length-`L` substrings `t_{i1}, …, t_{ir}` of the input strings, each given by
(string index, start position), is **admissible** (Figure 3 step 1) if two entries taken from the
same string `s_i` are the same substring: "allowing repeats, but if `t_{ij}` and `t_{ik}` are both
chosen from the same `s_i` then `t_{ij} = t_{ik}`". -/
def Admissible {n m L r : ℕ} (τ : Fin r → Fin n × Start m L) : Prop :=
  ∀ a b, (τ a).1 = (τ b).1 → (τ a).2 = (τ b).2

instance {n m L r : ℕ} : DecidablePred (@Admissible n m L r) := by
  intro τ; unfold Admissible; infer_instance

/-- The admissible tuples enumerated in step 1 of Figure 3. -/
abbrev AdmTuple (n m L r : ℕ) := {τ : Fin r → Fin n × Start m L // Admissible τ}

/-- The `a`-th substring `t_{ia}` of the tuple `τ`. -/
def tupleStr {n m L r : ℕ} (S : Fin n → Fin m → A) (τ : AdmTuple n m L r) (a : Fin r) :
    Fin L → A :=
  substr (S (τ.1 a).1) (τ.1 a).2

/-- The first substring `t_{i1}` of the tuple. -/
def firstStr {n m L r : ℕ} [NeZero r] (S : Fin n → Fin m → A) (τ : AdmTuple n m L r) :
    Fin L → A :=
  tupleStr S τ 0

/-- Step 1(a): `Q = {j | t_{i1}[j] = t_{i2}[j] = ⋯ = t_{ir}[j]}`. -/
def agreeQ {n m L r : ℕ} [DecidableEq A] (S : Fin n → Fin m → A) (τ : AdmTuple n m L r) :
    Finset (Fin L) :=
  Finset.univ.filter (fun j => ∀ a b, tupleStr S τ a j = tupleStr S τ b j)

/-- Step 1(a): `P = {1, …, L} − Q`. -/
def diffP {n m L r : ℕ} [DecidableEq A] (S : Fin n → Fin m → A) (τ : AdmTuple n m L r) :
    Finset (Fin L) :=
  (agreeQ S τ)ᶜ

/-- Step 1(b): the sample size `|R| = ⌈(4/ε²) log(nm)⌉`, with `log` the natural logarithm. -/
noncomputable def sampleSize (n m : ℕ) (ε : ℝ) : ℕ :=
  ⌈4 / ε ^ 2 * Real.log ((n : ℝ) * m)⌉₊

/-- Step 1(b): the law of the multiset `R` of `k` positions drawn independently and uniformly at
random from `P` (with replacement), as `R : Fin k → Fin L`. When `P = ∅` the sample is never read
(the weight `|P|/|R|` is `0` and problem (8) has no free position); it is then the constant
multiset at position `0`. -/
noncomputable def sampleLaw {L : ℕ} [NeZero L] (P : Finset (Fin L)) (k : ℕ) :
    Measure (Fin k → Fin L) :=
  if h : P.Nonempty then Measure.pi (fun _ => (PMF.uniformOfFinset P h).toMeasure)
  else Measure.dirac (fun _ => 0)

instance {L : ℕ} [NeZero L] (P : Finset (Fin L)) (k : ℕ) : IsProbabilityMeasure (sampleLaw P k) := by
  unfold sampleLaw; split <;> infer_instance

/-- `d(y, t|R)` for a string `y` of length `|R|` (step 1(c)): the number of entries `a` of the
multiset `R` with `y[a] ≠ t[R a]`. -/
def sampleMismatch {L k : ℕ} [DecidableEq A] (R : Fin k → Fin L) (y : Fin k → A)
    (v : Fin L → A) : ℕ :=
  (Finset.univ.filter (fun a => y a ≠ v (R a))).card

/-- Step 1(c)(i)'s objective for the substring of `s_i` starting at `p`:
`d(y, t′|R) × |P|/|R| + d(t_{i1}|Q, t′|Q)` (real-valued; `|R| = 0` gives weight `0`). -/
noncomputable def score {n m L r k : ℕ} [NeZero r] [DecidableEq A] (S : Fin n → Fin m → A)
    (τ : AdmTuple n m L r) (y : Fin k → A) (R : Fin k → Fin L) (i : Fin n) (p : Start m L) : ℝ :=
  (sampleMismatch R y (substr (S i) p) : ℝ) * ((diffP S τ).card / k)
    + (distOn (agreeQ S τ) (firstStr S τ) (substr (S i) p) : ℝ)

/-- With `1 ≤ L ≤ m` every string has a length-`L` substring (start position `0`). -/
theorem start_nonempty {m L : ℕ} [NeZero L] (hL : L ≤ m) :
    (Finset.univ : Finset (Start m L)).Nonempty :=
  ⟨⟨⟨0, by have := NeZero.pos L; omega⟩, by simpa using hL⟩, Finset.mem_univ _⟩

/-- Step 1(c)(i): the start position of `t′_i`, a minimizer of `score` over all length-`L`
substrings of `s_i`; ties are broken towards the smallest start position. -/
noncomputable def bestStart {n m L r k : ℕ} [NeZero r] [NeZero L] [DecidableEq A]
    (S : Fin n → Fin m → A) (hL : L ≤ m) (τ : AdmTuple n m L r) (y : Fin k → A)
    (R : Fin k → Fin L) (i : Fin n) : Start m L :=
  (Finset.univ.filter (fun p => score S τ y R i p =
      Finset.univ.inf' (start_nonempty hL) (score S τ y R i))).min' (by
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_inf' (start_nonempty hL) (score S τ y R i)
    exact ⟨p, by simp [hp]⟩)

/-- The optimum `d₀` of problem (8) (p. 9) for strings `t′ : Fin n → Fin L → A`, the position
set `P` and offsets `b i` (in the algorithm, `b i = d(t′_i|Q, t_{i1}|Q)`):
`d₀ = min_x max_i (d(t′_i|P, x) + b i)`, `x` ranging over all strings of length `L`, of which only
the positions in `P` are read (so this is the minimum over `x ∈ Σ^{|P|}`). -/
noncomputable def opt8 {n L : ℕ} [Fintype A] [DecidableEq A] [Nonempty A]
    (t' : Fin n → Fin L → A) (P : Finset (Fin L)) (b : Fin n → ℕ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun x : Fin L → A => Finset.univ.sup (fun i => distOn P (t' i) x + b i))

/-- A solver of problem (8): it receives only the instance of (8) — the strings `t′_i`, the position
set `P` and the offsets `b i` — and returns a string of length `L` whose positions in `P` are the
solution `x`. -/
abbrev Solver (A : Type*) (n L : ℕ) :=
  (Fin n → Fin L → A) → Finset (Fin L) → (Fin n → ℕ) → (Fin L → A)

/-- The guarantee step 1(c)(ii) asks of the solver: "the approximate solution within error
`ε|P|`" — on every instance of (8), the returned `x` satisfies every constraint of (8) with
`d = d₀ + ε|P|`. -/
def IsApproxSolver {n L : ℕ} [Fintype A] [DecidableEq A] [Nonempty A] (ε : ℝ)
    (solver : Solver A n L) : Prop :=
  ∀ (t' : Fin n → Fin L → A) (P : Finset (Fin L)) (b : Fin n → ℕ) (i : Fin n),
    (distOn P (t' i) (solver t' P b) : ℝ) + b i ≤ opt8 t' P b + ε * P.card

/-- Steps 1(c)(i)–(iii) for the tuple `τ`, the guess `y` of length `|R|` and the sample `R`: the
substrings `t′_i` of step (i), the solver's `x` for problem (8) with offsets
`d(t′_i|Q, t_{i1}|Q)` (step (ii)), and the candidate `s′` with `s′|P = x`, `s′|Q = t_{i1}|Q`
(step (iii)). -/
noncomputable def candidate1 {n m L r k : ℕ} [NeZero r] [NeZero L] [Fintype A] [DecidableEq A]
    [Nonempty A] (S : Fin n → Fin m → A) (hL : L ≤ m) (solver : Solver A n L)
    (τ : AdmTuple n m L r) (y : Fin k → A) (R : Fin k → Fin L) : Fin L → A :=
  let t' : Fin n → Fin L → A := fun i => substr (S i) (bestStart S hL τ y R i)
  let x := solver t' (diffP S τ) (fun i => distOn (agreeQ S τ) (t' i) (firstStr S τ))
  splice (diffP S τ) x (firstStr S τ)

/-- The candidate index set of step 3: one step-1 candidate for every admissible tuple and every
string `y` of length `k = |R|`, and one step-2 candidate for every length-`L` substring of `s_1`. -/
abbrev Cand (A : Type*) (n m L r k : ℕ) := (AdmTuple n m L r × (Fin k → A)) ⊕ Start m L

/-- The random input of the algorithm: one position multiset `R_τ : Fin k → Fin L` per admissible
tuple `τ`. -/
abbrev Sample (n m L r k : ℕ) := AdmTuple n m L r → Fin k → Fin L

/-- The center string proposed by each candidate. -/
noncomputable def candStr {n m L r : ℕ} [NeZero n] [NeZero r] [NeZero L] [Fintype A]
    [DecidableEq A] [Nonempty A] (S : Fin n → Fin m → A) (hL : L ≤ m) (ε : ℝ)
    (solver : Solver A n L) (ω : Sample n m L r (sampleSize n m ε)) :
    Cand A n m L r (sampleSize n m ε) → Fin L → A
  | Sum.inl (τ, y) => candidate1 S hL solver τ y (ω τ)
  | Sum.inr p => substr (S 0) p

theorem cand_nonempty {n m L r k : ℕ} [NeZero L] [Fintype A] [DecidableEq A] (hL : L ≤ m) :
    (Finset.univ : Finset (Cand A n m L r k)).Nonempty :=
  ⟨Sum.inr ⟨⟨0, by have := NeZero.pos L; omega⟩, by simpa using hL⟩, Finset.mem_univ _⟩

/-- **Algorithm closestSubstring** (Figure 3, p. 10): its output for the random samples `ω`, a
candidate of minimum cost `c = max_i min_{t_i ⊑ s_i} d(s′, t_i)` among the candidates of step 1
(every admissible tuple, every `y ∈ Σ^{|R|}`) and of step 2 (every length-`L` substring of `s_1`). -/
noncomputable def closestSubstring {n m L : ℕ} [NeZero n] [NeZero L] [Fintype A] [DecidableEq A]
    [Nonempty A] (S : Fin n → Fin m → A) (hL : L ≤ m) (r : ℕ) [NeZero r] (ε : ℝ)
    (solver : Solver A n L) (ω : Sample n m L r (sampleSize n m ε)) : Fin L → A :=
  candStr S hL ε solver ω
    (Finset.univ.exists_min_image (fun c => cost S (candStr S hL ε solver ω c))
      (cand_nonempty hL)).choose

/-- The law of the algorithm's randomness: the multisets `R_τ` are independent across tuples `τ`,
and `R_τ` has `sampleSize n m ε` independent uniform entries on `P_τ` (`sampleLaw`). -/
noncomputable def algLaw {n m L : ℕ} [NeZero L] [DecidableEq A] (S : Fin n → Fin m → A) (r : ℕ)
    (ε : ℝ) : Measure (Sample n m L r (sampleSize n m ε)) :=
  Measure.pi (fun τ => sampleLaw (diffP S τ) (sampleSize n m ε))

end ClosestString.PTAS



-- Prove2me | Definitions.Def_SerialBatchTardy_Construction
-- name    : SerialBatchTardy_Construction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:55.940839+00:00
-- url     : https://prove2.me/theorems/5fed02bb-cac9-47c2-aa39-92eaf311d806
-- title:
--   The reduction from k-Sum and the time reversal
-- statement:
--   Let $x_1,\dots,x_n$ be positive integers, $t$ a target, $k$ the parameter, $X=\sum_ix_i$, $S=\prod_ix_i$, and let $\alpha_{i,h}$ be the base-$n$ digits of $x_i$. For a list $L$ of leftover processing times, the **constructed instance** has setup time $\Delta=t$ and the jobs
--
--   1. for each entry $e$ of $L$, a **leftover job** with processing time $e$, weight $S\cdot k(X+n)$, release date $0$ and due date $3kt$;
--   2. for each $\ell\in\{0,\dots,k-1\}$, each $i$ and each $h$, $\alpha_{i,h}$ **normal jobs** with processing time $n^h$, weight $n^h(S+S/x_i)$, release date $3\ell t$ and due date $3\ell t+t+x_i$; these form the set $J_{x_i,\ell}$.
--
--   The **bound** is $S\cdot(kX-t+(n-1)k)$. For a schedule, $E_\ell$ is the set of early normal jobs of type $\ell$, and $p(E)$, $w(E)$ are total processing time and weight.
--
--   The **leftover list** $L(n,k,t)$: let $D$ be largest with $2n^D\le t$ and $Y=(k-1)t-k(n^D-1)$; it has $k(n-1)+\beta_h$ copies of $n^h$ for each $h<D$, where $\beta_h$ is the $h$-th base-$n$ digit of $Y$, and $\lfloor Y/n^D\rfloor$ copies of $n^D$.
--
--   The **reversed instance** of $I$ has the same setup time and, for every job, the same $p_j,w_j$, release date $-d_j$ and due date $-r_j$.
--
--   **Formalization Note** Weights and bound are those of the paper multiplied by $S$, which makes them integral. Gadget indices start at $0$. The paper uses $(k-1)t$ unit leftover jobs, the list $L$ = $(k-1)t$ ones; the leftover list $L(n,k,t)$ has the same total with $O(kn\log t)$ entries.
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), §4 "The construction", pp.550–551 (PDF pp.6–7); Lemma 12 proof, p.553 (PDF p.9)

import Definitions.Def_SerialBatchTardy_Model

set_option autoImplicit false

namespace SerialBatchTardy

/-! The reduction from k-Sum of Hermelin, Mnich & Omlor, *Serial batching to minimize the
weighted number of tardy jobs*, J. Scheduling 27 (2024), §4 "The construction", pp.550–551
(PDF pp.6–7), for an input list `xs = (x_1, …, x_n)`, a target `t`, the parameter `k` and a list
`L` of leftover processing times. Throughout, `n = xs.length`, `X = ∑ x_i`, `S = ∏ x_i`.

**Formalization Note.** Gadget indices `ℓ` run over `0, …, k-1` (the paper's `1, …, k`), so the
paper's release date `(ℓ-1)3t` is `ℓ * (3 * t)`. All weights are multiplied by `S = ∏ x_i`, as the
paper does to make them integral (p.551: "one can make them integral by multiplying them with
∏ x_i"), so the paper's `n^h + n^h/x_i` is `n^h * (S + S / x_i)` (exact division) and its bound
`kX − t + (n−1)k` becomes `S·(kX − t + (n−1)k)`. The base-`n` digits `α_{i,h}` of `x_i` are
`Nat.digits n x_i`, with `α_{i,h} = 0` beyond the last digit. The leftover jobs have the processing
times listed in `L`; the paper's `(k−1)t` unit jobs are `L = List.replicate ((k-1)*t) 1`. -/

/-- The label of a job of the constructed instance: a leftover job of processing time `e`, or a
normal job of gadget `ℓ` (0-based), input integer `x` and digit position `h` (processing `n^h`). -/
inductive JobLabel where
  | leftover (e : ℕ)
  | normal (ℓ x h : ℕ)
  deriving DecidableEq, Repr

/-- `some ℓ` for a normal job of gadget `ℓ`, `none` for a leftover job. -/
def JobLabel.gadget? : JobLabel → Option ℕ
  | .leftover _ => none
  | .normal ℓ _ _ => some ℓ

/-- `some x` for a normal job built from the input integer `x`, `none` for a leftover job. -/
def JobLabel.value? : JobLabel → Option ℕ
  | .leftover _ => none
  | .normal _ x _ => some x

/-- The job with a given label (p.551, both bullet lists, weights scaled by `S`):
* leftover, processing `e`: weight `S·k(X + n)`, release date `0`, due date `3kt`;
* normal `(ℓ, x, h)`: processing `n^h`, weight `n^h·(S + S/x)`, release date `ℓ·3t`, due date
  `ℓ·3t + t + x`. -/
def labelJob (xs : List ℕ) (t k : ℕ) : JobLabel → Job
  | .leftover e =>
      { p := e, w := xs.prod * (k * (xs.sum + xs.length)), r := 0, d := 3 * k * t }
  | .normal ℓ x h =>
      { p := xs.length ^ h, w := xs.length ^ h * (xs.prod + xs.prod / x),
        r := ((ℓ * (3 * t) : ℕ) : ℤ), d := ((ℓ * (3 * t) + t + x : ℕ) : ℤ) }

/-- The labels of the set `J_{x,ℓ}`: for each digit position `h`, `α_h` copies of `(ℓ, x, h)`,
where `α_h` is the `h`-th base-`n` digit of `x` (p.551: "This set consists of α_{i,h} many jobs,
for each h ∈ {0, …, ck}"). -/
def gadgetLabels (xs : List ℕ) (ℓ x : ℕ) : List JobLabel :=
  (List.range (Nat.digits xs.length x).length).flatMap fun h =>
    List.replicate ((Nat.digits xs.length x).getD h 0) (JobLabel.normal ℓ x h)

/-- All labels: the leftover jobs (one per entry of `L`), then for each `ℓ < k` and each input
integer `x`, the set `J_{x,ℓ}`. -/
def hardLabels (xs : List ℕ) (k : ℕ) (L : List ℕ) : List JobLabel :=
  L.map JobLabel.leftover ++
    (List.range k).flatMap fun ℓ => xs.flatMap fun x => gadgetLabels xs ℓ x

/-- The **constructed instance** (p.551): setup time `Δ = t` and the jobs of `hardLabels`. -/
def hardInstance (xs : List ℕ) (t k : ℕ) (L : List ℕ) : Instance where
  setup := t
  jobs := (hardLabels xs k L).map (labelJob xs t k)

/-- The **bound** `kX − t + (n − 1)k`, scaled by `S` (p.551: "We set the bound on the total weight
of tardy jobs to kX − t + (n − 1)k"), as an integer: `S·(k(X + n) − (t + k))`. -/
def hardBound (xs : List ℕ) (t k : ℕ) : ℤ :=
  (xs.prod : ℤ) * ((k : ℤ) * ((xs.sum : ℤ) + xs.length) - ((t : ℤ) + k))

/-- The label of job `j` of the constructed instance. -/
def labelOf (xs : List ℕ) (t k : ℕ) (L : List ℕ) (j : Fin (hardInstance xs t k L).jobs.length) :
    JobLabel :=
  (hardLabels xs k L).get (Fin.cast (by simp [hardInstance]) j)

/-- The set `J_{x,ℓ}` inside the constructed instance: the jobs labelled `(ℓ, x, ·)`. -/
def gadgetSet (xs : List ℕ) (t k : ℕ) (L : List ℕ) (ℓ x : ℕ) :
    Finset (Fin (hardInstance xs t k L).jobs.length) :=
  Finset.univ.filter fun j =>
    (labelOf xs t k L j).gadget? = some ℓ ∧ (labelOf xs t k L j).value? = some x

/-- The paper's `E_ℓ` (p.551): the early (not tardy) normal jobs of type `ℓ` in the schedule `σ`. -/
def earlyType {xs : List ℕ} {t k : ℕ} {L : List ℕ} (σ : Schedule (hardInstance xs t k L))
    (ℓ : ℕ) : Finset (Fin (hardInstance xs t k L).jobs.length) :=
  Finset.univ.filter fun j => (labelOf xs t k L j).gadget? = some ℓ ∧ ¬ σ.IsTardy j

/-- `p(E) = ∑_{j ∈ E} p_j`. -/
def pSum {I : Instance} (E : Finset (Fin I.jobs.length)) : ℕ := ∑ j ∈ E, (I.job j).p

/-- `w(E) = ∑_{j ∈ E} w_j`. -/
def wSum {I : Instance} (E : Finset (Fin I.jobs.length)) : ℕ := ∑ j ∈ E, (I.job j).w

/-- The **leftover list** that replaces the paper's `(k − 1)t` unit leftover jobs. Let `D` be
largest with `2·n^D ≤ t` (that is, `D = ⌊log_n ⌊t/2⌋⌋`) and `Y = (k − 1)t − k(n^D − 1)`. The list
has, for each `h < D`, `k(n − 1) + α_h` copies of `n^h`, where `α_h` is the `h`-th base-`n` digit
of `Y`, and `⌊Y / n^D⌋` copies of `n^D`. -/
def leftoverList (n k t : ℕ) : List ℕ :=
  let D := Nat.log n (t / 2)
  let Y := (k - 1) * t - k * (n ^ D - 1)
  (List.range D).flatMap (fun h => List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h))
    ++ List.replicate (Y / n ^ D) (n ^ D)

/-- **Time reversal** (Lemma 12, p.553, PDF p.9): the same setup time, and each job with the same
processing time and weight, release date `−d_j` and due date `−r_j`. -/
def reverseInstance (I : Instance) : Instance where
  setup := I.setup
  jobs := I.jobs.map fun j => { p := j.p, w := j.w, r := -j.d, d := -j.r }

end SerialBatchTardy



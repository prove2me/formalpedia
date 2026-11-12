-- Prove2me | Definitions.Def_RelatedSchedFPTAS796_Main_Problems
-- name    : RelatedSchedFPTAS796_Main_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:08.644351+00:00
-- url     : https://prove2.me/theorems/f420f20d-7aa9-401d-9ab4-a76a546eb423
-- title:
--   The randomized FPTAS for $Qm\|C_{\max}$ and the complete- and partial-profile problems on the word RAM
-- statement:
--   **Randomized FPTAS (p.8, Theorem 1.1).** For a fixed number $m$ of machines, a randomized FPTAS running in $\tilde O(n+(1/\varepsilon)^{m-1})$ time is one program $P$, with constants $b,C,c$ depending only on $m$, such that for every instance ($n\ge0$ jobs with positive rational sizes, $m$ positive rational speeds), every rational $\varepsilon,q\in(0,1)$ and every word width $w\ge b(\lfloor\log_2(n+M+2)\rfloor+1)$:
--
--   1. on every coin sequence the run halts within $C\,(n+(1/\varepsilon)^{m-1})\,(\log_2(n+2)\log_2(2/\varepsilon)\log_2(2/q))^c$ steps, and
--   2. with probability at least $1-q$ it halts within that bound with a schedule $\sigma$ in its output cells (cell $j-1$ holds the $0$-based machine of job $j$) satisfying $C_{\max}(\sigma)\le(1+\varepsilon)\,\mathrm{OPT}$.
--
--   The input words are $n$, the speeds, the sizes, $\varepsilon$ and $q$, each rational as numerator and denominator.
--
--   **Complete-profile problem (Definition 3.1).** At accuracy $\varepsilon=2^{-\ell}$, $\ell\ge1$, an instance $(J,t,q)$ consists of a multiset $J\subseteq[1/\varepsilon,2/\varepsilon)\cap\mathbb Z$ of $O(1/\varepsilon)$ jobs, $m$ positive rational targets $t_i=O(1/\varepsilon^2)$ and $q\in(0,1)$. An approximate solution is a set $\tilde S$ of size $\tilde O((1/\varepsilon)^{m-1})$ which, with probability at least $1-q$, approximates $\mathcal P(J,[0,t])$ with additive error $\tilde O(\varepsilon t)$. The problem is **approximately solved in $\tilde O(|J|+(1/\varepsilon)^{m-1})$ time** if for every constant $a$ (bounding $|J|\le a/\varepsilon$ and $t_i\le a/\varepsilon^2$) there are a program and constants $b,C,c$ such that on every such instance and every width $w\ge b(\lfloor\log_2(|J|+M+2)\rfloor+1)$ the run halts on every coin sequence within $C(|J|+(1/\varepsilon)^{m-1})\,\mathrm{polylog}$ steps with at most $C(1/\varepsilon)^{m-1}\mathrm{polylog}$ output vectors, and with probability at least $1-q$ its output approximates $\mathcal P(J,[0,t])$ with additive error $C\varepsilon t_i\,\mathrm{polylog}$ in coordinate $i$, where $\mathrm{polylog}=(\log_2(|J|+2)\log_2(2/\varepsilon)\log_2(2/q))^c$.
--
--   **Partial-profile problem (Definition 3.3).** An instance $(J,\kappa,q)$ has dimension $d\ge1$, a multiset $J\subseteq[1/\varepsilon,2/\varepsilon)\cap\mathbb Z$ of $O(1/\varepsilon)$ jobs with $\Sigma(J)\ge\frac{d+1}{d}\sum_i\kappa_i/\varepsilon$, rational parameters $1\le\kappa_1\le\dots\le\kappa_d=O(1/\varepsilon)$ and $q\in(0,1)$. Approximately solving it in $\tilde O(|J|+(1/\varepsilon)^d)$ time is defined as above, with output size $\tilde O((1/\varepsilon)^d)$ and the requirement that the output approximates
--   $$\mathcal S\Big(J,\Big[\frac{\kappa}{\varepsilon},\frac{(2d+1)\kappa}{2d\varepsilon}\Big)\Big)$$
--   with additive error $C\kappa_i\,\mathrm{polylog}$.
--
--   The definition also fixes the input encodings of the sumset lemmas (a set of points of $[N]^d$ as a duplicate-free list, $d$ words per point) and of Lemma 5.3 (jobs, $\kappa$, a $0/1$ word per job for $J'$, then the vectors of $S'$).
--
--   These predicates are the two sides of Lemmas 3.2, 3.4 and 5.9, and the goal is $\mathrm{RandomizedFPTAS}(m)$ for every $m\ge1$.
--
--   **Formalization Note** The admissibility constants "$O(1/\varepsilon)$ jobs, $t_i=O(1/\varepsilon^2)$, $\kappa_d=O(1/\varepsilon)$" are read as: for every constant $a$, with the program and its constants allowed to depend on $a$ (and on $m$ or $d$). The accuracy of the profile problems is given as the word $\ell$ with $\varepsilon=2^{-\ell}$, the paper's convention for §§3–5. The output size bound is required on every run.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, §2.2 p.8 lines 285–287; Theorem 1.1 p.3; Definition 3.1 p.9; Definition 3.3 pp.9–10; §2.1 p.7 lines 268–272

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-!
# The randomized FPTAS for `Qm∥Cmax`, the complete-profile and the partial-profile problems

Chen, Hu, Lian, Mao, Zhang, *Faster Approximation Schemes for Scheduling on Related Machines*,
STOC 2027 submission #796 (October 2026): §2.2 p.8 lines 285–287 ("An FPTAS returns a feasible
schedule whose value is at most 1 + ε times the minimum, in time polynomial in the input length and
1/ε. A randomized FPTAS has this guarantee with probability at least 1 − q and runs in time
polynomial also in log(1/q)."), Theorem 1.1 p.3 (time `Õ(n + (1/ε)^{m−1})`, `Õ` suppressing factors
polynomial in `log(n + 2)` and `log(2/ε)`, constants depending on `m`), Definition 3.1 p.9 (the
complete-profile problem), Definition 3.3 pp.9–10 (the partial-profile problem), §2.1 p.7 (`Õ` also
suppresses `log(2/q)`; in §§3–5, `1/ε` is a power of two).

**Formalization Note.**
* **FPTAS input** (`fptasInput`): `n`, then `s_1.num, s_1.den, …, s_m.num, s_m.den`, then
  `p_1.num, p_1.den, …, p_n.num, p_n.den`, then `ε.num, ε.den`, then `q.num, q.den`. The number `m`
  of machines is not an input: the program is chosen for each `m`. **Output:** cells `0, …, n − 1`
  hold `σ(1), …, σ(n)` as `0`-based machine indices.
* **`Õ` made explicit.** `Õ(X)` is `C · X · (log₂(n+2)·log₂(2/ε)·log₂(2/q))^c` with `C, c ∈ ℕ`
  chosen with the program, before the instance, `ε`, `q` and the width (`n = |J|` in the profile
  problems).
* **Admissibility** (Definitions 3.1, 3.3: "`O(1/ε)` jobs", "`t_i = O(1/ε²)`", "`κ_d = O(1/ε)`"):
  for every constant `a` the statement covers all instances with `|J| ≤ a/ε`, `t_i ≤ a/ε²`,
  `κ_d ≤ a/ε`; the program and its constants may depend on `a`.
* **Accuracy.** In the profile problems `ε = 2^{−ℓ}`, `ℓ ≥ 1` (the paper's convention for §§3–5),
  given as the word `ℓ`. Jobs are a list of integers in `[1/ε, 2/ε)`; targets, `κ` and `q` are
  rationals.
* **Profile-problem input/output.** Complete: `ℓ, |J|, J, t (num, den per coordinate), q.num, q.den`;
  partial: `ℓ, |J|, J, κ (num, den per coordinate), q.num, q.den`. The output set is written as in
  `outRatSet` (count, then the vectors as `num, den` words). The size bound is required on every
  run; the approximation with probability at least `1 − q`.
-/

open MatroidSensOracle MeasureTheory

/-! ### The randomized FPTAS -/

/-- The input words of an instance of `Qm∥Cmax` with accuracy `ε` and failure parameter `q`. -/
def fptasInput {n m : ℕ} (p : Fin n → ℚ) (s : Fin m → ℚ) (ε q : ℚ) : List ℤ :=
  (n : ℤ) :: (ratVecWords s ++ ratVecWords p ++ ratWords ε ++ ratWords q)

/-- The time bound `C·(n + (1/ε)^{m−1})·(log₂(n+2)·log₂(2/ε)·log₂(2/q))^c`. -/
noncomputable def fptasTime (C c n m : ℕ) (ε q : ℚ) : ℝ :=
  C * ((n : ℝ) + (1 / (ε : ℝ)) ^ (m - 1)) * polylog3 n ε q c

/-- The final memory holds the schedule `σ`: cell `j` holds the `0`-based index of `σ j`. -/
def OutputsSchedule {w n m : ℕ} (mem : ℤ → BitVec w) (σ : Fin n → Fin m) : Prop :=
  ∀ j : Fin n, (mem (j : ℤ)).toNat = (σ j : ℕ)

/-- **A randomized FPTAS for `Qm∥Cmax` in `Õ(n + (1/ε)^{m−1})` time** (p.8 and Theorem 1.1):
one program `P` with constants `b, C, c` (depending on `m` only) such that, for every instance
(`n ≥ 0` jobs with positive rational sizes, `m` machines with positive rational speeds), every
rational `ε, q ∈ (0, 1)` and every word width `w ≥ b·(⌊log₂(n + M + 2)⌋ + 1)`:
on every coin sequence the run halts within `C(n + (1/ε)^{m−1})(log₂(n+2)log₂(2/ε)log₂(2/q))^c`
steps, and with probability at least `1 − q` it halts within that bound with a schedule `σ` in its
output cells with `C_max(σ) ≤ (1 + ε)·OPT`. -/
def RandomizedFPTAS (m : ℕ) : Prop :=
  ∃ (P : List Instr) (b C c : ℕ), ∀ (n : ℕ) (p : Fin n → ℚ) (s : Fin m → ℚ) (ε q : ℚ),
    (∀ j, 0 < p j) → (∀ i, 0 < s i) → 0 < ε → ε < 1 → 0 < q → q < 1 →
    ∀ w : ℕ, widthMin b n (maxWord (fptasInput p s ε q)) ≤ w →
      HaltsWithin P w (fptasInput p s ε q) (fptasTime C c n m ε q) ∧
      FailsAtMost P w (fptasInput p s ε q) (fptasTime C c n m ε q)
        (fun mem => ∃ σ : Fin n → Fin m, OutputsSchedule mem σ ∧ IsNearOptimal p s ε σ) q

/-! ### Jobs as lists of integers -/

/-- The jobs of a list `J` of sizes, as a family over its occurrences. -/
def jobsOf (J : List ℕ) : Fin J.length → ℝ := fun j => ((J.get j : ℕ) : ℝ)

/-- Every job of `J` is an integer in `[1/ε, 2/ε) = [2^ℓ, 2^{ℓ+1})`. -/
def JobsInRange (ℓ : ℕ) (J : List ℕ) : Prop := ∀ x ∈ J, 2 ^ ℓ ≤ x ∧ x < 2 ^ (ℓ + 1)

/-! ### Definition 3.1: the complete-profile problem -/

/-- The input words of a complete-profile instance `(J, t, q)` at accuracy `ε = 2^{−ℓ}`. -/
def completeInput {m : ℕ} (ℓ : ℕ) (J : List ℕ) (t : Fin m → ℚ) (q : ℚ) : List ℤ :=
  (ℓ : ℤ) :: (J.length : ℤ) :: (J.map (fun x => (x : ℤ)) ++ ratVecWords t ++ ratWords q)

/-- An `a`-admissible complete-profile instance (Definition 3.1): `ε = 2^{−ℓ}` with `ℓ ≥ 1`, a
multiset `J ⊆ [1/ε, 2/ε) ∩ ℤ` of at most `a/ε` jobs, `m` positive targets `t_i ≤ a/ε²`, and
`q ∈ (0, 1)`. -/
def IsAdmissibleComplete {m : ℕ} (a ℓ : ℕ) (J : List ℕ) (t : Fin m → ℚ) (q : ℚ) : Prop :=
  1 ≤ ℓ ∧ JobsInRange ℓ J ∧ J.length ≤ a * 2 ^ ℓ ∧ (∀ i, 0 < t i ∧ t i ≤ a * 4 ^ ℓ) ∧
    0 < q ∧ q < 1

/-- **Definition 3.1, solved in `Õ(|J| + (1/ε)^{m−1})` time.** For every admissibility constant `a`
there are a program and constants `b, C, c` such that on every `a`-admissible instance `(J, t, q)`
on `m` machines and at every width `w ≥ b(⌊log₂(|J| + M + 2)⌋ + 1)`: on every coin sequence the run
halts within `C(|J| + (1/ε)^{m−1})·polylog` steps with an output of at most
`C(1/ε)^{m−1}·polylog` vectors, and with probability at least `1 − q` its output set `S̃`
approximates `𝒫(J, [0, t])` with additive error `C·ε·t·polylog` (Definition 2.1), where
`polylog = (log₂(|J|+2)·log₂(2/ε)·log₂(2/q))^c`. -/
def CompleteProfileSolvable (m : ℕ) : Prop :=
  ∀ a : ℕ, ∃ (P : List Instr) (b C c : ℕ), ∀ (ℓ : ℕ) (J : List ℕ) (t : Fin m → ℚ) (q : ℚ),
    IsAdmissibleComplete a ℓ J t q →
    ∀ w : ℕ, widthMin b J.length (maxWord (completeInput ℓ J t q)) ≤ w →
      (∀ ω : Coins, ∃ mem, runFor P w (completeInput ℓ J t q)
          (C * ((J.length : ℝ) + (1 / epsOf ℓ) ^ (m - 1)) * polylog3 J.length (epsOf ℓ) q c) ω
            = some mem ∧
          (outCount mem : ℝ) ≤ C * (1 / epsOf ℓ) ^ (m - 1) * polylog3 J.length (epsOf ℓ) q c) ∧
      FailsAtMost P w (completeInput ℓ J t q)
        (C * ((J.length : ℝ) + (1 / epsOf ℓ) ^ (m - 1)) * polylog3 J.length (epsOf ℓ) q c)
        (fun mem => ApproxAdd (workProfiles m (jobsOf J)) (outRatSet m mem)
          (Set.Icc 0 (fun i => (t i : ℝ)))
          (fun i => C * epsOf ℓ * (t i : ℝ) * polylog3 J.length (epsOf ℓ) q c)) q

/-! ### Definition 3.3: the partial-profile problem -/

/-- The input words of a partial-profile instance `(J, κ, q)` at accuracy `ε = 2^{−ℓ}`. -/
def partialInput {d : ℕ} (ℓ : ℕ) (J : List ℕ) (κ : Fin d → ℚ) (q : ℚ) : List ℤ :=
  (ℓ : ℤ) :: (J.length : ℤ) :: (J.map (fun x => (x : ℤ)) ++ ratVecWords κ ++ ratWords q)

/-- The parameter conditions of §4.2–§5 on `κ` (Definition 3.3): `1 ≤ κ_1 ≤ ⋯ ≤ κ_d ≤ a/ε`. -/
def KappaAdmissible {d : ℕ} (a ℓ : ℕ) (κ : Fin d → ℚ) : Prop :=
  Monotone κ ∧ ∀ i, 1 ≤ κ i ∧ κ i ≤ a * 2 ^ ℓ

/-- An `a`-admissible partial-profile instance (Definition 3.3): dimension `d ≥ 1`, `ε = 2^{−ℓ}`
with `ℓ ≥ 1`, a multiset `J ⊆ [1/ε, 2/ε) ∩ ℤ` of at most `a/ε` jobs with
`Σ(J) ≥ ((d+1)/d)·∑_i κ_i/ε`, parameters `1 ≤ κ_1 ≤ ⋯ ≤ κ_d ≤ a/ε`, and `q ∈ (0, 1)`. -/
def IsAdmissiblePartial {d : ℕ} (a ℓ : ℕ) (J : List ℕ) (κ : Fin d → ℚ) (q : ℚ) : Prop :=
  1 ≤ d ∧ 1 ≤ ℓ ∧ JobsInRange ℓ J ∧ J.length ≤ a * 2 ^ ℓ ∧
    ((d : ℚ) + 1) / d * ((∑ i, κ i) * 2 ^ ℓ) ≤ (J.sum : ℚ) ∧ KappaAdmissible a ℓ κ ∧
    0 < q ∧ q < 1

/-- The target box `[κ/ε, (2d+1)κ/(2dε))` of the partial-profile problem. -/
noncomputable def partialBox {d : ℕ} (ℓ : ℕ) (κ : Fin d → ℚ) : Set (Fin d → ℝ) :=
  boxIco (fun i => (κ i : ℝ) / epsOf ℓ)
    (fun i => (2 * (d : ℝ) + 1) * (κ i : ℝ) / (2 * (d : ℝ) * epsOf ℓ))

/-- **Definition 3.3, solved in `Õ(|J| + (1/ε)^d)` time.** For every admissibility constant `a`
there are a program and constants `b, C, c` such that on every `a`-admissible partial-profile
instance `(J, κ, q)` of dimension `d` and at every width `w ≥ b(⌊log₂(|J| + M + 2)⌋ + 1)`: on
every coin sequence the run halts within `C(|J| + (1/ε)^d)·polylog` steps with an output of at most
`C(1/ε)^d·polylog` vectors, and with probability at least `1 − q` its output set approximates
`𝒮(J, [κ/ε, (2d+1)κ/(2dε)))` with additive error `C·κ·polylog`. -/
def PartialProfileSolvable (d : ℕ) : Prop :=
  ∀ a : ℕ, ∃ (P : List Instr) (b C c : ℕ), ∀ (ℓ : ℕ) (J : List ℕ) (κ : Fin d → ℚ) (q : ℚ),
    IsAdmissiblePartial a ℓ J κ q →
    ∀ w : ℕ, widthMin b J.length (maxWord (partialInput ℓ J κ q)) ≤ w →
      (∀ ω : Coins, ∃ mem, runFor P w (partialInput ℓ J κ q)
          (C * ((J.length : ℝ) + (1 / epsOf ℓ) ^ d) * polylog3 J.length (epsOf ℓ) q c) ω
            = some mem ∧
          (outCount mem : ℝ) ≤ C * (1 / epsOf ℓ) ^ d * polylog3 J.length (epsOf ℓ) q c) ∧
      FailsAtMost P w (partialInput ℓ J κ q)
        (C * ((J.length : ℝ) + (1 / epsOf ℓ) ^ d) * polylog3 J.length (epsOf ℓ) q c)
        (fun mem => ApproxAdd (partialProfiles d (jobsOf J)) (outRatSet d mem) (partialBox ℓ κ)
          (fun i => C * (κ i : ℝ) * polylog3 J.length (epsOf ℓ) q c)) q

/-! ### Sumset inputs (Lemmas 2.3, 2.4) and dense-certificate inputs (Lemma 5.3) -/

/-- The input words of a sumset computation in `[N]^d`: `N`, `|A|`, `|B|`, then the points of
`A` (`d` words each, in the order of the list `lA`), then those of `B`. -/
def sumsetInput {d : ℕ} (N : ℕ) (lA lB : List (Fin d → ℕ)) : List ℤ :=
  (N : ℤ) :: (lA.length : ℤ) :: (lB.length : ℤ) ::
    (lA.flatMap natVecWords ++ lB.flatMap natVecWords)

/-- `A ⊆ [N]^d`, where `[N] = {0, …, N}`. -/
def InCube {d : ℕ} (N : ℕ) (A : Finset (Fin d → ℕ)) : Prop := ∀ x ∈ A, ∀ i, x i ≤ N

/-- The list `l` lists the finite set `A` without repetition (in any order). -/
def ListsSet {α : Type*} [DecidableEq α] (l : List α) (A : Finset α) : Prop :=
  l.Nodup ∧ l.toFinset = A

/-- The input words of Lemma 5.3: `ℓ`, `|J|`, the jobs `J`, `κ` (`num, den` per coordinate), then
one word per job occurrence, `1` if it belongs to `J'` and `0` otherwise, then `|S'|`, then the
vectors of `S'` (`num, den` per coordinate, in the order of the list). -/
def certInput {d : ℕ} (ℓ : ℕ) (J : List ℕ) (κ : Fin d → ℚ) (J' : Finset (Fin J.length))
    (S' : List (Fin d → ℚ)) : List ℤ :=
  (ℓ : ℤ) :: (J.length : ℤ) :: (J.map (fun x => (x : ℤ)) ++ ratVecWords κ ++
    (List.finRange J.length).map (fun j => if j ∈ J' then (1 : ℤ) else 0) ++
    (S'.length : ℤ) :: S'.flatMap ratVecWords)

/-- A rational vector viewed in `ℝ^d`. -/
def ratToReal {d : ℕ} (x : Fin d → ℚ) : Fin d → ℝ := fun i => (x i : ℝ)

end RelatedSchedFPTAS796.Main



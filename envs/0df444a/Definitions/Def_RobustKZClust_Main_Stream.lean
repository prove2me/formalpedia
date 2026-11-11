-- Prove2me | Definitions.Def_RobustKZClust_Main_Stream
-- name    : RobustKZClust_Main_Stream
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:11:37.620458+00:00
-- url     : https://prove2.me/theorems/71d360bc-84e2-4c16-8049-1cace2767914
-- title:
--   Dynamic geometric streams on [∆]^d, streaming algorithms with deterministic queries, adaptive adversaries and their runs
-- statement:
--   A **dynamic geometric stream** on $[\Delta]^d$ is a sequence of updates $\sigma e_x$: insert ($\sigma=+1$) or delete ($\sigma=-1$) one copy of a point $x\in\mathbb Z^d$. After updates $u_1,\dots,u_t$ the dataset is the frequency vector $\mu_t=\sum_{i\le t}\sigma_i e_{x_i}$.
--
--   A **streaming algorithm** consists of three programs of the machine: an initialization program, an update program, and a **query** program. The initialization call runs on the all-zero memory; the update call for $\sigma e_x$ receives the integer words $\sigma,x_1,\dots,x_d$; a query receives a list $c_0,\dots,c_{q-1}$ of centers, as the integer word $q$ and the real numbers $c_0(1),\dots,c_0(d),c_1(1),\dots$, and answers in real register $0$. The query call runs on the blank tape. Its answers on the memory $M_t$ after update $t$ define the **reported function** $\widehat{\mathrm{cost}}_t$ on center lists. A query list is **valid** if it consists of $1\le q\le k$ distinct points.
--
--   An **adaptive adversary** is a function that chooses the next update from the history: all previous updates, each paired with the whole function reported after it. It never sees the memory or the coins. It is **valid** on $[\Delta]^d$ if, on every history, its point lies in $[\Delta]^d$ and a deletion removes a point whose current frequency is positive.
--
--   The **run** of the algorithm against an adversary on coins $\omega=(\omega_0,\omega_1,\dots)$ is defined as follows. The initialization call uses tape $\omega_0$. Update $t+1$ is the adversary's choice on the current history; its call uses tape $\omega_{t+1}$, starts from $M_t$ and halts with $M_{t+1}$. The history is then extended by that update and the function reported from $M_{t+1}$.
--
--   This is the adaptive model of the paper (§1, §2): the update stream may depend on everything the algorithm has output so far.
--
--   **Formalization Note.** Adversaries are deterministic. A randomized adversary is a mixture of deterministic ones, so a guarantee for every deterministic adversary covers it. The reported functions are defined on all lists. Statements only constrain them on valid lists.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 1 (dynamic geometric streams, adaptive adversary), p. 13 §2, p. 28 Theorem 6.1 (µ_1, …, µ_m), p. 36 (updates σe_x)

import Mathlib
import Definitions.Def_RobustKZClust_Main_Cost
import Definitions.Def_RobustKZClust_Main_Machine

namespace RobustKZClust.Main

/-! Dynamic geometric streams of point insertions and deletions on `[∆]^d` (§1, p. 1; §6, p. 28),
streaming algorithms on the machine of `Def_RobustKZClust_Main_Machine` (an initialization call,
one update call per stream update, a deterministic query call reporting `ĉost_t`), adaptive
adversaries that see every reported function (§1, p. 1; §2, p. 13), and the run they generate. -/

/-- A stream update `σ e_x`: `ins = true` inserts one copy of the point `x ∈ ℤ^d`
(`σ = +1`), `ins = false` deletes one copy (`σ = −1`). -/
structure Update (d : ℕ) where
  ins : Bool
  pt : Fin d → ℤ

/-- The frequency vector after a list of updates, as a finitely supported weight vector on `ℝ^d`:
`µ = ∑ σ_i e_{x_i}`. -/
noncomputable def freqVec {d : ℕ} (us : List (Update d)) : Pt d →₀ ℝ :=
  (us.map fun u => Finsupp.single (gridPt u.pt) (if u.ins then (1 : ℝ) else -1)).sum

/-- A function reported after an update: it maps a list of centers to a real number. -/
abbrev Report (d : ℕ) := List (Pt d) → ℝ

/-- What the adversary has seen: the updates so far, each with the function reported after it. -/
abbrev History (d : ℕ) := List (Update d × Report d)

/-- A (deterministic) adaptive adversary: it chooses the next update from the previous updates
and all previously reported functions; it never sees the algorithm's memory or coins. -/
abbrev Adversary (d : ℕ) := History d → Update d

/-- A valid adversary on `[∆]^d`: on every history, the chosen point lies in `[∆]^d` and a deletion
removes a point whose current frequency is positive (so every frequency stays nonnegative). -/
def ValidAdversary {d : ℕ} (Δ : ℕ) (adv : Adversary d) : Prop :=
  ∀ h : History d,
    (∀ i, 1 ≤ (adv h).pt i ∧ (adv h).pt i ≤ (Δ : ℤ)) ∧
    ((adv h).ins = false → 0 < freqVec (h.map Prod.fst) (gridPt (adv h).pt))

/-- A streaming algorithm: the programs of the initialization, update and query calls. -/
structure StreamAlg where
  init : Program
  upd : Program
  qry : Program

/-- Input of the initialization call: empty. -/
def initInput : CallInput := ⟨[], []⟩

/-- Input of the update call for `σ e_x`: the integer words `σ, x_1, …, x_d`. -/
def updInput {d : ℕ} (u : Update d) : CallInput :=
  ⟨(if u.ins then (1 : ℤ) else -1) :: List.ofFn u.pt, []⟩

/-- Input of a query with the center list `c_0, …, c_{q−1}`: the integer word `q` and the reals
`c_0(0), …, c_0(d−1), c_1(0), …` (coordinate `j` of center `i` is real input `i·d + j`). -/
def queryInput {d : ℕ} (L : List (Pt d)) : CallInput :=
  ⟨[(L.length : ℤ)], L.flatMap fun p => List.ofFn fun i => p i⟩

/-- A valid query list: `1 ≤ q ≤ k` distinct centers. -/
def ValidQuery {d : ℕ} (k : ℕ) (L : List (Pt d)) : Prop :=
  L ≠ [] ∧ L.Nodup ∧ L.length ≤ k

/-- The function reported from the memory `M`: the query call (deterministic, run on the blank
tape) halts with its answer in real register `0`. -/
noncomputable def report {d : ℕ} (A : StreamAlg) (M : ℕ → ℤ) : Report d :=
  fun L => (callFinal A.qry blankTape (queryInput L) M).reg 0

/-- The run of `A` against `adv` on the coins `ω`: after `t` updates, the memory and the history.
The initialization call reads tape `ω 0`; update number `t + 1` reads tape `ω (t + 1)`. -/
noncomputable def runState {d : ℕ} (A : StreamAlg) (adv : Adversary d) (ω : ℕ → ℕ → Bool) :
    ℕ → (ℕ → ℤ) × History d
  | 0 => ((callFinal A.init (ω 0) initInput zeroMem).mem, [])
  | t + 1 =>
    let s := runState A adv ω t
    let u := adv s.2
    let M := (callFinal A.upd (ω (t + 1)) (updInput u) s.1).mem
    (M, s.2 ++ [(u, report A M)])

/-- The frequency vector `µ_t` after `t` updates of the run. -/
noncomputable def freqAt {d : ℕ} (A : StreamAlg) (adv : Adversary d) (ω : ℕ → ℕ → Bool)
    (t : ℕ) : Pt d →₀ ℝ :=
  freqVec ((runState A adv ω t).2.map Prod.fst)

end RobustKZClust.Main



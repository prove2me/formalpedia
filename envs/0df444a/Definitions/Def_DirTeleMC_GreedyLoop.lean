-- Prove2me | Definitions.Def_DirTeleMC_GreedyLoop
-- name    : DirTeleMC_GreedyLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:32:15.484883+00:00
-- url     : https://prove2.me/theorems/40b9d291-9563-4f27-8ed2-781c486f300c
-- title:
--   The recursive greedy procedure GREEDY (Algorithm 1) as a run relation
-- statement:
--   GREEDY$(\sigma, z, L, R)$ takes a node $\sigma$ of the unfolding of height $h \ge 1$, a demand $z \ge 1$, a state $L$ and a set $R$ of terminals still to be covered, and returns a list of structures rooted at $\sigma$. It keeps $L_{\mathrm{cur}}, R_{\mathrm{cur}}, z_{\mathrm{cur}}$ and, while $z_{\mathrm{cur}} > 0$:
--   1. for every child $\tau$ of $\sigma$ (every $w$ with $\mathrm{dist}(\lambda(\sigma), w) \le \theta$, including $w = \lambda(\sigma)$) it takes a path $P$ with at most $\theta$ arcs from $\lambda(\sigma)$ to $w$ minimizing $\Delta_{L_{\mathrm{cur}}}(P)$;
--   2. if $h = 1$, the node $\tau$ with the jump $P$ is a candidate; if $h \ge 2$, it calls GREEDY$(\tau, z_{\mathrm{cur}}, L_{\mathrm{cur}} + L_P, R_{\mathrm{cur}})$, which returns $C_1, \dots, C_q$, and for every $i \ge 1$ the node $\tau$ with the jump $P$ and $C_1, \dots, C_i$ below it is a candidate;
--   3. the count of a candidate is $\mathrm{cnt}(C) = \min\{|\mathrm{cov}(C) \cap R_{\mathrm{cur}}|, z_{\mathrm{cur}}\}$; if no candidate has positive count it returns its list;
--   4. otherwise it chooses a candidate with positive count minimizing $\Delta_{L_{\mathrm{cur}}}(C)/\mathrm{cnt}(C)$, appends it, and sets $L_{\mathrm{cur}} \leftarrow L_{\mathrm{cur}} + L_C$, $R_{\mathrm{cur}} \leftarrow R_{\mathrm{cur}} \setminus \mathrm{cov}(C)$, $z_{\mathrm{cur}} \leftarrow z_{\mathrm{cur}} - \mathrm{cnt}(C)$.
--
--   The relation contains every run: every minimizing path and every minimizing candidate may be chosen. The data of one iteration and the chosen candidate are also named separately, for Lemma B.5.
--
--   **Formalization Note** A node of the unfolding enters only through its label and its height.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Algorithm 1, p.23 (PDF p.24); §B.4 "The recursive greedy algorithm", pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_DirTeleMC_IsJumpArb
import Definitions.Def_DirTeleMC_Phi

namespace DirTeleMC

open JTree

variable {n : ℕ}

/-- The labels of the children in `U_{η,θ}` of a node labelled `u` (of height at least `1`): every `w` with
`dist(u, w) ≤ θ`, including `w = u` (§B.3, p.20: "dist(w_{i−1}, w_i) ≤ θ for all i (we allow
w_i = w_{i−1})"), listed in increasing order. -/
noncomputable def kids (adj : Fin n → Fin n → Bool) (θ : ℕ) (u : Fin n) : List (Fin n) := by
  classical
  exact (List.finRange n).filter fun w => HopReach adj θ u w

/-- `P` is a cheapest jump from `u` to `w` in the state `L` (Algorithm 1, line 6: "a path from λ(σ) to λ(τ)
with at most θ arcs that minimizes Δ_{L_cur}(P)"): a path with at most `θ` arcs from `u` to `w` whose increase
is at most that of every such path. -/
def IsCheapest (adj : Fin n → Fin n → Bool) (θ : ℕ) (Γ : ℝ) (L : Fin n → ℕ) (u w : Fin n)
    (P : List (Fin n)) : Prop :=
  IsJump adj θ u w P ∧ P.Nodup ∧
    ∀ P', IsJump adj θ u w P' → P'.Nodup → incr Γ L (pathLoads P) ≤ incr Γ L (pathLoads P')

/-- **The candidates of one iteration** of the while loop of Algorithm 1 at a node labelled `u` of height
`h`, given for every child label `w` the chosen jump `P w` and, when `h ≥ 2`, the list `out w` returned by
the recursive call at that child (Algorithm 1, lines 5–11): for `h = 1`, the node `w` with the jump `P w`;
for `h ≥ 2`, for every `i = 1, …, q` with `q = |out w|`, the node `w` with the jump `P w` and the first `i`
structures of `out w` below it. Each candidate is a structure rooted at the node labelled `u`. -/
def candsOf (u : Fin n) (h : ℕ) (ws : List (Fin n)) (P : Fin n → List (Fin n))
    (out : Fin n → List (JTree n)) : List (JTree n) :=
  ws.flatMap fun w =>
    if h = 1 then [node u [(P w, node w [])]]
    else (List.range (out w).length).map fun i => node u [(P w, join w ((out w).take (i + 1)))]

/-- The count `cnt(C) = min{|cov(C) ∩ R_cur|, z_cur}` of a candidate (Algorithm 1, line 14). -/
def cnt (h : ℕ) (R : Finset (Fin n)) (z : ℕ) (C : JTree n) : ℕ := min (R ∩ cov h C).card z

/-- **The while loop of GREEDY (Algorithm 1), as a run relation.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Algorithm 1, p.23, and §B.4 "The recursive greedy algorithm", pp.21–22.

`GreedyLoop adj θ Γ u h z L R out` says: the while loop of `GREEDY` at a node labelled `u` of height `h`,
entered with current state `L`, residual set `R` and residual demand `z`, can return the list `out`
(the structures chosen from now on, in order). The three constructors are the three ways an iteration ends:

* `demandMet`: `z_cur = 0`, the loop ends (line 3) and nothing more is chosen;
* `noCandidate`: `z_cur > 0`; for every child label `w` a cheapest jump `P w` is chosen (line 6) and, if
  `h ≥ 2`, the recursive call `GREEDY(τ, z_cur, L_cur + L_P, R_cur)` returns `out w` (line 10); no candidate
  has positive count, and the function returns (lines 14–16);
* `choose`: the same, but the candidate `C` has positive count and minimizes `Δ_{L_cur}(C)/cnt(C)` among the
  candidates with positive count (line 18); it is appended and the state is updated (line 19):
  `L_cur ← L_cur + L_C`, `R_cur ← R_cur \ cov(C)`, `z_cur ← z_cur − cnt(C)`.

**Formalization Note.** Every choice the page leaves open (the minimizing path of line 6 and the minimizing
candidate of line 18) is left open: the relation contains every run. A node of `U` enters only through its
label `u` and its height `h` (the children of a node and its candidates depend on nothing else). The
recursive calls are the runs `GreedyLoop w (h − 1) z_cur (L_cur + L_P) R_cur (out w)` started from their
initial state. The ratio is a real division; it is only compared for candidates with positive count. -/
inductive GreedyLoop (adj : Fin n → Fin n → Bool) (θ : ℕ) (Γ : ℝ) :
    Fin n → ℕ → ℕ → (Fin n → ℕ) → Finset (Fin n) → List (JTree n) → Prop
  | demandMet (u : Fin n) (h : ℕ) (L : Fin n → ℕ) (R : Finset (Fin n)) :
      GreedyLoop adj θ Γ u h 0 L R []
  | noCandidate (u : Fin n) (h z : ℕ) (L : Fin n → ℕ) (R : Finset (Fin n))
      (P : Fin n → List (Fin n)) (out : Fin n → List (JTree n)) (hz : 0 < z)
      (hP : ∀ w ∈ kids adj θ u, IsCheapest adj θ Γ L u w (P w))
      (hrec : 2 ≤ h → ∀ w ∈ kids adj θ u,
        GreedyLoop adj θ Γ w (h - 1) z (L + pathLoads (P w)) R (out w))
      (hnone : ∀ C ∈ candsOf u h (kids adj θ u) P out, cnt h R z C = 0) :
      GreedyLoop adj θ Γ u h z L R []
  | choose (u : Fin n) (h z : ℕ) (L : Fin n → ℕ) (R : Finset (Fin n))
      (P : Fin n → List (Fin n)) (out : Fin n → List (JTree n)) (C : JTree n) (rest : List (JTree n))
      (hz : 0 < z)
      (hP : ∀ w ∈ kids adj θ u, IsCheapest adj θ Γ L u w (P w))
      (hrec : 2 ≤ h → ∀ w ∈ kids adj θ u,
        GreedyLoop adj θ Γ w (h - 1) z (L + pathLoads (P w)) R (out w))
      (hC : C ∈ candsOf u h (kids adj θ u) P out) (hpos : 0 < cnt h R z C)
      (hmin : ∀ C' ∈ candsOf u h (kids adj θ u) P out, 0 < cnt h R z C' →
        incr Γ L C.loads / (cnt h R z C : ℝ) ≤ incr Γ L C'.loads / (cnt h R z C' : ℝ))
      (hrest : GreedyLoop adj θ Γ u h (z - cnt h R z C) (L + C.loads) (R \ cov h C) rest) :
      GreedyLoop adj θ Γ u h z L R (C :: rest)

/-- **A run of GREEDY (Algorithm 1)**: `GREEDY(σ, z, L, R)` at a node labelled `u` of height `h ≥ 1`, with
demand `z ≥ 1`, can return the list `out` (Algorithm 1, input: "σ: a node of U of height h ≥ 1; z ≥ 1: the
demand"). -/
def GreedyRun (adj : Fin n → Fin n → Bool) (θ : ℕ) (Γ : ℝ) (u : Fin n) (h z : ℕ) (L : Fin n → ℕ)
    (R : Finset (Fin n)) (out : List (JTree n)) : Prop :=
  1 ≤ h ∧ 1 ≤ z ∧ GreedyLoop adj θ Γ u h z L R out

/-- **The data of one iteration** of the while loop of Algorithm 1 at a node labelled `u` of height `h`, with
state `L`, residual set `R` and residual demand `z` (lines 5–13): the cheapest jumps `P w` for all child labels
`w` and, when `h ≥ 2`, the lists `out w` returned by the recursive calls. These are exactly the premises
`hP`, `hrec` of the constructors `noCandidate` and `choose` of `GreedyLoop`; the candidates are
`candsOf u h (kids adj θ u) P out`. -/
def IterationData (adj : Fin n → Fin n → Bool) (θ : ℕ) (Γ : ℝ) (u : Fin n) (h z : ℕ)
    (L : Fin n → ℕ) (R : Finset (Fin n)) (P : Fin n → List (Fin n)) (out : Fin n → List (JTree n)) :
    Prop :=
  (∀ w ∈ kids adj θ u, IsCheapest adj θ Γ L u w (P w)) ∧
    (2 ≤ h → ∀ w ∈ kids adj θ u, GreedyLoop adj θ Γ w (h - 1) z (L + pathLoads (P w)) R (out w))

/-- **The candidate chosen in line 18**: a candidate with positive count that minimizes `Δ_L(C)/cnt(C)` among
the candidates with positive count. These are the premises `hC`, `hpos`, `hmin` of `GreedyLoop.choose`. -/
def IsChosen (Γ : ℝ) (h z : ℕ) (L : Fin n → ℕ) (R : Finset (Fin n)) (cands : List (JTree n))
    (C : JTree n) : Prop :=
  C ∈ cands ∧ 0 < cnt h R z C ∧
    ∀ C' ∈ cands, 0 < cnt h R z C' →
      incr Γ L C.loads / (cnt h R z C : ℝ) ≤ incr Γ L C'.loads / (cnt h R z C' : ℝ)

end DirTeleMC



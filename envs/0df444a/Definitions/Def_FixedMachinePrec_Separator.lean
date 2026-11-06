-- Prove2me | Definitions.Def_FixedMachinePrec_Separator
-- name    : FixedMachinePrec_Separator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:57.253747+00:00
-- url     : https://prove2.me/theorems/76f0ae8a-9a7b-4b6e-a122-d7a3b609fb99
-- title:
--   Priority orders, normalized schedules, separators and $B_z(H)$
-- statement:
--   Fix a domain $U\subseteq J$.
--
--   1. A **priority order** on $U$ is a strict total order $\lhd_U$ on $U$ extending the induced precedence; list $U$ as $u_1\lhd_U\dots\lhd_U u_s$, with priority position $\rho_U(u_i)=i$. Its **priority prefix** (cutoff) of length $k$ is $S_k=\{u_1,\dots,u_k\}$.
--   2. For a feasible full schedule $\pi$ of $U$, $\mathrm{enc}_{\lhd}(\pi)$ lists the priority positions of each slot in increasing order and concatenates. A feasible full schedule $\pi^*$ of $U$ is **normalized** if $\mathrm{enc}_{\lhd}(\pi^*)\le_{\mathrm{lex}}\mathrm{enc}_{\lhd}(\pi)$ for every feasible full schedule $\pi$ of $U$.
--   3. Let $\sigma_U=(Z_1,\dots,Z_q)$ be a schedule of $U$ with local time $\tau_U$, and $S$ an ideal of the induced order on $U$. An actual slot $z=Z_r$ **separates** $S$ on $U$ if
--   $$x\in U\setminus S,\ \tau_U(x)<r\ \Rightarrow\ x\in P_z,\qquad x\in S,\ \tau_U(x)>r\ \Rightarrow\ x\in D_z,$$
--   with cones computed on all of $J$.
--   4. For $H\subseteq J$, $B_z(H)=P_z\cup(H\setminus\hat D_z)$ with $\hat D_z=z\cup D_z$.
--
--   These objects turn a temporal prefix of a normalized witness schedule into a short global Boolean description, the core of the structural theorem.
--
--   **Formalization Note** A priority order is a duplicate-free list of $U$ extending precedence. Separation covers actual slots only, and includes the requirement that $S$ is an ideal of $U$. Exchanging two jobs is the image of every slot under their transposition.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §7.1, pp.29–31; Definition 7.2, p.33; §7.2, p.34

import Mathlib
import Definitions.Def_FixedMachinePrec_FullSchedule

namespace FixedMachinePrec

/-- **A priority order on a domain `U`** (Jansen, *Precedence Constraint Scheduling on a Fixed
Number of Machines*, manuscript, sha256 08cdf3e1…, §7.1, pp.29–30): "a strict total order ◁_U on
the jobs of U that extends their induced precedence order … Equivalently, list U as
u_1 ◁_U · · · ◁_U u_s and define its priority position ρ_U(u_i) = i."

`IsPriorityList prec U pri`: the list `pri` enumerates `U` without repetition and `x ≺ y` in `U`
puts `x` earlier. `x ◁_U y` is `pri.idxOf x < pri.idxOf y`, and the priority position is
`ρ_U(x) = pri.idxOf x + 1`.

**Formalization Note** One fixed frame: `prec` is the precedence of that frame; the reversed frame
is the dual order, so results stated for every strict partial order cover both frames. -/
def IsPriorityList {N : ℕ} (prec : Fin N → Fin N → Prop) (U : Finset (Fin N)) (pri : List (Fin N)) :
    Prop :=
  pri.Nodup ∧ pri.toFinset = U ∧ ∀ x ∈ U, ∀ y ∈ U, prec x y → pri.idxOf x < pri.idxOf y

/-- The priority prefix (cutoff) `S_k = {u_1, …, u_k}` (pp.30, 33). -/
def priorityPrefix {N : ℕ} (pri : List (Fin N)) (k : ℕ) : Finset (Fin N) :=
  (pri.take k).toFinset

/-- `enc_◁(π)` (p.30): sort the jobs of each slot by increasing priority position and concatenate
the resulting lists of priority positions. -/
def priEnc {N : ℕ} (pri : List (Fin N)) (π : List (Finset (Fin N))) : List ℕ :=
  π.flatMap fun A => (A.image fun x => pri.idxOf x + 1).sort (· ≤ ·)

/-- **A normalized schedule** (pp.30–31): a feasible full schedule `π*` of exactly `U` with
`enc_◁(π*) ≤_lex enc_◁(π)` for every feasible full schedule `π` of `U`. -/
def IsNormalized {N : ℕ} (prec : Fin N → Fin N → Prop) (m : ℕ) (U : Finset (Fin N))
    (pri : List (Fin N)) (π : List (Finset (Fin N))) : Prop :=
  IsFullSchedule prec m U π ∧ ∀ π', IsFullSchedule prec m U π' → priEnc pri π ≤ priEnc pri π'

/-- Exchange the slots of the jobs `x` and `y` in a schedule, all other jobs fixed. -/
def swapJobs {N : ℕ} (π : List (Finset (Fin N))) (x y : Fin N) : List (Finset (Fin N)) :=
  π.map fun A => A.image (Equiv.swap x y)

/-- **Separator** (Jansen, manuscript, sha256 08cdf3e1…, Definition 7.2, p.33). For the local
schedule `Zs = (Z_1, …, Z_q)` of the domain `U = Z_1 ∪ ⋯ ∪ Z_q`, local time `τ_U`, an ideal `S`
of the induced order on `U`, and an actual slot `z = Z_r` (`1 ≤ r ≤ q`): "x ∈ U \ S, τ_U(x) < r
⟹ x ∈ P_z, x ∈ S, τ_U(x) > r ⟹ x ∈ D_z" (the earlier-high and later-low properties). Cones are
computed on all of `J` (p.33).

**Formalization Note** Only actual slots are covered (the exterior-boundary case of the definition
is not needed by the items of this mission). The ideal hypothesis on `S` is made part of the
predicate. -/
def Separates {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (Zs : List (Finset (Fin N))) (S : Finset (Fin N)) (r : ℕ) : Prop :=
  IsIdealIn prec (unionSlots Zs) S ∧ 1 ≤ r ∧ r ≤ Zs.length ∧
  (∀ x ∈ unionSlots Zs \ S, localTime Zs x < r → x ∈ predCone prec (Zs.getD (r - 1) ∅)) ∧
  (∀ x ∈ S, r < localTime Zs x → x ∈ succCone prec (Zs.getD (r - 1) ∅))

/-- `B_z(H) = P_z ∪ (H \ D̂_z)`, `D̂_z = z ∪ D_z` (p.34). -/
def sepFormula {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (z H : Finset (Fin N)) :
    Finset (Fin N) :=
  predCone prec z ∪ (H \ weakSuccCone prec z)

end FixedMachinePrec



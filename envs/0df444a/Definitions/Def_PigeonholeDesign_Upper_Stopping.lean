-- Prove2me | Definitions.Def_PigeonholeDesign_Upper_Stopping
-- name    : PigeonholeDesign_Upper_Stopping
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:06.758405+00:00
-- url     : https://prove2.me/theorems/3d4e980f-bd1e-479f-8c51-c19c21e1dd32
-- title:
--   p. ec7 — stopping time τ, matched set 𝒯_M, unmatched set 𝒯_U, counts H⁰_τ and H¹_τ
-- statement:
--   These are the objects of the proof of Lemma 3 (pp. ec7–ec8) for a run of the pigeonhole design with a fixed coin vector.
--
--   **Stopping time.** With $n^0_t,n^1_t$ the numbers of control and treated subjects after subject $t$ is assigned,
--   $$\tau=\min\Bigl\{t\in[T]\ :\ n^0_t=\tfrac T2\ \text{ or }\ n^1_t=\tfrac T2\Bigr\},$$
--   the first time one group is full. Up to and including subject $\tau$, Step 1 of the design has not been triggered.
--
--   **Matched and unmatched subjects.** Among the first $\tau$ subjects, those falling in the same pigeonhole are paired in arrival order: the first with the second, the third with the fourth, and so on. The matched set $\mathcal T_M$ consists of the paired subjects; a pigeonhole holding an odd number of the first $\tau$ subjects leaves its last one unpaired, and these form the unmatched set $\mathcal T_U$. Thus each pigeonhole has at most one unmatched subject.
--
--   **Counts.** $H^0_\tau$ and $H^1_\tau$ are the numbers of unmatched subjects assigned to control and to treatment, respectively (equivalently, the numbers of pigeonholes whose unmatched subject is in control, resp. treatment).
--
--   The matched set carries Component 1 of the proof of Lemma 3, and the unmatched subjects together with the last $T-\tau$ subjects carry Component 2.
--
--   **Formalization Note** Time is counted by the number $n$ of subjects already assigned, so $\tau$ is the paper's 1-based index, the least $n\in[1,T]$ at which one group holds $T/2$ subjects. For even $T\ge2$ the defining set contains $n=T$ and is nonempty; for $T=0$ it is empty and Lean's `sInf` returns $0$. The pairing "in arrival order" is encoded through the rank of a subject among the earlier subjects of its pigeonhole: a subject before $\tau$ is matched iff its rank is below $2\lfloor m/2\rfloor$, where $m$ is the number of the first $\tau$ subjects in its pigeonhole.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. ec7-ec8, proof of Lemma 3 (definition of τ, 𝒯_M, 𝒯_U, H⁰_τ, H¹_τ)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

/-- Proof of Lemma 3, p. ec7: the stopping time `τ`, the least `n ∈ [1, T]` such that after the first
`n` subjects the control or the treated group holds `T/2` subjects (`n` is the paper's 1-based `t`).
For even `T ≥ 2` the set is nonempty (`n = T` belongs to it); for `T = 0` it is empty and `τ = 0`. -/
noncomputable def tau {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ n ≤ T ∧
    ((prefixAssign T (cellOf hole x) (coinOf coin) n).count false = T / 2 ∨
     (prefixAssign T (cellOf hole x) (coinOf coin) n).count true = T / 2)}

/-- The number of subjects among the first `m` that share the pigeonhole of subject `s`. -/
def cellCount {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E) (m : ℕ)
    (s : Fin T) : ℕ :=
  (Finset.univ.filter (fun s' : Fin T => (s' : ℕ) < m ∧ hole (x s') = hole (x s))).card

/-- The rank of subject `s` inside its pigeonhole: the number of earlier subjects in the same one. -/
def cellRank {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (s : Fin T) : ℕ :=
  (Finset.univ.filter (fun s' : Fin T => s' < s ∧ hole (x s') = hole (x s))).card

/-- The matched set `𝒯_M` (proof of Lemma 3, p. ec7): among the first `τ` subjects, those of each
pigeonhole are paired in arrival order (1st with 2nd, 3rd with 4th, …); a subject is matched unless
its pigeonhole holds an odd number of the first `τ` subjects and it is the last of them. -/
noncomputable def matched {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : Finset (Fin T) :=
  Finset.univ.filter (fun s : Fin T => (s : ℕ) < tau hole x coin ∧
    cellRank hole x s < 2 * (cellCount hole x (tau hole x coin) s / 2))

/-- The unmatched set `𝒯_U`: the first `τ` subjects that are not matched. -/
noncomputable def unmatched {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : Finset (Fin T) :=
  Finset.univ.filter (fun s : Fin T => (s : ℕ) < tau hole x coin ∧ s ∉ matched hole x coin)

/-- `H⁰_τ`: the number of unmatched subjects assigned to control. -/
noncomputable def H0 {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : ℕ :=
  ((unmatched hole x coin).filter (fun s => assign hole x coin s = false)).card

/-- `H¹_τ`: the number of unmatched subjects assigned to treatment. -/
noncomputable def H1 {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
    (coin : Fin T → Bool) : ℕ :=
  ((unmatched hole x coin).filter (fun s => assign hole x coin s = true)).card

end PigeonholeDesign.Upper



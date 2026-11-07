-- Prove2me | Definitions.Def_StableVotingDistortion_slices
-- name    : StableVotingDistortion_slices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:46.377297+00:00
-- url     : https://prove2.me/theorems/b6298a70-565c-4447-9113-2b383af87cb6
-- title:
--   Threshold slices: $S_t$, $p_t$, $q_v(t)$, $z_v(t)$, $s_v$, $k_v(t)$
-- statement:
--   Fix a lottery $D$, $\rho:C\to\mathbb R_{\ge0}$ and a threshold $t$. Then $S_t=\{b\in C:\rho(b)>t\}$ and $p_t=D(S_t)$. On $v$'s rank line:
--
--   1. $q_v(t)=\min_{c\notin S_t}\mathrm{rank}_v(c;D)$, the left-boundary rank of the first candidate outside $S_t$;
--   2. $z_v(t)$ is the rightmost endpoint of any candidate in $S_t$ with positive mass, or $0$ if there is none;
--   3. $s_v=\Pr_{b\sim D}[a^\star\succ_v b]$ is the left endpoint of $a^\star$'s interval;
--   4. the score of a set $S$ of candidates is $\sum_{b\in S}\int_{\mathrm{rank}_v(b)}^{\mathrm{rank}_v(b)+D(b)}(-\phi)$, and $k_v(t)$ is the score of $S_t$.
--
--   These slice $L_v$ by height.
--
--   **Formalization Note** If $S_t=C$ the minimum defining $q_v(t)$ is empty and the value here is $1$. This does not occur in the mission's statements, where $\rho(a^\star)=0$ and $t\ge0$. The minimum includes zero-mass candidates; only $z_v$ is restricted to positive mass.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.2, p.22; §6.3.1, pp.27–28

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_leftRank

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

open Classical in
/-- The slice `S_t = {b ∈ C : ρ(b) > t}`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, p.27. -/
noncomputable def St {C : Type} [Fintype C] (ρ : C → ℝ) (t : ℝ) : Finset C :=
  Finset.univ.filter (fun b => t < ρ b)

/-- The mass `p_t = D(S_t)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, p.27. -/
noncomputable def pt {C : Type} [Fintype C] (D ρ : C → ℝ) (t : ℝ) : ℝ :=
  ∑ b ∈ St ρ t, D b

open Classical in
/-- `q_v(t) = min_{c ∉ S_t} rank_v(c; D)`, the left-boundary rank of the first candidate outside `S_t`.
The minimum runs over all candidates outside `S_t`, zero mass included.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, p.27.

**Formalization Note.** When every candidate lies in `S_t` the printed minimum is over the empty set and
the value here is `1`. That case does not occur in the mission's statements: there `ρ(a⋆) = 0` and
`t ≥ 0`, so `a⋆ ∉ S_t`. -/
noncomputable def qv {V C : Type} [Fintype C] (E : Election V C) (D ρ : C → ℝ) (v : V) (t : ℝ) : ℝ :=
  if h : (Finset.univ.filter (fun c => c ∉ St ρ t)).Nonempty then
    (Finset.univ.filter (fun c => c ∉ St ρ t)).inf' h (fun c => leftRank E D v c)
  else 1

open Classical in
/-- `z_v(t)`, the rightmost endpoint of any candidate in `S_t` with positive mass in `D`, or `0` if there
is none.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, p.27: "Let z_v(t) denote the rightmost endpoint of any candidate in S_t with positive
mass in D (or 0 if there is none)." -/
noncomputable def zv {V C : Type} [Fintype C] (E : Election V C) (D ρ : C → ℝ) (v : V) (t : ℝ) : ℝ :=
  if h : (Finset.univ.filter (fun b => b ∈ St ρ t ∧ 0 < D b)).Nonempty then
    (Finset.univ.filter (fun b => b ∈ St ρ t ∧ 0 < D b)).sup' h (fun b => leftRank E D v b + D b)
  else 0

/-- `s_v = Pr_{b ∼ D}[a⋆ ≻_v b]`, the left endpoint of `a⋆`'s interval on `v`'s rank line.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, p.27. -/
noncomputable def sv {V C : Type} [Fintype C] (E : Election V C) (D : C → ℝ) (aStar : C) (v : V) : ℝ :=
  leftRank E D v aStar

/-- The total score of a set `S` of candidates on `v`'s rank line,
`∑_{b ∈ S} ∫_{rank_v(b)}^{rank_v(b) + D(b)} (−ϕ)`, the score of a candidate being `−ϕ` averaged over
its interval.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.2, p.22: "a candidate's score on a voter's rank line is the average of −ϕ over its interval".
-/
noncomputable def blockScore {V C : Type} [Fintype C] (E : Election V C) (D : C → ℝ) (ϕ : ℝ → ℝ)
    (v : V) (S : Finset C) : ℝ :=
  ∑ b ∈ S, ∫ r in (leftRank E D v b)..(leftRank E D v b + D b), -ϕ r

/-- `k_v(t)`, the total score of `S_t` on `v`'s rank line.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, p.28. -/
noncomputable def kv {V C : Type} [Fintype C] (E : Election V C) (D ρ : C → ℝ) (ϕ : ℝ → ℝ)
    (v : V) (t : ℝ) : ℝ :=
  blockScore E D ϕ v (St ρ t)

end StableVotingDistortion



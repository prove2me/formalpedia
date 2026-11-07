-- Prove2me | Definitions.Def_SingleOrSample_deficit
-- name    : SingleOrSample_deficit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:31.100131+00:00
-- url     : https://prove2.me/theorems/fcc0cf71-0a2a-442e-869e-b5090cb13387
-- title:
--   Active MMS bundles and the deficit $D_j$
-- statement:
--   This is the potential of the analysis of one agent. Fix a labelling $P$ and weights $w$.
--
--   Initially all bundles are **active**. A non-special round leaves the active collection unchanged. After a special round selecting $e$, the bundle of $e$ is deactivated if it is active, and otherwise an arbitrary active bundle is. With $\mathcal B_j$ the active bundles after $j$ rounds, the **surviving weight** and the **deficit** are
--   $$W_j=\sum_{h\in\mathcal B_j}\ \sum_{e\in P_h\cap R_{j+1}}w_e,\qquad D_j=N_j-W_j,\quad N_j=|\mathcal B_j|.$$
--
--   These deactivations are part of the analysis only: they do not change the algorithm.
--
--   **Formalization Note** The function $ch$ supplies the page's "arbitrary currently active bundle" as a function of the history before the special round; statements assume that $ch(h)$ is active whenever some bundle is. $N_j$ is defined as $|\mathcal B_j|$, and the equality $N_j=n-t_j$ is part of the milestone `deficit_special_round`.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.2.2, eq. (5), p.15

import Mathlib
import Definitions.Def_SingleOrSample_Hist

namespace SingleOrSample

/-- One step of the active collection (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online
Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256
28cd3d7b…, §4.2.2, p.15): after a non-special round nothing changes; after a special round selecting `e`,
the bundle of `e` is deactivated if it is active, and otherwise the bundle `ch pre` is, where `pre` is the
history before that round. -/
def activeStep {m n : ℕ} (P : Fin m → Fin n) (ch : Hist m → Fin n) (pre : Hist m)
    (A : Finset (Fin n)) : Round m → Finset (Fin n)
  | .special e => if P e ∈ A then A.erase (P e) else A.erase (ch pre)
  | .sampled _ => A

/-- The active collection after the rounds `rest`, following the prefix `pre` and the collection `A`. -/
def activeFrom {m n : ℕ} (P : Fin m → Fin n) (ch : Hist m → Fin n) :
    Hist m → Finset (Fin n) → Hist m → Finset (Fin n)
  | _, A, [] => A
  | pre, A, r :: rest => activeFrom P ch (pre ++ [r]) (activeStep P ch pre A r) rest

/-- The active MMS bundles `B_j` after a history: initially all of them (§4.2.2, p.15).

**Formalization Note.** `ch` supplies the page's "arbitrary currently active bundle"; statements assume
that `ch h` is active whenever some bundle is. It may depend on the history, as the page's choice may. -/
def activeBundles {m n : ℕ} (P : Fin m → Fin n) (ch : Hist m → Fin n) (h : Hist m) : Finset (Fin n) :=
  activeFrom P ch [] Finset.univ h

/-- The surviving supporting weight `W_j = ∑_{h ∈ B_j} ∑_{e ∈ P_h ∩ R_{j+1}} w_e` (§4.2.2, p.15). -/
def survivingWeight {m n : ℕ} (P : Fin m → Fin n) (w : Fin m → ℝ) (ch : Hist m → Fin n) (h : Hist m) : ℝ :=
  ∑ b ∈ activeBundles P ch h, ∑ e ∈ (remaining h).filter (fun e => P e = b), w e

/-- The deficit `D_j = N_j − W_j` of (5), p.15, with `N_j = |B_j|`.

**Formalization Note.** `N_j` is the number of active bundles, which equals `n − t_j` on a run
(`deficit_special_round`). -/
noncomputable def deficit {m n : ℕ} (P : Fin m → Fin n) (w : Fin m → ℝ) (ch : Hist m → Fin n)
    (h : Hist m) : ℝ :=
  ((activeBundles P ch h).card : ℝ) - survivingWeight P w ch h

end SingleOrSample



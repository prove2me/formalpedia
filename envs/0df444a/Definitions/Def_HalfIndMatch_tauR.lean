-- Prove2me | Definitions.Def_HalfIndMatch_tauR
-- name    : HalfIndMatch_tauR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:52.49125+00:00
-- url     : https://prove2.me/theorems/c30e5dc5-e881-441e-b85c-65287430e215
-- title:
--   The stopping time $\tau_r=\min\{t\in[n]:|A_t(G)|\ge r\}$
-- statement:
--   For an online algorithm $A$, a graph $G$ and $r\ge0$, let
--
--   $$\tau_r=\min\{t\in[n]:|A_t(G)|\ge r\},$$
--
--   the first round after which the matching held by $A$ has at least $r$ edges, with $\min\emptyset=\infty$.
--
--   It is the stopping time at which the proof of Theorem 2.3 splits the run: $r$ edges have been found by time $\tau_r$, and Lemma 3.2 bounds the chance of $s$ further acceptances.
--
--   **Formalization Note** The value lies in `ℕ∞`; $\infty$ is `⊤`, and the rounds are $t\in\{1,\dots,n\}$.
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (7), §3.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_HalfIndMatch_OnlineAlg

open scoped Classical

namespace HalfIndMatch

/-- The stopping time `τ_r = min{t ∈ [n] : |A_t(G)| ≥ r}` of (7), with `min ∅ = ∞` (`⊤ : ℕ∞`).

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (7),
§3.2, p.15 (PDF p.17).

**Formalization Note** Rounds are `t ∈ {1, …, n}` (`Finset.Icc 1 n`), as in the paper; the value is
in `ℕ∞`, finite values being the round. -/
noncomputable def tauR {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ∞ :=
  if h : ((Finset.Icc 1 n).filter fun t => r ≤ (At A G t).card).Nonempty then
    (((Finset.Icc 1 n).filter fun t => r ≤ (At A G t).card).min' h : ℕ∞)
  else ⊤

end HalfIndMatch



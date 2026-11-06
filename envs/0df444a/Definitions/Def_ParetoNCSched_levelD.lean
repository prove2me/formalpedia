-- Prove2me | Definitions.Def_ParetoNCSched_levelD
-- name    : ParetoNCSched_levelD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:24:13.932921+00:00
-- url     : https://prove2.me/theorems/dd133b8c-9c72-4254-aa96-90e119c40977
-- title:
--   The level $\ell(t)$ on a correct order
-- statement:
--   On a correct order (jobs relabelled so that $\sigma$ is the identity), the level is
--   $$\ell(t)=\begin{cases} e_n(t) & t\le t_f,\\ \ell_f:=e_n(t_f) & t\ge t_f,\end{cases}$$
--   where job $n$ is the last job of the order.
--
--   **Formalization Note** Job $n$ of the relabelled instance is $\sigma(n-1)$ (0-based positions), and $\ell(t)=e_{\sigma(n-1)}(\min(t,t_f))$; with no job the level is $0$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma D.1(b), p.21

import Mathlib
import Definitions.Def_ParetoNCSched_firstSingleTime

namespace ParetoNCSched

/-- **The level `ℓ(t)` on a correct order.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma D.1(b), p.21: "define the level by
ℓ(t) = eₙ(t) for t ≤ t_f and ℓ(t) = ℓ_f := eₙ(t_f) for t ≥ t_f", where job `n` is the last job of
the (relabelled) correct order.

**Formalization Note.** Job `n` of the relabelled instance is `σ (n − 1)` (0-based positions), and
`ℓ(t) = e_{σ(n−1)}(min(t, t_f))`. With no job (`n = 0`) the level is `0`. -/
noncomputable def levelD {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (t : ℝ) : ℝ :=
  if h : 0 < n then
    elapsed (mrcRate R p σ) (σ ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩) (min t (firstSingleTime R p σ))
  else 0

end ParetoNCSched



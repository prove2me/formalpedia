-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_HalfThinning
-- name    : PooledTestingAdaptivity_Gap_HalfThinning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:15.524577+00:00
-- url     : https://prove2.me/theorems/f511396d-68dc-4bfe-a647-355c9a2d447c
-- title:
--   Independent occurrence thinning, individual clearance and subcube companions
-- statement:
--   For an ordered allocation $P=(t_1,\ldots,t_k)$, use independent fair bits $c_{b,i}$ for each test position and person. Retain $i$ in pool $b$ exactly when $c_{b,i}=1$, delete empty pools, and keep the remaining order. Bits assigned to people outside a pool have no effect. Define
--
--   $$d_i(x)=\mathbf1\{i\in C(P_\pi(x),x)\},\qquad h_i(P,y)=2^{-nk}\sum_{c\in\{0,1\}^{k\times n}}\mathbf1\{i\in C(\operatorname{thin}(P,c),y)\}.$$
--
--   The allocation $P$ is fixed while this probability is computed. The evaluation profile $y$ is not used to choose any coins or any pool. Separate occurrences have separate bits, including repeated tests.
--
--   For a free set $E\subseteq[n]$ and an assignment $a$ on its complement, $x_a(v)$ extends a free assignment $v\in\{0,1\}^E$. Its companion is $x_a(1-v)$, complementing only free coordinates. Empty free sets and all locations and health states of the focal person are included. These are the actual functions used in both comparison lemmas.
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), §4.1–4.2, printed p. 13, PDF p. 14; Lemma 4.5, printed p. 15, PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Policies

namespace PooledTestingAdaptivity.Gap

/-- Separate fair bits for each test position and person. Bits outside the pool are ignored. -/
abbrev OccurrenceCoins {n : ℕ} (P : Allocation n) := Fin P.length → Fin n → Bool

/-- Shrink pools using the occurrence bits, delete empty pools, retain their order. -/
def halfThin {n : ℕ} (P : Allocation n) (coins : OccurrenceCoins P) : Allocation n :=
  (List.ofFn fun k : Fin P.length => (P.get k).filter (fun i => coins k i)).filter
    (fun t => t.Nonempty)

def clearanceIndicator {n : ℕ} (π : Policy n) (i : Fin n) (x : Profile n) : ℝ :=
  if i ∈ cleared (run π x) x then 1 else 0

/-- Exact uniform average of independent occurrence coins, conditional on P and y.
The n*length(P) bits include harmless dummy bits outside the pools. -/
noncomputable def thinningClearance {n : ℕ} (P : Allocation n) (y : Profile n) (i : Fin n) : ℝ :=
  (∑ coins : OccurrenceCoins P, if i ∈ cleared (halfThin P coins) y then (1 : ℝ) else 0) /
    (2 : ℝ) ^ (n * P.length)

/-- Fixed coordinates are assigned only outside E; no extra irrelevant coordinates in a. -/
def extendProfile {n : ℕ} (E : Finset (Fin n)) (a : {i : Fin n // i ∉ E} → Bool)
    (v : {i : Fin n // i ∈ E} → Bool) : Profile n :=
  fun i => if h : i ∈ E then v ⟨i, h⟩ else a ⟨i, h⟩

end PooledTestingAdaptivity.Gap



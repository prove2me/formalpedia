-- Prove2me | Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_Memory
-- name    : RandOnlineSetCoverSqrt_LowerBound_Supplement_Memory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:11:57.712317+00:00
-- url     : https://prove2.me/theorems/5e550ef1-8a08-4970-96f8-28d7caf7e40c
-- title:
--   Randomized online set-cover algorithms with S bits of memory on the known universe
-- statement:
--   The paper measures the **memory** of an online algorithm as "the information preserved between requests", assuming that "past requests cannot be reread if not stored in memory"; computation between requests is unlimited.
--
--   Fix $m$ and $S$. An **$S$-bit randomized online algorithm** on the canonical known universe $U_m$ (elements = nonempty subsets of $[m]$, set $i$ covering $u_A$ iff $i\in A$) consists of
--
--   1. a joint law $\mu_0$ of the initial memory state $s_0\in\{0,\dots,2^S-1\}$ and of the labels $Y_0\subseteq[m]$ bought before the first request;
--   2. a transition kernel $\delta(s,u)$: on the current state $s$ and the arriving element $u\in U_m$ it draws, with fresh randomness, the next state and the labels bought at this arrival.
--
--   No time index, past request or purchase record is available except through the $2^S$ states. On a finite request list $B=(u_1,\dots,u_T)$ the run tracks the state, the accumulated purchases $X_t=Y_0\cup\dots\cup Y_t$, and whether every request $u_t$ was covered by $X_t$ (purchases up to and including its arrival). The algorithm is **valid** if, for every finite list $B$ over $U_m$, this holds with probability one. Its **expected cost** on $B$ is $\mathbb E[|X_T|]$, pre-request purchases included. $\operatorname{OPT}(B)$ is the minimum number of labels covering every request of $B$.
--
--   **Formalization Note** The run is a finite PMF obtained by binding $\mu_0$ and $\delta$ along the list. $\operatorname{OPT}$ is the published `listOpt` of the incidences, converted to a natural number; it is finite because every element of $U_m$ has a nonempty incidence.
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Theorem 1.5 and the memory model, printed p. 3 / PDF p. 4; Definition 2.1, printed p. 6 / PDF p. 7; simulation in the proofs of Lemma 6.1 and Theorem 1.5, printed pp. 17, 19 / PDF pp. 18, 20

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Canonical

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement

/-- A randomized online set-cover algorithm on the canonical known universe `U_m` that keeps
`S` bits of memory between requests (printed p. 3 / PDF p. 4; proof printed 16-19 / PDF 17-20).
Its memory states are `Fin (2 ^ S)`. `init` is the joint law of the starting state and of the
labels bought before the first request; on the current state and the arriving element, `step`
draws, with fresh randomness and unlimited computation, the next state and the labels bought at
this arrival. Nothing else (time index, past requests, purchase record) is available. -/
structure MemAlg (m S : ℕ) where
  init : PMF (Fin (2 ^ S) × Finset (Fin m))
  step : Fin (2 ^ S) → Element m → PMF (Fin (2 ^ S) × Finset (Fin m))

/-- Configuration of a run: memory state, all labels bought so far, and a flag recording that
every request so far was covered by the purchases made up to and including its arrival. -/
abbrev MemConfig (m S : ℕ) := Fin (2 ^ S) × Finset (Fin m) × Bool

/-- One arrival of the element `u`. -/
noncomputable def MemAlg.arrive {m S : ℕ} (A : MemAlg m S) (x : MemConfig m S) (u : Element m) :
    PMF (MemConfig m S) :=
  (A.step x.1 u).map fun y =>
    (y.1, x.2.1 ∪ y.2, x.2.2 && decide ((x.2.1 ∪ y.2) ∩ u.val).Nonempty)

/-- The law of the configuration after the requests of the finite list `B`, in list order. -/
noncomputable def MemAlg.run {m S : ℕ} (A : MemAlg m S) (B : List (Element m)) :
    PMF (MemConfig m S) :=
  B.foldl (fun μ u => μ.bind fun x => A.arrive x u) (A.init.map fun y => (y.1, y.2, true))

/-- Feasibility on every finite request list, with probability one. -/
def MemAlg.IsValid {m S : ℕ} (A : MemAlg m S) : Prop :=
  ∀ B : List (Element m), ∀ x : MemConfig m S, A.run B x ≠ 0 → x.2.2 = true

/-- Expected number of distinct purchased sets (pre-request purchases included). -/
noncomputable def MemAlg.expectedCost {m S : ℕ} (A : MemAlg m S) (B : List (Element m)) : ℝ :=
  ∑ x : MemConfig m S, (A.run B x).toReal * (x.2.1.card : ℝ)

/-- Offline optimum of a request list (finite for every list over `U_m`). -/
noncomputable def listOptNat {m : ℕ} (B : List (Element m)) : ℕ :=
  (RandOnlineSetCover.InfoLB.listOpt (incidences B)).toNat

end RandOnlineSetCoverSqrt.LowerBound.Supplement



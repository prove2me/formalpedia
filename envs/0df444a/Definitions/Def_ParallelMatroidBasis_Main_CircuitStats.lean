-- Prove2me | Definitions.Def_ParallelMatroidBasis_Main_CircuitStats
-- name    : ParallelMatroidBasis_Main_CircuitStats
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:40.553548+00:00
-- url     : https://prove2.me/theorems/793439b5-6a8b-4bd5-ab30-1cb1b98e4eae
-- title:
--   Definitions 3.6–3.8 — permutation-induced circuit $C_\pi$, marginals $p_{x,M}$, $q_S$ and the α-value
-- statement:
--   Let $M$ be a matroid and $S$ a finite subset of its ground set; $M|S$ is the restriction of $M$ to $S$. An **ordering** of $S$ is a bijection $\pi:\{1,\dots,|S|\}\to S$. If the prefix $\{\pi(1),\dots,\pi(j)\}$ is independent but $\{\pi(1),\dots,\pi(j+1)\}$ is dependent, the **permutation-induced circuit** $C_\pi$ is the unique circuit contained in $\{\pi(1),\dots,\pi(j+1)\}$, namely the set of its elements $y$ whose removal leaves an independent set (Definition 3.6). For a uniformly random ordering $\pi$ of $S$, in $M|S$,
--   $$p_{x,M|S}=\Pr_\pi[x\in C_\pi],\qquad q_A=\Pr_\pi[C_\pi\subseteq A]$$
--   (Definition 3.8; for a matroid $N$ with ground set $E$, $q_A$ is computed with $S=E$). The **α-value** of $S$ (Definition 3.7) is the median number of elements sampled from $S$ when a circuit first forms:
--   $$\alpha(S)=\min\Big\{k\in[|S|]\ :\ \Pr_{T\sim\binom{S}{k}}[\mathrm{Ind}(T)=1]\le\tfrac12\Big\},$$
--   where $T$ is a uniformly random $k$-element subset of $S$ and $[|S|]=\{1,\dots,|S|\}$.
--
--   These statistics drive the decomposition of §5 (the α-values of the peeled sets, Claim 5.6) and the hypotheses of the deletion procedure of §6 ($\alpha(S)/|S|$ small and $p_{x,M|S}\ge n^{-9}$).
--
--   **Formalization Note.** Matroids are Mathlib's `Matroid α`; independence in $M|S$ of a subset of $S$ is independence in $M$. The paper uses these quantities only for matroids containing a circuit and $\alpha(S)$ only for dependent $S$. When $S$ is independent the Lean values are: $C_\pi=\emptyset$, hence $p_{x,M|S}=0$ and $q_A=1$; and $\alpha(S)=0$. Every theorem that uses them either assumes $p_{x,M|S}\ge n^{-9}$ (impossible when $S$ is nonempty and independent), or assumes $\alpha\ge 50$ (impossible when $\alpha$ takes its default value) or that the relevant set is dependent.
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Definitions 3.6, 3.7, 3.8, p.11 (PDF p.13)

import Mathlib

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-! # Permutation-induced circuits, marginal probabilities and α-values
(Putterman–Khanna–Song, STOC 2027 submission #589, Definitions 3.6–3.8, PDF p.13)

Matroids are Mathlib's `Matroid α`. A finite set `S : Finset α` plays the role of the ground set
of the restriction `M|S`; for a matroid `N` with finite ground set `E` (`N.E = ↑E`) the statistics
taken with `S = E` are those of `N` itself. Independence of a subset of `S` in `M|S` is
independence in `M`, so all statistics below only read `M.Indep` on subsets of `S`. -/

variable {α : Type*}

/-- The orderings of `S`: bijections `π : [|S|] → S` (Definition 3.6 uses `π : [n] → E`). The
uniform distribution on this finite type is a uniformly random permutation of `S`. -/
abbrev Ordering (S : Finset α) := Fin S.card ≃ S

/-- The prefix `{π(1), …, π(j)}` of an ordering (0-indexed: the images of `0, …, j − 1`). -/
def prefixSet (S : Finset α) (π : Ordering S) (j : ℕ) : Finset α :=
  (Finset.univ.filter (fun i : Fin S.card => i.val < j)).image (fun i => (π i : α))

/-- Definition 3.6 (PDF p.13), the permutation-induced circuit `C_π` of `M|S`. If the first
dependent prefix of `π` is `P = {π(1), …, π(j+1)}` (so `{π(1), …, π(j)}` is independent), `C_π` is
the unique circuit contained in `P`, i.e. the set of `y ∈ P` with `P − y` independent. If `S` is
independent there is no circuit and the value is `∅` (a convention: the paper uses `C_π` only for
matroids containing a circuit). -/
def firstCircuit (M : Matroid α) (S : Finset α) (π : Ordering S) : Finset α :=
  if h : ∃ j, ¬ M.Indep (↑(prefixSet S π j) : Set α) then
    (prefixSet S π (Nat.find h)).filter
      (fun y => M.Indep (↑((prefixSet S π (Nat.find h)).erase y) : Set α))
  else ∅

/-- `Pr_π[P(C_π)]` for a uniformly random ordering `π` of `S`, in the matroid `M|S`. -/
def circuitProb (M : Matroid α) (S : Finset α) (P : Finset α → Prop) : ℝ :=
  ((Finset.univ.filter (fun π : Ordering S => P (firstCircuit M S π))).card : ℝ) /
    (Fintype.card (Ordering S) : ℝ)

/-- Definition 3.8 (PDF p.13): the marginal probability `p_{x,M|S} = Pr_π[x ∈ C_π]` in the
restriction `M|S`. It is `0` when `S` is independent. -/
def pMarg (M : Matroid α) (S : Finset α) (x : α) : ℝ :=
  circuitProb M S (fun C => x ∈ C)

/-- Definition 3.8 (PDF p.13): `q_A = Pr_π[C_π ⊆ A]` in the matroid `M|E` (for a matroid `N`
with ground set `E`, `qVal N E A` is the paper's `q_A`). It is `1` when `E` is independent. -/
def qVal (M : Matroid α) (E A : Finset α) : ℝ :=
  circuitProb M E (fun C => C ⊆ A)

/-- `Pr_{T ∼ (S choose k)}[Ind(T) = 1]`: the fraction of the `k`-element subsets of `S` that are
independent. -/
def indepFrac (M : Matroid α) (S : Finset α) (k : ℕ) : ℝ :=
  ((S.powersetCard k).filter (fun T => M.Indep (↑T : Set α))).card / (S.card.choose k : ℝ)

/-- Definition 3.7 (PDF p.13), the α-value
`α(S) = min {k ∈ [|S|] : Pr_{T ∼ (S choose k)}[Ind(T) = 1] ≤ 1/2}`. For dependent `S` the set is
nonempty (`k = |S|` qualifies). For independent `S` it is empty and the value is `0` (the paper
uses `α(S)` only for dependent `S`). -/
def alphaVal (M : Matroid α) (S : Finset α) : ℕ :=
  if h : ∃ k, 1 ≤ k ∧ k ≤ S.card ∧ indepFrac M S k ≤ 1 / 2 then Nat.find h else 0

end ParallelMatroidBasis.Main



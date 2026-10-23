-- Prove2me | Definitions.Def_RandomGames_BRD_Percolation
-- name    : RandomGames_BRD_Percolation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:54.807453+00:00
-- url     : https://prove2.me/theorems/26b224bd-338b-492e-bd14-29af928f275c
-- title:
--   §4, pp. 12–15 — bond percolation B^β_N on the hypercube, the cluster of 0, the fragment M^β_N, Hamming balls B_r(s) (4.15) and m_β (4.16)
-- statement:
--   **Bond percolation on the hypercube** (p. 12). Let $\mathscr H_N$ be the hypercube on $\{0,1\}^N$, with an edge between profiles that differ in exactly one coordinate. In bond percolation $\mathscr B^\beta_N$ with parameter $\beta\in[0,1]$, every edge is declared **open** independently with probability $\beta$ and **closed** otherwise; the percolation graph keeps all $2^N$ vertices and the open edges.
--
--   - $\mathscr L^{\beta,\mathbf 0}_N$ is the vertex set of the open cluster (connected component) containing $\mathbf 0$.
--   - The **giant component** $\mathscr L^\beta_N$ is the component with the largest number of vertices, and the **fragment** is $\mathscr M^\beta_N = \mathscr V_N\setminus\mathscr L^\beta_N$ (p. 14), so
--   $$\mathsf{card}(\mathscr M^\beta_N) = 2^N - \max_{C}\ \mathsf{card}(C),$$
--   the maximum over the open clusters $C$.
--   - The event $\mathscr L^\beta_N\neq\mathscr L^{\beta,\mathbf 0}_N$, i.e. $\mathbf 0\notin\mathscr L^\beta_N$ (4.13).
--
--   **Hamming balls** (4.15). With $h(\boldsymbol s,\boldsymbol t)=\mathsf{card}\{i : s_i\neq t_i\}$ the Hamming distance, $B_r(\boldsymbol s) := \{\boldsymbol t : h(\boldsymbol s,\boldsymbol t)\le r\}$. Finally
--   $$m_\beta := \left\lfloor \frac{1}{-\log_2(1-\beta)}\right\rfloor. \tag{4.16}$$
--
--   These are the percolation objects used in Propositions 4.1–4.2 and Lemmas 4.3–4.4.
--
--   **Formalization Note** An edge is a pair `(s, i)` with `s i = false`, standing for the edge between `s` and `s` with coordinate `i` flipped; configurations are `Edge N → Bool` (`true` = open) under the product of Bernoulli($\beta$) laws (`bernoulliMeasure β`, a probability measure for $\beta\in[0,1]$, which every statement assumes). `fragmentCard` does not depend on the choice of a largest cluster. `NotInGiant` reads $\mathscr L^\beta_N\neq\mathscr L^{\beta,\mathbf 0}_N$ conservatively: some cluster not containing $\mathbf 0$ is at least as large as the cluster of $\mathbf 0$, so on a tie for the largest cluster $\mathbf 0$ counts as outside the giant. The floor in $m_\beta$ is `Int.floor`.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, pp. 12–15, §4 (bond percolation, p. 12; giant component and fragment, p. 14), (4.13), (4.15), (4.16)

import Mathlib
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

open MeasureTheory

/-- p. 12: the edges of the hypercube `H_N`. The pair `(s, i)` with `s i = false` is the edge
between `s` and `flip s i`. -/
abbrev Edge (N : ℕ) := {p : Profile N × Fin N // p.1 p.2 = false}

/-- p. 12: the Bernoulli law on `Bool` with `P(true) = p` (`true` = open), for `0 ≤ p ≤ 1`. -/
noncomputable def bernoulliMeasure (p : ℝ) : Measure Bool :=
  (Real.toNNReal p) • Measure.dirac true + (Real.toNNReal (1 - p)) • Measure.dirac false

/-- p. 12: independent bond percolation on `H_N` with parameter `β`: every edge is open
(`ω e = true`) independently with probability `β`. -/
noncomputable def percMeasure (β : ℝ) (N : ℕ) : Measure (Edge N → Bool) :=
  Measure.pi (fun _ : Edge N => bernoulliMeasure β)

/-- p. 12: the percolation graph on `V_N`: `s, t` are adjacent iff they are neighbours in `H_N`
and the edge between them is open. -/
def openGraph {N : ℕ} (ω : Edge N → Bool) : SimpleGraph (Profile N) :=
  SimpleGraph.fromRel (fun s t => ∃ e : Edge N, ω e = true ∧ s = e.1.1 ∧ t = flip e.1.1 e.1.2)

/-- p. 12: `L^{β,0}_N`, the vertex set of the open cluster of `0`. -/
def cluster0 {N : ℕ} (ω : Edge N → Bool) : Set (Profile N) :=
  {t | (openGraph ω).Reachable (zeroProfile N) t}

open Classical in
/-- The number of vertices of the open cluster of `s`. -/
noncomputable def compCard {N : ℕ} (ω : Edge N → Bool) (s : Profile N) : ℕ :=
  (Finset.univ.filter (fun t => (openGraph ω).Reachable s t)).card

/-- p. 14: `card(M^β_N) = 2^N − card(L^β_N)`, the number of vertices outside a largest open
cluster (the giant component). It does not depend on the choice of a largest cluster. -/
noncomputable def fragmentCard {N : ℕ} (ω : Edge N → Bool) : ℕ :=
  2 ^ N - Finset.univ.sup (fun s => compCard ω s)

/-- p. 14, (4.7), (4.13): `L^β_N ≠ L^{β,0}_N`, read conservatively: some open cluster not
containing `0` has at least as many vertices as the cluster of `0` (on a tie for the largest
cluster, `0` counts as outside the giant). -/
def NotInGiant {N : ℕ} (ω : Edge N → Bool) : Prop :=
  ∃ s, ¬ (openGraph ω).Reachable (zeroProfile N) s ∧ compCard ω (zeroProfile N) ≤ compCard ω s

open Classical in
/-- (4.15), p. 15: the Hamming ball `B_r(s) = {t : h(s, t) ≤ r}`. -/
noncomputable def ball {N : ℕ} (s : Profile N) (r : ℕ) : Finset (Profile N) :=
  Finset.univ.filter (fun t => hammingDist s t ≤ r)

/-- (4.16), p. 15: `m_β = ⌊1 / (−log₂(1 − β))⌋`. -/
noncomputable def mBeta (β : ℝ) : ℤ := Int.floor (1 / (-Real.logb 2 (1 - β)))

end RandomGames.BRD



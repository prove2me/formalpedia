-- Prove2me | Definitions.Def_StreamColour_Capacity
-- name    : StreamColour_Capacity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:41.226294+00:00
-- url     : https://prove2.me/theorems/e5284388-6a62-473e-8740-882d909d72ea
-- title:
--   Step 1 of Algorithm B — random capacities, $\mathcal R^\star$, and the conclusion of Lemma 5.23
-- statement:
--   Each vertex starts with capacity $b(v)=b_0$ and independently tosses fair coins: on heads $b(v)$ becomes $\min\{2b(v),n\}$; on tails it stops; it stops also when $b(v)=n$. With $j_{\max}=\lceil\log_2(n/b_0)\rceil$, capacity $2^jb_0$ has probability $2^{-j-1}$ for $0\le j<j_{\max}$, and capacity $n$ has probability $2^{-j_{\max}}$.
--
--   For a partition with pieces $C_i$ the set of recoverable vertices is
--
--   $$\mathcal R^\star=\bigcup_i\{v\in C_i:|C_i\triangle N_G[v]|\le b(v)\}.$$
--
--   With $L=100h$, the capacities are **anchored** if every near piece $C$ admits (i) a complement matching with $L$ pairs, each having an endpoint in $\mathcal R^\star$, or (ii) a maximal complement matching with fewer than $L$ pairs, all of whose unmatched vertices belong to $\mathcal R^\star$.
--
--   **Formalization Note** The recursion carries fuel $n$, which is enough from $b_0\ge1$ to reach capacity $n$. Capacities at different vertices are independent, by the product measure on $\mathbb N^n$.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Step 1, p.75 (PDF 77); §5.10.1, p.77 (PDF 79); §5.10.3, p.79 (PDF 81)

import Mathlib
import Definitions.Def_StreamColour_GraphQuantities
import Definitions.Def_StreamColour_ACD
import Definitions.Def_StreamColour_Expansion

namespace StreamColour

open MeasureTheory

/-! # Random capacities, the recovered set, the anchored matchings

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), Step 1 of Algorithm B, p.75
(PDF 77): "start with capacity b(v) = b₀. Independently toss fair coins: on heads replace b(v) by min{2b(v), n};
on tails stop. Stop also when b(v) = n." §5.10.3, p.79 (PDF 81): `R⋆ = ⋃_i {v ∈ C_i : |C_i △ N_G[v]| ≤ b(v)}`.

**Formalization Note.** `capacityFrom` carries fuel. Starting from `b₀ ≥ 1`, the capacity reaches `n` within `n`
heads, so fuel `n` never truncates a run, and `capacityLaw` is the law printed in §5.10.1, p.77. Capacity vectors
are independent, by the product measure on `Fin n → ℕ`. The set `R⋆` runs over all pieces, near or far, and has
no colour sample in it. -/

/-- The capacity law from the current capacity `b`, with fuel. A fair coin is uniform on `Bool`. -/
noncomputable def capacityFrom (n : ℕ) : ℕ → ℕ → PMF ℕ
  | 0, b => PMF.pure b
  | f + 1, b =>
    if n ≤ b then PMF.pure b
    else (PMF.uniformOfFintype Bool).bind fun heads =>
      if heads then capacityFrom n f (min (2 * b) n) else PMF.pure b

/-- The law of one capacity started at `b₀`. -/
noncomputable def capacityLaw (n b₀ : ℕ) : PMF ℕ := capacityFrom n n b₀

/-- The law of the capacity vector: independent capacities at the `n` vertices. -/
noncomputable def capacityMeasure (n b₀ : ℕ) : Measure (Fin n → ℕ) :=
  Measure.pi fun _ => (capacityLaw n b₀).toMeasure

variable {V : Type} [Fintype V]

open Classical in
/-- `R⋆ = ⋃_i {v ∈ C_i : |C_i △ N_G[v]| ≤ b(v)}`. -/
noncomputable def Rstar (G : SimpleGraph V) (π : V → ℕ) (b : V → ℕ) : Finset V :=
  Finset.univ.filter fun v =>
    1 ≤ π v ∧ (symmDiff (piece π (π v)) (closedNbrs G v)).card ≤ b v

/-- The conclusion of Lemma 5.23 at the capacities `b`, with `L = 100h`: every near piece admits (i) a complement
matching with `L` pairs, each with an endpoint in `R⋆`, or (ii) a maximal complement matching with fewer than `L`
pairs, all of whose unmatched vertices belong to `R⋆`. -/
def AnchoredMatchings (A : ℝ) (h Δ : ℕ) (G : SimpleGraph V) (π : V → ℕ) (b : V → ℕ) : Prop :=
  ∀ i, 1 ≤ i → IsNear A h Δ (piece π i) →
    (∃ M, IsComplementMatching G (piece π i) M ∧ M.card = 100 * h ∧
      ∀ p ∈ M, p.1 ∈ Rstar G π b ∨ p.2 ∈ Rstar G π b) ∨
    (∃ M, IsMaximalCM G (piece π i) M ∧ M.card < 100 * h ∧
      ∀ v ∈ unmatched (piece π i) M, v ∈ Rstar G π b)

end StreamColour



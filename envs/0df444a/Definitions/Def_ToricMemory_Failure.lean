-- Prove2me | Definitions.Def_ToricMemory_Failure
-- name    : ToricMemory_Failure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:48.729719+00:00
-- url     : https://prove2.me/theorems/15f91b82-79ea-4282-9e99-8212071f56e4
-- title:
--   Recovery failure, failure probability and reliable storage
-- statement:
--   Let $D$ be a decoder and $E$ the error history, and write $E_{\min}=D(\partial E)$. The **$x$-winding count** of a chain $C$ is the number of its $x$-links that cross from $x=L-1$ to $x=0$; the $y$-winding count is defined in the same way. For a cycle these parities record how often it winds around the spatial torus.
--
--   1. Recovery **fails** on $E$ if $E+E_{\min}$ contains a cycle $C$ ($\partial C=\emptyset$) whose $x$-winding count or $y$-winding count is odd.
--   2. The **failure probability** is $\mathrm{Prob}_{\rm fail}(D)=\sum_{E}\mu_{p,q}(E)\,\mathbf 1[\text{recovery fails on }E]$.
--   3. Storage is **reliable** at $(p,q)$ if, for every number of time slices $T(L)\ge1$ growing at most polynomially, $T(L)\le C'L^{k'}$, and every $\varepsilon>0$, there is $L_0$ such that for all $L\ge\max(L_0,1)$ every maximum-likelihood decoder on the $L\times L\times T(L)$ lattice has $\mathrm{Prob}_{\rm fail}\le\varepsilon$. The threshold $L_0$ does not depend on the decoder.
--
--   The paper says the encoded information is damaged when $E+E_{\min}$ contains a homologically nontrivial path, and asks that $\mathrm{Prob}_{\rm fail}$ become arbitrarily small as $L$ grows with $T$ at most polynomial in $L$.
--
--   **Formalization Note** On the 3-torus a cycle winding only in time has no horizontal links and does not damage the encoded qubits, so "homologically nontrivial" is read as an odd spatial winding. The failure event contains the event that the homology class of $E+E_{\min}$ itself is spatially nontrivial, so a bound on it is at least as strong.
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, p. 20 ("The encoded quantum information is damaged if E + E_min contains homologically nontrivial paths"); Sec. V C, p. 20 ("Prob_fail becomes arbitrarily small as L gets large (with T increasing no faster than a polynomial of L)")

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder

open Finset

namespace ToricMemory

/-- The `x`-winding count of a chain: the number of its `x`-links that cross from `x = L − 1` to
`x = 0`. For a cycle, its parity is the parity of the number of times the cycle winds around the
`x`-direction of the spatial torus. -/
def xWind {L T : ℕ} (C : Finset (Link L T)) : ℕ :=
  (C.filter fun ℓ => ℓ.2 = 0 ∧ ℓ.1.1 = -1).card

/-- The `y`-winding count of a chain: the number of its `y`-links that cross from `y = L − 1` to
`y = 0`. -/
def yWind {L T : ℕ} (C : Finset (Link L T)) : ℕ :=
  (C.filter fun ℓ => ℓ.2 = 1 ∧ ℓ.1.2.1 = -1).card

/-- **Recovery failure**, arXiv:quant-ph/0110143v1, Sec. V B, p. 20: "The encoded quantum
information is damaged if `E + E_min` contains homologically nontrivial paths." Here
`E_min = D(∂E)`, and the event is that `E + E_min` contains a cycle `C` (a chain with empty
boundary) that winds an odd number of times around the spatial torus in the `x` or in the `y`
direction.

**Formalization Note** On the 3-torus a cycle winding only in time does not damage the
encoded information (it has no horizontal links, while p. 20 says a damaging path has at least
`L` of them), so "homologically nontrivial" is read as spatially nontrivial. The event contains
the event that the homology class of `E + E_min` itself is spatially nontrivial. -/
def Fails {L T : ℕ} [NeZero L] [NeZero T] (D : Finset (Site L T) → Finset (Link L T))
    (E : Finset (Link L T)) : Prop :=
  ∃ C ⊆ symmDiff E (D (boundary E)), boundary C = ∅ ∧ (Odd (xWind C) ∨ Odd (yWind C))

open Classical in
/-- The failure probability `Prob_fail` of the decoder `D` (arXiv:quant-ph/0110143v1,
Sec. V B, p. 20): the probability, under independent link errors (`chainProb p q`), that the
error history `E` makes recovery fail. -/
noncomputable def probFail {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ)
    (D : Finset (Site L T) → Finset (Link L T)) : ℝ :=
  ∑ E : Finset (Link L T), if Fails D E then chainProb p q E else 0

/-- **Reliable quantum storage** at error rates `p, q` (arXiv:quant-ph/0110143v1, Sec. V C,
p. 20): "`Prob_fail` becomes arbitrarily small as `L` gets large (with `T` increasing no faster
than a polynomial of `L`)". For every number of time slices `T(L) ≥ 1` bounded by a polynomial
`C' L^{k'}`, and every `ε > 0`, there is `L₀` such that for every `L ≥ max(L₀, 1)` every
maximum-likelihood decoder on the `L × L × T(L)` lattice fails with probability at most `ε`.
`L₀` does not depend on the decoder. -/
def ReliableStorage (p q : ℝ) : Prop :=
  ∀ (Tf : ℕ → ℕ) (C' : ℝ) (k' : ℕ),
    (∀ L : ℕ, 1 ≤ L → 1 ≤ Tf L ∧ (Tf L : ℝ) ≤ C' * (L : ℝ) ^ k') →
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, max L₀ 1 ≤ L →
      ∀ [NeZero L] [NeZero (Tf L)] (D : Finset (Site L (Tf L)) → Finset (Link L (Tf L))),
        IsMLDecoder p q D → probFail p q D ≤ ε

end ToricMemory



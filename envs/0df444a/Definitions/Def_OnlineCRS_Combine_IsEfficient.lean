-- Prove2me | Definitions.Def_OnlineCRS_Combine_IsEfficient
-- name    : OnlineCRS_Combine_IsEfficient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:24:57.934661+00:00
-- url     : https://prove2.me/theorems/d511c70a-58bc-421d-9f20-bc489c86b11b
-- title:
--   Efficient greedy OCRS (Definition 1.7)
-- statement:
--   A greedy OCRS $\pi$ is **efficient** if there is a polynomial-time algorithm that, for a given input $x$, samples an efficient independence oracle for $\mathcal F_{\pi,x}$, that is, an oracle that answers queries "is $S\subseteq N$ in $\mathcal F_{\pi,x}$?" in polynomial time.
--
--   Precisely, for a family of greedy OCRSs $\pi_i$ (instance $i$ on ground set $\{0,\dots,n_i-1\}$ with description $\mathrm{code}_i$) and sets $P_i$, the family is efficient if there are
--   1. a polynomial-time Turing machine computing a number $m(i,x)\in\mathbb N$ from $(i,x)$, and
--   2. a polynomial-time Turing machine computing a Boolean $D(i,x,r,S)$,
--
--   such that for every instance $i$ and every rational $x\in P_i$, the law of $\mathcal F_{\pi_i,x}$ equals the law of the family
--   $$\{S\subseteq N : D(i,x,r,S)=\mathrm{true}\},\qquad r \text{ uniform on } \{0,1,\dots,m(i,x)\}.$$
--   The sampled oracle is $S\mapsto D(i,x,r,S)$.
--
--   **Formalization Note**
--   1. Machines are Mathlib's `Turing.TM2ComputableInPolyTime` with the fixed binary input encodings of this mission and Mathlib's binary output encodings of $\mathbb N$ and of Booleans.
--   2. Inputs $x$ are rational, as an algorithm's input is finite; the requirement applies to $x\in P_i$, as for an OCRS for $P_i$.
--   3. Randomness is one uniform draw from a computed range rather than fair coins only: the paper counts its knapsack OCRS, which flips a coin of rational bias, as efficient.
--   4. The definition is for instance families; a one-element index set is the paper's single relaxation $P$.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7, p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS
import Definitions.Def_OnlineCRS_Combine_encSampler
import Definitions.Def_OnlineCRS_Combine_encQuery

namespace OnlineCRS.Combine

/-- **Efficient greedy OCRS (Definition 1.7).**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4: "A greedy OCRS `π` is efficient if there exists a polynomial time
algorithm that, for a given input `x`, samples an efficient independence oracle for the set
`F_{π,x}`. That is, an oracle that answers in polynomial time queries of the form: is a set
`S ⊆ N` in `F_{π,x}`?"

`IsEfficient n code P π` holds for a family of greedy OCRSs `π i` (instance `i` on ground set
`Fin (n i)`, described by `code i`) if there are
1. a polynomial-time Turing machine computing a number `m(i, x)` from `(i, x)`, and
2. a polynomial-time Turing machine computing a Boolean `D(i, x, r, S)`,
such that for every instance `i` and every rational `x` with `x ∈ P i`, the law of `F_{π i,x}`
equals the law of `{S | D(i, x, r, S) = true}` for `r` uniform on `{0, …, m(i, x)}`. The
sampled oracle is `S ↦ D(i, x, r, S)`.

**Formalization Note.** Reading 6:
* machines are `Turing.TM2ComputableInPolyTime` over the fixed binary encodings `encSampler`,
  `encQuery` (input) and `Computability.encodeNat`, `Computability.encodeBool` (output); the
  structure is data, so it is asserted with `Nonempty`;
* inputs `x` are rational (an algorithm's input is finite), and the requirement is for `x` with
  `x ∈ P i`, as for an OCRS for `P`;
* randomness is one uniform draw from a computed range `{0, …, m}` (not fair coins only): the
  paper counts its knapsack OCRS, which flips a coin of rational bias, as efficient;
* instance families indexed by `ι` (generalization): `ι = Unit` is the paper's single `P`. -/
def IsEfficient {ι : Type} (n : ι → ℕ) (code : ι → List Bool)
    {F : ∀ i, Finset (Finset (Fin (n i)))} (P : ∀ i, Set (Fin (n i) → ℝ))
    (π : ∀ i, GreedyOCRS (F i)) : Prop :=
  ∃ (m : (Σ i, Fin (n i) → ℚ) → ℕ)
    (D : (Σ i, (Fin (n i) → ℚ) × ℕ × Finset (Fin (n i))) → Bool),
    Nonempty (Turing.TM2ComputableInPolyTime (encSampler n code) Computability.encodeNat m) ∧
    Nonempty (Turing.TM2ComputableInPolyTime (encQuery n code) Computability.encodeBool D) ∧
    ∀ i (x : Fin (n i) → ℚ), (fun j => (x j : ℝ)) ∈ P i →
      (π i).law (fun j => (x j : ℝ)) =
        (PMF.uniformOfFintype (Fin (m ⟨i, x⟩ + 1))).map
          (fun r => Finset.univ.filter fun S => D ⟨i, x, (r : ℕ), S⟩ = true)

end OnlineCRS.Combine



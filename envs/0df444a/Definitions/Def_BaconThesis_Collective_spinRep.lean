-- Prove2me | Definitions.Def_BaconThesis_Collective_spinRep
-- name    : BaconThesis_Collective_spinRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:22.523851+00:00
-- url     : https://prove2.me/theorems/5eb85c62-1760-4dab-ba1c-ae623b050123
-- title:
--   The spin-$J$ representation $S_\alpha(2J+1)$ of $\mathfrak{su}(2)$
-- statement:
--   For $d=2J\in\mathbb N$, the **standard $(2J+1)$-dimensional representation** of $\mathfrak{su}(2)$ acts on the basis $|m\rangle$, $m=J,J-1,\dots,-J$, by
--   $$
--   S_z|m\rangle=m|m\rangle,\qquad S_+|m\rangle=\sqrt{(J-m)(J+m+1)}\,|m+1\rangle,\qquad S_-|m\rangle=\sqrt{(J+m)(J-m+1)}\,|m-1\rangle,
--   $$
--   with $S_-=S_+^\dagger$, $S_x=\tfrac12(S_++S_-)$ and $S_y=\tfrac1{2i}(S_+-S_-)$. These are the matrices $S_\alpha(2J+1)$ of (8.43), with the ladder normalization of (8.50). For $J=\tfrac12$ they are $\tfrac12\sigma_\alpha$.
--
--   **Formalization Note** $J$ is encoded by $d=2J$, and the basis index $k\in\{0,\dots,d\}$ stands for $m=J-k$ (decreasing $m$).
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.43), §8.6, p.118 (PDF p.135); normalization of (8.50), p.121 (PDF p.138)

import Mathlib
import Definitions.Def_BBPSSW_Distill_Axis

open scoped Matrix

namespace BaconThesis.Collective

/-- **The `(2J+1)`-dimensional representation `S_α(2J+1)` of `su(2)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.43), §8.6, p.118 (PDF p.135): "`S_α(2J+1)` is the `2J+1` dimensional representation of
`su(2)`", in the standard angular momentum basis `|m⟩`, `m = J, J−1, …, −J`, with the ladder action
of (8.50), p.121 (PDF p.138).

Here `d = 2J`. The basis index `k ∈ {0, …, d}` stands for `m = J − k`. With the raising matrix
`S_+|m⟩ = √((J − m)(J + m + 1)) |m + 1⟩`, i.e. `⟨k−1|S_+|k⟩ = √(k(d − k + 1))`, and
`S_− = S_+†`,

* `spinRep d .x = S_x = (S_+ + S_−)/2`,
* `spinRep d .y = S_y = (S_+ − S_−)/(2i)`,
* `spinRep d .z = S_z = diag(J, J−1, …, −J)`.

Then `S_−|m⟩ = √((J + m)(J − m + 1)) |m − 1⟩`, the normalization of (8.50).

**Formalization Note.** `J` is encoded by `d = 2J ∈ ℕ` (no half-integers), and the basis is
ordered by decreasing `m`. For `d = 1` the matrices are `σ_α / 2`. -/
noncomputable def spinRep (d : ℕ) (α : BBPSSW.Distill.Axis) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  let Sp : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.of fun j k =>
    if j.val + 1 = k.val then
      ((Real.sqrt ((k.val : ℝ) * ((d : ℝ) - k.val + 1)) : ℝ) : ℂ)
    else 0
  match α with
  | .x => (1 / 2 : ℂ) • (Sp + Spᴴ)
  | .y => (-(Complex.I / 2)) • (Sp - Spᴴ)
  | .z => Matrix.diagonal fun k => ((d : ℂ) / 2 - (k.val : ℂ))

end BaconThesis.Collective



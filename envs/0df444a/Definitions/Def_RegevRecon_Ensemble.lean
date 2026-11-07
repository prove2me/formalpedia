-- Prove2me | Definitions.Def_RegevRecon_Ensemble
-- name    : RegevRecon_Ensemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:58.678002+00:00
-- url     : https://prove2.me/theorems/042c6c29-d890-47cb-a073-d2d4c27e20d7
-- title:
--   The random regular ensemble $\mathbb G_{\mathrm{reg}}(n,k,D,p,S,\Lambda)$
-- statement:
--   The ensemble draws $\bar B$ uniformly from the $\{0,1\}$-valued $m\times n$ matrices with exactly $D$ ones in each column and $k$ ones in each row, with $m=nD/k$. It fills the $D$ nonzero entries of each column with an independent draw from $\Lambda$, and draws the offsets $\tau_1,\dots,\tau_m$ independently and uniformly from $\mathbb F_p$.
--
--   **Formalization Note** The probability of an event is a finite sum, which needs no nonemptiness proof: on an empty matrix set it is $0$, which happens only at finitely many $n$. The coordinates of a column's tuple are assigned to its ones in increasing row order, and exchangeability makes the order immaterial.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §2, p.3; Definition 2, p.4

import Mathlib
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- The `{0,1}`-valued `m × n` matrices with exactly `D` ones in each column and `k` in each row,
Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), §2, p.3. -/
def biregular (k D m n : ℕ) : Finset (Matrix (Fin m) (Fin n) Bool) :=
  univ.filter fun Bbar =>
    (∀ i, (univ.filter fun j => Bbar i j = true).card = k) ∧
      ∀ j, (univ.filter fun i => Bbar i j = true).card = D

/-- **Filling a graph with coefficients**, Definition 2, p.4: `B_ij = 0` where `B̄_ij = 0`; otherwise the
`r`-th coordinate of the column tuple `c_j`, `r` the rank of row `i` among the ones of column `j`, in
increasing row order. (The value `0` for a rank `≥ D` is never read on `biregular`.) -/
def fillMatrix {D m n : ℕ} (Bbar : Matrix (Fin m) (Fin n) Bool)
    (c : Fin n → Fin D → (ZMod p)ˣ) : Matrix (Fin m) (Fin n) (ZMod p) :=
  fun i j =>
    if Bbar i j = true then
      (let r := (univ.filter fun i' => i' < i ∧ Bbar i' j = true).card
       if h : r < D then (((c j ⟨r, h⟩) : (ZMod p)ˣ) : ZMod p) else 0)
    else 0

open Classical in
/-- **The ensemble probability** of an event on `(B, τ)`, `𝔾_reg(n, k, D, p, S, Λ)`, Definition 2, p.4:
`B̄` uniform on `biregular`, independent column tuples `c_j ∼ Λ`, independent uniform offsets `τ_j`.

**Formalization Note** The finite sum needs no nonemptiness proof: on an empty `biregular` every event
has probability `0`, which occurs only at finitely many `n` (those with `n < k`). The exchangeability of
`Λ` makes the increasing row order immaterial. -/
noncomputable def instanceProb {D : ℕ} (k m n : ℕ) (Λ : PMF (Fin D → (ZMod p)ˣ))
    (E : Matrix (Fin m) (Fin n) (ZMod p) → (Fin m → ZMod p) → Prop) : ℝ :=
  ∑ Bbar ∈ biregular k D m n, ∑ c : Fin n → Fin D → (ZMod p)ˣ, ∑ τ : Fin m → ZMod p,
    ((biregular k D m n).card : ℝ)⁻¹ * (∏ j, (Λ (c j)).toReal) * ((p : ℝ) ^ m)⁻¹ *
      (if E (fillMatrix Bbar c) τ then 1 else 0)

/-- The average of `f(B)` over the graph and the coefficients of the ensemble (no offsets), as in the
block error of Proposition 2, p.15 and (40), p.16. -/
noncomputable def graphAverage {D : ℕ} (k m n : ℕ) (Λ : PMF (Fin D → (ZMod p)ˣ))
    (f : Matrix (Fin m) (Fin n) (ZMod p) → ℝ) : ℝ :=
  ∑ Bbar ∈ biregular k D m n, ∑ c : Fin n → Fin D → (ZMod p)ˣ,
    ((biregular k D m n).card : ℝ)⁻¹ * (∏ j, (Λ (c j)).toReal) * f (fillMatrix Bbar c)

end RegevRecon



-- Prove2me | Definitions.Def_ExactAmpDich_Coord
-- name    : ExactAmpDich_Coord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:33.235921+00:00
-- url     : https://prove2.me/theorems/880010d7-3ac1-49da-a5ae-f64b99ff2aed
-- title:
--   Coordinates $\alpha$ of a library, the relation ideal $I$ (35), standard monomials and the normal form $\mathrm{NF}_I$
-- statement:
--   Let $\alpha=(\alpha_1,\dots,\alpha_s)\in\mathbb R^s$ list the real and imaginary parts of all entries of all gates of a library $G$, with their matrix positions recorded; a variable order is an enumeration of these positions as $X_1,\dots,X_s$. The **relation ideal** is the full kernel of evaluation
--
--   $$I=\{p\in\mathbb Q[X_1,\dots,X_s]: p(\alpha)=0\}. \tag{35}$$
--
--   Under graded lexicographic order, a monomial is **standard** if it is not divisible by the leading monomial of any nonzero element of $I$. For a value $v\in\mathbb Q[\alpha]$, the **normal form** $\mathrm{NF}_I(v)$ is the unique rational polynomial supported on standard monomials whose value at $\alpha$ is $v$; equivalently, the remainder of any representative $p$ with $p(\alpha)=v$ on division by a Gröbner basis of $I$, so that $p(\alpha)=q(\alpha)\iff \mathrm{NF}_I(p)=\mathrm{NF}_I(q)$.
--
--   For a real tuple $\beta$ indexed by the same positions, the **specialized library** $G_\beta$ has the same gate shapes, with each entry replaced by $\beta(\mathrm{re})+i\,\beta(\mathrm{im})$.
--
--   This is the exact-output convention of the paper for arbitrary complex gate entries.
--
--   **Formalization Note** The variable order is an enumeration $e$ of the coordinate positions by $\mathrm{Fin}\,s$; graded lexicographic order is Mathlib's `MonomialOrder.degLex` ($X_0>X_1>\cdots$ within a degree). The normal form is chosen from the value by `Classical.epsilon`; its uniqueness is proved in the mission's sanity file.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), §1.1, p.2 (PDF p.3); App. G.1, Eq. (35), pp.51–52 (PDF pp.52–53); Lemma G.6, p.54 (PDF p.55) for G_β

import Mathlib
import Definitions.Def_ExactAmpDich_Library

set_option autoImplicit false

namespace ExactAmpDich

open QAlgorithms

/-- The **coordinate positions** of a library: one for the real part and one for the imaginary
part of every matrix entry `(y, x)` of every gate `j` (`false` = real part, `true` = imaginary
part). Liu–Meng, App. G.1, p.51 (PDF p.52): "Let α = (α1, . . . , αs) ∈Rs list the real and
imaginary parts of the gate entries, with their matrix positions recorded." -/
abbrev Library.Coord (L : Library) := Σ j : Fin L.t, Qubits (L.k j) × Qubits (L.k j) × Bool

/-- The real coordinate tuple `α` of the library: the real or imaginary part of the entry at each
coordinate position. -/
noncomputable def Library.alpha (L : Library) : L.Coord → ℝ
  | ⟨j, y, x, b⟩ => if b then (L.U j y x).im else (L.U j y x).re

/-- The **specialized library** `G_β`: the same gate shapes, with every entry replaced by
`β(re) + i β(im)` at its coordinate positions. Liu–Meng, Lemma G.6, p.54 (PDF p.55). Note
`L.specialize L.alpha = L` entrywise. -/
def Library.specialize (L : Library) (β : L.Coord → ℝ) : Library where
  t := L.t
  k := L.k
  one_le_k := L.one_le_k
  U j y x := ⟨β ⟨j, y, x, false⟩, β ⟨j, y, x, true⟩⟩

/-- The **full relation ideal** `I = {p ∈ ℚ[X₁, …, X_s] : p(α) = 0}` (35) of the coordinates,
with the variables `X₀, …, X_{s-1}` attached to coordinate positions by an enumeration
`e : L.Coord ≃ Fin s` (the "fixed variable order"). Liu–Meng, §1.1, p.2: "We reduce modulo the
full relation ideal Iα"; App. G.1, Eq. (35), p.51: "The ideal I is the full kernel of
evaluation".

**Formalization Note.** `I` is the whole kernel of evaluation at `α`, not the ideal of a chosen
generating set. -/
noncomputable def relIdeal (L : Library) {s : ℕ} (e : L.Coord ≃ Fin s) :
    Ideal (MvPolynomial (Fin s) ℚ) :=
  RingHom.ker (MvPolynomial.aeval (fun i => L.alpha (e.symm i)) :
    MvPolynomial (Fin s) ℚ →ₐ[ℚ] ℝ).toRingHom

/-- A monomial `m` is **standard** for the ideal `I` under graded lexicographic order: it is not
divisible by the leading monomial of any nonzero `p ∈ I`. Liu–Meng, App. G.1, p.52 (PDF p.53):
"the standard monomials, namely those not divisible by a leading monomial of the basis".

**Formalization Note.** The order is Mathlib's `MonomialOrder.degLex` on `Fin s` (total degree
first, ties broken lexicographically with `X₀ > X₁ > ⋯`); divisibility of monomials is the
pointwise order `≤` on exponent vectors. For a Gröbner basis of `I` the leading monomials of the
basis and of all nonzero elements of `I` generate the same monomial ideal, so this is the
paper's notion. -/
def IsStandard {s : ℕ} (I : Ideal (MvPolynomial (Fin s) ℚ)) (m : Fin s →₀ ℕ) : Prop :=
  ∀ p ∈ I, p ≠ 0 → ¬ (MonomialOrder.degLex.degree p ≤ m)

/-- The **normal form** `NF_I` of a real value `v ∈ ℚ[α]`: the unique rational polynomial
supported on standard monomials whose value at `α` is `v`. Liu–Meng, App. G.1, p.52: "Polynomial
division gives the unique remainder NFI(p) supported on the standard monomials … In particular,
p(α) = q(α) ⇐⇒ NFI(p) = NFI(q)."

**Formalization Note.** The normal form is defined from the value, which by the quoted
equivalence is the same as reducing any representative `p` with `p(α) = v`. It is chosen by
`Classical.epsilon`; uniqueness is proved in the mission's sanity checks, and existence for every
`v ∈ ℚ[α]` is the division theorem. For `v ∉ ℚ[α]` the value is unspecified, but every real and
imaginary part of an amplitude lies in `ℚ[α]`. -/
noncomputable def nf (L : Library) {s : ℕ} (e : L.Coord ≃ Fin s) (v : ℝ) :
    MvPolynomial (Fin s) ℚ :=
  Classical.epsilon (fun r : MvPolynomial (Fin s) ℚ =>
    MvPolynomial.aeval (fun i => L.alpha (e.symm i)) r = v ∧
      ∀ m ∈ r.support, IsStandard (relIdeal L e) m)

end ExactAmpDich



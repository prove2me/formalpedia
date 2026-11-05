-- Prove2me | Definitions.Def_MayersQKD_Bits
-- name    : MayersQKD_Bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:36.245117+00:00
-- url     : https://prove2.me/theorems/117b49b5-cdc2-4d67-9b6a-057214ab5512
-- title:
--   Strings, bases, photon space, $N=\lfloor .24n\rfloor$, $d_E$, $w[E]$ and the matrix $f$
-- statement:
--   The basic data of the String-QOT protocol. Strings in $\{0,1\}^n$ form the vector space $\mathrm{GF}(2)^n$, with $\oplus$ the coordinatewise sum. A string of bases is an element of $\{+,\times\}^n$, and the $n$ photons live in the Hilbert space spanned by the computational basis indexed by $\{0,1\}^n$, with $|\psi_{w,\theta}\rangle$ the product BB84 state.
--
--   The module also fixes the block length $N=\lfloor .24n\rfloor$, the distance on a set of positions
--
--   $$
--   d_E(\alpha,\alpha')=\#\{i\in E\mid \alpha_i\ne\alpha'_i\},
--   $$
--
--   the restricted string $w[E]$, the bits $w[\bar E]$ announced at the end of the protocol, and the type of the $(r+m)\times N$ boolean matrix $f$, whose first $r$ rows form $g$ and following $m$ rows form $h$.
--
--   These are the common vocabulary of every statement in the mission.
--
--   **Formalization Note** A basis is a Boolean (`false` is $+$, `true` is $\times$) and bits are elements of $\mathbb Z/2$. Positions $1,\dots,n$ are `Fin n`, a shift by one. $w[E]$ reads $E$ in increasing position order; the paper fixes no order, and another one only permutes the columns of the uniform matrix $f$. $w[\bar E]$ is stored as the string equal to $w$ off $E$ and $0$ on $E$; the view always contains $E$. The rows of $f$ are indexed by `Fin r ⊕ Fin m`.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §3 p.5, §4 p.6, §5 p.7, §6 p.8, §7 p.9

import Mathlib
import Definitions.Def_MayersBC_bb84State

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §3, p.5: boolean strings of length `n`, the vector space
`GF(2)ⁿ` with `⊕` the coordinatewise sum mod 2.

**Formalization Note.** Bits are `ZMod 2`, so `⊕` is `+`. Positions `1, …, n` of the page are
`Fin n` (position `i` of the page is `i - 1` here). -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- Mayers, arXiv:quant-ph/9606003v1, §4, p.6: strings of bases `θ ∈ {+, ×}ⁿ`.

**Formalization Note.** `false` is `+`, `true` is `×`, the convention of `MayersBC.bb84Amp`. -/
abbrev Bases (n : ℕ) : Type := Fin n → Bool

/-- Mayers, arXiv:quant-ph/9606003v1, §4, p.6: the state space of `n` photons, with the
computational basis indexed by `{0, 1}ⁿ`. `MayersBC.bb84State θ w` is `|ψ_{w,θ}⟩`. -/
abbrev Photons (n : ℕ) : Type := EuclideanSpace ℂ (Bits n)

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7: `N = ⌊.24 n⌋`, the length of the string shared
between Alice and Bob before privacy amplification. -/
noncomputable def blockLen (n : ℕ) : ℕ := ⌊(0.24 : ℝ) * n⌋₊

/-- Mayers, arXiv:quant-ph/9606003v1, §7, p.9: `d_E(α, α′) = #{i ∈ E | αᵢ ≠ α′ᵢ}`. -/
def posDist {n : ℕ} (E : Finset (Fin n)) (α α' : Bits n) : ℕ :=
  (E.filter fun i => α i ≠ α' i).card

/-- Mayers, arXiv:quant-ph/9606003v1, §4, p.6: the string `w[E]`, with `w[E]ᵢ = w_{γᵢ}` for
`E = {γ₁, …, γ_N}`.

**Formalization Note.** `E` is read in increasing position order (`Finset.orderEmbOfFin`). The
paper fixes no order; another one only permutes the columns of the uniform matrix `f`. When
`E` does not have `N` elements the value is the zero string; the protocol only uses sets of
size `N`. -/
noncomputable def restrictTo {n : ℕ} (N : ℕ) (E : Finset (Fin n)) (w : Bits n) : Bits N :=
  fun i => if h : E.card = N then w (E.orderEmbOfFin h i) else 0

/-- Mayers, arXiv:quant-ph/9606003v1, §6, p.8: the announcement `w[Ē_c]`, as the string that
agrees with `w` off `E` and vanishes on `E`.

**Formalization Note.** `Ē` is the complement of `E` in `{1, …, n}`, see (1) and the line
`w′[Ē_c] = w[Ē_c]` on p.10. The view always contains `E`, so this string carries exactly the
bits `w[Ē]`. -/
noncomputable def offBlock {n : ℕ} (E : Finset (Fin n)) (w : Bits n) : Bits n := by
  classical exact fun i => if i ∈ E then 0 else w i

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7, step 1: the `(r + m) × N` boolean matrix `f`,
whose `r` first rows are the matrix `g` used for error correction and whose `m` following rows
are the matrix `h` used for privacy amplification.

**Formalization Note.** The rows are indexed by `Fin r ⊕ Fin m`: the `Sum.inl` rows are `g`, the
`Sum.inr` rows are `h`. -/
abbrev HashMatrix (r m N : ℕ) : Type := Matrix (Fin r ⊕ Fin m) (Fin N) (ZMod 2)

end MayersQKD



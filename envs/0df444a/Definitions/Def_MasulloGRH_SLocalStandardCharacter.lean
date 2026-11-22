-- Prove2me | Definitions.Def_MasulloGRH_SLocalStandardCharacter
-- name    : MasulloGRH_SLocalStandardCharacter
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T10:48:59.332158+00:00
-- url     : https://prove2.me/theorems/fab74d1e-e2cb-4ce9-bc3a-67d5949c194b
-- title:
--   Example A.3.1.11, eq. (A.3.1.9) — the standard additive character $\psi_{S,\mathrm{std}}=\bigotimes_{v\in S}\psi_v$ of the $S$-adeles $\mathbb A_{F,S}$
-- statement:
--   **The standard additive character of the $S$-adeles** (Example A.3.1.11, eq. (A.3.1.9) of the source).
--
--   Let $F$ be a number field. Let $S$ be a finite set of places of $F$ containing all archimedean places and $S_f\subset S$ the set of its finite places. Write
--   $$\mathbb A_{F,S}=\prod_{v\in S}F_v,\qquad \mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times,\qquad |g|_{F,S}=\prod_{v\in S}|g_v|_v$$
--   for the ring of $S$-adeles (with the product topology), the group of $S$-ideles and the $S$-idelic norm, and
--   $$\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\ \text{for every place }v\notin S\}$$
--   for the ring of $S$-integers, embedded diagonally in $\mathbb A_{F,S}$ as a discrete cocompact subgroup.
--
--   For a place $v$ of $F$ the **standard additive character** $\psi_v\colon F_v\to\mathrm U(1)$ is
--   $$\psi_w(x)=\exp\big(-2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)\big)\ \ (w\mid\infty),\qquad \psi_v(x)=\exp\big(2\pi i\,\{\mathrm{Tr}_{F_v/\mathbb Q_p}(x)\}_p\big)\ \ (v\mid p),$$
--   where $\{\cdot\}_p\colon\mathbb Q_p\to\mathbb Q_p/\mathbb Z_p\subset\mathbb R/\mathbb Z$ is the $p$-adic fractional part. These are the local components of the standard character $\psi_{F,\mathrm{std}}=\psi_{\mathbb Q,\mathrm{std}}\circ\mathrm{Tr}$ of the adele ring $\mathbb A_F$, which is trivial on $F$. The file defines `sStdCharacter Sf`, the **standard additive character of $\mathbb A_{F,S}$**
--   $$\psi_{S,\mathrm{std}}=\bigotimes_{v\in S}\psi_v,\qquad \psi_{S,\mathrm{std}}(x)=\prod_{v\in S}\psi_v(x_v)\quad(x\in\mathbb A_{F,S}).$$
--
--   It is computed as follows. By strong approximation every $x\in\mathbb A_{F,S}$ is congruent to an $S$-integer at the finite places of $S$: there is $\xi\in\mathcal O_{F,S}$ with $x_v-\xi\in\mathcal O_{F_v}$ for all $v\in S_f$. For any such $\xi$,
--   $$\psi_{S,\mathrm{std}}(x)=\exp\Big(-2\pi i\sum_{w\mid\infty}\mathrm{Tr}_{F_w/\mathbb R}(x_w-\xi)\Big),\qquad \mathrm{Tr}_{F_w/\mathbb R}(y)=\begin{cases}y,&F_w\simeq\mathbb R,\\ 2\,\mathrm{Re}(y),&F_w\simeq\mathbb C,\end{cases}$$
--   and the right-hand side does not depend on $\xi$, since two choices differ by an element of $\mathcal O_F$, whose trace to $\mathbb Q$ is an integer. (Indeed each $\psi_v$, $v$ finite, is trivial on $\mathcal O_{F_v}$, and $\prod_{v\in S}\psi_v(\xi)=\prod_{v\notin S}\psi_v(\xi)^{-1}=1$ for $\xi\in\mathcal O_{F,S}$ because $\psi_{F,\mathrm{std}}$ is trivial on $F$.)
--
--   The character $\psi_{S,\mathrm{std}}$ identifies $\mathbb A_{F,S}$ with its Pontryagin dual via the pairing $\langle x,y\rangle_S=\psi_{S,\mathrm{std}}(xy)$ of (A.3.1.10); it is the character defining the $S$-local Fourier transform of the source, for which the $S$-local Tamagawa measure $\nu_S$ is self-dual and the lattice $\mathcal O_{F,S}$ is its own annihilator when $S$ contains the ramified places.
--
--   **Deviation from the source.** Examples A.3.1.5–A.3.1.8 print the local characters with the same sign at the real and at the $p$-adic places ($e^{2\pi i x}$ and $e^{2\pi i\{x\}_p}$); their product is then not trivial on $\mathbb Q$ (it takes the value $e^{4\pi i/3}$ on $1/3$), and the self-annihilation of $\mathcal O_{F,S}$ asserted in Example A.3.1.11 fails. The definition uses the convention of Tate's thesis, with opposite signs at the archimedean and the finite places, as the platform definition `MasulloGRH.stdAdelicCharacter` of $\psi_{F,\mathrm{std}}$ does: `sStdCharacter Sf x` is the value of that character on the adele obtained from $x$ by putting $0$ at the places outside $S$.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. The value is the complex number given by the displayed formula for a chosen $\xi$ (`Classical.choose`); the alternative branch of the definition (value $1$ if no such $\xi$ exists) never occurs. $\mathrm{Tr}_{F_w/\mathbb R}(y)$ is `w.mult * (InfinitePlace.Completion.extensionEmbedding w y).re`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 558–559, Example A.3.1.11, eq. (A.3.1.9), with the local standard characters of Examples A.3.1.5–A.3.1.10, pp. 557–558

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles

/-!
# The standard additive character of the `S`-adeles

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix A, §A.3.1.1,
Example A.3.1.11, eq. (A.3.1.9) (pp. 558–559), with the local standard characters of
Examples A.3.1.5–A.3.1.10 (pp. 557–558) in the sign convention of Tate's thesis (see below).

As in `MasulloGRH.SAdeleRing`, a finite set `S` of places containing all archimedean places is
represented by the finite set `Sf` of its finite places.
-/

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The standard additive character `ψ_{S,std} = ⊗_{v ∈ S} ψ_v` of `𝔸_{F,S}` (A.3.1.9), where
`ψ_w(x) = exp(-2πi Tr_{F_w/ℝ}(x))` at an infinite place `w` and
`ψ_v(x) = exp(2πi {Tr_{F_v/ℚ_p}(x)}_p)` at a finite place `v` above `p` (`{·}_p` is the `p`-adic
fractional part); these are the local components of the standard character
`ψ_{F,std} = ψ_{ℚ,std} ∘ Tr` of `𝔸_F`, which is trivial on `F`
(`MasulloGRH.stdAdelicCharacter`).

Every `S`-adele `x` is congruent to an `S`-integer `ξ ∈ 𝒪_{F,S}` modulo `∏_{v ∈ S_f} 𝒪_{F_v}` at the
finite places of `S`, i.e. `x_v - ξ ∈ 𝒪_{F_v}` for all `v ∈ S_f`, and then
`ψ_{S,std}(x) = exp(-2πi ∑_{w ∣ ∞} Tr_{F_w/ℝ}(x_w - ξ))`;
the value does not depend on the choice of `ξ`, because two choices differ by an element of `𝒪_F`,
whose trace is an integer.  Here `Tr_{F_w/ℝ}(y) = mult(w) · Re(y)`. -/
def sStdCharacter (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf) : ℂ :=
  if h : ∃ ξ : F, ξ ∈ SIntegers (F := F) Sf ∧
      ∀ v : Sf, (x - sDiagonal Sf ξ).2 v ∈
        (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F then
    Complex.exp (-(2 * Real.pi * Complex.I) *
      ∑ w : InfinitePlace F,
        (w.mult : ℂ) *
          ((InfinitePlace.Completion.extensionEmbedding w
            ((x - sDiagonal Sf h.choose).1 w)).re : ℂ))
  else 1

end

end MasulloGRH



-- Prove2me | Definitions.Def_BosonicResources_IsClassical
-- name    : BosonicResources_IsClassical
-- status  : Definition
-- author  : @Senrui Chen
-- created : 2026-11-27T05:24:50.953814+00:00
-- url     : https://prove2.me/theorems/6a2739cf-5ac5-5e02-ae6d-ae9fc9341835
-- title:
--   Classical measurements: POVMs all of whose elements have non-negative Wigner functions
-- statement:
--   Let $E$ be a POVM on $N$ copies of an $n$-mode bosonic system (Hilbert space $\ell^2((\mathbb N^n)^N)$, with Fock basis $\lvert u\rangle$, $u=(u_1,\dots,u_N)$, $u_t\in\mathbb N^n$), with outcomes in a measurable space $\mathcal O$. Write $E(B)$ for the POVM element of a measurable set $B\subseteq\mathcal O$.
--
--   **Wigner function of a bounded operator.** A bounded measurable function $W_A$ on the $N$-copy phase space $(\mathbb R^{2n})^N$ is the Wigner function of an operator $A$ if, for all Fock states $u,v$,
--
--   $$
--   \langle u\rvert A\lvert v\rangle=(2\pi)^{nN}\int_{(\mathbb R^{2n})^N} W_A(r)\,\prod_{t=1}^{N}W_{\lvert v_t\rangle\langle u_t\rvert}(r_t)\,dr ,\qquad r=(r_1,\dots,r_N),
--   $$
--
--   where $W_{\lvert v_t\rangle\langle u_t\rvert}$ is the one-copy Wigner function of the Fock matrix unit $\lvert v_t\rangle\langle u_t\rvert$ and $dr$ is Lebesgue measure. This is the formula $\operatorname{Tr}(\rho\hat O)=(2\pi)^{n}\int d^{2n}r\,W_\rho(r)W_{\hat O}(r)$ of Sec. 2, with $\rho$ replaced by the matrix unit $\lvert v\rangle\langle u\rvert$ and $\hat O$ by $A$. Two kinds of Wigner functions appear in it: $W_A$, the Wigner function of the operator in question, and the $W_{\lvert v_t\rangle\langle u_t\rvert}$, the Wigner functions of the Fock matrix units, which are fixed test functions (complex-valued in general, and not non-negative unless $u_t=v_t=0$).
--
--   **Classical measurement.** The POVM $E$ is a *classical measurement* if, for every measurable set $B$ of outcomes, the element $E(B)$ has a Wigner function $W_{E(B)}$ with $W_{E(B)}(r)\ge 0$ for all $r$. Non-negativity is asked of the Wigner functions of the POVM elements only.
--
--   This is the paper's definition: "We refer to a POVM as a classical measurement if every element of it has a non-negative Wigner function." It is the hypothesis of the $\Omega(n^3/\varepsilon^2)$ lower bound (Theorem 2, Theorem S3) and of Lemma C.2.
--
--   **Formalization Note** The POVM is an operator-valued measure $B\mapsto E(B)$, so "every element" is "$E(B)$ for every measurable $B$"; for a discrete POVM $\{M_x\}$ this is the same as asking it of every $M_x$, since $E(B)=\sum_{x\in B}M_x$. An operator that is bounded but not trace class need not have a Wigner function given by the Fourier formula of Sec. 2, so "$A$ has Wigner function $W_A$" is stated through the pairing with the (Schwartz) Wigner functions of the Fock matrix units, which converges absolutely for bounded $W_A$ and determines $W_A$ up to a null set. The Wigner function is asked to be a bounded function. This excludes no POVM: $E(B)$ and $E(B^{c})=I-E(B)$ both have non-negative Wigner functions, and they add up to the Wigner function $(2\pi)^{-nN}$ of the identity (footnote 5), so $0\le W_{E(B)}\le(2\pi)^{-nN}$ almost everywhere. The numbers $(2\pi)^{nN}W_{E(B)}(r)$ are the conditional probabilities $p(x\mid\alpha)$ of Lemma C.2; that they form a Markov kernel, with which the measurement is simulated from samples of the Wigner distribution, is the content of that lemma and is not part of this definition. In Lean the two notions are `HasWignerFunction A w` and `IsClassical E`, where the variable `w` (written $w$, $w_B$ in the read-back) is the function called $W_A$, $W_{E(B)}$ here; $E$ is a `BosonicLearn.FockPOVM` and the one-copy Wigner functions are `fockWigner (v t) (u t)`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (classical measurements); Sec. 3.2, Theorem 2; App. C.1, Theorem S3, Lemma C.2, Eq. (S57) and footnote 5

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_BosonicResources_fockWigner

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn (FockPOVM)

open MeasureTheory ProbabilityTheory

namespace BosonicResources

/-- **A bounded operator on `N` copies has the (bounded) Wigner function `w`.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "Any observable expectation value can be computed using Wigner functions
according to Tr(ρÔ) = (2π)^n ∫ d^{2n}r W_ρ(r) W_Ô(r)"; App. C.1, footnote 5: "the identity operator has a Wigner
function of constant value (2π)^{-nN}".

For an operator `A` on the `N`-copy, `n`-mode Fock space `ℓ²((ℕⁿ)^N)`, given by its Fock matrix elements
`A u v = ⟨u|A|v⟩`, and a function `w` on the `N`-copy phase space `(ℝ²ⁿ)^N`: `w` is measurable and bounded, and for
all Fock states `u, v`

`⟨u|A|v⟩ = (2π)^{nN} ∫ w(r) · ∏ₜ W_{|vₜ⟩⟨uₜ|}(rₜ) dr`,

with `W_{|v⟩⟨u|}` the one-copy Wigner function `fockWigner v u` of the Fock matrix unit and `dr` Lebesgue measure.

Here `w` is the function the paper writes `W_A`, the Wigner function of the operator `A`. It is not to be confused with
the functions `W_{|v⟩⟨u|}` under the integral, the Wigner functions of the Fock matrix units, which are fixed test
functions (complex-valued in general, and not non-negative unless `u = v = 0`).

**Formalization Note.** This is the paper's trace formula with `ρ` replaced by the matrix units `|v⟩⟨u|`
(`Tr(A |v⟩⟨u|) = ⟨u|A|v⟩`). An operator that is bounded but not trace class need not have a Wigner function given by
the Fourier formula of §2, so the relation "`A` has Wigner function `w`" is stated through this pairing; the integrals
converge absolutely because `w` is bounded and the Wigner functions of the matrix units are Schwartz functions. The
Wigner functions of the matrix units span a dense subspace of the integrable functions, so a bounded `w` with this
property is unique up to a Lebesgue null set. -/
def HasWignerFunction {n N : ℕ}
    (A : Matrix (Fin N → Occupation (Fin n)) (Fin N → Occupation (Fin n)) ℂ)
    (w : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → ℝ) : Prop :=
  Measurable w ∧ (∃ C : ℝ, ∀ r, |w r| ≤ C) ∧
    ∀ u v : Fin N → Occupation (Fin n),
      A u v = (((2 * Real.pi) ^ (n * N) : ℝ) : ℂ) *
        ∫ r, (w r : ℂ) * ∏ t, fockWigner (v t) (u t) (r t)

/-- **Classical measurements: POVMs all of whose elements have non-negative Wigner functions.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "We refer to a POVM as a classical measurement if every element of it has a
non-negative Wigner function. Here 'classical' refers to the existence of a classical phase-space description of the
measurement statistics"; Theorem 2: "A POVM is classical if all of its elements have non-negative Wigner functions";
Theorem S3 (App. C.1): "any (collective) POVM whose elements all have non-negative Wigner functions".

`IsClassical E` for a POVM `E` on `N` copies of an `n`-mode system (Fock space `ℓ²((ℕⁿ)^N)`), with outcomes in a
measurable space `O`: for every measurable set `B` of outcomes, the element `E(B)` has a Wigner function
`w_B = W_{E(B)}` (`HasWignerFunction`) with `w_B(r) ≥ 0` for every `r ∈ (ℝ²ⁿ)^N`.

**Formalization Note.** The POVM is an operator-valued measure `B ↦ E(B)`, so "every element" is "`E(B)` for every
measurable `B`"; for a discrete POVM `{M_x}` this is the same as asking it of every `M_x`, since `E(B) = ∑_{x∈B} M_x`.
The Wigner function is asked to be a bounded function. This excludes no POVM: `E(B)` and `E(Bᶜ) = I − E(B)` both have
non-negative Wigner functions, and they add up to the Wigner function `(2π)^{-nN}` of the identity (footnote 5), so
`0 ≤ w_B ≤ (2π)^{-nN}` almost everywhere. Non-negativity is asked at every point; `w_B` is determined up to a null
set, so this is the same as almost everywhere. The numbers `(2π)^{nN} w_B(r)` are the conditional probabilities
`p(x|α)` of Lemma C.2, with which the measurement is simulated from samples of the Wigner distribution; that they
form a Markov kernel is the content of that lemma (`lemma_C2`), not part of this definition. -/
def IsClassical {n N : ℕ} {O : Type} [MeasurableSpace O]
    (E : FockPOVM (Fin N → Occupation (Fin n)) O) : Prop :=
  ∀ B : Set O, MeasurableSet B →
    ∃ w : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → ℝ,
      HasWignerFunction (E.effect B) w ∧ ∀ r, 0 ≤ w r

end BosonicResources



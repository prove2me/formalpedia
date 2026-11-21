-- Prove2me | Definitions.Def_MasulloGRH_TraceFormula
-- name    : MasulloGRH_TraceFormula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:44:53.072457+00:00
-- url     : https://prove2.me/theorems/dcdd505d-2e7c-4f10-9e3f-ddbc1cbd0c1a
-- title:
--   The objects of the Trace Formula: test functions on $C_F$, local terms, zeros of $L$ on $\Omega(C_F)$
-- statement:
--   This file defines the terms that appear in the Trace Formula on the idele class group $C_F$ of a number field $F$.
--
--   1. A **test function** on $C_F$, $\varphi\in\mathcal D(C_F)=C_c^\infty(C_F)$, is a Schwartz–Bruhat function on $C_F$ with compact support.
--   2. The **Mellin transform** of a function $\varphi$ on $C_F$ at a quasi-character $c$ is
--   $$M(\varphi)(c)=\int_{C_F}\varphi(g)\,c(g)\,d\bar\mu(g),$$
--   with $\bar\mu$ the Tamagawa measure on $C_F$.
--   3. For a place $v$, $\varphi(g_v)$ denotes the value of $\varphi$ on the class of the idele with coordinate $g_v\in F_v^\times$ at $v$ and $1$ elsewhere.
--   4. The **local term at an Archimedean place** $v$ is
--   $$\frac{1}{M_v}\int_{F_v^\times}\frac{\varphi(g_v)\,|g_v|_v^{1/2}}{|1-g_v|_v}\,d\mu_v(g_v),\qquad M_v=\begin{cases}2&v\text{ real},\\2\pi&v\text{ complex},\end{cases}$$
--   with $\mu_v=|\cdot|_v^{-1}\nu_v$ the local multiplicative Tamagawa measure, $\nu_v=dx$ for $v$ real and $\nu_v=|dz\wedge d\bar z|$ for $v$ complex.
--   5. The **local term at a finite place** $v$ is
--   $$\frac{\log q_v}{\mu_v(\mathcal O_{F_v}^\times)}\int_{F_v^\times}\frac{\varphi(g_v)\,|g_v|_v^{1/2}}{|1-g_v|_v}\,d\mu_v(g_v),$$
--   with $q_v$ the cardinality of the residue field and $\mu_v$ a Haar measure on $F_v^\times$.
--   6. For a quasi-character $c$ of $C_F$, write $c=\chi|\cdot|_F^{\sigma}$ with $\chi=c/|c|$ unitary and $\sigma=\sigma(c)$ the abscissa. The **order of the Hecke $L$-function at $c$** is the order of the completed Hecke $L$-function $s\mapsto L(s,\chi)$ at $s=\sigma$; $c$ is a **zero** if this order is positive, and the order is then its **multiplicity** $N(c)$.
--   7. For $\alpha>0$, the **zeros in the strip** are the zeros $c$ with $|\sigma(c)-\tfrac12|<\alpha$, i.e. the zeros in the interior of the relative vertical strip $\Omega(C_F)_{1/2+I}$, $I=[-\alpha,\alpha]$.
--
--   **Formalization Note** In items 4 and 5 the integrals are ordinary integrals. They are used for test functions that vanish on $C_F^1$; for such functions the integrand vanishes where $|g_v|_v=1$, and the Connes–Weil principal values of Definition B.4.4.1 coincide with these integrals (Lemma B.4.4.3 at the finite places). The term of item 4 is written as $\nu(B)^{-1}\int\varphi(x)|x|_v^{1/2}/(|1-x|_v|x|_v)\,d\nu(x)$ with $\nu$ any Haar measure on $F_v$ and $B$ the unit ball, since $\nu_v(B)=M_v$; the term of item 5 does not depend on the normalization of $\mu_v$. The Haar measures are selected by choice.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1, eqs. (12.5.1.1)–(12.5.1.3) (pp. 519–520); Theorem B.4.4.7 and the description of D(C_F) after it (p. 623); Definition A.3.2.2 (p. 560); Remark B.4.4.2 and Lemma B.4.4.3 (p. 620)

import Definitions.Def_MasulloGRH_CompletedL

/-!
# The objects of the Trace Formula on the idele class group

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026): Theorem 12.5.1.1,
eqs. (12.5.1.1)–(12.5.1.3) (pp. 519–520); Theorem B.4.4.7 and the description of `D(C_F)` after
it (p. 623); Definition A.3.2.2 (p. 560); Remark B.4.4.2 (p. 620); Lemma B.4.4.3 (p. 620).
-/

namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### Test functions on `C_F` -/

/-- `φ ∈ D(C_F) = C_c^∞(C_F)`: `φ` is a test function on the idele class group, i.e. a
Schwartz–Bruhat function on `C_F` with compact support. -/
def IsTestFunction (φ : IdeleClassGroup F → ℂ) : Prop :=
  φ ∈ schwartzBruhatSubmodule (IdeleClassGroup F) ∧ HasCompactSupport φ

/-- The Mellin transform `M(φ)(c) = ∫_{C_F} φ(g) c(g) d\bar μ(g)` of a function on `C_F`, with the
Tamagawa measure `\bar μ` on `C_F`; `c` is a quasi-character, given as a function on the ideles. -/
def classMellin (φ : IdeleClassGroup F → ℂ) (c : IdeleGroup F → ℂ) : ℂ :=
  ∫ x : IdeleClassGroup F, φ x * c x.out ∂(tamagawaIdeleClass F)

/-! ### Local terms -/

/-- The Borel σ-algebra of the completion at an infinite place. -/
scoped instance infiniteCompletionMeasurableSpace (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _

scoped instance infiniteCompletionBorelSpace (w : InfinitePlace F) : BorelSpace w.Completion :=
  ⟨rfl⟩

/-- The Borel σ-algebra of the multiplicative group of the completion at a finite place. -/
scoped instance finiteCompletionUnitsMeasurableSpace (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _

scoped instance finiteCompletionUnitsBorelSpace (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩

open Classical in
/-- A Haar measure on the additive group of the completion `F_w` at an infinite place. -/
def archAddHaar (w : InfinitePlace F) : Measure w.Completion :=
  if h : ∃ ν : Measure w.Completion, ν.IsAddHaarMeasure then h.choose else 0

open Classical in
/-- A Haar measure on the multiplicative group `F_vˣ` at a finite place. -/
def finiteMulHaar (v : HeightOneSpectrum (𝓞 F)) : Measure (v.adicCompletion F)ˣ :=
  if h : ∃ μ : Measure (v.adicCompletion F)ˣ, μ.IsHaarMeasure then h.choose else 0

open Classical in
/-- The restriction of a function `φ` on `C_F` to `F_wˣ`, for an infinite place `w`, extended by
`0` at `0`: `x ↦ φ(j_w(x))`. -/
def archRestrict (φ : IdeleClassGroup F → ℂ) (w : InfinitePlace F) (x : w.Completion) : ℂ :=
  if hx : x ≠ 0 then φ (QuotientGroup.mk (ideleSingleInfinite w (Units.mk0 x hx))) else 0

/-- The term of an infinite place `w` in the Trace Formula (12.5.1.1):
`(1/M_w) ∫_{F_wˣ} φ(g) |g|_w^{1/2} / |1 - g|_w dμ_w(g)` with `M_w = 2` for `w` real, `M_w = 2π` for
`w` complex, and `μ_w = |·|_w⁻¹ ν_w` the local multiplicative Tamagawa measure
(Definition A.3.2.2), `ν_w` being `dx`, respectively `|dz ∧ d\bar z|`.  Since `ν_w` gives the
unit ball `{|x| ≤ 1}` the volume `M_w`, the term is
`ν(ball)⁻¹ ∫ φ(x) |x|_w^{1/2} / (|1 - x|_w |x|_w) dν(x)` for any Haar measure `ν` on `F_w`. -/
def archLocalTerm (φ : IdeleClassGroup F → ℂ) (w : InfinitePlace F) : ℂ :=
  ((archAddHaar w {x : w.Completion | ‖x‖ ≤ 1}).toReal : ℂ)⁻¹ *
    ∫ x : w.Completion,
      archRestrict φ w x *
        (((‖x‖ ^ w.mult) ^ (1 / 2 : ℝ) / (‖1 - x‖ ^ w.mult * ‖x‖ ^ w.mult) : ℝ) : ℂ)
      ∂(archAddHaar w)

/-- The term of a finite place `v` in the Trace Formula (12.5.1.2):
`(log q_v / μ_v(𝒪_{F_v}ˣ)) ∫_{F_vˣ} φ(g) |g|_v^{1/2} / |1 - g|_v dμ_v(g)`, which does not depend on
the normalization of the Haar measure `μ_v` on `F_vˣ`. -/
def finiteLocalTerm (φ : IdeleClassGroup F → ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  (Real.log (Ideal.absNorm v.asIdeal) : ℂ) *
    ((finiteMulHaar v {x : (v.adicCompletion F)ˣ |
        Valued.v (x : v.adicCompletion F) = 1}).toReal : ℂ)⁻¹ *
    ∫ x : (v.adicCompletion F)ˣ,
      φ (QuotientGroup.mk (ideleSingle v x)) *
        ((‖(x : v.adicCompletion F)‖ ^ (1 / 2 : ℝ) / ‖1 - (x : v.adicCompletion F)‖ : ℝ) : ℂ)
      ∂(finiteMulHaar v)

/-! ### Zeros of the Hecke L-function on the surface of quasi-characters -/

open Classical in
/-- The unitary part `c / |c|` of a quasi-character `c` of `C_F`, as a Hecke character. -/
def quasiUnitaryPart (c : IdeleGroup F → ℂ) : HeckeCharacter F :=
  if h : ∃ χ : HeckeCharacter F, ∀ g : IdeleGroup F,
      ((χ (QuotientGroup.mk g) : Circle) : ℂ) = c g / ‖c g‖ then
    h.choose
  else 1

/-- The order of the Hecke L-function `c ↦ L(c)` at the quasi-character `c`: writing
`c = χ |·|_F^σ` with `χ` unitary and `σ = σ(c)` real, it is the order of the completed Hecke
L-function `s ↦ L(s, χ)` at `s = σ`. -/
def quasiLOrder (c : IdeleGroup F → ℂ) : WithTop ℤ :=
  meromorphicOrderAt (completedHeckeLFunction (quasiUnitaryPart c)) (quasiAbscissa c)

/-- The multiplicity `N(c)` of `c` as a zero of the Hecke L-function (`0` if `c` is not a
zero). -/
def quasiZeroMultiplicity (c : IdeleGroup F → ℂ) : ℕ := (quasiLOrder c).untop₀.toNat

variable (F)

/-- The set of zeros `c ∈ Ω(C_F)` of the Hecke L-function `c ↦ L(c)` in the interior of the
relative vertical strip `Ω(C_F)_{1/2 + I}`, `I = [-α, α]`: the quasi-characters `c` with
`|σ(c) - 1/2| < α` at which `L` vanishes. -/
def heckeZerosInStrip (α : ℝ) : Set (IdeleGroup F → ℂ) :=
  {c | IsQuasiCharacter c ∧ |quasiAbscissa c - 1 / 2| < α ∧ 0 < quasiLOrder c}

end

end MasulloGRH



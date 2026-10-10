-- Prove2me | Definitions.Def_ArtinHeckeProbe
-- name    : ArtinHeckeProbe
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T10:46:15.366851+00:00
-- url     : https://prove2.me/theorems/a4976f7c-7915-40cb-bf0d-edfa88d9487b
-- title:
--   The principal correction ℋ_η and the Mellin integral f_η of the proof of Theorem 1.2, with the cubic residue character and its Jacobi sum
-- statement:
--   Objects of §§7.3–8.3 of OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 46–60, built on the bundle `Def_ArtinHecke` (`HeckeChar F 𝔪`, `HeckeChar.LSeries`). Write $Q = \mathrm N P$ for a nonzero prime ideal $P$ of $\mathcal O_F$.
--
--   - `SmallPrimesDvd N₀ 𝔪`: every nonzero prime ideal of $\mathcal O_F$ of absolute norm at most $N_0$ divides $\mathfrak m$ (as ideals, $\mathfrak m \le P$).
--   - `cubicResidueChar ι P x`: for a residue $x \ne 0$ modulo $P$, the value $\iota(\omega)$, where $\omega \in \mathcal O_F$ is a cube root of unity with $\omega \equiv x^{(Q-1)/3} \pmod P$ (a choice, and $0$ if there is none); its value at $0$ is $0$. Here $\iota : F \to \mathbb C$ is a ring homomorphism.
--   - `cubicJacobiSum ι P`: the Jacobi sum $J(\rho, \rho) = \sum_{x \bmod P} \rho(x)\rho(1 - x)$ of $\rho = $ `cubicResidueChar ι P`.
--   - `jacobiPhaseSix ι P`: $Q^{-3} J(\rho, \rho)^6$; the paper writes this as $\Lambda(\mathfrak p)^6$ for its Gauss correction character $\Lambda$ (Lemma 3.4), using $\Lambda^6 = (Q^{-1/2}J)^6$.
--   - `principalLocalFactor Q e θ s`: with $D = eQ^{-s}$ and $E = \theta Q^{3-6s}$, the number $\bigl[(1 - Q^{-2}) + (1 - Q^{-1})^2(1 + Q^{-1})(E - D)/(1 - E)\bigr]/(1 - D)$.
--   - `χ.principalCorrection ι s`: the infinite product (`tprod`) over the nonzero prime ideals $P$ coprime to $\mathfrak m$ of `principalLocalFactor` $(Q, \chi(P), \overline{\texttt{jacobiPhaseSix}\ \iota\ P}\cdot\chi(P)^6, s)$.
--   - `principalMellinOf H L Z`: $\frac{1}{2\pi}\int_{\mathbb R} Z^{2+i\tau-8/15} e^{(2+i\tau-5/6)^2} H(2+i\tau)/L(2+i\tau)\,d\tau$, that is, $\frac{1}{2\pi i}\int_{(2)} Z^{s-8/15}e^{(s-5/6)^2}H(s)/L(s)\,ds$ for functions $H, L : \mathbb C \to \mathbb C$ and real $Z$.
--   - `χ.principalMellin ι Z`: `principalMellinOf` with $H = $ `χ.principalCorrection ι` and $L = $ `χ.LSeries`.
--
--   **Formalization note.** The paper fixes a finite set $S$ of places (p. 8) and works with $L^S(s, \eta) = \prod_{\mathfrak p \notin S}(1 - \eta(\mathfrak p)q_{\mathfrak p}^{-s})^{-1}$ (p. 16). Here $S$ is the complex places together with the primes dividing the modulus $\mathfrak m$, so that `χ.LSeries` is the paper's $L^S(s, \eta)$ for the primitive $\eta$ inducing $\chi$, and the paper's requirement that $S$ contain every prime of norm at most a fixed constant becomes `SmallPrimesDvd N₀ 𝔪`. The paper's correction at $u = 1$ is $\mathcal H_{1,\mathfrak p} = (1 - V)\frac{1 - W}{1 - D_1}\mathcal F_{1,\mathfrak p}$ with $\mathcal F_{1,\mathfrak p}$ from (7.19), $V = Q^{-6z}$, $W = Q^{-w}$, $D_1 = \eta(\mathfrak p)Q^{-\xi}$ and $E_1 = \vartheta(\mathfrak p)^6Q^{4-6\xi}V$; at $(\xi, w, z) = (s, 1, 1/6)$ this is $V = W = Q^{-1}$, and multiplying out gives the closed form of `principalLocalFactor`. The value $\vartheta(\mathfrak p)^6$ is entered as $\overline{\Lambda(\mathfrak p)^6}\,\eta(\mathfrak p)^6$: $\vartheta = \overline\Lambda\,\overline G\,\eta$ (p. 15), $G(\mathfrak p) = \overline{\chi_{\mathfrak p}(4)}\gamma_3(\mathfrak p)$ is a sixth root of unity because $\gamma_3(\mathfrak p)$ is a sign (Lemma 3.4), and $\Lambda(\mathfrak p)^6 = \gamma_2(\mathfrak p)^{18} = (Q^{-1/2}J(\rho, \rho))^6$ by (3.9) and (3.11), with $\rho = \chi_{\mathfrak p}^2$ the cubic residue character $x \mapsto x^{(Q-1)/3}$ (p. 13). The paper reads residue symbols in $\mu_6 \subset F$ and passes to $\mathbb C$ through an embedding of $F$; that embedding is the parameter $\iota$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 50: “For the remainder of the proof, write $\mathcal H_\eta(s) := \mathcal H_1(s, 1, 1/6)$. This is the principal specialization announced in Section 4.” and p. 56: “$f_\eta(Z) = \frac{1}{2\pi i}\int_{(2)} Z^{C_*(\xi)}e^{(\xi-5/6)^2}\frac{\mathcal H_\eta(\xi)}{L^S(\xi, \eta)}\,d\xi$. (8.13)”, where $C_*(\xi) = \xi - 8/15$ by (8.10) (p. 55).
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 8, 13, 15, 46–50, 55–56, §§3, 7.3, 8.2 (the set S, the cubic residue character and Jacobi sum of Lemma 3.4, the principal correction ℋ_η of Proposition 7.3, the Mellin integral f_η (8.13))

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- The finite set `S` of the proof of Theorem 1.2 (§3, p. 8), as a condition on the modulus: every
nonzero prime ideal of `𝓞 F` of absolute norm at most `N₀` contains (divides) `𝔪`. -/
def SmallPrimesDvd (N₀ : ℕ) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 F), P.IsPrime → P ≠ ⊥ → Ideal.absNorm P ≤ N₀ → 𝔪 ≤ P

open Classical in
/-- The cubic residue character `ρ_𝔭` of Lemma 3.4 (p. 13), read in `ℂ` through `ι`: a nonzero
residue `x` modulo `P` goes to `ι ω`, where `ω ∈ 𝓞 F` is a cube root of unity with
`ω ≡ x^{(N P − 1)/3} (mod P)`, and `0` goes to `0`. -/
noncomputable def cubicResidueChar (ι : F →+* ℂ) (P : Ideal (𝓞 F)) (x : 𝓞 F ⧸ P) : ℂ :=
  if x = 0 then 0 else
    if h : ∃ ω : 𝓞 F, ω ^ 3 = 1 ∧ Ideal.Quotient.mk P ω = x ^ ((Ideal.absNorm P - 1) / 3)
    then ι (h.choose : F) else 0

/-- The Jacobi sum `J(ρ_𝔭, ρ_𝔭) = ∑_{x mod P} ρ_𝔭(x) ρ_𝔭(1 − x)` of Lemma 3.4 (p. 13). -/
noncomputable def cubicJacobiSum (ι : F →+* ℂ) (P : Ideal (𝓞 F)) : ℂ :=
  ∑ᶠ x : 𝓞 F ⧸ P, cubicResidueChar ι P x * cubicResidueChar ι P (1 - x)

/-- `(N P)^{-3} J(ρ_𝔭, ρ_𝔭)^6`: the sixth power of `(N P)^{-1/2} J(ρ_𝔭, ρ_𝔭)`, the right side of
the third identity of (3.11) in Lemma 3.4 (p. 13). -/
noncomputable def jacobiPhaseSix (ι : F →+* ℂ) (P : Ideal (𝓞 F)) : ℂ :=
  ((Ideal.absNorm P : ℂ) ^ 3)⁻¹ * cubicJacobiSum ι P ^ 6

/-- A local factor from the proof of Proposition 7.3 (pp. 48–49): `ℋ_{u,𝔭} = (1 − V)(1 − W)
(1 − D₁)⁻¹ ℱ_{u,𝔭}` with `ℱ_{u,𝔭}` given by (7.19), at `u = 1`, `w = 1`, `z = 1/6`, `ξ = s`, where
`Q = N𝔭`, `V = W = Q⁻¹`, `D = e Q^{-s}` (`e` in the place of `η(𝔭)`) and `E = θ Q^{3 − 6s}` (`θ` in
the place of `ϑ(𝔭)^6`), simplified to
`[(1 − Q^{-2}) + (1 − Q⁻¹)^2 (1 + Q⁻¹)(E − D)/(1 − E)] / (1 − D)`. -/
noncomputable def principalLocalFactor (Q : ℕ) (e θ s : ℂ) : ℂ :=
  let D := e * (Q : ℂ) ^ (-s)
  let E := θ * (Q : ℂ) ^ (3 - 6 * s)
  ((1 - ((Q : ℂ) ^ 2)⁻¹) + (1 - (Q : ℂ)⁻¹) ^ 2 * (1 + (Q : ℂ)⁻¹) * (E - D) / (1 - E)) / (1 - D)

/-- The principal correction, after `ℋ_η(s) := ℋ₁(s, 1, 1/6) = ∏_{𝔭 ∉ S} ℋ_{1,𝔭}` of p. 50: the
product over the nonzero prime ideals `P` coprime to `𝔪` of `principalLocalFactor (N P) (χ P) θ s`, with
`θ = conj (jacobiPhaseSix ι P) · (χ P)^6` in the place of `ϑ(𝔭)^6`, `ϑ = Λ̄ Ḡ η` (p. 15). -/
noncomputable def HeckeChar.principalCorrection {𝔪 : Ideal (𝓞 F)} (ι : F →+* ℂ)
    (χ : HeckeChar F 𝔪) (s : ℂ) : ℂ :=
  ∏' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤},
    principalLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
      (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) s

/-- The inverse Mellin integral of (8.13) (p. 56) for a numerator `H` and a denominator `L`:
`(1/2πi) ∫_{(2)} Z^{s − 8/15} e^{(s − 5/6)^2} H(s) / L(s) ds`, written on the line
`s = 2 + iτ` as `(1/2π) ∫_ℝ … dτ`. -/
noncomputable def principalMellinOf (H L : ℂ → ℂ) (Z : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ,
    (Z : ℂ) ^ ((2 : ℂ) + τ * Complex.I - 8 / 15) *
      Complex.exp (((2 : ℂ) + τ * Complex.I - 5 / 6) ^ 2) *
      H (2 + τ * Complex.I) / L (2 + τ * Complex.I)

/-- `f_η(Z)` of (8.13) (p. 56): `principalMellinOf` with numerator the principal correction
`χ.principalCorrection ι` and denominator the `L`-series `χ.LSeries`. -/
noncomputable def HeckeChar.principalMellin {𝔪 : Ideal (𝓞 F)} (ι : F →+* ℂ)
    (χ : HeckeChar F 𝔪) (Z : ℝ) : ℂ :=
  principalMellinOf (χ.principalCorrection ι) χ.LSeries Z

end ArtinPrimitiveRoots



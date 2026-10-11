-- Prove2me | Definitions.Def_ArtinHeckeTheta
-- name    : ArtinHeckeTheta
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T12:57:43.993409+00:00
-- url     : https://prove2.me/theorems/2ed377f2-7465-4c33-b8ce-02ef092b0728
-- title:
--   The theta sum B_m(Z), the probe I(X, Y, Z) and its Poisson rows, with the S-integers, residue symbols, allowed generators and Gauss sums of §3
-- statement:
--   Objects of §§3, 4, 7 and 8.2 of OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 8–16, 42–46 and 56, built on the bundles `Def_ArtinHecke` (`HeckeChar F 𝔪`) and `Def_ArtinHeckeProbe` (`SmallPrimesDvd`, `cubicJacobiSum`). Throughout, $\mathfrak m$ is an ideal of $\mathcal O_F$, $\iota : F \to \mathbb C$ is a ring homomorphism, and $q_{\mathfrak a} = \mathrm N\mathfrak a$ is the absolute norm.
--
--   - `placesOf 𝔪`: the height-one primes of $\mathcal O_F$ containing $\mathfrak m$. `SInt 𝔪` is the ring $R$ of $S$-integers (`Set.integer`: elements of $F$ integral at every other height-one prime) and `SUnit 𝔪` its unit group $U_S$ (`Set.unit`); `SClass 𝔪` is $U_S/U_S^6$, and `SClass.rep` picks a representative, as an element of $R$.
--   - `IsExterior 𝔪 I`: $I \ne 0$ and $I + \mathfrak m = \mathcal O_F$. `IsSixthPowerFree I`: every ideal $J$ with $J^6 \mid I$ is the unit ideal. `quotLift` picks a representative in $R$ of a residue class modulo an ideal of $R$.
--   - `sexticResidueSymbol ι 𝔪 P x`, for $x \in R$: $0$ if $x \in PR$; otherwise $\iota(\zeta)$ for a sixth root of unity $\zeta \in \mathcal O_F$ with $\zeta \equiv x^{(\mathrm NP - 1)/6} \pmod{PR}$ (a choice, and $0$ if there is none). `residueSymbol ι 𝔪 𝔞 x` is the product of these over the prime factors of $\mathfrak a$ counted with multiplicity, so $1$ for $\mathfrak a = \mathcal O_F$.
--   - `AllowedGen ι 𝔪`: a function `gen` from ideals of $\mathcal O_F$ to $R$ such that, for exterior $I, J$: `gen I` generates the ideal $IR$; `gen (I * J)` $= \varepsilon^6\,$`gen I`$\,$`gen J` for some $S$-unit $\varepsilon$; and for distinct exterior primes $P, P'$, `sexticResidueSymbol ι 𝔪 P (gen P')` $=$ `sexticResidueSymbol ι 𝔪 P' (gen P)`.
--   - `sAddChar 𝔪 x`, for $x \in F$: $\exp(-2\pi i\,\mathrm{Tr}_{F/\mathbb Q}(y))$ for an element $y \in F$ (a choice) with $x - y \in R$ and $y$ integral at every prime of `placesOf 𝔪`, and $0$ if there is none.
--   - `gaussSumAt g 𝔞 k`: $\sum_{v \bmod \mathfrak aR} \chi_{\mathfrak a}(v)\,e(kv/a)$, with $\chi_{\mathfrak a} = $ `residueSymbol ι 𝔪 𝔞`, $e = $ `sAddChar 𝔪` and $a = $ `g.gen 𝔞`.
--   - `gaussPhase g j 𝔠`: $q_{\mathfrak c}^{-1/2}\sum_{x \bmod \mathfrak cR}\chi_{\mathfrak c}(x)^j e(x/c)$, with $c = $ `g.gen 𝔠`.
--   - `gaussLambda ι 𝔞`: the product over the prime factors $P$ of $\mathfrak a$, with multiplicity, of $-(\mathrm NP)^{-1/2}\,$`cubicJacobiSum ι P`. `gaussG g 𝔞`: the product over the same factors of $\overline{\chi_P(4)}\,$`gaussPhase g 3 P`.
--   - `χ.thetaChar g 𝔞`: $\overline{\texttt{gaussLambda ι 𝔞}}\cdot\overline{\texttt{gaussG g 𝔞}}\cdot\chi(\mathfrak a)$.
--   - `gaussianPG t`: $(2\sqrt\pi)^{-1}\exp(-(\log t)^2/4)$.
--   - `χ.thetaSum g m Z`, for $m \in R$ and real $Z$: the sum (`tsum`) over pairs of a squarefree exterior $\mathfrak c$ and an exterior $\mathfrak n$, with $\mathfrak A = \mathfrak c\mathfrak n^3$, of $\gamma_2(\mathfrak c)\,q_{\mathfrak c}^{-1/2}q_{\mathfrak n}^{-1}\,\vartheta(\mathfrak A)\,\chi_{\mathfrak A}(m)\,P_G(q_{\mathfrak A}/Z)$, where $\gamma_2 = $ `gaussPhase g 2`, $\vartheta = $ `χ.thetaChar g` and $P_G = $ `gaussianPG`.
--   - `RowClass 𝔪`: pairs $(\mathfrak b, \varepsilon)$ of an exterior ideal and a class in $U_S/U_S^6$; `rowElt g r` is $m = \varepsilon_{\mathrm{rep}}\cdot$`g.gen 𝔟` $\in R$.
--   - `additiveFactor g W₁ V X Y r`: with $m = $ `rowElt g r` and $\mathfrak b = r.1$, the sum over exterior $\mathfrak s$ of $Y^{-1}W_1(q_{\mathfrak s}/Y)\,(q_{\mathfrak s}X)^{-1/2}\,q_{\mathfrak s}^{-1/2}\,V\bigl(q_{\mathfrak b}/(q_{\mathfrak s}X)\bigr)\,$`gaussSumAt g 𝔰 (−m)`, for real functions $W_1, V$.
--   - `χ.probe g W₁ V X Y Z`: the sum over row classes $r$ of `additiveFactor g W₁ V X Y r` $\cdot$ `χ.thetaSum g (rowElt g r) Z`.
--   - `simplePart 𝔟`: the product of the primes dividing $\mathfrak b$ exactly once.
--   - `poissonFactor g 𝔰 𝔄 h`, for $h \in R$: the sum over $d \bmod \mathfrak sR$ with $h - Ad \in \mathfrak sR$ of $\chi_{\mathfrak s}(d)\,$`gaussSumAt g 𝔄`$((h - Ad)/s)$, with $s, A$ the generators `g.gen` of $\mathfrak s, \mathfrak A$.
--   - `FreqClass 𝔪`: pairs $(\mathfrak u, \varepsilon)$ of a sixth-power-free exterior ideal and a class in $U_S/U_S^6$; `freqElt g r` is $u = \varepsilon_{\mathrm{rep}}\cdot$`g.gen 𝔲`; `principalFreq 𝔪` is $(\mathcal O_F, 1)$.
--   - `χ.freqSeries g u ξ w z`: the sum over squarefree exterior $\mathfrak c$ and exterior $\mathfrak n, \mathfrak s, \mathfrak r$, with $\mathfrak A = \mathfrak c\mathfrak n^3$, of $\gamma_2(\mathfrak c)\,\vartheta(\mathfrak A)\,$`poissonFactor g 𝔰 𝔄`$(u\,r^6)\,q_{\mathfrak c}^{-1/2-\xi}q_{\mathfrak n}^{-1-3\xi}q_{\mathfrak s}^{-w}q_{\mathfrak r}^{-6z}$, with $r = $ `g.gen 𝔯`.
--   - `χ.rowIntegral g W₁ M r X Y Z`: $(2\pi)^{-3}\int\!\!\int\!\!\int X^{1/2-z}Z^{\xi+z-1}Y^{w-1}e^{(\xi+z-1)^2}M(z)\,\widehat W_1(w)\,q_{\mathfrak u}^{-z}\,\mathcal F_u(\xi, w, z)\,d\tau_3\,d\tau_2\,d\tau_1$ (iterated integrals over $\mathbb R$) on $\xi = 4 + i\tau_1$, $w = 4 + i\tau_2$, $z = 2 + i\tau_3$, where $\widehat W_1$ is the Mellin transform `mellin` of $W_1$, $\mathfrak u = r.1$, $u = $ `freqElt g r` and $\mathcal F_u = $ `χ.freqSeries g u`.
--   - `sZetaResidue 𝔪`: `NumberField.dedekindZeta_residue F` times $\prod(1 - \mathrm NP^{-1})$ over the nonzero primes $P \supseteq \mathfrak m$. `principalConstant 𝔪 W₁ M`: $(R_S^2/6)\,M(1/6)\,\widehat W_1(1)$ with $R_S = $ `sZetaResidue 𝔪`.
--   - `IsProbeWeight W`: $W : \mathbb R \to \mathbb R$ is $C^\infty$ (`ContDiff ℝ (⊤ : ℕ∞)`) with compact support contained in $(0, \infty)$. `IsMellinWeight M`: $M$ is holomorphic on $\operatorname{Re} z > 0$, and for all $a > 0$, $b$ and $A$ some $C$ has $|M(z)| \le C(1 + |\operatorname{Im} z|)^{-A}$ for $a \le \operatorname{Re} z \le b$.
--
--   **Formalization note.** The paper's $S$ is the complex places together with the primes dividing $\mathfrak m$, as in `Def_ArtinHeckeProbe`; exterior ideals of $R$ are written as the exterior ideals $I$ of $\mathcal O_F$, through $I \mapsto IR$, with the same norm. The paper reads residue symbols in $\mu_6 \subset F$; here they are read in $\mathbb C$ through $\iota$, which is injective, so equalities between symbols are unchanged.
--
--   *Allowed generators.* The paper chooses an isotropic complement $B$ of the unit image $E$ in $F_S^\times/F_S^{\times 6}$ for the $S$-product $H_S$ of sextic Hilbert symbols and calls a generator allowed when its class lies in $B$ (Lemma 3.2, p. 10, and p. 11); allowed generators are unique up to $U_S^6$ and their products are allowed. `AllowedGen` records the three properties the paper uses: generation, multiplicativity up to $U_S^6$, and the exact reciprocity (3.3). Conversely these properties make the classes of the generators an isotropic complement of $E$: they form a subgroup by multiplicativity; $H_S(p, p') = \chi_{\mathfrak p}(p')\chi_{\mathfrak p'}(p)^{-1} = 1$ for distinct primes by Hilbert reciprocity and (3.3), and $H_S$ is alternating; and the subgroup together with $E$ spans the whole group, since every class is that of an element of $F^\times$, which is an $S$-unit times a generator. Since $E$ is Lagrangian, an isotropic subgroup that spans with $E$ meets it trivially. Every quantity below is independent of the choice of generator within its class modulo $U_S^6$ (pp. 13, 16, 42, 45).
--
--   *The additive character.* The paper's $e(x) = \prod_{v \in S}\psi_v(x)$ for the standard trace character $\psi$ is used only at $x \in F$. By the product formula it equals $\prod_{\mathfrak p \notin S}\psi_{\mathfrak p}(-x)$; for $y$ as in `sAddChar` this is $\prod_{\mathfrak p}\psi_{\mathfrak p}(-y)$ over all finite places, since $S$ contains the places where $\mathcal O_v$ is not self-dual (p. 8) and $\psi_{\mathfrak p}$ is trivial on $\mathcal O_{\mathfrak p}$ there, which equals $\psi_\infty(y) = \exp(-2\pi i\,\mathrm{Tr}_{F/\mathbb Q}y)$. Any two choices of $y$ differ by an element of $\mathcal O_F$, whose trace is an integer. The prime Gauss sums and $g_{\mathfrak s}$ do not depend on the sign convention of $\psi$, because $\chi_{\mathfrak a}(-1) = 1$ (p. 13).
--
--   *Λ and G.* By (3.9) and (3.11), $\Lambda(\mathfrak p) = -\gamma_2(\mathfrak p)^3 = -(\mathrm N\mathfrak p)^{-1/2}J(\rho_{\mathfrak p}, \rho_{\mathfrak p})$ with $\rho_{\mathfrak p} = \chi_{\mathfrak p}^2$ the cubic residue character; `gaussLambda` and `gaussG` are the completely multiplicative functions with the prime values of Lemma 3.4, which is how the paper's Hecke characters act on exterior ideals.
--
--   *The probe.* The paper defines (7.3) as an integral over $F_S^1/U_S^6$ of a sum over all $m \in R$ weighted by $W_0(m/(t_0\ell_{q_{\mathfrak s}X}))$. The integrand is invariant under $m \mapsto \epsilon m$, $\epsilon \in U_S^6$ (p. 42), so grouping $m$ into classes $mU_S^6$ and unfolding the integral gives, for each class, $\int_{F_S^1}W_0\bigl(t\,m/\ell_{q_{\mathfrak s}X}\bigr)\,dt = V\bigl(q_m/(q_{\mathfrak s}X)\bigr)$, where $V(T) = \int_{F_S^1}W_0(t\ell_T)\,dt$ is the norm-sheet profile of $W_0$ and $q_m = q_{\mathfrak b}$ for $\mathfrak b = (m)R$ (Lemma 3.1, p. 9). This is the same unfolding the paper performs on the Poisson side (p. 45). So `χ.probe g W₁ V` is the paper's $I(X, Y, Z)$ when $V$ is the profile of $W_0$; the classes $mU_S^6$ are the pairs $(\mathfrak b, \varepsilon)$ with $m = \varepsilon b$. The weight $W_0$ on $F_S$ enters the statements only through $V$, and through $M$, the Mellin transform of the profile of $\widehat W_0$ (p. 45).
--
--   *The rows.* The paper's frequencies are $u \in \mathcal U$, representatives modulo $U_S^6$ of the nonzero $S$-integers with exterior valuations in $\{0, \dots, 5\}$ (Lemma 3.3, p. 12); they correspond to the pairs `FreqClass`, and $\mathcal F_u$ depends only on the class of $u$ (p. 45). $q_u = |u|_S = q_{\mathfrak u}$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 16: “Write $\vartheta = \overline\Lambda\,\overline G\,\eta$. For $m \in R$ and $Z > 0$ define $B_m(Z) = \sum_{\mathfrak c \text{ squarefree},\, \mathfrak n} \frac{\gamma_2(\mathfrak c)}{q_{\mathfrak c}^{1/2}q_{\mathfrak n}}\vartheta(\mathfrak A)\chi_{\mathfrak A}(m)P_G\bigl(\frac{q_{\mathfrak A}}{Z}\bigr)$, $\mathfrak A = \mathfrak c\mathfrak n^3$, $A = cn^3$. (4.2)”; p. 42: “Define $I(X, Y, Z) = \int_{F_S^1/U_S^6}\frac1Y\sum_{\mathfrak s}W_1(q_{\mathfrak s}/Y)\frac{1}{\sqrt{q_{\mathfrak s}X}}\sum_{m \in R}q_{\mathfrak s}^{-1/2}g_{\mathfrak s}(-m)W_0\bigl(\frac{m}{t_0\ell_{q_{\mathfrak s}X}}\bigr)B_m(Z)\,dt_0$. (7.3)”; p. 46: “$I(X, Y, Z) = \frac{1}{(2\pi i)^3}\int_{(4)}\int_{(4)}\int_{(2)}X^{1/2-z}Z^{\xi+z-1}Y^{w-1}e^{(\xi+z-1)^2}M(z)\widehat W_1(w)\times\sum_{u \in \mathcal U}q_u^{-z}\mathcal F_u(\xi, w, z)\,dz\,dw\,d\xi$, (7.10) where the innermost line is $\operatorname{Re} z = 2$, the middle line is $\operatorname{Re} w = 4$, and the outer line is $\operatorname{Re}\xi = 4$, and $\mathcal F_u(\xi, w, z) = \sum_{\mathfrak c \text{ squarefree},\, \mathfrak n, \mathfrak s, \mathfrak r}\gamma_2(\mathfrak c)\vartheta(\mathfrak A)F(s, A, ur^6)q_{\mathfrak c}^{-1/2-\xi}q_{\mathfrak n}^{-1-3\xi}q_{\mathfrak s}^{-w}q_{\mathfrak r}^{-6z}$, $\mathfrak A = \mathfrak c\mathfrak n^3$. (7.11)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 8–17, 42–46, 56, §§3–4, 7.1–7.2, 8.2 (S-integers and S-units, sextic residue symbols, allowed generators of Lemma 3.2, the additive character e, the Gauss sums γ_j, g_𝔰 and the characters Λ, G, ϑ of Lemma 3.4, the theta sum B_m(Z) (4.2), the probe I(X, Y, Z) (7.3), the Poisson rows of (7.10)–(7.11), R_S and c₀ (8.13))

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F]

/-- The finite places of the set `S` of §3 (p. 8) for the modulus `𝔪`: the height-one primes of
`𝓞 F` containing `𝔪`. -/
def placesOf (𝔪 : Ideal (𝓞 F)) : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | 𝔪 ≤ v.asIdeal}

/-- The ring `R = 𝓞_S` of `S`-integers of §3 (p. 8), with `S` the complex places and
`placesOf 𝔪`. -/
abbrev SInt (𝔪 : Ideal (𝓞 F)) : Type _ :=
  ↥((placesOf 𝔪).integer F)

/-- The group `U_S = R^×` of `S`-units (p. 8), as a subgroup of `Fˣ`. -/
abbrev SUnit (𝔪 : Ideal (𝓞 F)) : Type _ :=
  ↥((placesOf 𝔪).unit F)

/-- `U_S / U_S^6`, the `S`-units modulo sixth powers. -/
abbrev SClass (𝔪 : Ideal (𝓞 F)) : Type _ :=
  SUnit 𝔪 ⧸ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range

/-- An exterior ideal (p. 8), as an ideal of `𝓞 F`: nonzero and coprime to `𝔪`. -/
def IsExterior (𝔪 I : Ideal (𝓞 F)) : Prop :=
  I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤

/-- The ideal `I` has no sixth-power factor other than the unit ideal. -/
def IsSixthPowerFree (I : Ideal (𝓞 F)) : Prop :=
  ∀ J : Ideal (𝓞 F), J ^ 6 ∣ I → IsUnit J

/-- A chosen representative in `R` of a residue class modulo an ideal of `R`. -/
noncomputable def quotLift {𝔪 : Ideal (𝓞 F)} {I : Ideal (SInt 𝔪)} (x : SInt 𝔪 ⧸ I) : SInt 𝔪 :=
  Function.surjInv Ideal.Quotient.mk_surjective x

/-- A chosen `S`-unit representing a class in `U_S / U_S^6`, as an element of `R`. -/
noncomputable def SClass.rep {𝔪 : Ideal (𝓞 F)} (ε : SClass 𝔪) : SInt 𝔪 :=
  ((Set.unitEquivUnitsInteger (placesOf 𝔪) F
    (Function.surjInv QuotientGroup.mk_surjective ε) : (SInt 𝔪)ˣ) : SInt 𝔪)

open Classical in
/-- The sextic residue character `χ_𝔭` of §3 (p. 11) on `R`, read in `ℂ` through `ι`: for `x` not
in `P R`, the value `ι ζ`, where `ζ ∈ 𝓞 F` is a sixth root of unity with
`ζ ≡ x^{(N P − 1)/6}` modulo `P R` (a choice, and `0` if there is none); `0` on `P R`. -/
noncomputable def sexticResidueSymbol (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) : ℂ :=
  if Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x = 0 then 0 else
    if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) ζ) =
          Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^ ((Ideal.absNorm P - 1) / 6)
    then ι (h.choose : F) else 0

/-- The symbol `χ_𝔞(x) = ∏_{𝔭 ∣ 𝔞} χ_𝔭(x)^{k_𝔭}` of §3 (p. 11), for `𝔞 = ∏ 𝔭^{k_𝔭}`: the product
of `sexticResidueSymbol` over the prime factors of `𝔞` counted with multiplicity. -/
noncomputable def residueSymbol (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) : ℂ :=
  ((normalizedFactors 𝔞).map fun P => sexticResidueSymbol ι 𝔪 P x).prod

/-- A system of allowed generators (Lemma 3.2, p. 10, and the definition on p. 11), given by the
properties used in the paper: `gen I` generates `I R` for every exterior `I`; generators are
multiplicative up to sixth powers of `S`-units; and sextic reciprocity holds exactly for the
generators of distinct exterior primes, (3.3) (p. 11). -/
structure AllowedGen (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) where
  /-- the chosen generator of `I R` -/
  gen : Ideal (𝓞 F) → SInt 𝔪
  span_gen : ∀ I : Ideal (𝓞 F), IsExterior 𝔪 I →
    Ideal.span {gen I} = I.map (algebraMap (𝓞 F) (SInt 𝔪))
  gen_mul : ∀ I J : Ideal (𝓞 F), IsExterior 𝔪 I → IsExterior 𝔪 J →
    ∃ ε : SUnit 𝔪, ((gen (I * J) : SInt 𝔪) : F) =
      (((ε : Fˣ) : F)) ^ 6 * (gen I : F) * (gen J : F)
  reciprocity : ∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P →
    IsExterior 𝔪 P' → P ≠ P' →
      sexticResidueSymbol ι 𝔪 P (gen P') = sexticResidueSymbol ι 𝔪 P' (gen P)

open Classical in
/-- The additive character `e(x) = ∏_{v ∈ S} ψ_v(x)` of §3 (p. 8) on `F`, for the standard trace
character `ψ`: `exp(−2πi Tr_{F/ℚ}(y))` for an element `y` with `x − y ∈ R` and `y` integral at
every finite place of `S` (a choice; `0` if there is none). -/
noncomputable def sAddChar (𝔪 : Ideal (𝓞 F)) (x : F) : ℂ :=
  if h : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧ ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 then
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F h.choose : ℚ) : ℂ))
  else 0

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The sum `∑_{v mod 𝔞} χ_𝔞(v) e(k v / a)`, with `a` the allowed generator of `𝔞`: the sum
`g_𝔰(k)` of §7.1 (p. 42) for `𝔞 = 𝔰`, and `g_{χ_𝔄}(A, k)` of §7.2 (p. 44) for `𝔞 = 𝔄`. -/
noncomputable def gaussSumAt (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (k : F) : ℂ :=
  ∑ᶠ v : SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)),
    residueSymbol ι 𝔪 𝔞 (quotLift v) * sAddChar 𝔪 (k * (quotLift v : F) / (g.gen 𝔞 : F))

/-- The normalized Gauss sum `γ_j(𝔠) = q_𝔠^{-1/2} ∑_{x mod 𝔠} χ_𝔠(x)^j e(x/c)` of (3.8) (p. 13). -/
noncomputable def gaussPhase (g : AllowedGen ι 𝔪) (j : ℕ) (𝔠 : Ideal (𝓞 F)) : ℂ :=
  ((Real.sqrt (Ideal.absNorm 𝔠) : ℝ) : ℂ)⁻¹ *
    ∑ᶠ x : SInt 𝔪 ⧸ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪)),
      residueSymbol ι 𝔪 𝔠 (quotLift x) ^ j * sAddChar 𝔪 ((quotLift x : F) / (g.gen 𝔠 : F))

/-- The Hecke character `Λ` of Lemma 3.4 (p. 13) on ideals: completely multiplicative, with
`Λ(𝔭) = −γ₂(𝔭)^3 = −(N 𝔭)^{-1/2} J(ρ_𝔭, ρ_𝔭)` at primes, by (3.9) and (3.11). -/
noncomputable def gaussLambda (ι : F →+* ℂ) (𝔞 : Ideal (𝓞 F)) : ℂ :=
  ((normalizedFactors 𝔞).map fun P =>
    -(((Real.sqrt (Ideal.absNorm P) : ℝ) : ℂ)⁻¹ * cubicJacobiSum ι P)).prod

/-- The finite-order Hecke character `G` of Lemma 3.4 (p. 13) on ideals: completely
multiplicative, with `G(𝔭) = conj(χ_𝔭(4)) γ₃(𝔭)` at primes, (3.9). -/
noncomputable def gaussG (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) : ℂ :=
  ((normalizedFactors 𝔞).map fun P =>
    starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P 4) * gaussPhase g 3 P).prod

/-- `ϑ = conj(Λ) conj(G) η` (p. 15), with `η` the values of `χ`. -/
noncomputable def HeckeChar.thetaChar (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (𝔞 : Ideal (𝓞 F)) : ℂ :=
  starRingEnd ℂ (gaussLambda ι 𝔞) * starRingEnd ℂ (gaussG g 𝔞) * χ.toFun 𝔞

/-- The Gaussian `P_G(t) = (2√π)^{-1} exp(−(log t)^2/4)` of (4.1) (p. 16). -/
noncomputable def gaussianPG (t : ℝ) : ℝ :=
  (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4)

/-- The theta sum `B_m(Z)` of (4.2) (p. 16): the sum over squarefree exterior `𝔠` and exterior
`𝔫` of `γ₂(𝔠) q_𝔠^{-1/2} q_𝔫^{-1} ϑ(𝔄) χ_𝔄(m) P_G(q_𝔄/Z)`, with `𝔄 = 𝔠 𝔫^3`. -/
noncomputable def HeckeChar.thetaSum (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (m : SInt 𝔪)
    (Z : ℝ) : ℂ :=
  ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
      {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
    gaussPhase g 2 p.1.1 /
        ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
      χ.thetaChar g (p.1.1 * p.2.1 ^ 3) * residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) m *
      ((gaussianPG (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) / Z) : ℝ) : ℂ)

/-- Row classes: nonzero `m ∈ R` modulo `U_S^6`, as pairs `(𝔟, ε)` with `m = ε b`, `b` the
allowed generator of the exterior ideal `𝔟 = (m)R` and `ε ∈ U_S / U_S^6`. -/
abbrev RowClass (𝔪 : Ideal (𝓞 F)) : Type _ :=
  {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟} × SClass 𝔪

/-- The element `m = ε b` of `R` representing a row class. -/
noncomputable def rowElt (g : AllowedGen ι 𝔪) (r : RowClass 𝔪) : SInt 𝔪 :=
  r.2.rep * g.gen r.1.1

/-- The additive factor of the probe (7.3) (p. 42) at a row class `m`, with the integral over
`F_S^1 / U_S^6` unfolded against the classes `m U_S^6`:
`∑_𝔰 Y^{-1} W₁(q_𝔰/Y) (q_𝔰 X)^{-1/2} q_𝔰^{-1/2} g_𝔰(−m) V(q_m/(q_𝔰 X))`, where
`V(T) = ∫_{F_S^1} W₀(t ℓ_T) dt` is the norm-sheet profile of the weight `W₀`. -/
noncomputable def additiveFactor (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ) (X Y : ℝ)
    (r : RowClass 𝔪) : ℂ :=
  ∑' 𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰},
    ((Y⁻¹ * W₁ (Ideal.absNorm 𝔰.1 / Y) / Real.sqrt (Ideal.absNorm 𝔰.1 * X) /
        Real.sqrt (Ideal.absNorm 𝔰.1) * V (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) : ℝ) :
        ℂ) * gaussSumAt g 𝔰.1 (-((rowElt g r : SInt 𝔪) : F))

/-- The probe `I(X, Y, Z)` of (7.3) (p. 42), unfolded over the row classes:
`∑_m (additive factor at m) · B_m(Z)`. -/
noncomputable def HeckeChar.probe (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (W₁ V : ℝ → ℝ)
    (X Y Z : ℝ) : ℂ :=
  ∑' r : RowClass 𝔪, additiveFactor g W₁ V X Y r * χ.thetaSum g (rowElt g r) Z

open Classical in
/-- The squarefree part `𝔡 = ∏_{v_𝔭(𝔟) = 1} 𝔭` of `𝔟` (p. 16); `𝔟 = 𝔥 𝔡` with `𝔥` powerful. -/
noncomputable def simplePart (𝔟 : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ((normalizedFactors 𝔟).toFinset.filter fun P => (normalizedFactors 𝔟).count P = 1).prod id

open Classical in
/-- `F(s, A, h)` of (7.7) (p. 44): the sum over `d mod 𝔰` with `h ≡ A d (mod 𝔰)` of
`χ_𝔰(d) g_{χ_𝔄}(A, (h − A d)/s)`, with `s, A` the allowed generators of `𝔰, 𝔄`. -/
noncomputable def poissonFactor (g : AllowedGen ι 𝔪) (𝔰 𝔄 : Ideal (𝓞 F)) (h : SInt 𝔪) : ℂ :=
  ∑ᶠ d : SInt 𝔪 ⧸ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)),
    if h - g.gen 𝔄 * quotLift d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) then
      residueSymbol ι 𝔪 𝔰 (quotLift d) *
        gaussSumAt g 𝔄 (((h - g.gen 𝔄 * quotLift d : SInt 𝔪) : F) / (g.gen 𝔰 : F))
    else 0

/-- Frequency classes `u ∈ 𝒰` (Lemma 3.3, p. 12): nonzero `u ∈ R` with exterior valuations in
`{0, …, 5}`, modulo `U_S^6`, as pairs `(𝔲, ε)` with `𝔲 = (u)R` sixth-power-free and
`u = ε · (allowed generator of 𝔲)`. -/
abbrev FreqClass (𝔪 : Ideal (𝓞 F)) : Type _ :=
  {𝔲 : Ideal (𝓞 F) // IsExterior 𝔪 𝔲 ∧ IsSixthPowerFree 𝔲} × SClass 𝔪

/-- The element `u ∈ R` representing a frequency class. -/
noncomputable def freqElt (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪) : SInt 𝔪 :=
  r.2.rep * g.gen r.1.1

/-- The principal frequency class `u = 1`. -/
noncomputable def principalFreq (𝔪 : Ideal (𝓞 F)) : FreqClass 𝔪 :=
  (⟨⊤, ⟨top_ne_bot, top_sup_eq _⟩, fun J hJ =>
    (isUnit_pow_iff (by norm_num : (6 : ℕ) ≠ 0)).1
      (isUnit_of_dvd_one (by rwa [Ideal.one_eq_top]))⟩, 1)

/-- The Dirichlet series `ℱ_u(ξ, w, z)` of (7.11) (p. 46): the sum over squarefree exterior `𝔠`
and exterior `𝔫, 𝔰, 𝔯` of `γ₂(𝔠) ϑ(𝔄) F(s, A, u r^6) q_𝔠^{-1/2-ξ} q_𝔫^{-1-3ξ} q_𝔰^{-w}
q_𝔯^{-6z}`, with `𝔄 = 𝔠 𝔫^3`. -/
noncomputable def HeckeChar.freqSeries (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (u : SInt 𝔪)
    (ξ w z : ℂ) : ℂ :=
  ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
      {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰} ×
      {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯},
    gaussPhase g 2 p.1.1 * χ.thetaChar g (p.1.1 * p.2.1.1 ^ 3) *
      poissonFactor g p.2.2.1.1 (p.1.1 * p.2.1.1 ^ 3) (u * g.gen p.2.2.2.1 ^ 6) *
      (Ideal.absNorm p.1.1 : ℂ) ^ (-(1 / 2 + ξ)) * (Ideal.absNorm p.2.1.1 : ℂ) ^ (-(1 + 3 * ξ)) *
      (Ideal.absNorm p.2.2.1.1 : ℂ) ^ (-w) * (Ideal.absNorm p.2.2.2.1 : ℂ) ^ (-(6 * z))

/-- The row of the frequency class `u` in the triple Mellin integral (7.10) (p. 46):
`(2πi)^{-3} ∫_{(4)} ∫_{(4)} ∫_{(2)} X^{1/2-z} Z^{ξ+z-1} Y^{w-1} e^{(ξ+z-1)^2} M(z) Ŵ₁(w)
q_u^{-z} ℱ_u(ξ, w, z) dz dw dξ`, written on the lines `ξ = 4 + iτ₁`, `w = 4 + iτ₂`, `z = 2 + iτ₃`;
`Ŵ₁` is the Mellin transform of `W₁`. -/
noncomputable def HeckeChar.rowIntegral (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (W₁ : ℝ → ℝ)
    (M : ℂ → ℂ) (r : FreqClass 𝔪) (X Y Z : ℝ) : ℂ :=
  ((2 * Real.pi) ^ 3 : ℂ)⁻¹ * ∫ τ₁ : ℝ, ∫ τ₂ : ℝ, ∫ τ₃ : ℝ,
    (X : ℂ) ^ ((1 / 2 : ℂ) - (2 + τ₃ * Complex.I)) *
      (Z : ℂ) ^ ((4 + τ₁ * Complex.I) + (2 + τ₃ * Complex.I) - 1) *
      (Y : ℂ) ^ ((4 + τ₂ * Complex.I) - 1) *
      Complex.exp (((4 + τ₁ * Complex.I) + (2 + τ₃ * Complex.I) - 1) ^ 2) *
      M (2 + τ₃ * Complex.I) * mellin (fun t => (W₁ t : ℂ)) (4 + τ₂ * Complex.I) *
      (Ideal.absNorm r.1.1 : ℂ) ^ (-(2 + τ₃ * Complex.I)) *
      χ.freqSeries g (freqElt g r) (4 + τ₁ * Complex.I) (4 + τ₂ * Complex.I)
        (2 + τ₃ * Complex.I)

/-- `R_S = Res_{s=1} ζ_F^S(s)` (p. 56): the residue of the Dedekind zeta function times
`∏ (1 − N P^{-1})` over the nonzero primes `P` containing `𝔪`. -/
noncomputable def sZetaResidue (𝔪 : Ideal (𝓞 F)) : ℝ :=
  NumberField.dedekindZeta_residue F *
    ∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}, (1 - (Ideal.absNorm P : ℝ)⁻¹)

/-- The constant `c₀ = (R_S^2/6) M(1/6) Ŵ₁(1)` of (8.13) (p. 56). -/
noncomputable def principalConstant (𝔪 : Ideal (𝓞 F)) (W₁ : ℝ → ℝ) (M : ℂ → ℂ) : ℂ :=
  ((sZetaResidue 𝔪 ^ 2 / 6 : ℝ) : ℂ) * M (1 / 6) * mellin (fun t => (W₁ t : ℂ)) 1

/-- The weight class of `W₁` (p. 42) and of the norm-sheet profile `V` of `W₀`: smooth, with
compact support in `(0, ∞)`. -/
def IsProbeWeight (W : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) W ∧ HasCompactSupport W ∧ tsupport W ⊆ Set.Ioi 0

/-- The class of the Mellin transform `M` of (7.1)–(7.2) (p. 42): holomorphic on `Re z > 0`, and
`O_{a,b,A}((1 + |Im z|)^{-A})` on every strip `a ≤ Re z ≤ b` with `a > 0`, for every `A`. -/
def IsMellinWeight (M : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ M {z | 0 < z.re} ∧
    ∀ a b A : ℝ, 0 < a → ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖M z‖ ≤ C * (1 + |z.im|) ^ (-A)

end ArtinPrimitiveRoots



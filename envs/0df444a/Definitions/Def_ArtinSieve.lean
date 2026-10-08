-- Prove2me | Definitions.Def_ArtinSieve
-- name    : ArtinSieve
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T09:26:31.873176+00:00
-- url     : https://prove2.me/theorems/afa4afb0-d3d0-443b-a960-d134ce161bb2
-- title:
--   Sieve parameters, prime groups and marks, rough-number densities, and the construction weights and masses of §§10–12
-- statement:
--   Definitions for §§10–12 of OpenAI's *Primitive roots for every admissible integer base* (2026), pp. 63–79. Throughout, $L = \log x$.
--
--   - `IsRough y m`: $m > 0$ and every prime factor of $m$ exceeds $y$; this is $P^-(m) > y$. The paper (p. 63): “For an integer $m > 1$, write $P^-(m)$ for its least prime factor, and put $P^-(1) = \infty$. Thus $P^-(m) > y$ means that $m$ is $y$-rough.” Only comparisons $P^-(m) > y$ occur, so $P^-$ itself is not defined; the predicate is false at $m = 0$.
--   - `mertensProduct y`, `sieveLevel x`: $V(y) = \prod_{p \le y}(1 - 1/p)$ and $W = \exp(L^{0.24})$, from (10.1), p. 63: “$L = \log x$, $W = \exp(L^{0.24})$, $V(y) = \prod_{p \le y}\bigl(1 - \frac1p\bigr)$.”
--   - `primeGroup x a`, `groupPrimes x a`: the prime group $\{p \text{ prime} : \exp(L^{a}) \le p \le \exp(2L^{a})\}$, and the union $\bigcup_i \mathcal P_i$ of the groups for band exponents `a : Fin K → ℝ`. (10.2), p. 63: “$\mathcal P_i = \{p \text{ prime} : \exp(L^{a_i}) \le p \le \exp(2L^{a_i})\}$ $(1 \le i \le K)$.”
--   - `groupPart x a h`: $h_{\mathcal P} = \prod_{p \in \bigcup_i \mathcal P_i} p^{v_p(h)}$, (10.3), p. 63.
--   - `groupReciprocalSum`, `groupOmega`, `markOmega`, `mark q x a h`: $V_i$, $\omega_i(h)$, $\omega(h)$ and the mark $\mathcal W(h)$ with parameter $q$, (10.4), p. 63: “$V_i = \sum_{p \in \mathcal P_i} \frac1p$, $\omega_i(h) = \sum_{p \in \mathcal P_i} \mathbf 1_{p \mid h}$, $\omega(h) = \sum_{i=1}^K \omega_i(h)$, $\mathcal W(h) = q^{\omega(h) - K} \prod_{i=1}^K \frac{\omega_i(h)}{V_i}$, $0 < q < 1$.”
--   - `roughDensityTerm γ w j`, `roughDensity γ w`: $D_{\gamma,j}(w)$ and $D_\gamma(w) = \sum_{j \ge 1} D_{\gamma,j}(w)$, (10.11), p. 66: “$D_\gamma(w) = \sum_{j \ge 1} D_{\gamma,j}(w)$, $D_{\gamma,1}(w) = \frac1w$, $D_{\gamma,j}(w) = \frac1{j!}\int_{t_i \ge \gamma\ (1 \le i < j),\ \sum_{i<j} t_i \le w - \gamma} \frac{1}{w - \sum_{i<j} t_i} \prod_{i<j} \frac{\mathrm dt_i}{t_i}$ $(j \ge 2)$.” For $j \ge 2$ the integral is a Lebesgue integral over the closed simplex in $\mathbb R^{j-1}$; the term at $j = 0$ is $0$.
--   - `predecessorIndicator x a c h`, `constructionWeight M c u Ψ x a d`: $F(h)$ and $w(d)$, with marks of parameter $q = 1/2$, (12.2), p. 74: “$F(h) = \mathbf 1_{\{h/h_{\mathcal P} = cQ \text{ for a prime } Q > x^{0.9}\}}$, $w(d) = \mathbf 1_{\{d \equiv u \pmod M\}}\Psi(d/x)F(d-1)\mathcal W(d-1)$ $(d \ge 2)$. Set $w(1) = 0$.” The Lean definition also gives $w(0) = 0$.
--   - `roughIndicator x γ m`, `roughProxy x γ m`: $R_\gamma(m)$ and $B_\gamma(m)$, (12.5), p. 75: “$R_\gamma(m) = \mathbf 1_{\{P^-(m) > x^\gamma\}}$, $B_\gamma(m) = \frac{D_\gamma(\log m/L)}{LV(W)}\mathbf 1_{\{P^-(m) > W\}}$.” The paper puts them for integers $m > x^\gamma$; the Lean formulas are defined for every $m$.
--   - `IsGroupInteger x a r`: $r > 0$ and every prime factor of $r$ lies in $\bigcup_i \mathcal P_i$. The paper (p. 74): “Call a positive integer a *group integer* if all its prime divisors belong to $\bigcup_i \mathcal P_i$, and include $1$.”
--   - `harmonicMass x a`, `predecessorMass M c u Ψ x r`, `totalMass M c u Ψ x a`: $J_0$, $A_r$ and $X_0$, (12.8), p. 76: “$J_0 = \sum_r \frac{\mathcal W(r)}{r}$, $A_r = \sum_{Q > x^{0.9} \text{ prime},\ crQ+1 \equiv u \pmod M} \Psi((crQ+1)/x)$, $X_0 = \sum_d w(d) = \sum_r \mathcal W(r)A_r$”, with $r$ over group integers. $X_0$ is defined as $\sum_d w(d)$.
--   - `predecessorMassDvd M c u Ψ x r ℓ`, `localDensity M r ℓ`, `massRemainder M c u Ψ x r ℓ`: $A_r(\ell)$, $g_r(\ell)$ and $E_r(\ell)$, (12.12), p. 77: “For an odd squarefree integer $\ell$, let $A_r(\ell)$ denote the sum defining $A_r$ with the additional condition $\ell \mid crQ + 1$, and set $g_r(\ell) = \frac{\mathbf 1_{\{(\ell, Mr) = 1\}}}{\varphi(\ell)}$, $E_r(\ell) = A_r(\ell) - g_r(\ell)A_r$.” The Lean definitions apply to every $\ell$, and $A_r = A_r(1)$.
--   - `singularSeries M`: $\mathfrak S_M$, (12.19), p. 79: “$\mathfrak S_M = 2\prod_{p > 2}\bigl(1 - \frac{1}{(p-1)^2}\bigr)\prod_{p \mid M,\ p > 2}\bigl(1 - \frac{1}{p-1}\bigr)^{-1} > 0$.”
--   - `primeCountingAP Y q v`, `logIntegral Y`: $\pi(Y; q, v) = \#\{p \le Y \text{ prime} : p \equiv v \pmod q\}$ and $\mathrm{Li}(Y) = \int_2^Y dt/\log t$, as in (12.16), p. 77: “Here $\mathrm{Li}(Y) = \int_2^Y dt/\log t$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 63–84, §§10–12 (sieve parameters, marks, rough density, weights)

import Mathlib

namespace ArtinPrimitiveRoots

open Real

/-! ## The sieve parameters of §10 -/

/-- The roughness condition `P^-(m) > y` of §10 (after (10.1)): `m` is a positive integer all of
whose prime factors exceed `y`. Here `P^-(m)` is the least prime factor of `m > 1`, and
`P^-(1) = ∞`. -/
def IsRough (y : ℝ) (m : ℕ) : Prop :=
  0 < m ∧ ∀ p ∈ m.primeFactors, y < (p : ℝ)

/-- The product `V(y) = ∏_{p ≤ y} (1 - 1/p)` over primes, (10.1). -/
noncomputable def mertensProduct (y : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-- The roughness level `W = exp(L^{0.24})`, where `L = log x`, (10.1). -/
noncomputable def sieveLevel (x : ℝ) : ℝ :=
  exp (log x ^ (0.24 : ℝ))

/-! ## Prime groups and marks, (10.2)–(10.4) -/

/-- The prime group `𝒫 = {p prime : exp(L^a) ≤ p ≤ exp(2 L^a)}` with `L = log x`, (10.2);
the `i`th group `𝒫_i` is `primeGroup x (a i)`. -/
noncomputable def primeGroup (x a : ℝ) : Finset ℕ :=
  (Finset.range (⌊exp (2 * log x ^ a)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ exp (log x ^ a) ≤ (p : ℝ))

/-- The set `⋃_i 𝒫_i` of group primes for the band exponents `a_1, …, a_K`, (10.2). -/
noncomputable def groupPrimes (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun i => primeGroup x (a i)

/-- The complete group part `h_𝒫 = ∏_{p ∈ ⋃_i 𝒫_i} p^{v_p(h)}` of `h`, (10.3). -/
noncomputable def groupPart (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : ℕ :=
  ∏ p ∈ groupPrimes x a, p ^ h.factorization p

/-- The reciprocal sum `V_i = ∑_{p ∈ 𝒫_i} 1/p` of a prime group, (10.4). -/
noncomputable def groupReciprocalSum (x a : ℝ) : ℝ :=
  ∑ p ∈ primeGroup x a, 1 / (p : ℝ)

/-- `ω_i(h) = ∑_{p ∈ 𝒫_i} 1_{p ∣ h}`, the number of primes of the group dividing `h`, (10.4). -/
noncomputable def groupOmega (x a : ℝ) (h : ℕ) : ℕ :=
  ((primeGroup x a).filter (· ∣ h)).card

/-- `ω(h) = ∑_{i=1}^K ω_i(h)`, (10.4). -/
noncomputable def markOmega (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : ℕ :=
  ∑ i, groupOmega x (a i) h

/-- The mark `𝒲(h) = q^{ω(h) - K} ∏_{i=1}^K ω_i(h) / V_i` with parameter `q`, (10.4). -/
noncomputable def mark (q x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : ℝ :=
  q ^ ((markOmega x a h : ℤ) - K) *
    ∏ i, (groupOmega x (a i) h : ℝ) / groupReciprocalSum x (a i)

/-! ## The rough-number density, (10.11) -/

/-- The terms `D_{γ,j}(w)` of (10.11): `D_{γ,1}(w) = 1/w` and, for `j ≥ 2`,
`D_{γ,j}(w) = (1/j!) ∫_{t_i ≥ γ (i < j), ∑_{i<j} t_i ≤ w - γ} (w - ∑_{i<j} t_i)⁻¹ ∏_{i<j} dt_i/t_i`.
The value at `j = 0` is `0` (the sum in (10.11) starts at `j = 1`). -/
noncomputable def roughDensityTerm (γ w : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / w
  | j + 2 => (1 / ((j + 2).factorial : ℝ)) *
      ∫ t in {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ},
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹

/-- The rough-number density `D_γ(w) = ∑_{j ≥ 1} D_{γ,j}(w)` for `w > γ > 0`, (10.11). -/
noncomputable def roughDensity (γ w : ℝ) : ℝ :=
  ∑' j : ℕ, roughDensityTerm γ w j

/-! ## The weights of §12, (12.2) and (12.5) -/

/-- `F(h) = 1{h / h_𝒫 = cQ for a prime Q > x^{0.9}}`, (12.2). -/
noncomputable def predecessorIndicator (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) : ℝ := by
  classical
  exact if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ h / groupPart x a h = c * Q then 1 else 0

/-- The weight `w(d) = 1{d ≡ u (mod M)} Ψ(d/x) F(d - 1) 𝒲(d - 1)` for `d ≥ 2`, with marks of
parameter `q = 1/2`, (12.2); and `w(1) = 0` (also `w(0) = 0`). -/
noncomputable def constructionWeight (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) (d : ℕ) : ℝ := by
  classical
  exact if 2 ≤ d ∧ (d : ℤ) ≡ u [ZMOD M] then
    Ψ (d / x) * predecessorIndicator x a c (d - 1) * mark (1 / 2) x a (d - 1) else 0

/-- `R_γ(m) = 1{P^-(m) > x^γ}`, (12.5). -/
noncomputable def roughIndicator (x γ : ℝ) (m : ℕ) : ℝ := by
  classical
  exact if IsRough (x ^ γ) m then 1 else 0

/-- `B_γ(m) = D_γ(log m / L) / (L V(W)) · 1{P^-(m) > W}`, (12.5). -/
noncomputable def roughProxy (x γ : ℝ) (m : ℕ) : ℝ := by
  classical
  exact roughDensity γ (log m / log x) / (log x * mertensProduct (sieveLevel x)) *
    if IsRough (sieveLevel x) m then 1 else 0

/-! ## Masses and local densities of §12, (12.8), (12.12), (12.19) -/

/-- A group integer: a positive integer all of whose prime divisors belong to `⋃_i 𝒫_i`
(including `1`), §12.1. -/
def IsGroupInteger (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (r : ℕ) : Prop :=
  0 < r ∧ ∀ p ∈ r.primeFactors, p ∈ groupPrimes x a

/-- The harmonic mass `J_0 = ∑_r 𝒲(r)/r` over group integers `r`, with `q = 1/2`, (12.8). -/
noncomputable def harmonicMass (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : ℝ :=
  ∑' r : {r : ℕ // IsGroupInteger x a r}, mark (1 / 2) x a r / (r : ℝ)

/-- `A_r(ℓ) = ∑_{Q > x^{0.9} prime, crQ+1 ≡ u (mod M), ℓ ∣ crQ+1} Ψ((crQ+1)/x)`, (12.8) and
(12.12); `A_r = A_r(1)`. -/
noncomputable def predecessorMassDvd (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r ℓ : ℕ) : ℝ :=
  ∑' Q : {Q : ℕ // Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
      ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1},
    Ψ (((c * r * Q.1 + 1 : ℕ) : ℝ) / x)

/-- `A_r = ∑_{Q > x^{0.9} prime, crQ+1 ≡ u (mod M)} Ψ((crQ+1)/x)`, (12.8). -/
noncomputable def predecessorMass (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  predecessorMassDvd M c u Ψ x r 1

/-- The total mass `X_0 = ∑_d w(d)`, (12.8). -/
noncomputable def totalMass (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) : ℝ :=
  ∑' d : ℕ, constructionWeight M c u Ψ x a d

/-- The local density `g_r(ℓ) = 1{(ℓ, Mr) = 1} / φ(ℓ)`, (12.12). -/
noncomputable def localDensity (M r ℓ : ℕ) : ℝ :=
  if Nat.Coprime ℓ (M * r) then 1 / (Nat.totient ℓ : ℝ) else 0

/-- The remainder `E_r(ℓ) = A_r(ℓ) - g_r(ℓ) A_r`, (12.12). -/
noncomputable def massRemainder (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r ℓ : ℕ) : ℝ :=
  predecessorMassDvd M c u Ψ x r ℓ - localDensity M r ℓ * predecessorMass M c u Ψ x r

/-- The constant `𝔖_M = 2 ∏_{p>2} (1 - 1/(p-1)^2) ∏_{p ∣ M, p > 2} (1 - 1/(p-1))⁻¹`, (12.19). -/
noncomputable def singularSeries (M : ℕ) : ℝ :=
  2 * (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)) *
    ∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹

/-! ## Prime counting in progressions (for the classical inputs) -/

/-- `π(Y; q, v) = #{p ≤ Y prime : p ≡ v (mod q)}`. -/
noncomputable def primeCountingAP (Y : ℝ) (q v : ℕ) : ℕ :=
  ((Finset.range (⌊Y⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ v [MOD q]).card

/-- The logarithmic integral `Li(Y) = ∫_2^Y dt / log t`, as in (12.16). -/
noncomputable def logIntegral (Y : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..Y, 1 / log t

end ArtinPrimitiveRoots



-- Prove2me | Definitions.Def_MixedSpinColorCoding_Counting_Model
-- name    : MixedSpinColorCoding_Counting_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:42.545298+00:00
-- url     : https://prove2.me/theorems/c036320c-ab5a-41ee-a3e3-4b23c3ac75df
-- title:
--   Mixed p-spin Hamiltonian, partition function and second-moment threshold
-- statement:
--   Fix an integer $p_{\max}\ge2$ and real coefficients $\gamma_2,\dots,\gamma_{p_{\max}}$. For $n\ge1$ the disorder $G$ has one coordinate $G^{(p)}_{i_1,\dots,i_p}$ for every order $2\le p\le p_{\max}$ and every **ordered** tuple $(i_1,\dots,i_p)\in[n]^p$, repeated indices included; under the disorder law these coordinates are independent standard Gaussians. For $\sigma\in\{\pm1\}^n$,
--   $$H_G(\sigma)=\sum_{p=2}^{p_{\max}}\frac{\gamma_p}{n^{(p-1)/2}}\sum_{i_1,\dots,i_p=1}^nG^{(p)}_{i_1,\dots,i_p}\sigma_{i_1}\cdots\sigma_{i_p},\qquad Z_G(z)=2^{-n}\sum_{\sigma}e^{zH_G(\sigma)},$$
--   with $z$ real or complex, and $Y_G(z)=e^{-n\xi(1)z^2/2}Z_G(z)$, where $\xi(q)=\sum_{p=2}^{p_{\max}}\gamma_p^2q^p$ (so $\mathbb E_GZ_G(z)=e^{n\xi(1)z^2/2}$). The mixture is nonzero when some $\gamma_p\ne0$. With the natural-log binary entropy $h$ ($h(0)=h(1)=0$), the second-moment threshold is
--   $$\beta_{2\mathrm{nd}}=\Big(\inf_{0<q\le1}\frac{\log2-h((1+q)/2)}{\xi(q)}\Big)^{1/2}.$$
--   For a nonzero mixture the set under the infimum is nonempty and bounded below by $0$, so the real infimum is the true one. Sites are zero-based `Fin n`, spins are units of $\mathbb Z$, and an order $p$ is stored as $p=k+2$.
-- source:
--   Alina Harbuzova, Saba Lepsveridze, Mahbod Majid, Ankur Moitra, STOC 2027 submission #592 (October 2026), Color Coding for the Sherrington–Kirkpatrick Model, §1 Eqs. (1)–(4) and Definition 1.1, printed p.1 / PDF p.3; §A.1, printed p.20 / PDF p.22. PDF SHA-256 5559e422541f71e2e270b74941f426295f0ea249bd88d4ff218bb950ad81646b; citation_basis: published.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-!
# The mixed p-spin model, its partition function and the second-moment threshold

A. Harbuzova, S. Lepsveridze, M. Majid, A. Moitra, *Color Coding for the
Sherrington–Kirkpatrick Model*, STOC 2027 submission #592 (October 2026), §1, Eqs. (1)–(4),
Definition 1.1 (PDF p.3), and §A.1, the normalized partition function (PDF p.22).

* Sites are `Fin n` (the source's `[n]`, zero based). Spins are `σ : Fin n → ℤˣ`, i.e.
  `σ i ∈ {−1, +1}`; the uniform law `ρ` on `{±1}ⁿ` is the normalized sum `2^{-n} ∑_σ`.
* An interaction order `p ∈ {2, …, pmax}` is written `p = k + 2` with `k : Fin (pmax - 1)`.
  For each order the disorder has one coordinate `G_{p,i}` per **ordered** tuple
  `i : Fin p → Fin n`, repeated indices included. All coordinates are independent `N(0,1)`
  (`disorderLaw`, a finite product of `gaussianReal 0 1`).
* `n^{(p-1)/2}` is the real power (`Real.rpow`), so half-integer exponents are kept.
* `γ : ℕ → ℝ`; only the values `γ 2, …, γ pmax` are used.
* `binEntropy` is Mathlib's natural-log binary entropy, `h(u) = −u log u − (1−u) log(1−u)`,
  with `h(0) = h(1) = 0`.
* The threshold takes the real infimum of the ratio over `q ∈ (0,1]`. For a nonzero mixture this
  set is nonempty (`q = 1`) and bounded below by `0` (`h ≤ log 2` and `ξ(q) > 0`), so `sInf` is
  the true infimum and `Real.sqrt` is applied to a nonnegative number.
-/

namespace MixedSpinColorCoding.Counting

/-- Disorder coordinates: an order `p = k + 2 ∈ {2, …, pmax}` and an ordered tuple in `[n]^p`. -/
abbrev DisorderIndex (n pmax : ℕ) := Σ k : Fin (pmax - 1), (Fin (k.val + 2) → Fin n)

/-- A disorder realization `G = (G^{(p)}_{i})`. -/
abbrev Disorder (n pmax : ℕ) := DisorderIndex n pmax → ℝ

/-- The law of the disorder: independent standard Gaussians across orders and tuples. -/
noncomputable def disorderLaw (n pmax : ℕ) : Measure (Disorder n pmax) :=
  Measure.pi (fun _ : DisorderIndex n pmax => gaussianReal 0 1)

/-- The real value `±1` of a spin. -/
def spinValue (s : ℤˣ) : ℝ := ((s : ℤ) : ℝ)

/-- The mixed p-spin Hamiltonian (1):
`H_G(σ) = ∑_{p=2}^{pmax} γ_p n^{-(p-1)/2} ∑_{i ∈ [n]^p} G_{p,i} σ_{i_1} ⋯ σ_{i_p}`. -/
noncomputable def hamiltonian (n pmax : ℕ) (γ : ℕ → ℝ) (G : Disorder n pmax)
    (σ : Fin n → ℤˣ) : ℝ :=
  ∑ k : Fin (pmax - 1),
    γ (k.val + 2) / (n : ℝ) ^ ((((k.val + 2 : ℕ) : ℝ) - 1) / 2) *
      ∑ i : Fin (k.val + 2) → Fin n, G ⟨k, i⟩ * ∏ a, spinValue (σ (i a))

/-- The partition function `Z_G(β) = E_{σ∼ρ} exp(β H_G(σ))` at real inverse temperature. -/
noncomputable def partitionFunction (n pmax : ℕ) (γ : ℕ → ℝ) (G : Disorder n pmax)
    (β : ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → ℤˣ, Real.exp (β * hamiltonian n pmax γ G σ)

/-- The partition function at a complex argument, `Z_G(z) = E_σ exp(z H_G(σ))`. -/
noncomputable def partitionFunctionC (n pmax : ℕ) (γ : ℕ → ℝ) (G : Disorder n pmax)
    (z : ℂ) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ σ : Fin n → ℤˣ, Complex.exp (z * (hamiltonian n pmax γ G σ : ℂ))

/-- The mixture function `ξ(q) = ∑_{p=2}^{pmax} γ_p² q^p`. -/
noncomputable def xi (pmax : ℕ) (γ : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 pmax, γ p ^ 2 * q ^ p

/-- The normalized partition function `Y_G(z) = e^{-n ξ(1) z²/2} Z_G(z)`
(`E_G Z_G(z) = e^{n ξ(1) z²/2}`, §A.1, PDF p.22). -/
noncomputable def normalizedPartitionFunction (n pmax : ℕ) (γ : ℕ → ℝ) (G : Disorder n pmax)
    (z : ℂ) : ℂ :=
  Complex.exp (-((n : ℂ) * (xi pmax γ 1 : ℂ) * z ^ 2 / 2)) * partitionFunctionC n pmax γ G z

/-- The mixture is nonzero: some `γ_p`, `2 ≤ p ≤ pmax`, is nonzero (equivalently `ξ ≢ 0`). -/
def NonzeroMixture (pmax : ℕ) (γ : ℕ → ℝ) : Prop :=
  ∃ p ∈ Finset.Icc 2 pmax, γ p ≠ 0

/-- The ratio `(log 2 − h((1+q)/2)) / ξ(q)` of Definition 1.1. -/
noncomputable def secondMomentRatio (pmax : ℕ) (γ : ℕ → ℝ) (q : ℝ) : ℝ :=
  (Real.log 2 - Real.binEntropy ((1 + q) / 2)) / xi pmax γ q

/-- Definition 1.1, (4): `β_2nd = (inf_{0<q≤1} (log 2 − h((1+q)/2)) / ξ(q))^{1/2}`. -/
noncomputable def beta2nd (pmax : ℕ) (γ : ℕ → ℝ) : ℝ :=
  Real.sqrt (sInf (secondMomentRatio pmax γ '' Set.Ioc 0 1))

end MixedSpinColorCoding.Counting



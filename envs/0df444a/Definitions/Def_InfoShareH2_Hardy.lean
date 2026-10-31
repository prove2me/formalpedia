-- Prove2me | Definitions.Def_InfoShareH2_Hardy
-- name    : InfoShareH2_Hardy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:43.462155+00:00
-- url     : https://prove2.me/theorems/aa2cfa81-961f-465b-b090-feb1025dde75
-- title:
--   Hardy space $H^2$: outer and inner functions, Blaschke products, singular inner functions, the outer part (29), $S_1(Q)$ and $\tilde C(Q)$
-- statement:
--   This module sets up the Hardy-space vocabulary of §5–§6.
--
--   1. **$H^2$** (p.22) is the space of power series $\tilde\psi(z)=\sum_{n\ge0}\tilde\psi_nz^n$ with $\sum|\tilde\psi_n|^2<\infty$, identified with its coefficient sequence; its values on the unit circle $\mathbb T$ are radial limits.
--   2. **Outer functions** (Definition 3): $\tilde\psi$ is outer if the closed linear span of $\{z^n\tilde\psi:n\ge0\}$ is all of $H^2$.
--   3. **Inner functions** (Definition 4): $|\tilde\psi|=1$ almost everywhere on $\mathbb T$.
--   4. **Blaschke products** (30), Definition 5: $B(z)=c\,z^{m_0}\prod_k\frac{|z_k|}{z_k}\frac{z_k-z}{1-\bar z_kz}$, with $|c|=1$, $m_0\in\mathbb N$, zeros $0<|z_k|<1$ and $\sum_k(1-|z_k|)<\infty$.
--   5. **Singular inner functions** (31), Definition 5: $G(z)=c\exp\bigl(-\int\frac{e^{i\lambda}+z}{e^{i\lambda}-z}\,d\mu(\lambda)\bigr)$, with $|c|=1$ and $\mu$ a finite positive Borel measure on $\mathbb T$ singular with respect to Lebesgue measure.
--   6. **The outer part (Szegő function)** (29): $Q(z)=\exp\bigl(\frac1{2\pi}\int_{-\pi}^{\pi}\frac{e^{i\lambda}+z}{e^{i\lambda}-z}\log|\tilde\psi(e^{i\lambda})|\,d\lambda\bigr)$.
--   7. **$S_1(Q)$** (40): $S_1(Q)=\frac1{2\pi}\int_{-\pi}^{\pi}|Q_I(z)|^2d\lambda$ with $Q_I(z)=\frac{zQ(z)-1}{1-z}$ and $z=e^{-i\lambda}$.
--   8. **$\tilde C(Q)$** (41): $\tilde C(Q)=S_1(Q)+\max\bigl(-\tfrac12\log\frac{\sigma/\sigma_\epsilon}{|Q(0)|},0\bigr)$, and its parametrization $Q_\theta=\exp(\sum_{n\ge0}\theta_nz^n)$ with $\theta_0=-\sum_{n\ge1}\theta_n$ (p.28).
--   9. The inventory variance (8) and the no-sharing forecast error (26), extended to complex coefficient sequences, are used for functions not known to be admissible policies.
--
--   These definitions are reusable for any formalization of Hardy-space factorization or of the Kolmogorov–Szegő prediction theory.
--
--   **Formalization Note** The Blaschke product carries the convergence factors $|z_k|/z_k$ and a unimodular constant (footnote, p.24); the paper's (30) omits both, and without the factors the product diverges for zeros accumulating away from $-1$. A Blaschke product is recorded as data (constant, order at $0$, countable family of zeros) together with the convergence of the product on the disk. The measure of a singular inner function lives on $\mathbb R$ and is carried by $[-\pi,\pi)$. The outer part uses the orientation of (29); for real coefficients it coincides with (32). $S_1$, $\tilde C$ and the extended inventory variance take values in $[0,\infty]$.
--
--   A **Stolz region** at $1$ (Definition 6) is $R(K)=\{z\in\mathbb D:|1-z|\le K(1-|z|)\}$.
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, p.22 (H²), Definitions 3–5 pp.23–24, Definition 6 p.39, (29) p.23, (30)–(31) p.24, (40)–(41) p.27, p.28 (θ-parametrization)

import Mathlib
import Definitions.Def_InfoShareH2_Model

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **The open unit disk** `D = {z ∈ ℂ : |z| < 1}` (p.20, after (27)). -/
def Disk : Set ℂ := Metric.ball (0 : ℂ) 1

/-- **A Stolz region at `1`** (Definition 6, p.39): `R(K) = {z ∈ D : |1 − z| ≤ K (1 − |z|)}`. -/
def StolzRegion (K : ℝ) : Set ℂ := {z | z ∈ Disk ∧ ‖1 - z‖ ≤ K * (1 - ‖z‖)}

/-- **The Hardy space `H²`** (p.22): `H²(D) = {ψ̃(z) = ∑ ψ̃_n zⁿ : ∑ |ψ̃_n|² < ∞}`.
SSRN 4319721 (v. 2024-01-20), §5, p.22.

**Formalization Note** An element of `H²` is represented by its coefficient sequence
`a : ℕ → ℂ` with `∑ |a_n|² < ∞` (the paper's isomorphism `ℓ² ≅ H²(D)`); its function on `D` is
`zTransform a`, its boundary function is the radial limit `boundary a`. -/
def H2 : Set (ℕ → ℂ) := {a | Memℓp a 2}

/-- **Multiplication by `zⁿ` on coefficients**: the `n`-fold right shift,
`(zⁿψ̃)_k = ψ̃_{k−n}` for `k ≥ n` and `0` otherwise. -/
def shiftSeq (n : ℕ) (a : ℕ → ℂ) : ℕ → ℂ := fun k => if n ≤ k then a (k - n) else 0

/-- **Outer functions** (Definition 3, p.23): `ψ̃ ∈ H²` is outer if `E_ψ̃ = H²`, where
`E_ψ̃ = sp{zⁿψ̃ : n ≥ 0}` (the closed linear span). `H²_O` is the class of outer functions.

**Formalization Note** On coefficients, `zⁿψ̃` is `shiftSeq n a`; the closed span is taken in
`ℓ²(ℕ, ℂ)` (`lp (fun _ => ℂ) 2`), the paper's isomorphic copy of `H²`. -/
def IsOuter (a : ℕ → ℂ) : Prop :=
  Memℓp a 2 ∧
    (Submodule.span ℂ {x : lp (fun _ : ℕ => ℂ) 2 | ∃ n : ℕ, (x : ℕ → ℂ) = shiftSeq n a}).topologicalClosure = ⊤

/-- **Inner functions** (Definition 4, p.23): `ψ̃ ∈ H²` is inner if `|ψ̃(z)| = 1` almost everywhere
on `T`.

**Formalization Note** `T` is parametrized by `z = e^{−iλ}`, `λ ∈ (−π, π]`, with Lebesgue measure;
the value on `T` is the radial limit `boundary a λ` (p.22). -/
def IsInner (a : ℕ → ℂ) : Prop :=
  Memℓp a 2 ∧ ∀ᵐ lam ∂(volume.restrict (Set.Ioc (-Real.pi) Real.pi)), ‖boundary a lam‖ = 1

/-- **Conjugate symmetry** (§9.3, p.39): `ψ̃(z̄) = \overline{ψ̃(z)}` for `z ∈ D`. -/
def IsConjSymm (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ Disk, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)

/-- **Data of a Blaschke product** (30), p.24, with the unimodular constant of the footnote on p.24:
`B(z) = c · z^{m₀} · ∏_k (|z_k|/z_k) (z_k − z)/(1 − \bar z_k z)`, with `|c| = 1`, `m₀ ∈ ℕ`, and a
finite or countable family of zeros `z_k ∈ D ∖ {0}` (counted with multiplicity) with
`∑_k (1 − |z_k|) < ∞`.

**Formalization Note** The paper writes (30) without the convergence factors `|z_k|/z_k` and says
(footnote, p.24) that the product may differ from (30) by a unimodular constant. Without the
factors, (30) diverges for zeros accumulating away from `−1`; with them it is the standard
convergent Blaschke product, and the unimodular constant is carried by `c`. The field `hmult`
records that the product converges for `z ∈ D` (true for every Blaschke family); it fixes
`tprod` to the actual product. -/
structure BlaschkeData where
  c : ℂ
  hc : ‖c‖ = 1
  m0 : ℕ
  ι : Type
  [hcount : Countable ι]
  zs : ι → ℂ
  hzs : ∀ k, zs k ≠ 0 ∧ ‖zs k‖ < 1
  hsum : Summable (fun k => 1 - ‖zs k‖)
  hmult : ∀ z ∈ Disk, Multipliable
    (fun k => ((‖zs k‖ : ℂ) / zs k) * (zs k - z) / (1 - (starRingEnd ℂ) (zs k) * z))

/-- The Blaschke product of `BlaschkeData` evaluated at `z`. -/
noncomputable def BlaschkeData.eval (B : BlaschkeData) (z : ℂ) : ℂ :=
  B.c * z ^ B.m0 *
    ∏' k, ((‖B.zs k‖ : ℂ) / B.zs k) * (B.zs k - z) / (1 - (starRingEnd ℂ) (B.zs k) * z)

/-- **`H²_B`, the Blaschke products** (Definition 5, p.24): functions in `H²` that admit a
representation (30). -/
def IsBlaschke (b : ℕ → ℂ) : Prop :=
  Memℓp b 2 ∧ ∃ B : BlaschkeData, ∀ z ∈ Disk, zTransform b z = B.eval z

/-- **Data of a singular inner function** (31), p.24:
`G(z) = c exp(−∫_{−π}^{π} (e^{iλ} + z)/(e^{iλ} − z) dµ(λ))`, with `c ∈ T` and `µ` a positive finite
Borel measure on `T` singular with respect to Lebesgue measure.

**Formalization Note** `T` is parametrized by `λ ∈ [−π, π)` via `e^{iλ}`: `µ` is a finite measure on
`ℝ` carried by `[−π, π)` and mutually singular with Lebesgue measure. `µ = 0` is allowed. -/
structure SingularData where
  c : ℂ
  hc : ‖c‖ = 1
  μ : Measure ℝ
  [hfin : IsFiniteMeasure μ]
  hsupp : μ (Set.Ico (-Real.pi) Real.pi)ᶜ = 0
  hsing : μ.MutuallySingular volume

/-- The singular inner function of `SingularData` evaluated at `z`. -/
noncomputable def SingularData.eval (G : SingularData) (z : ℂ) : ℂ :=
  G.c * exp (-∫ lam, (exp ((lam : ℂ) * I) + z) / (exp ((lam : ℂ) * I) - z) ∂G.μ)

/-- **`H²_S`, the singular inner functions** (Definition 5, p.24): functions in `H²` that admit a
representation (31). -/
def IsSingularInner (g : ℕ → ℂ) : Prop :=
  Memℓp g 2 ∧ ∃ G : SingularData, ∀ z ∈ Disk, zTransform g z = G.eval z

/-- **The outer part (Szegő function) of `ψ̃`** (29), p.23 (and (32), p.24):
`Q(z) = exp((1/2π) ∫_{−π}^{π} (e^{iλ} + z)/(e^{iλ} − z) log |ψ̃(e^{iλ})| dλ)`, `z ∈ D`.

**Formalization Note** Orientation of (29): `|ψ̃(e^{iλ})|` is the boundary value at `e^{−i(−λ)}`,
i.e. `boundary a (−λ)`. For real coefficients this equals the printed (32), which has
`log |ψ̃(e^{−iλ})|`; for complex coefficients only (29) gives the outer factor (see Lemma 2). -/
noncomputable def outerPart (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  exp ((1 / (2 * Real.pi) : ℂ) * ∫ lam in (-Real.pi)..Real.pi,
    (exp ((lam : ℂ) * I) + z) / (exp ((lam : ℂ) * I) - z) * (Real.log ‖boundary a (-lam)‖ : ℂ))

/-- **`S1(Q)`** (40), p.27: `S1(Q) = (1/2π) ∫_{−π}^{π} Q_I(z) Q_I(\bar z) dλ` with
`Q_I(z) = (zQ(z) − 1)/(1 − z)` and `z = e^{−iλ}`.

**Formalization Note** `Q_I(z) Q_I(\bar z) = |Q_I(z)|²` for the conjugate-symmetric `Q` of the paper;
the integral is a lower Lebesgue integral in `ℝ≥0∞`, so `S1(Q) = ∞` is allowed. The boundary value
`Q(e^{−iλ})` is the radial limit. The single point `λ = 0` (`z = 1`) is Lebesgue-null. -/
noncomputable def S1 (Q : ℂ → ℂ) : ENNReal :=
  ENNReal.ofReal (1 / (2 * Real.pi)) *
    ∫⁻ lam in Set.Ioc (-Real.pi) Real.pi,
      ‖(exp (-(lam : ℂ) * I) * radialLim Q lam - 1) / (1 - exp (-(lam : ℂ) * I))‖ₑ ^ 2

/-- **The `θ`-parametrization of `Q`** (p.28; §9.7 Step 2, p.43). Given the free coefficients
`t k = θ_{k+1}` (`k ≥ 0`), set `θ_0 = −∑_{n≥1} θ_n` ("according to Assumption 1", i.e. `Q(1) = 1`)
and `Q_θ(z) = exp(∑_{n≥0} θ_n zⁿ)`.

**Formalization Note** `∑_{n≥1} θ_n` is the limit of the partial sums (`limUnder`); it is used only
where these partial sums converge. -/
noncomputable def QOfTheta (t : ℕ → ℝ) (z : ℂ) : ℂ :=
  exp (-(limUnder atTop (fun N => ∑ k ∈ Finset.range N, t k) : ℂ) +
    ∑' k, (t k : ℂ) * z ^ (k + 1))

/-- **The objective `C̃(Q)`** (41), p.27:
`C̃(Q) = S1(Q) + max(−(1/2) log((σ/σ_ε)/|Q(0)|), 0)`.

**Formalization Note** Valued in `ℝ≥0∞` because `S1(Q)` may be infinite; the second summand is a
nonnegative real. -/
noncomputable def Ctilde (σε σ : ℝ) (Q : ℂ → ℂ) : ENNReal :=
  S1 Q + ENNReal.ofReal (max (-(1 / 2) * Real.log ((σ / σε) / ‖Q 0‖)) 0)

/-- **Partial sums of a complex coefficient sequence** `∑_{n < N} a_n`. -/
def partialSumC (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, a n

/-- **Inventory variance (8) for an arbitrary coefficient sequence, in `ℝ≥0∞`**:
`σ²_I(a) = σ_ε² (1 + ∑_{n≥1} |∑_{k=0}^{n−1} a_k − 1|²)`, p.11.

**Formalization Note** Used for sequences not known to lie in `Ψ̃` (Lemma 3), where the series may
diverge; the value is then `∞`. For real `ψ ∈ Ψ̃` it equals `ENNReal.ofReal (invVar σ_ε ψ)`. By
Parseval's identity it equals the frequency-domain form (37). -/
noncomputable def invVarE (σε : ℝ) (a : ℕ → ℂ) : ENNReal :=
  ENNReal.ofReal (σε ^ 2) * (1 + ∑' n, ‖partialSumC a (n + 1) - 1‖ₑ ^ 2)

/-- **Kolmogorov's expression (26) for a complex coefficient sequence**:
`σ_ε² exp((1/2π) ∫_{−π}^{π} log |ψ̃(e^{−iλ})|² dλ)`. For real coefficients this is `nsVar`
(`nsVarC σε (ofRealSeq ψ) = nsVar σε ψ` by definition). -/
noncomputable def nsVarC (σε : ℝ) (a : ℕ → ℂ) : ℝ :=
  σε ^ 2 * Real.exp ((1 / (2 * Real.pi)) *
    ∫ lam in (-Real.pi)..Real.pi, Real.log (‖boundary a lam‖ ^ 2))

end InfoShareH2



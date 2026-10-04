-- Prove2me | Definitions.Def_MarkovChain_HeatKernels
-- name    : MarkovChain_HeatKernels
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-04T11:09:36.974292+00:00
-- url     : https://prove2.me/theorems/a50f7290-1026-4f86-a62f-438c4b87e8c9
-- title:
--   Erschler–Zheng, pp. 18, 24, 49–52 — Dirichlet eigenvalues, isoperimetric profiles and heat kernels of Markov kernels
-- statement:
--   Definitions for the Markov-chain and heat-kernel arguments of A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), cited with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2): the Green function (p. 18); the Dirichlet form, Dirichlet eigenvalues, the $\ell^2$-isoperimetric profile and the size of a boundary (p. 24); and the heat kernel of a jump kernel, its near and far parts, the Davies quantity and the Nash inequality (pp. 49–52).
--
--   Conventions shared by all the definitions:
--
--   - A kernel is a real-valued function `J : X → X → ℝ` on an arbitrary type `X`, and a weight is a function `π : X → ℝ`. No definition here asks a kernel to be non-negative or stochastic. The statements that use them take `X` countable and assume `DurrettProbability.IsTransition` from the [Durrett Markov chain definitions](https://prove2.me/theorems/b90972d5-610c-46f2-b94c-2a4dcd6fa18f): $P(x,y) \ge 0$, and every row of $P$ is summable with $\sum_y P(x,y) = 1$. The $n$-step kernel $P^n$ is `DurrettProbability.stepProb P n` from the same bundle: $P^0(x,y)$ is $1$ if $x = y$ and $0$ otherwise, and $P^{n+1}(x,y) = \sum_z P(x,z)P^n(z,y)$.
--   - Sums over `X`, over $X \times X$ and over $\mathbb N$ are unconditional sums of real numbers, and a family that is not absolutely summable has sum $0$ (Mathlib’s convention). Under the hypotheses of the statements that use these definitions, the sums that occur converge. Quantities that can be infinite take values in $[0, \infty]$ instead: `green`, `carreDuChamp`, `daviesSq` and `supNorm`, where each real term enters through its positive part (`ENNReal.ofReal`).
--   - An infimum of real numbers (`sInf`) is $0$ for a set that is empty or not bounded below. So the Dirichlet eigenvalue of the empty set is $0$ here, where the paper’s would be $+\infty$. The statements assume the sets non-empty and the weight positive, which makes each such infimum a genuine one.
--   - Several definitions take `DecidableEq X`, used only to decide the cases $x = y$; their values do not depend on the instance.
--
--   The definitions:
--
--   - `IsSymmetric J`: $J(x,y) = J(y,x)$ for all $x, y$. Erschler and Zheng work with “a symmetric transition kernel on a countable set $X$” (p. 49). For a kernel with counting measure this is reversibility with respect to $\pi \equiv 1$.
--   - `IsReversible P π`: $\pi(x)P(x,y) = \pi(y)P(y,x)$ for all $x, y$, as on p. 24: “We assume that $P$ is reversible with respect to $\pi$, that is $\pi(x)P(x,y) = \pi(y)P(y,x)$.” Nothing is asked of $\pi$; the statements add $\pi > 0$.
--   - `green P x y`: the Green function $G_P(x,y) = \sum_{n \ge 0} P^n(x,y)$, a value in $[0, \infty]$ that may be $\infty$. On p. 18: “The Green function $\mathbf G_{P_\mu}(x,y)$ of the $P_\mu$-random walk is $\mathbf G_{P_\mu}(x,y) = \sum_{n=0}^{\infty} P^n_\mu(x,y)$.” The sum starts at $n = 0$. It is the quantity bounded in Erschler and Zheng’s Proposition 7.11 (p. 42).
--   - `dirichletForm P π f`: $\mathcal E_P(f) = \frac12\sum_{x,y\in X}(f(x)-f(y))^2P(x,y)\pi(x)$ for real $f$, as on p. 24: “The Dirichlet form of $P$ is defined by $\mathcal E_P(f) = \frac12\sum_{x,y\in X}(f(x)-f(y))^2P(x,y)\pi(x)$.” It is one sum over the ordered pairs of $X \times X$. With the weight `fun _ => 1` it is the form $\mathcal E_J(f,f) = \frac12\sum_{x,y}(f(x)-f(y))^2J(x,y)$ of a kernel with counting measure, which pp. 51–52 use.
--   - `normSq π f`: $\|f\|^2_{\ell^2(\pi)} = \sum_x f(x)^2\pi(x)$ (p. 24: “Denote by $\|f\|_{\ell^2(\pi)}$ the $\ell^2$-norm of $f$ with respect to the measure $\pi$.”). With the weight $1$ it is $\|f\|_2^2$.
--   - `dirichletEigenvalue P π Ω`: for a finite set `Ω : Finset X`, the infimum of $\mathcal E_P(f)$ over the real functions $f$ that vanish outside $\Omega$ and have $\|f\|^2_{\ell^2(\pi)} = 1$. On p. 24: “Given a finite subset $\Omega \subset X$, denote by $\lambda_1(\Omega)$ the smallest Dirichlet eigenvalue: $\lambda_1(\Omega) = \inf\{\mathcal E_P(f) : \mathrm{supp} f \subseteq \Omega,\ \|f\|_{\ell^2(\pi)} = 1\}$.” When $\pi \le 0$ on all of $\Omega$ (for instance when $\Omega$ is empty), no $f$ qualifies and the value is $0$.
--   - `isoperimetricProfile P π v`: the $\ell^2$-isoperimetric profile $\Lambda_P(v)$, the infimum of $\lambda_1(\Omega)$ over the finite non-empty $\Omega$ with $\sum_{x\in\Omega}\pi(x) \le v$. On p. 24: “The best possible choice of the function $\Lambda$ is defined as the $\ell^2$-isoperimetric profile $\Lambda_P$ of $P$, $\Lambda_P(v) := \inf\{\lambda_1(\Omega) : \Omega \subset X \text{ and } \pi(\Omega) \leqslant v\}$.” The sets are finite because $\lambda_1$ is defined for finite sets, and non-empty because the empty set, whose eigenvalue would be $+\infty$ in the paper and does not affect the infimum there, has the value $0$ here. The profile is built from Dirichlet eigenvalues (a Faber–Krahn profile); no boundary quantity enters it. Its value is $0$ when no set qualifies.
--   - `boundarySize P π Ω`: $|\partial_P\Omega| = \sum_{x\in\Omega}\sum_{y\notin\Omega}\pi(x)P(x,y)$, the flow out of the finite set $\Omega$. On p. 24: “where $|\partial_P\Omega| = \sum_{x\in\Omega,y\in\Omega^c}\pi(x)P(x,y)$ is the size of the boundary of $\Omega$ with respect to $(P,\pi)$.” The inner sum runs over the complement of $\Omega$ as a subtype.
--   - `uniformize J`: the kernel $J(x,y) + \mathbf 1_{x=y}\bigl(1 - \sum_z J(x,z)\bigr)$, that is, $J$ with the deficit of each row added on the diagonal. It equals $J$ when $J$ is a transition kernel. When $J \ge 0$ has summable rows with sums at most $1$, it is a transition kernel that agrees with $J$ off the diagonal. It is used only to define `heatKernel`.
--   - `heatKernel J t x y`: defined as the series $p(t,x,y) = \sum_{n\ge0}e^{-t}\frac{t^n}{n!}U^n(x,y)$, where $U$ is `uniformize J`. Erschler and Zheng write on p. 49: “Let $J(x,y)$ be a symmetric transition kernel on a countable set $X$. For technical reasons, it is more convenient to consider continuous time random walk. Let $P_t$ be the associated heat semigroup and $p(t,x,y)$ its transition density.” On p. 51: “Let $p_R(t,x,y)$ be transition density of the jumping process with jump kernel $J_1^R$.” The measure on $X$ is the counting measure, so a transition density is a transition probability. For a transition kernel $J$, $U = J$, and the series is the transition function $e^{t(J-I)}$ of the walk that jumps according to $J$ at the times of a rate-one Poisson clock; this is the continuous-time kernel $\mathcal P_t$ of T. Delmotte, Rev. Mat. Iberoam. 15 (1999) 181–232, [doi:10.4171/RMI/254](https://doi.org/10.4171/RMI/254), p. 186 (see `Delmotte.stepProb_le_mul_heatKernel_of_le_diag`). The near part $J^R_1$ (below) of a transition kernel has rows summing to at most $1$, and uniformizing turns the missing mass, the jumps longer than $R$, into staying put. The series is then $e^{t(U-I)}$, whose generator $f \mapsto \sum_y J^R_1(x,y)(f(y)-f(x))$ is that of the jumping process with jump kernel $J^R_1$, which gives Erschler and Zheng’s $p_R$. The definition is the series itself and asserts nothing about semigroups. It accepts any real $t$; the statements use $t > 0$, except `Delmotte.stepProb_le_mul_heatKernel_of_le_diag`, which takes integer $t \ge 0$.
--   - `IsMetric ρ`: $\rho : X \to X \to \mathbb R$ with $\rho(x,x) = 0$, $\rho(x,y) = 0 \Rightarrow x = y$, $\rho(x,y) = \rho(y,x)$ and $\rho(x,z) \le \rho(x,y) + \rho(y,z)$ (p. 49: “let $\rho$ be a metric on $X$”). Distances are finite real numbers, and non-negativity follows from the four conditions.
--   - `nearPart J ρ R` and `farPart J ρ R`: $J^R_1(x,y) = J(x,y)\mathbf 1_{\{\rho(x,y)\le R\}}$ and $J^R_2(x,y) = J(x,y)\mathbf 1_{\{\rho(x,y)>R\}}$. On p. 51: “First split the jumping kernel $J$ into two parts: $J_1^R(x,y) = J(x,y)\mathbf 1_{\{\rho(x,y)\leqslant R\}}$ and $J_2^R(x,y) = J(x,y)\mathbf 1_{\{\rho(x,y)>R\}}$.” Pairs at distance exactly $R$ belong to the near part, and $J = J^R_1 + J^R_2$. Here $\rho$ may be any function.
--   - `carreDuChamp J f x`: $\Gamma(f,f)(x) = \sum_y (f(y)-f(x))^2J(x,y)$, a value in $[0,\infty]$. This is the quantity of p. 52, “$\Gamma_R(f,g)(x) = \sum_{y\in X}(f(y)-f(x))(g(y)-g(x))J_1^R(x,y)$”, on the diagonal $g = f$, which is the only case the Davies quantity uses, and with a general kernel in place of $J^R_1$. There is no factor $\frac12$, as in the paper; the carré du champ of E. A. Carlen, S. Kusuoka and D. W. Stroock, Ann. Inst. H. Poincaré Probab. Statist. 23 (1987) 245–287 (no DOI; [Numdam](https://www.numdam.org/item/AIHPB_1987__23_S2_245_0/)), (3.7), p. 265, carries one (see `CarlenKusuokaStroock.heatKernel_le_exp_davies`). It takes values in $[0,\infty]$ so that a divergent row gives $\infty$: a real sum would give the junk value $0$ there and make $\Lambda(\psi)^2$ finite where it is infinite.
--   - `daviesSq J ψ`: $\Lambda(\psi)^2 = \max\{\sup_x e^{-2\psi(x)}\Gamma(e^\psi,e^\psi)(x),\ \sup_x e^{2\psi(x)}\Gamma(e^{-\psi},e^{-\psi})(x)\}$, a value in $[0,\infty]$. On p. 52: “$\Lambda_R(\psi)^2 = \max\{\|e^{-2\psi}\Gamma(e^\psi,e^\psi)\|_\infty, \|e^{2\psi}\Gamma(e^{-\psi},e^{-\psi})\|_\infty\}$”, here with a general kernel in place of $J^R_1$. The definition is the square itself; no root is taken.
--   - `supNorm J`: $\|J\|_\infty = \sup_{x,y}J(x,y)$, a value in $[0,\infty]$, each entry entering through its positive part; it appears on p. 51 as $\|J_2^R\|_\infty$ in (7.14). For a non-negative kernel it is the supremum of the entries over all pairs of $X$, and $0$ when $X$ is empty.
--   - `SatisfiesNash J C δ β`: the Nash inequality of p. 51, “$\|f\|_2^{2(1+\beta)} \leqslant C\left(\mathcal E_{J_1^R}(f,f) + \frac{4}{\phi(R)}\|f\|_2^2\right)\|f\|_1^{2\beta}$”, with a general kernel $J$ and constant $\delta$ in place of $J^R_1$ and $4/\phi(R)$: $\bigl(\sum_x f(x)^2\bigr)^{1+\beta} \le C\bigl(\mathcal E_J(f) + \delta\sum_x f(x)^2\bigr)\bigl(\sum_x|f(x)|\bigr)^{2\beta}$ for every finitely supported $f : X \to \mathbb R$, with counting measure. It quantifies over finitely supported $f$ because for $f \notin \ell^1$ the real sum $\sum_x|f(x)|$ takes the junk value $0$, and for $\beta > 0$ the inequality over all $f$ would then fail for every kernel on an infinite $X$. For a symmetric kernel with non-negative entries and row sums at most $1$, $\mathcal E_J(f) \le 2\|f\|_2^2$, so the inequality passes from finitely supported $f$ to every $f \in \ell^1(X)$ by truncation. The powers are real powers, with $0^s = 0$ for $s \ne 0$; the statements take $\beta > 0$.
-- source:
--   A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), pp. 18, 24 and 49–52

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

/-!
# Markov chains on a countable set: Dirichlet forms, isoperimetric profiles and heat kernels

Definitions for kernels `X → X → ℝ` on a state space `X`, taken from A. Erschler and T. Zheng,
*Growth of periodic Grigorchuk groups*, arXiv:1802.09077v2 (cited as EZ, with its page numbers),
§3 (p. 18), §5.1 (p. 24) and §7.5 (pp. 49–52). Kernel powers `Pⁿ` and transition kernels are
`DurrettProbability.stepProb` and `DurrettProbability.IsTransition`.

Functions on `X` are real valued; sums over `X` are `tsum`s. Quantities that may be infinite (the
Green function, sup norms) take values in `[0, ∞]`.
-/

open DurrettProbability
open scoped ENNReal

namespace MarkovChain

variable {X : Type*}

/-- A symmetric kernel, `J(x, y) = J(y, x)` (EZ p. 49). -/
def IsSymmetric (J : X → X → ℝ) : Prop := ∀ x y, J x y = J y x

/-- `P` is reversible with respect to `π`: `π(x)P(x, y) = π(y)P(y, x)` for all `x, y` (EZ p. 24). -/
def IsReversible (P : X → X → ℝ) (π : X → ℝ) : Prop := ∀ x y, π x * P x y = π y * P y x

/-- The Green function `G_P(x, y) = ∑_{n ≥ 0} Pⁿ(x, y)` (EZ p. 18), a value in `[0, ∞]`. -/
noncomputable def green [DecidableEq X] (P : X → X → ℝ) (x y : X) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (stepProb P n x y)

/-- The Dirichlet form `ℰ_P(f) = ½ ∑_{x,y ∈ X} (f(x) − f(y))² P(x, y) π(x)` (EZ p. 24). -/
noncomputable def dirichletForm (P : X → X → ℝ) (π : X → ℝ) (f : X → ℝ) : ℝ :=
  (1 / 2) * ∑' p : X × X, (f p.1 - f p.2) ^ 2 * P p.1 p.2 * π p.1

/-- The squared norm `‖f‖²_{ℓ²(π)} = ∑_x f(x)² π(x)` (EZ p. 24). -/
noncomputable def normSq (π : X → ℝ) (f : X → ℝ) : ℝ := ∑' x, f x ^ 2 * π x

/-- The smallest Dirichlet eigenvalue of a finite set `Ω` (EZ p. 24):
`λ₁(Ω) = inf {ℰ_P(f) : supp f ⊆ Ω, ‖f‖_{ℓ²(π)} = 1}`. -/
noncomputable def dirichletEigenvalue (P : X → X → ℝ) (π : X → ℝ) (Ω : Finset X) : ℝ :=
  sInf {e | ∃ f : X → ℝ, (∀ x ∉ Ω, f x = 0) ∧ normSq π f = 1 ∧ dirichletForm P π f = e}

/-- The `ℓ²`-isoperimetric profile (EZ p. 24): `Λ_P(v) = inf {λ₁(Ω) : π(Ω) ≤ v}`, the infimum
taken over finite non-empty sets `Ω`. -/
noncomputable def isoperimetricProfile (P : X → X → ℝ) (π : X → ℝ) (v : ℝ) : ℝ :=
  sInf {e | ∃ Ω : Finset X, Ω.Nonempty ∧ ∑ x ∈ Ω, π x ≤ v ∧ dirichletEigenvalue P π Ω = e}

/-- The size of the boundary of a finite set `Ω` with respect to `(P, π)` (EZ p. 24):
`|∂_P Ω| = ∑_{x ∈ Ω, y ∉ Ω} π(x) P(x, y)`. -/
noncomputable def boundarySize (P : X → X → ℝ) (π : X → ℝ) (Ω : Finset X) : ℝ :=
  ∑ x ∈ Ω, ∑' y : {y // y ∉ Ω}, π x * P x y

/-- The kernel `J` with the mass `1 − ∑_y J(x, y)` added at `(x, x)`; used to define
`heatKernel`. -/
noncomputable def uniformize [DecidableEq X] (J : X → X → ℝ) : X → X → ℝ :=
  fun x y => J x y + if x = y then 1 - ∑' z, J x z else 0

/-- The heat kernel `p(t, x, y)` of the jump kernel `J` (EZ pp. 49–51), defined as the series
`e^{−t} ∑_{n ≥ 0} (tⁿ / n!) Uⁿ(x, y)`, where `U = uniformize J`. -/
noncomputable def heatKernel [DecidableEq X] (J : X → X → ℝ) (t : ℝ) (x y : X) : ℝ :=
  ∑' n : ℕ, Real.exp (-t) * t ^ n / n.factorial * stepProb (uniformize J) n x y

/-- `ρ` is a metric on `X` (EZ p. 49). -/
structure IsMetric (ρ : X → X → ℝ) : Prop where
  self_eq : ∀ x, ρ x x = 0
  eq_of_eq_zero : ∀ x y, ρ x y = 0 → x = y
  symm : ∀ x y, ρ x y = ρ y x
  triangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z

/-- The part of `J` of range at most `R` (EZ p. 51): `J^R_1(x, y) = J(x, y) 1{ρ(x, y) ≤ R}`. -/
noncomputable def nearPart (J : X → X → ℝ) (ρ : X → X → ℝ) (R : ℝ) : X → X → ℝ :=
  fun x y => if ρ x y ≤ R then J x y else 0

/-- The part of `J` of range greater than `R` (EZ p. 51): `J^R_2(x, y) = J(x, y) 1{ρ(x, y) > R}`. -/
noncomputable def farPart (J : X → X → ℝ) (ρ : X → X → ℝ) (R : ℝ) : X → X → ℝ :=
  fun x y => if R < ρ x y then J x y else 0

/-- `Γ(f, f)(x) = ∑_y (f(y) − f(x))² J(x, y)` (EZ p. 52, `Γ_R(f, g)` with `g = f` and a general
kernel `J` in place of `J^R_1`), a value in `[0, ∞]`. -/
noncomputable def carreDuChamp (J : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ∑' y, ENNReal.ofReal ((f y - f x) ^ 2 * J x y)

/-- `Λ(ψ)² = max {‖e^{−2ψ} Γ(e^ψ, e^ψ)‖_∞, ‖e^{2ψ} Γ(e^{−ψ}, e^{−ψ})‖_∞}` (EZ p. 52, `Λ_R(ψ)²`
with a general kernel `J` in place of `J^R_1`), a value in `[0, ∞]`. -/
noncomputable def daviesSq (J : X → X → ℝ) (ψ : X → ℝ) : ℝ≥0∞ :=
  max (⨆ x, ENNReal.ofReal (Real.exp (-2 * ψ x)) * carreDuChamp J (fun y => Real.exp (ψ y)) x)
    (⨆ x, ENNReal.ofReal (Real.exp (2 * ψ x)) * carreDuChamp J (fun y => Real.exp (-ψ y)) x)

/-- `‖J‖_∞ = sup_{x,y} J(x, y)` (EZ p. 51), a value in `[0, ∞]`. -/
noncomputable def supNorm (J : X → X → ℝ) : ℝ≥0∞ := ⨆ x, ⨆ y, ENNReal.ofReal (J x y)

/-- The Nash inequality with constants `C`, `δ` and exponent `β` for the kernel `J` (EZ p. 51):
`‖f‖₂^{2(1+β)} ≤ C (ℰ_J(f, f) + δ ‖f‖₂²) ‖f‖₁^{2β}` for every finitely supported `f : X → ℝ`,
the norms and the Dirichlet form taken with respect to the counting measure. -/
def SatisfiesNash (J : X → X → ℝ) (C δ β : ℝ) : Prop :=
  ∀ f : X → ℝ, (Function.support f).Finite →
    normSq (fun _ => 1) f ^ (1 + β) ≤
      C * (dirichletForm J (fun _ => 1) f + δ * normSq (fun _ => 1) f) * (∑' x, |f x|) ^ (2 * β)

end MarkovChain



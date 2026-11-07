-- Prove2me | Definitions.Def_StationarityTest_Lindbladian
-- name    : StationarityTest_Lindbladian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:13.144977+00:00
-- url     : https://prove2.me/theorems/fb8840b9-c133-4842-ba6d-0904e55918c3
-- title:
--   The operator Fourier transform, the [CKG23] Lindbladian $\mathcal L_{G,a}$, its dual $\mathcal L^\dagger$ and the stationarity test
-- statement:
--   Fix a Hamiltonian $G$, an inverse temperature $\beta>0$ and a self-adjoint jump operator $A$. With the Gaussian filter $f_\sigma(t)=e^{-\sigma^2t^2}\sqrt{\sigma\sqrt{2/\pi}}$, the **operator Fourier transform** and its time evolution are
--
--   $$\hat A_{G,\sigma}(\omega)=\frac1{\sqrt{2\pi}}\int_{-\infty}^\infty e^{iGt}Ae^{-iGt}e^{-i\omega t}f_\sigma(t)\,dt,\qquad \hat A_{G,\sigma}(\omega,t)=e^{iGt}\hat A_{G,\sigma}(\omega)e^{-iGt}.$$
--
--   With the shifted Metropolis weight $\gamma(\omega)=\exp(-\beta\max(\omega+\beta\sigma^2/2,0))$ and $c(t)=1/(\beta\sinh(2\pi t/\beta))$, the [CKG23] **Lindbladian** is
--
--   $$\mathcal L_{G,a}[X]=-i[C_a,X]+\int_{-\infty}^\infty\gamma(\omega)\Big(\hat A(\omega)X\hat A(\omega)^\dagger-\tfrac12\{\hat A(\omega)^\dagger\hat A(\omega),X\}\Big)d\omega,$$
--
--   with coherent part
--
--   $$C_a=\int_0^\infty c(t)\big(Q(t)-Q(-t)\big)dt,\qquad Q(t)=\int\gamma(\omega)\hat A(\omega,t)^\dagger\hat A(\omega,t)\,d\omega.$$
--
--   Throughout $\sigma=\beta^{-1}$. For a set $A$ of Pauli jumps, $\mathcal L_{G,A}=\sum_{a\in A}\mathcal L_{G,a}$, and $\mathcal L_{G,i}=\mathcal L_{G,S_i}$. The dual $\mathcal L^\dagger$ is defined by $\operatorname{tr}[\mathcal L^\dagger[O]Y]=\operatorname{tr}[O\,\mathcal L[Y]]$. The **stationarity test** is
--
--   $$\mathrm{Test}_A[O,G;\sigma]=\operatorname{Tr}\big[\sigma\,\mathcal L^\dagger_{G,A}[O]\big],$$
--
--   with $\mathrm{Test}_a$ for one jump and $\mathrm{Test}_i=\mathrm{Test}_{S_i}$. The superoperator norm is $\|N\|_{\infty-\infty}=\sup_{\|O\|\le1}\|N[O]\|$ in operator norm.
--
--   The test is the paper's central primitive: it is evaluated on samples of $\rho_H$ and vanishes when the guess $G$ equals $H$.
--
--   **Formalization Note** Operator integrals are entrywise integrals. The kernel $c(t)$ is not integrable at $t=0$, so (41) is a principal value. It is written in the symmetrized form (255) that the paper uses, whose integrand is bounded near $0$ and decays. $\mathcal L^\dagger[O]$ has entries $\operatorname{tr}[O\,\mathcal L[|z\rangle\langle y|]]$. For a Hermiticity-preserving $\mathcal L$ this trace dual agrees with the Hilbert–Schmidt adjoint.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Definition 2.10, (31)–(32), p.16; Definition 2.17, (40)–(43), p.17; Lemma 2.18, p.17; Definition 3.1, (53), pp.19–20; (249)–(255), pp.58–59

import Definitions.Def_StationarityTest_Pauli

open Matrix MeasureTheory

namespace StationarityTest

/-!
# The operator Fourier transform, the [CKG23] Lindbladian and the stationarity test

T. Bergamaschi, *The stationarity test*, arXiv:2610.01074 (held file sha256 0b7e46fb…),
Definition 2.10, (31)–(32), p.16; Definition 2.17, (40)–(43), p.17; Lemma 2.18, p.17;
Definition 3.1, (53), pp.19–20; Definition 1.1, (3), p.4; proof of Lemma A.4, (249)–(255),
pp.58–59.

**Formalization Note.** Integrals of operator-valued functions are taken entrywise (`matInt`),
which equals the Bochner integral whenever the integrand is integrable, as all integrands here
are (Gaussian filters). `e^{iGt}` is the matrix exponential. The coherent term (41) has the
kernel `c(t) = 1/(β sinh(2πt/β))`, which is not integrable at `t = 0`: (41) is a principal value.
It is written in the symmetrized form the paper itself uses in (255),
`C_a = ∫_0^∞ c(t) (Q(t) − Q(−t)) dt` with `Q(t) = ∫ γ(ω) Â(ω,t)† Â(ω,t) dω`, whose integrand is
bounded near `0` and decays exponentially. `L†` is the trace dual of `L`,
`tr[L†[O] Y] = tr[O L[Y]]` for all `Y`, defined entrywise by `L†[O]_{yz} = tr[O L[|z⟩⟨y|]]`. The
superoperator norm `‖N‖_{∞−∞}` is the supremum of `‖N[O]‖` over `‖O‖ ≤ 1`, both operator
(spectral) norms; for a linear `N` the set is nonempty and bounded.
-/

variable {n q : ℕ}

/-- The entrywise integral `∫ f(t) dt` of an operator-valued function. -/
noncomputable def matInt (f : ℝ → Op n q) : Op n q :=
  Matrix.of fun y z => ∫ t, f t y z

/-- The entrywise integral `∫_S f(t) dt` over a set `S ⊆ ℝ`. -/
noncomputable def matIntOn (S : Set ℝ) (f : ℝ → Op n q) : Op n q :=
  Matrix.of fun y z => ∫ t in S, f t y z

/-- (32): the Gaussian filter `f_σ(t) = e^{−σ²t²} √(σ √(2/π))`. -/
noncomputable def filterF (σ t : ℝ) : ℝ :=
  Real.exp (-(σ ^ 2 * t ^ 2)) * Real.sqrt (σ * Real.sqrt (2 / Real.pi))

/-- The Heisenberg evolution `e^{iGt} A e^{−iGt}`. -/
noncomputable def heis (G : Op n q) (t : ℝ) (A : Op n q) : Op n q :=
  NormedSpace.exp ((Complex.I * t) • G) * A * NormedSpace.exp ((-(Complex.I * t)) • G)

/-- Definition 2.10, (31): the operator Fourier transform
`Â_{G,σ}(ω) = (2π)^{−1/2} ∫ e^{iGt} A e^{−iGt} e^{−iωt} f_σ(t) dt`. -/
noncomputable def oft (G : Op n q) (σ : ℝ) (A : Op n q) (ω : ℝ) : Op n q :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
    matInt fun t => (Complex.exp (-(Complex.I * ω * t)) * (filterF σ t : ℂ)) • heis G t A

/-- (42): `Â_{G,σ}(ω, t) := e^{iGt} Â_σ(ω) e^{−iGt}`. -/
noncomputable def oftT (G : Op n q) (σ : ℝ) (A : Op n q) (ω t : ℝ) : Op n q :=
  heis G t (oft G σ A ω)

/-- (43): the shifted-Metropolis weight `γ_M(ω) = exp(−β max(ω + βσ²/2, 0))`. -/
noncomputable def gammaM (β σ ω : ℝ) : ℝ :=
  Real.exp (-(β * max (ω + β * σ ^ 2 / 2) 0))

/-- (42): `c(t) := 1/(β sinh(2πt/β))`. -/
noncomputable def cKernel (β t : ℝ) : ℝ :=
  1 / (β * Real.sinh (2 * Real.pi * t / β))

/-- `Q(t) := ∫ γ(ω) Â(ω, t)† Â(ω, t) dω` (proof of Lemma A.4, p.58). -/
noncomputable def cohQ (G : Op n q) (β σ : ℝ) (A : Op n q) (t : ℝ) : Op n q :=
  matInt fun ω => ((gammaM β σ ω : ℝ) : ℂ) • ((oftT G σ A ω t)ᴴ * oftT G σ A ω t)

/-- (41), as the principal value (255): `C_a = ∫_0^∞ c(t) (Q(t) − Q(−t)) dt`. -/
noncomputable def coherent (G : Op n q) (β σ : ℝ) (A : Op n q) : Op n q :=
  matIntOn (Set.Ioi 0) fun t => ((cKernel β t : ℝ) : ℂ) • (cohQ G β σ A t - cohQ G β σ A (-t))

/-- Definition 2.17, (40): the [CKG23] Lindbladian of a single jump `A` at energy width `σ`,
`L_{G,a}[X] = −i[C_a, X] + ∫ γ(ω)(Â(ω) X Â(ω)† − ½{Â(ω)†Â(ω), X}) dω`. -/
noncomputable def lindbladSigma (G : Op n q) (β σ : ℝ) (A : Op n q) (X : Op n q) : Op n q :=
  (-Complex.I) • (coherent G β σ A * X - X * coherent G β σ A) +
    matInt fun ω => ((gammaM β σ ω : ℝ) : ℂ) •
      (oft G σ A ω * X * (oft G σ A ω)ᴴ -
        (1 / 2 : ℂ) • ((oft G σ A ω)ᴴ * oft G σ A ω * X + X * ((oft G σ A ω)ᴴ * oft G σ A ω)))

/-- The Lindbladian `L_{G,a}` with the paper's choice `σ := β^{−1}` (p.17, "Henceforth"). -/
noncomputable def lindblad (G : Op n q) (β : ℝ) (A : Op n q) : Op n q → Op n q :=
  lindbladSigma G β β⁻¹ A

/-- `L_{G,A} := Σ_{a∈A} L_{G,a}` for a set `A` of Pauli jumps (Definition 3.1). -/
noncomputable def lindbladSet (G : Op n q) (β : ℝ) (A : Finset (PauliString n q)) :
    Op n q → Op n q :=
  fun X => ∑ a ∈ A, lindblad G β a.mat X

/-- `L_{G,i} := Σ_{a∈S_i} L_{G,a}`, all single-site Pauli jumps on site `i` (p.17). -/
noncomputable def lindbladSite (G : Op n q) (β : ℝ) (i : Fin n) : Op n q → Op n q :=
  lindbladSet G β (singleSite i)

/-- The trace dual `N†` of a superoperator: `tr[N†[O] Y] = tr[O N[Y]]` for all `Y` when `N` is
linear; entrywise `N†[O]_{yz} = tr[O N[|z⟩⟨y|]]`. -/
noncomputable def adjointSO (N : Op n q → Op n q) (O : Op n q) : Op n q :=
  Matrix.of fun y z => trace (O * N (Matrix.single z y 1))

/-- Definition 3.1, (53): `Test_A[O, G; σ] := Tr[σ L†_{G,A}[O]]`. -/
noncomputable def testSet (A : Finset (PauliString n q)) (β : ℝ) (O G σ : Op n q) : ℂ :=
  trace (σ * adjointSO (lindbladSet G β A) O)

/-- Definition 3.1: `Test_a`, the test for a single jump `a`. -/
noncomputable def testJump (a : PauliString n q) (β : ℝ) (O G σ : Op n q) : ℂ :=
  trace (σ * adjointSO (lindblad G β a.mat) O)

/-- Definition 1.1, (3) and Definition 3.1: `Test_i = Test_{S_i}`, the sum over the single-site
Pauli jumps on site `i`. -/
noncomputable def testSite (i : Fin n) (β : ℝ) (O G σ : Op n q) : ℂ :=
  testSet (singleSite i) β O G σ

/-- `‖N‖_{∞−∞} = sup_{‖O‖ ≤ 1} ‖N[O]‖`, the operator-to-operator norm of a superoperator
(Lemma 2.18), with the spectral norm `QAlgorithms.specNorm` on both sides. -/
noncomputable def superNorm (N : Op n q → Op n q) : ℝ :=
  sSup {r : ℝ | ∃ O : Op n q, QAlgorithms.specNorm O ≤ 1 ∧ r = QAlgorithms.specNorm (N O)}

end StationarityTest


